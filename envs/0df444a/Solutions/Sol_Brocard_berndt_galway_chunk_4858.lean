-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4858
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T13:58:02.373401+00:00
-- url     : https://prove2.me/submissions/6e5ab757-daf6-4482-a238-cf5c1e5b9fbb

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 873561151 ≤ n < 873741007 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 873562401 1250 873561151 873561181
    0x170c0a05060901020a0b070219112704120513030506090d2115050a0b0a030b18010302040e0a021c0323030c0a02070308030705030108160302090a020903071706 70
    0x358081c600030042c1d4400c60380e01040c00801709500c40b0f85556141c882c0301d012840d010501083e00d1450140020601c10b00414100c0903925000403208411403020060484d050000d20700a0494800480e0011500103800340001d2148081c0742e1400508000080440041510075540161941e0b040300080c8105420203004091013094682403842c0070f0328400d07000b000803c00400e509080503503a0380102010500d280c0c4040001c1c20f0041190b4102d80d00c59460f50096407007403501501180c0b41054180060a006881f03141d03070b404418803501260b03c0d41d028080a406000b280d00e0340c600424040700c0060380c601c202110051040c0b040c181c0380501d1031801400a10040d4000007a084007404180000321114040720340c03244140503c141c542c0383d011000c0e442c01696400082900700040108840258000051030484d90f4071000c0711008900140fa4442c3c2c1e01c620f020180d0030103860070005e04692400c0c0c008103000580541242c0a1a036101c07082c40e846041540c50100e207812140c1480020407601c5a5 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 873563651 1250 873562401 873562409
    0x702010e0415060f1809140a0c0804120509090c0a110118031407240f0c2f030d0b0103051602031c02091929040b090604170c0a 56
    0x108110100c0103281220030003544110020010444c2c00300e614684510321490035003505540d0f4a043c01d40340c0106001030100642c6c0b614007200c1180014a010800e030040d002c1141ca03a447d0400300d9102c689620b010711103034a2025040c010100422107a6858a0120510074001c03510401d4a5010543e40100600d00a030b410300e8541e030400300306000b918000c603a903000d6194981800c21a01601c2180346803c2e01481c28003500541c00c0046c81c204102c4c25400c1e00000c000c4940741080100b100c1c808031403c40e940c51400074009034404010b02c030315401010803a014020481200c100754402007840a1070741d4040319084103c59200c5c0d544018958040c051941c0040c291f0722001b1050040e058025aa03015044d00010294602c40b01d450207100c00340d040301c0d50618042d00d10315000328541d1030340036201490f02c01e207043e060f50514140e444001c980600d101314207402101d00c3c900f5280100c2d003c0207811202030564800020480000c2c03005d01d0b6411600d2000001e000740000200003400c12240c049144c1c0 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 873564901 1250 873563651 873563659
    0x11116051003110d020723010605100f08060405040c0f03230604080a1d0d05030a1707052709240a0b0a0804140303011806292d0702010e 60
    0xc28102c440e803440f000d031400c1c40704520005849421034280203111581c00d0001c00c140c402c0100d17607502d405406400400170381c0c1042d00c001520501008003143c14180060140001400ca0f902103002071501c1e801054001c0e000b03030703151030f01c03c0d071164050469038105501c104c564804550944022100103c4008404071907580039002501c0d164496a0042c4aa051103c0070040c1c50310000c42824040c846802400c200070b40780810048272490301940d01d501c14a11a001f0a161118248e010801c50440c517108050300c1d500d070390034201031441c440d480100303c00d00c214a5407000e0b070341c0f1080d60320307400091403084804040e440d8112864081c0b00c410380d211500300c10f0184a00c6103051110b21a018103d60741ca080303920700307008031b55120300340715480c0a4402c43d55030b12404004000500000349070002000040303103204c200602665041202c01000490900316044550300703402e400d0081081014005c170b25242c02c01c56444980501d49401010100040d400500501140960075540e20142103100880c0690b = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 873566151 1250 873564901 873564911
    0xf0902010504030320011a1806150a11030f04051309030c020603040f211101150303141306030903030e06040b0612120c07060807140703030506011116051003 69
    0x50002801c511441c00090280b01c8101c00000d00b013256840784005085628008000c2040c0b6400403003600314070700f104140f05107034003010450940301d00b203001402103400a00f40c038041001c0744944140c640000c0d0b00301042c010380003400340c00024240700070030200b05052040ca54643c02e210400004200c1d003091035000c2e51034042c0c40c10001e508072109240998044401c0c50b1030303544515114200ca20441401401042c469103040003200001d0f405006c64255902d52803400c158007501036080b600700482030011540c45e1182000420b0084030500007142c03000d10303918a0180000202003250300e80703610043c0001e9030f40c0c5028085c983e141c8240002100d07000060400c906007910340b090b0b804800b83c078031441043c0c880035205130202c04100d40742c15070180c0c0d1002ca85803100c030018541c692174a07208520104003024009802c0d0f51240304200c8400c206005002c0c204002518110020540106418103003c42c0c1c0b000c582d8100c00801c040801c5006811034400414208028806c201c440300d0303032540c05e040c140 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 873567401 1250 873566151 873566153
    0x20712030806040b06160b040303050604020c0613020f03060112170f072d0c050f090f16020a0212010c0306051207140d0813032603010e04051c050a030f09 68
    0x800c10703940d00404121008039401d44034500181c064416003441d441110480c2c00c00310b08100e206c016a0303101e60700944040020341d94050500085e882108401401c075004400040c0042210720000e80c440ca00180c0404001488200480c1c6445000c0c1c1000301c16041d074000d60001c0100702801c4404101401e041c850400c00801c3c0c80c040140a41c0c1c0004004603410f0240c5080200f1240d04040b01000c0b0b000c80222284060404500150080c05038601a0501103604020307810070004460148800802441140d0764031015414001040c00100e011409111b80007000760381c8a0488001086441c40006468948500003900b15001a030080340101030f010741081c50340b1004680c1c001142c0344e903404c410b460580b82d000038040d6462108024440000420619000c034111910300098034403a24030542048072044080b80001881190164002001c00041c407401e18940d000c2038006200341d00315101d0b1590101103000040c1c010f1201000100e000c81d001171181c0d032500405552141e404401c2060b407031070b = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 873568651 1250 873567401 873567407
    0x2070b04060b100e1c060606030b031b06220e0406020c1e030a18080304150f05040e0411040b030d2c370e10141f0c05031902071203 58
    0x1913221548500c0102503244688000e1864080c4032642c40403040141070703201c41c0007034014207221030414002e03c1001c07055644520040d040c0320b001c510041c42d003070400056050b00d0910007108000c004043c5502180007600305500d070a09806075104000c05602c0e400040300c03c03450080f0104d15011118410040101401d9022040380c004ca0050b00c1c1944103070b040c40e04c001c407030741d0300320307070108646103c0050005401e01420b16000b01d40012580d070b1280720106600110b0b00c0340504c0c060249a2446800031600140804048141002c000b51020030750891b02d00009003090a4072002c10089960140d9a003150b1141102d0000341008410f0000e8030380e4480b002061002d0b94540700311211003000c1d0f4601c120740a15042c044410301e43e800441d204a6251400c12008131001d48500c0c50722080048041586200900c501901010103400c010709036140f20324030780000008840070014408000281c0d0085481440240035200702c0c40d11001c5543d40c5040001d141021aa000e28820788540c3d004100184e4 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 873569901 1250 873568651 873568667
    0x3060509150c090d02031b0a0b03150d11130b030105012111010c12090305060f0c190306090f02070510050408030103060b06040f0602150a0b0a0e0a0f02070b04060b10 73
    0x4070410402e03440707500c480e001c2410a000524081d51520401d0810038999072103600100380c4503016503500c00c4881d51104554040e000988600b68040c0740302c203290303029040c0940e450784180d0140000f2160be090b403201141e401252b4120b1451181e4a0305400402400c0034042c1d130380181407043d00f90766840141040c004140284240003068090440d140e911203a10030b000e08014a508503803a10490608080083c08501c0a807104a505010300000242d5030803250059a02ca003282c20a41844e103044910b0040f600c88480e1540001d15540301c401003040720941c07003000f039801003000c00165100d4050034081e18202810384001e021341d040404000009105030300343c2c1d0441364490004124410351030009a002e0040b5082030410300c03440c1e400064056130024500542c89200c002c070500e07540301c2ca00c0034070a4030070055849070000c41c50b03182041229941102903900c0301820000042088900c100c00c410b90380328110550f0010858410300043c0040c3e84140c11a050048403070718009001e862000d003d0324 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 873571151 1250 873569901 873569911
    0x204180e0f07153911150901180f0f061d0d020d1406071e0807081602010902030d0504180203060f060903010e0a0302071a030903030a020304050f160306050915 70
    0x809075601c1118854880441501c518100130030000168600350109211000288815140903403800c15604142c240322151900305c881c03129080f480c00c0089001501c3c1d01c0300c4003e944a01040190000403013403103100c00000986040b4071034145947c50b0007002014003405d41901e10b07140d0010025118180e580c017000b100c203030b541540c1138044c4050a080090802d1031144144a0a02455080202890740301c2282e041c40c1c1002d00540c3c041d501384080032078001e1011680e14021030700e182e0120b40030201040e50310407400e00034800410305880c107901007424260b0036010800481c801107024005814a0f14040c07005a045400440c01c501c0c0040c000343e208149502401e0069100103410500c2d03403001c4d0000c0001e04807140c2151240d14031071400039511881e034421101107158850200c45100c904a08803801180740780000c50030364480d044c0900082d400a84100c0e040d1150700081060b56500340100c01110f21510209403500e40f850510703506991004122000340d8026101201c1c1c2d1040e141d458079001 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 873572401 1250 873571151 873571157
    0x6050603010512070b12040c06021903111207060c0206160e0108040227040213020a0c1e020a060504081b0d03080601030b03011e0f050f0c0d0204180e0f0715 69
    0x91458103544c18058250404200d40c1d0b000910261100c1c1800006030066119443e442c8050380e6541c4200e888143c0d06041d11100c43c141c1c40c8450100740f18810b0704860103407080940d500702c88261900c3c0303001e5100c0032007241d5580c0c80c0d039905d0307000c5501072010513800076640700040400b81d8601c1300100781d01d01d00803455040c444004085015515072207552502404000c085088100035804d100c0d0301e80b54210b608074400c1c0180e41180541d103417180242c039070402d10303130710f03140300c0c0c00036580d102046c286410410200101d2004240400345c0d03a1005d182005000540b40c1b10740d51428000c80398180249002d2954500004000c0030a0f5a10f81540350007155405d071034603400e951170b0ec00040313024004d0b000002e581513007426a43d5000750041d005a060391015444100003009a1b400e41d401610011104901c1d00100c0000103000307050900c00812004070940001842c140e1503024140403010f02683e0038905070307500c0344030030280142008544003001d9004000c0c04e000c1e00d44001103844200c0c014482c010 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 873573651 1250 873572401 873572419
    0xa2c1e04020c010e07091b080c0f0307030b0a0614040b0c0a0f030c0506010806011a090301060503010c05181906050304030e04050a091e080307030e010b0d050610150e06030c070c06120f060506030105 87
    0x210484406681c80603803015602980d07401d28cc0d800030701401003c5100340c810485140c0c0003880718040c2600d81005078900f00300504180c9010000c2682e80c100312840f0615010340c10070303c13001403400c01040c0300640c400e0b112550002070310708045191900580081d00c0f2a4402001406016214007600410101c0130803c50b0b910602d050100c0c0c05800c103030384826015802d0058203560310341c1000c0544000030190a400111800100c10401c520710945a90029030040203410312809101c1d4004580c854000c1c10881c80c0c0440900105041b00c1c4200d5040415961f28005e410400143e40c0308042040440c100c0301e45180180d88400c03aa51001420785c1d81815501c10005890000039048011003540040442d000c21100382071058580340c003222000707003035003543c08007140d0340450030302d074000b6504c945c3c1d940003d569280090180d240e1010740f0801403008180f0088000580000d81c00015003403a50f501c02c10300600c1541042a91807107010642c03040d00700b00042c003840d00d44105403070440b68112840d1403 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 873574901 1250 873573651 873573661
    0x7060e060912060f0717041208040317010f06030e06071d011404091d070e0601050d0f0f09050d03060302030a02090c0403170a2c1e04020c010e07091b08 67
    0x460440400b4190590f80605001c11565003c0b1040c0241303c0c50440c0c94107001e891052000b12076103c81298003c0c801e541044660300c40783d00c42d411099006100c0c2c10502e800c120503610840050070242c0c8151140c1c20010001c1c421654135000790f0025404c2c03030300242282e0801c500d0150840c00d80c400d1245280401000340b101d0380c0c6c0b05403004040c03060740d5002c0550f0b85032102a118051b00600d00181e0780d00c49058100342c40c032a000920702080b26801d14016980e41c403038500440320f0707501c0112121403203500c60a41030b04000480c8070f0a141050f41000002c1c01e20054904039081030150700380d8805152610408001585012514101b410390440e400a1690755118040c10180261340000d40403e4081908284902d442001085182403584401e401d61604174810850083c0140e0361440c01c01003030200807410300301140e801c0e00e40c052400441d20101c045134045002c07a0042000000507a44501e540745e9942c40c103000913000390106074014408010782680c40f800c0c40c01d81d8080700c0c040102d9900000c1d = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 873576151 1250 873574901 873574909
    0x50301060c06091e0305120610020714040207020a060c02010906050f0a08250f080f150f030f10061e0303020d05030429190e0d0c02010c061d0d0207060e0609 69
    0x209513035241c200c4050131089080c010301303d8000c50000d60700c5140ca0004152245001401c2490342035543e8010a505400c0c9000c00d0282c00c480e030003440d080f940a210307010059031010110405440550740b20040c4400d0f500005000011542c89502441710400c0256003800c0e00700c044802548440c03c000711192994007042c074260000c180f0705060054925800c14510707500041d007040600c500d0ba246045034894000d004050201541c034040c840314600c20081d041d04005000c0e03000380c0f90080aaa01c01400942080d00700413460144844040d43d0b100103009060590341100d4a801d090100501d01b0707400c60360302030361325840d0b1503144c41445000701c0020100b03c03140c01c8950302c1c1c0000390811482c1d1030751103410145d00641034500e102c0f0412151103003961170b82c2510a650a0001000c000c0c6548400900b06440441d1502c1003a810041d1402644011451601401000c400d211640300c142000e061842e904042602e460041150000e01c07003000011707070210740c0c20f03160041103d81580c2c0f041d00030001 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 873577401 1250 873576151 873576173
    0x8030a03110405060706090308010e0709032306010936111c0804030311030c15061201021209010e0a030801300b0a0b0f01090b07030e030a080901020c01050301060c0609 74
    0x380d40c42100050170408201203500701c143c055119032960860350740c94030411086440111084000120b161004001051b580510b040d410780c814542e49030b1460426001504100c405d030071050090707480f00356020a9520010007403001248203140c00c241c801404103c100c07460401d0401401c10106000320001d141d99840b881c440070300349103511000500080c500f0310400e40007480240c01140d40700c1901000d40c8008000c070b84031703554460090a03100480010324078040a0191000b600010100507001d07104e1000d00c0180019000c400c1440313140c0c03409600250139243c984666491b107810a044140c0001c0e00458502d055841c2c088880c3c0d00d52003011a540303031841c080001050103580308420390052140a031103243c00f4100940007444018812001e0101c0041c6d0168114002034000004126107200000038001c042e109240110a90709070f4800070303140441c00d50741134a20b0800000c43c60415a010803046c1c1c603a84003030808900f190b24061000e0520707010403101820b8580c90f2141003040100d0b901d06 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 873578651 1250 873577401 873577409
    0x1a09010503270a030206100b0405182203020a150e0303070c0f0f0305120610020d0302071e120801060825030f0f1406060702210708061e060a08030a031104 68
    0x303ca401110904001b07645510035030702c02c240d01002c0c08010441807414000c407010380d01c010b0a42c0b40a00144561762452000042008806140e2401c4d0a0040002aa046640325000e0390040c45c0c00d100d541000b40780b6405400d90000c155140042d160500c480100503280e00501e9820b0207418100181403041c01e803c200031009000070100e40c10b4108054101025100c00461901080710350390307036001403040704600d504407100581c5c4025442d410403407180d0028840c042c4904a807451800d556165040308440400c011240b0714440c00c00c2400565000540030300405403071911003414140030f009000c414200301200c0800c56010301844481902135044503510841415007000034032140c40d50500202803410003031040030204000b142d07051030640283c2d4a110b800a00080404001c0340d0300c07504403400f100300d02c2c0c800c0c00b44220024806809101d4184186003100c561500070216480208031004014042841040f1061042c460740c20008256a8045140d08000400b80c004850043c400d00407540 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 873579901 1250 873578651 873578653
    0x30c010603030302041503060e0c0f070b0103060902100206010e01052808070501030b150a030b0d0c060806011209030c08130504090602070b130f0605130506101a0901050327 76
    0x400008143d030590060040320500c0d030f4911030f10026000210117a070210300c54500c0303000445002c00c015100f08002803e2a0624901c40752420341c0c0c541d21400840c82c2644165001a5a61045420750600c0040154a0346651001e44029810100c01c6064124103018450052070880c5440c0100c43c3e007401c86908130039070000c0b500384099070f810750300741e03280321034004c0c80d0000381060240340c081d0400426441c082014048070900b04001660120001c1c0550340e10b0342c1e44442c4038020b803404209225007041c042d040590b190061880c000300090142b440b450000c440300d51800c0101008aa0f0081d014503290758002c240541d01ea822058141c0d0340032042e00300a034440e190643c40070412019038000d1403040d06c03c12a04141e0360382c048880d230040803200d60150001d800c980b55071002441551041c4d9001030300b04000345a959007038540525101c81240e43c900c00f1030740e40358240802c980c244102010f00c1101504180340440441c0000c1aa00010340b2181800c003a1615803180c8403600b042081006461034 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 873581151 1250 873579901 873579911
    0x1624050d0e010b120f190c05060304060603061d060406090303020421020406090e060c0d06030f0303050603120f1c1407050a091e03030e040b040f0207020901050d0b060909030c01 78
    0xc0c481c82c001d007102e0202c070b4401c03850080c81a005002c0403603207050200c0380102809115082511111030342c00016012a442d080f56500030442c3d541e0580a940070364054000010010300b94a0503108032100c40070000d42e01241085040d03c2090001901a0702951040001c20500150314080d0042d0085410510b000325004419100e2040d5101501c2c4450303000f110180142a0f80e920550111800860108031940008000808800c00ca000800505500c0e80000801d2070362922001c800b0240507000300c001039160f800f0301240f86420020301c04800550909030b440c0c850f440c2c40000c00c610031516601d2007100c8100d03880132140b803240c0c060214601c031800500035916002d03030000c02544c443c44d44000418000c5001280ca0060348030000001071404030001156421a01c064030580100f020595025440e0300386650503498a000f0040e0006075900056154040f62040017100407050f0003990003402c2c07141000c4040780e5070550701a00030500751050101c6488034000581144526101610a9800c1c2 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 873582401 1250 873581151 873581171
    0x11030106050d11040501080103021002120a03020903100c021009061d0a0210020708031b030d09050705030c03031c050705040909110108090a050624120f1624050d 71
    0x11900804042c00400d40810429446004644080c040c900505002404100c011300050403c00000d211120450046450040e0440c03013403402c550001e25080f001903000700d804211428100310100b0003a00024060003004a0480300a41d00c000304400d140e5441c0e00c4102c00424005c0c66400010000c504607200051000c0280c426aa50840010300304c0c000e2005c00008811103201252540654070700c47e010b1407500040d54091a500307030843c0400c0040b4002040301110f003002d03d100f12540c80c0c0c803500107804014600f1702014140480501d055020ba0810450071100002c013441600c0003001c078000000e1503480d0100c08590380e01a03900541d0041d80f4210b1840f00b80445621100c1405001341e271b07050043d5a03044c01082d19140d528400601c0e80d8800000316031004014001e81c40306114034120085e00404410009545070703605c1d40d440c0d03019084401c2c100c2c600c407030601c4080c4824491410f01c0c60704038580520131000000c0c050700d507000311050448101801c0e202d81e003150201c00300402c0c18803560100c = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 873583651 1250 873582401 873582407
    0x110d1205160f1b0e04080a030902040222050901080d02100e031909030b0a020f0a110123011e031a06010311031512010b0d02012313080d0c0f02040f11030106 69
    0x10b80c40d005204404200360002d5403213000000e080c030499214510f01d041c0208158140c000d0183c0c188200d138015000d103c2e01c400d034116030040303590039131410400303514551030007052104001041c1c00c110015003200d0500400d4030340001d240403410020f18000114135000b8030045007140200714405203000c1c4240240e00d00036a00070803100c141ca008015103801c90321040e024004a02c00d41514850500c414020002c1c00c40c01800840c000e081620004241105014580794446da50440107403c9200500014070040e1421010b80680d0355032440701d08413650847d16081d0141c0040000d007404c8148550000e00c00f030b442074003e6000d00f415680380c10b441c2e0409184a1b00d10007084020340340140d0102000c890280c030140504403081c10080d00f21441d81d880d50b0011520032240302e40003105401c6000c141d905848000d17009041100300700c12a440f4140c01e001b0380500700114081d120ac1001041c00084012415403840c0f1000190f0440b00001c41d41d00c038007a6240500001c10f00e031095450003000005126070 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 873584901 1250 873583651 873583673
    0x5330f01390c1d01050d05070b1603080a090b0c0a0201060545180106031217070e0306010b03090c0d0804090b1903030c150e0a110d1205160f 62
    0x311610303941ca441503e0340c45940401c40505400042c1d03200c0341c0010499800c201c0c40c1d04400600450a035a101e07501d4406000c1540d20402030300e01144d0500034440c0506500c4111160048408042806007070036503140e481c00c10f0b1000d0310000c10034000040d5299524000d5129900406001c1d05001080d412403026440c242480c0d0250081190360485e81102680000c03070488480d910610344152a0301e900010f060100001e602c00341c1e0565880b0b10100200300000032116000c00256100e8400030180140344084100107070005041c000c3c000403020440e0380105920303041d540c01034010341d20f0383c0d14105040d151011036040c02d90400506c200c1c01090000350001041540c1080000b80070101101c0d043c0000001e40c2d41c0c00d200b282c03000c20414400244a0242c000d521070061100e1040c082d0910082d008903401d40c03505200a501511010f0204900c0b000000400d00e400c40300010200d680e03890303100b001d51003400b011080110029a141030203031203071181461260094400710a142c07241c6040d0003145 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 873586151 1250 873584901 873584903
    0xd381806041e1a1e0904060f020705120309070e130807020a150305090c0a05150901051c02090a06140a030c020f031c200a030902011205330f0139 64
    0xd03450004510401e000044d84c20188001030300200340350350f440d00c5881c010450003581c0807255400300200d001044e001c0104000a210810700f03176660f0300740320710400d250502c00e601c4a0462602d030030070404907071290703140d12011681242580c0d69034221440014201d000d150840d80002c01405241516280d00d5032040f403040c1010400c448105440034200088000584202d9522550150248014000c0b43c07003d00156081810118200056040c460710500c01d481e08480d0210f5021a00c0301c004e25051802200401203030902c06222144c072524440e042c801d5a500703006064540341c503000c17402d20805c140c0002a1007002034070f440d40d04c240a01c603000d00c003801e84a0707901c40c04c00c507240e01183c07291140807080e030100361440c43c41c10548900c10307130281482c05400e030306200c0c2003402c01e0004000d5006003803048141c601d41c1e0310401001d5400b0000c0003000e0b0070b5070300c42c0c0011030218030903034a8504040007210001d090803000032550482e200760324280809c0d002580d906000d0000145903525403607003045 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 873587401 1250 873586151 873586159
    0xb0c030a0206060306060d03032c0d0905040606090b0306010c06020c01091a0108071a041d07080f270a0210090608180303010b0d381806041e1a 63
    0x50f00e07600f0400da5503040c2501d900d50300c05001c80884001a0007980000824014148442642094030000010788422600301d1501d5030482c03a800e400c80b507448950440649412a420050a03007040802044030701240101098107000001050329680129020022560310002c155503500440401d40e002c0d10740441c045524042c40c480f140340d400720911510381a240760741c005028552420920502c041c40c8007003c3c1d00204010080842d805203895821004600003244802850501600c010600c51004018940640d415010b01642c80e0840d002c0c2c04820940c1111100324a80300c060040c1800070345a0001d5201031000010400c1c0350308000031804907800c40e10f0b02c100568603c0c0703201c80d50740150b080300c0003a50010001800700c250b0840c003802c0d0345c007040880010340c020400305810b504144110380c100501c0c00380800d484541625401c2d0141001c00381c0350041e1402800017003d10210300680014416515040075a81c01005604408040782940201b4805000284a58598118145012070103 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 873588651 1250 873587401 873587413
    0x90d0213061802090603060d0c0f060206070906020606010c0b100b13080d02060c0421151b0f0512040201030b06030103030905130504050a021002240105130905100b06040b0c030a02 79
    0x1048030603c00d45040d064090402882e540d03441080150b200d00e182130846035500c41c2c00e0080f54101800e00444017604e050340080256091110020b001005654442400c540c0b04408004503039034419990001107520880704c581c42e44440500119100d9039800c41c1c4000040401c0c40300c03401c50800116012141c4003010748200f1821a601213031180c00846d1102907a1100708401c12144d081c0c4241d4081001402d000d0300340314049565031480c01c2c03806110210f44aa101c01002d00071412046c54039585c4039650518103004c0545030310140c107a0184d440d0164221554200190641e4000e81080e403004c40001e1019a0320342e100c3c640500518007900035140540c25480b500f02c3d5a400702d00c15280115004401810f20842541c01c110900e82c0c2c00880f80214062041440340c1c0745103003100008402a0941070b0300b0740d5030400081c0b0030b041011045ca403406900700b0701c081000c282c001c52801004c4c1c0c070314000400c00001348004100c0c035102d40e81c0300045502001604044801010000d08038041c416425121 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 873589901 1250 873588651 873588689
    0x71b05070e0f0421032306090105091303180b0f041802031e0402010c05011d101103160311040308040314060601090941090f0604020402090d021306 65
    0x425002101c00030800801c1d1000c00c202c1101e070b4030b0b0341081c0c04c80703601d40481d01540045440d944640f034030400c01c3c01c85141c0000d200d010320344242e985014040c00d544601d611329107000307080c460301c2441c5c02c081c042c0001c420060002045411000d0081c18030409043c1c0c2d81d452006d072000b0564401e200700e04032151042103000701000c0754000c480c0503103260b110340c169050045507096840c520143c0101d040c082d0703035030184000a0080c000c15401c0c0a40c03d005040400480c4601400d040940c2c0c40c07802a40c1c0b811000510310b9841030305881d0413041a00c0003140c1d980f1106e1056005000d816010316a40c00d002c18004100728040c802041641c1c0300741001c91511000070200d07955214150384290100d2181c05040c030840380d095205240309050201924003420003641ca0028102400c5003c907007240c3c2030410750112900c41102150491340c00c0340140120554081c1c080d0300c4a002410081c459500042c0c03422203030381e800303244030b55894004101203064130382e403281c40c4000c00241c8204410407070a94000c0d8 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 873591151 1250 873589901 873589921
    0xf020106080c062110050a0b0910111f0506010e0301021e0a030b120609010e300d0e01050702010b1c0f0f0b04050d1211070209071b05070e 61
    0x8000c94800c0001400504401420081c090308a184040c4204071040d00440403007a0364510103004500c4510303640e040071b0600003400451603035070308444ca010b20208040081d0b600d07102c6410481c4000c0e40341200b80002d0b00017240d030503d03044201488252105548070700c14504c3d145e126a0040c0400d03210302d00410660b4003414242e0107080c03d041802c05030102c0048035103120030b0003482441c2c00ca24000401d216210000f62208030701c0007188402d0ba00040c100711a17100b0034400c8003603076065a4000c204404035400d03000e03d010100040d503080607000038818100d501c05601a620074240c0c0d00b009011301045030340c0707a40c0240030032221800158241200d90701c107424640e000385078443c1920300c00380d110b460b507444481001d2103000f82140d581000d0a45d40020406000b1918080c0d07200d1000740994854060000b014900303c00402e4480c0340c5000d01c8041d61580000031500700703680c180c035903104540d0f822100381c411003400c801440701403800401d800100300010810f04103440003101a00740584406c0504 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 873592401 1250 873591151 873591161
    0xc0309240c082404060504090807020906040615030b030a060c02011a0a080d0c080705030a090906050f130903020f06010b070b0a11160c0f12230d0e01090b07030c030f0201 75
    0xa09900d82c1e1030b201403003003c00d2180c0c041810078090000728900e56507001080446c1c1c0b46120030341e0050780c042402821403514486840e01b16030112024001e460400c403004044049021200080c19552900c01206031000d10146030301c260001820040c02042070b40c007031b02134600150009281c02d45450003039840e02d080180a801e64912100078410040d2100c8207840c040c142c1c01c8181d54040d014011803000490410080120240030790b513943d00d603407500f45072000ba80c8440e04200c4c07198458080d901483d4a4030780d2480c900c0c03800c4a00104540303c10303080580c107000450319401e280d1b028100011920118880c0109051481581e00614a554143c030410440b600c03080408880070382000346492841c01403898020450140c0d0010090380d64550303041d0790105690b44445600c54410f0180800e02c02c80b0b600c0011001c4500310000750b4201090b0182e40c80390800c0c0703004003d001c040060307960564459050400540a040c45040e501e0300301e802c014002c0c4030740034021800a40104034030317421a44103000f5 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 873593651 1250 873592401 873592411
    0x9040f0c0e190920060d020d0c080112150902010e090403020106080c0906030a03050c0f01050a06091a030a032105010e0901051e0606211501090501020a080d0c0309240c08 75
    0x8081c019000c10752440c0300c0c0c051044540d0340c441c506120b0b9006c013200030700c010000c00108038000282500c10700c0300500a07810584c4019041030340c04410001103049004142520610020b001070a84003602c010b8822600c0c00c200560080d010b0002c1104150b0154420b00954100104840d050540c03c4108030640740215840d41d00f6400003101c9000290144001d0030444108800360703000a00007091540c02c580c800c03180e00991549a0700200b02000700c91084617042c250302c02d01c0d0140c0d01c060002103541c41400c2e0030b008041003a00d20380d0f6103803c121185002c905505150080c425960340b03000c410382900c002d035010071640d4030700004280460407401034031240040200f03545040740e880d04200041d035001038030760f030035900200034110b8075104502980340d00c2100480d07007002958082e1000104030725840d80055040d5802104004007148004095174095410001d004c50407001c44c180440117813841c014014180341e4160042c1c9040c0042540946525414910400240310071100444000741d05a40b = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 873594901 1250 873593651 873593663
    0x121504020a0b0f04050f0d02030307030f120e031207200604110303270607060519200702041a03030f190507030e0108041a01080307050c030304031109040f0c0e1909 72
    0x44104040d041408041c00b5402d001007d008581d00b4a801180c1154840c00b01100001c41022401d1042a003100f00b2a54030880300074200461035420300f55941d00d108a0030601040c1102a00045105114002c4e68410724041d00320a05015000380030107503034500c140c90072178000221076a0030b15039040c00019601d0340c030712100d03060702c000c1040d8400c200c4c680303041034500d13400c00b030108082c40100ea11400783c10b018009041c044031045030140c560608498120885241080b404002084041c649400303941070141c04032000525817606031100c0c2030704404041d00f103416000104007004a00b40c0c8c0c8001e01040d00190600d41024400c082d802c86031071203007040c000d0114400451148a07544110710842e0300902c02c1301e9051000203510300c41045200c00b640400c81513030000801804014040c070050051540030380c020350905040d5502d4014034078004283e03500884c04080010140002c081c01e11680c40d07007216203040c1c80382d00d660a80c04a0042100c00d80203000c060701002d001080c41d84200019550456 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 873596151 1250 873594901 873594907
    0x501091d0601120609060f081902092d01080c01090b0408061308090310051006090302030d21050a0615021f051e2e0605070b06121504020a0b0f 63
    0x401940d881010014000c2c03c550748207408038100c4801d02c42c0f80040c00d405140c3c0304d43c40b480d2034076072031400641814011009481203d90001a100c14880c0ca4000c40d0f455880d800c00103101064160600c038021102941082074000020b070782c1004034214408030802c1c1c0c0c50070b02c519111492621144954401d0041542c403400c00564114031245148100b41e2181c88aa89042401c4d00000d02c2c110b101d01c0501025982c540030700c00503600d01d016100003000d903424040d1020f460758000a845078020108101400075015003840f5040451800800300d8074a00c00420030340c11710003170320340040882d4081d40882c0e070100d0103c48802e170700008405070b41c039800708203d850540450081801815018125900001102960191958441d065140303d02003104040c0e144024081907103600d85004081394040b2000ca8005108480c2d1080c00c0b03801042d003184800c00c04ea151400458140b00d144480c1c3c1d0030354000c0000c01c0040405501c0706502650086540054607500e41c81101040c0c418807502018801c410 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 873597401 1250 873596151 873596161
    0x103030210020f0715050609130f02040b03030c07080c1809030d0f0605030703150c0e1c030c0b01031505010602030c03041e09090813060302120f100f06090501091d 72
    0x540003000c40303001c00c00c2e483e03040c0140c0e682c8035412025104c5207150a00e4541e4204103007030401d003a540b41e01070194036416240c610262200700d41054081030190145403900d02c01081c0751004c000300c82c0300076844011510065503a00705a41c440c606220300301d00c41c00004800203540310780c60b11030a0159641034055450807040040d407900400b1500b1903040741036200c10780000e05940074084a001540140c010074440d82c145030300f26084904003c0040140400144443d403e6140e40d100d40c80740f03506c07018a81564400f0780c01c0a50322500c0450b0010a50103000001004000d45844030020b694200300040c0616601c614061b603c0b40244002004943d1003071204000709044465803001c00e5007621517612417151203c1d4004180c0760a541c060700e40c0240015503c2c448150807460900030800b91070b046082c05504070f6098070041003c2c101000035640200400c5407444070902445c01051154070300d503d8a41e98400c0940741000d94460180401d040e0b82000a004c0c100c104401340256900c40480c42c0c541e01d07 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 873598651 1250 873597401 873597433
    0x1d1e010e090a080c0d11060c03010e04050a06050a0b03010f06151d1f0f0e0904080c100504140c0a03020a30051b1801090c0e041505090c0301030302 65
    0x80207142850502c590725620022030302840041c9003911540c00074001d00f00c0d1011015101001c4151030300243d601c05420091100314084c1504d05440c0780d8600c5516585940c20064a030401083c0040d01440c60310040c0004819981e025003070001083e0000d01111220f4100501100d20328030600920105000d03075415407600c511401500026403008241c010820040402c0c9400440b108600000805003d00c0703800541041d03c0314400640d91801844241e00791303020a008543c0a400100511004180460340503014408a1403c45001c0001c00540c034080c141361202e114822140880c0e8040c04440d20118281201200241e030b070090b100d0032010349072084810408400343d000350103913036076648800c0007803412034841c0c0c4900380988020b040310120041c0d80044215407040091140903d072080c5001f07031740404249070466000180001d2007203c074281c01d503444003503102043d1b8018603001d034020408022808400680308295151900c56840030060038140c8028080500035a000410415007280 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 873599901 1250 873598651 873598679
    0xf060a120b0105071b0f0806090c241c1a061c0b03150a0b042d020d0f0504060c141204023d090f0e1f1d1e01 48
    0x1c1c06240461500c03803592550741e2456007044551290340c1c1c8080042121404101140001d0202c0030040c0ca0a420030030201c1c0d50b130745044100c03140140c42e940e940e031400d140c1e0540404600c000e641c1da03081d078411000940e0755400f8040042400c00900e000403083d0000e50001c0540e070404401ba0217103260a000e0019407041d008010988085162248040c2d02c031a1000c3c4248000d610b1990704038400c0b8240001d040080d031b01c4602105010300d05d48005440f15420140c2407103003081e0304070301491005000c24051310107031040b0074020701d001c3d090040000035a880b540c40240301d035020b0541084005d6642d0303070481e4030411041d149002c05109001c041c80c042150108030785c100d84018211003410320350030040040c401e0001e013a40d44c145d15940700d200c00c10304840c5441e100d52020b0325106000346c0c142800c000c0c0d9960f49004420035a1850f07800600c2d44018a035117610361140e139010040701c05640d084050501300903c2030040e0500c0102001c40d444034a4088400c09000c8409200c05250707007044100c804845c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 873601151 1250 873599901 873599921
    0x2040b071407120b0a0e06040b040303020d0b041109040e0c0a05060a020a06050a14090c01200c1c020a0e010f030308070509120d1b08030720030f07020f060a12 70
    0x2c081d07280c0000b084000302120540e55441849a000d541c94404440000c40d000c1c5400c4581d1a0408000c200c00151010641030340300750705060060700d030a14000b01070300808000320b4103074201d032800240036080340c1003101410f880c01c402c0354180312040328815859181c5500420490700002543d81c240314510b084000350041c101d5901c1100c80c5c80d07206445c3c01d0b06461094492141303e0707a41d0461f9098101c401c400c01da5100105000401d000790905000030f10452a00700c3d6034090350028910300740440b03c240100d00040e0f000401e55841c5550b01000d22480d034030801802c901c5090701d9280000e4044051603814125075004160b000200c2c91500e041d0ba407403000420010401c03000300300c08484c0e56246480c002c0700808840060207030000c135a00c080d11840f0340400f0418001c0300c9101103c0000c06000440f070b40260145481030780c504601c488412005481c41074121140404140803003800301c000064a042802280d000000e451810184081c0e8894501c156000031101c400c406521061303030b0070180c040 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 873602401 1250 873601151 873601153
    0x210901050c03071b060503060922021206070f08160e0411030f010608060301020c0319050f0a080601021605030c04092402041802091813060216051002040b0714 70
    0x4070701451810760860780400400ca8a80c2400000c80d08800c0740300d540e1074060411401d0040c6981411400900404001440300307502d510000c4011158510b8981d22a1030f0a60180250000024042c4195201c240864001c1c00003a00d080032188a90700c141c03122405155541d5030002500b40386201152801148141540c1060303c401907200300e64459802140301d601d01100b0a40c0ca94101003000b8512103028240764480d0303006000c03880280c1004001c8a008408841c1c10b103a0303030b0a500030255018001c0b040c007014040300114a08050b150055580382c4140310036400d40303002c5c1d12043c0840761071662a002c2c3d15050b0b03018114064060500354403003c030640c025100d46500c0807030b00b03d412880c858454812042c442d00420100494445201c0f81e000d604a038400a50400451501051600286d04401541c40310741001040341440b11040b5031055030b030810402d664520b04208854204004200700b00c0d40c03403040020201c00c0c02c11500c20750b016640c0e40e0980c41e02d82905511039940950b00c40c4140219 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 873603651 1250 873602401 873602407
    0xb040b0d0b0607050c1005031902031b0a050301080c0109031208070905060c100605040e030304020603132f030a0c090b0609060309070e180c040908070b0403091721090105 75
    0x16545a00242403038900c504d0051441c01c4102050282c40c043c40b071040e2003803240030f000b4400a254841100c0c4011003030340400603160303030394004c0012050104044c1d001202c1b200140c500c0d1000d034480001c41c140c86020b401c60310780c080407000454054805102c0a4441e240d1a024090b51a116004194010745d291900e00d03096500d69000409a40c0110303c156030741d5100003c00809a2841e014040091408903410081c1c3d030901c82c9003c2e01d910008000030b03c1a4400000118811000101c034815590442401c002204180070217501080c1050000300e0b0766550070204c41c4107407900046603000180e0016880c1951072900021501034001d48141560182090010079025202c14021310702c24a881002010201e00c0e2070710b0f00500c90000b6000400c4107888142807504400d0010f07010b0162a070903140045d9661131420184142c0c014000c0c010000100303581031105060b4441e46000542e4400684404040a280400303641c4007100d403030b80c032142500700c084464444c810b00050000f05606042c03841c5 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 873604901 1250 873603651 873603671
    0x52407050d1d060907090516110703061b08180705040e07030605090105060103050c040609053c1c020f060304020d08030a021305011407020f06160b061008010b040b0d 73
    0x41d1a00c00302642c0c14290703101d00200f002c02d00080010750018000104c0030892810030440041161110b034140034103100d034258940d000508200705100083d508104100300c026504614000c81001480ca1040001c138140301160038002c5030f402c0b6942030f40141000b00340a602d46030030b0102500b06080000503d00480c540080814002d0081a01c28404800009a070b440c0c5180098100e440160880050710700a000500a040d04805814252030085074869001c1000b0003000c1503003004401d620f00f600c40510400c1505500490009849603021100c0420805c1c1c00b0700e1101e004001c081000e50302007030320000f0b1240d60500030000d60300310f4009000e030424044240c840d8011540140d40c14034041e6400079074034818550402c030030005405c2c00d2800031b02d20003d242500e4035900814602910030740041c1011030b01580d600040f290084050462003c0081ca01d0600450419040300c07480e004881400114a4261060fa0340a040e1210300d00c002e8201410000c0c2c3e0781721a00001080d003800c030354954904c0 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 873606151 1250 873604901 873604931
    0x603140f071b06020702100504030b01140a031e050714031018020d03110c0d2406030516061106132312040501021b0a17030f03010f03052407050d 64
    0xb5140e0342c010203025949460500c14060700c40140b2003142c0c10020244014000070303056003581411241083c030201c40040648000411040c05980300524001001d1488100b031549020907041d594003840a0329140c035a01d08002c0840b180c030140103545604581030032407000c1840e0307010b040000c5401207040c3c8062019804a41880d0f00517105401080c0a4500020b00c104e04002903200008180d50702d00c0070310701c0350b0384012421201a0780550002c50503000030300031800c9070b03000351b00444d0400c0440b00f424003400d03103081c058002802008005051840c004003803038000034490303010f035440c158020f110768160784680526288008111800700c80480d101c2580c400304100c010317403415000c2ca85640d40d6240600280c90207100d0050141e84c1a105181a5a1591070404420840388041b0300c44604600f008075030f50452040055003a459000800042003288540c03556030281c91140048510040040e000d60120b090b241d0040c06905580c48001251140301d0000307400710611080002c11111010740d050 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 873607401 1250 873606151 873606197
    0x151c050109021201060c212d020c0105070c2907030815011e200303010e1b04030f03140c0a200118050415050a090204030c0603140f07 59
    0x2514070982c01207500b6041c400d0f80103400c1c1c0140f00600b00001007030283e64900c0e45000200c82280280705800b40000401402141e401c419480300c0d50508039241c000c46642c06000d817160b034800005108030401c95038194002c0044581c02500948101d0790140b900c0e05000786640a03a400200d4440414401c5c0d00f00c1030b07201c0240200ca07219456844951900d070401d2000500064109030410840300c04d410110503c0020200c00c1c0c00703070341c54281c550741070708082e841d1035040d803010141c401e120010000032000010517000740241c040344000d00b041d1803051300c111041e01031400094189002c0500340c2000038011140c0c0d24039a1501c01d4000d0515142148460514807849000d40b000c0c0c4d403a2449801007942001034032103910003400c00d6080304840c80c0d29032944400b6402103c2c01940c0e1030282e4201143c03400d00440041800510f01210315844da804d0001130340040c802294041d112a6020814500038000d401d8184035607894018542e0b9020706880d080c1c40c002d000c080611071089081d5501100c00080 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 873608651 1250 873607401 873607409
    0x3031606020405190311040f15031109130803070e01020a0b0703091424090c0405160f1b03120e070f05090a0504120c0c1206050420151c0501 62
    0x80140c440e403070081408000507241c0500d1651414000040c17000440d10390801910740340648001401038442440c0700e0080140d10f803407102040c0705220000810001090401c40030030141c40d03801544d106c145080200c00b6546400808501c0b081c40041c190510550240c0c4646074140704599064505860300809500c00b80c031301c3c04c00652560f14080030310040d401e284140503582001484803503140000035901d004e04600d19840072501c0300c040758000e4020407101c11b40d800300500c204254104103500001032039960304d00d80e002c00c9841a00884150140c00d00103140001c104607200601e49981c1c00716501a0482032000c007003541c1c0c2c0c0d031510b0304240c1084020082d028100c607114009040c40304110400310000c00e84014282400d0400c400113001e400d584a08104a09060100c090f041c60894820318041c0c100b10031040998044070203004007a080540141d0140090300301e10840c1109510105156820458112450340c0c80900c010120300700070f00c4894158650351400c1004da81c1490b06451007030348 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 873609901 1250 873608651 873608663
    0x9020301060824091f1505040e070c02030703150e010c031d010b0a0b0c03040b0a0806120a0f02060d02040807090e19032322060212070b04060b030316 66
    0x108030b69015400f00100e043c80801d50941194600e040c0001d0014a0091400c500061090085141c40900000000c007404242101018419406070000c0c5641c00c00c0c850a12082d03804404186124011301502d00071913005400740404905540b129044000c0459a00c00915911a100e500800c002e11030001105081d981c0803d1413480503c4c2c0c110b9002c00c00542110a901d800b958240316910380140c1003c5841d030009081e103981a010500341180110350044035010400030342c080384e40c1d0344040d034980703e00c004541c0001004007120720b41d99a5115400010403e10108002034050710304038010741080003034940c0140c44d1940700e07820241025540c0d4840c50140362921f40c8895407210602152a4252511007204c00c0551161030041c001104041d251845440e210703243d02e1901c034a0070454240300020408100186500d1011a2529200388540401800703400c0e02c80c2d0441043c081118600c07504526485855210340c1c85420040c0b505810080c2d16220400040c110403691110304111140240 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 873611151 1250 873609901 873609917
    0x50c0603060d0204150e1b030115140408010f110304050d08091903080912030613020d0902152205012708060c030103060e0105160806180a0f0b09101e0902030106 71
    0x11a4500d02c1d46c8094503840001c02c140e69542000389519095134115100c01d444100d0520002c8800c0d00c0d088800c05e80d640d0100800600460640e40c1500900244804004208081249800241901d00043c1c03401003440e0040e10621007040d205641704ea070002d50280c19287c403a0111003120300c0c03046107584101c010408150400c4402070084c40040441da000400706071642c03810f9400944000030800c0500459507000c1030248001e05a0b9004940555002d490460300f1b298043c0414080e4001c152041c0144111040c603501003c0825030320001c460041c6c603600b4410301c90000140610302c0300d8617140c941c01619400003d0380001000380070300865022181565950550030900182c442c0050489a260b0515081c850310341703030016102d0400c521514202c80c443c0c981d4800621082540060480d141c0c2190041c0524410f0a910030f80d00d21014000410030010440c00f40034103d2400c8500101030942281e0401034002e8201002d040101d8040d04180b0107030325004140c00702d80081e004000003440390 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 873612401 1250 873611151 873611159
    0x30424091707020108070f030e0106090905210301170a06110702010f0224070509031c030b03070515030c190906090503150a0c02012703020712050c0603060d020415 72
    0x1030425031070712805416205250003007580000e88031604c05049182040142201840c00c14403c0d88440120301d1810001d0103840c1e07540b401103015100080d400e42d401d00540c6001c0400390031024113860040355240c013090843c1c0c83d0440c2c8201101352a600c1b08803038040c0c103598200044591003001c078910302041c500c0782c07103956030300006208910002a00d000d560020560780000031101640358407040300c0300a00207160b918800c044a00b8055810510b07014842e114480f120300c8040041d00c22814015501004680c8050003015036a0349107200da6074010f40503075000030700c6241034001154818280d0250070314054070651014030601200700a03d00280d4145404e03c030781d9038054079440c0100030883c0240348401c0000301c000c82c1000041c0c100101170b940c41080b01c0101d4000c1d0000105207140c41c1c070815064440c0d0b01100070801c14841c088005020316500412130880c00c1d021203610f0f41d000030003400c0d0b900380f24060040a40c0040c100e19484540c0c0c0c0794030720040c8d40e6030141124040d044082c0941c0540341c = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 873613651 1250 873612401 873612413
    0x20070302040608030a1103160f030504032102010e010b0108150a08060c0306150c06060f0103060f08070317030709060e01030908040810200a180306090b010e06060406090b03042409 79
    0x9400f10558008101d03403907420800b0505402d4141d0020094022003500cad140075560361003a544024001281803640588480d040c900c11580cae9009a0001d00c0641d2611105900302c5800403409400301c0c107100041002501501d00d00303040d082018001c3c18055440d60001890214200c45200c075010001040084900b41901000c000100c002c010303d0074103103114511602c51038005c2909004000600102c16643e1007034210740010224108692030f015250f40d9400c1d12110715000c182c1c0c40c19295122000e40c0c50008003124413400c4c241d5a80040c16042140c01ca035a10040700791681055280c290030404584401e00802c0185240c2d0000c00c61902c3d401c04000503920b10158652465542c61805180304032003400f102e0a0344114505000c102d40707908940d9646400030341002e0b10240c0780c03650a400300800303a0001c83c140c075400c0041e101c0e00c0c0c0e40c003010000da51160340122000904001810024403c041001d16001031150b94008003026180805020032100303a0560710f661a10b5240d06028054 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 873614901 1250 873613651 873613667
    0xc07060510140f0112020d0b0402160506160804020d11030102130914061c0302070e0901090c0803040b1c0b031006050114030c0a0818240a050720070302040608030a 72
    0xa002c0d10b4481000f021800080c20469925035001441a00003414454103034181d07025036141c40008004640750240c6258507007c500344070700c0494041c410a00461040c1d80d00724040b00400c0c6560359441c0c02030303549609200c0d014141d010300326028000d058101804d41c0d401e0001c3c22501240c8107403400458600343e00942a11180c00c01d1000c0280110f060000648500c010780000c2c1d008000798420028051400304c5c80c280e903662125000c1c0001c80107200c1c14040641202294502071060032502e142ca0b9209513880380314900c64000d204008004492040d82d00140d455010007044800060f50900c0001107800c2408050354107221554595040c00203680200d401c416042c800c42e01c01c0d046280c0311044404d40c0c401c403010501480700400c001480304d010410000c508072603070000e507000740101040000c210506001c020030318541190000740030303100c40d02c503030381c0300c0d04840e0745c0d840d00d4010b46810303030b4022900b104510941d4040c2e80b8021001da200c50080e40001d0507a0700085540c0ca007000d070001c001c09 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 873616151 1250 873614901 873614939
    0x60f040317060f120f07090b04050105011e1b02060703270f050405041b030606150305040803060904290114030d020a03180504140703052a030c07060510 67
    0x544048107100054842c0f60442d8a542416210340c1584641a4085031030020800d10100051007a05000314424440d6044112501e50540b402d001e00c2c0d0f22031006641100c141140f104c45001014030341d0ba204c0c0d00c28200e00925041051030b0300803516180d0040ba560342d101240550114840c0b41500d40d405842c0002c10f000810f401092800e01400c115100e201c1091b24896948120b4031100070030306000f01414040003151000c10a01000399880c585100600110b10803120342e4070410901001c228001c1c050184641d611905642c60350781e0301c2040181c00900500b085c1e900140e4614150300003001e407840080c04109076841e050f070540c9403d21000d081c021110100e40207820503e050021160001080c407003e952600702a01031018081200c1107082560380403e40c0242400700b1442101d6410032094002c88850f03a0502050381e075109405003082c62034032071814182131030440701c041020b010061600f08030120743c030a00e0851103232286400d1300e905075800b5042d0000130504100704c18521094900780 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 873617401 1250 873616151 873616187
    0x507020a0e060114071502160c080105040305030c13051c060506060c0604030f050712050a1b0803010510020f010f1b031b0804050a02030d12060b0f0306061605060f0403 74
    0xd440c103580001c4c00c42c4401c01c034010021102043c0c074420042c1c0a085180505541402192940b03c1c0034181804c511851b001900e840b40c207040d01040a80c011f000c0c0c180b00b243c243c0c45a6145d0b0b103032680c0b01c00d150f50001c0d402c01d804008034180466a641d841d40f29014410380c018644a0012aa0070141c08448000d04140c0c81002d042100070b0032503030041242a800b5405062242802415a000303031154821140c0003040c2e80010341007407030040d4102002e80800c400313030350316641c101803c0820210a80c04410000c0c210b4802440100800c1c60b18040004004000d4411b5070494102ca146d254217686a030703402e0130741e03094580e2102c029402240c80e0312004260399103410302c00c03600214220241c2c5603611b03451604002102e000281400410480503440c158003a0859100c0d20011a0040911103420320704081c2c0ca0a107540003444c01c402400342d4a003040c001e18010301d10784421b41048015440440308030b0b4030031568004c0002040c0b05200c000d202d58450035110742c542c46c007468020b10303500c0c25002c00c2c045 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 873618651 1250 873617401 873617429
    0x607030e1c151d0c0640080a030c12030b060c0309180705070609022710060f02120706061205101401210c15020c040f0203090d030f060e070507020a 65
    0x10310301c000104c03112018001d540b2a9500c0744140711105205086203040404a10748180c0d800d9210700900c030018000034104010020580c4810000d07850344480c14001d00015003441e46040802c00c1020f0214011060303090001c2c24032003040204a02d600250712800d03036600b0208074056542000705600c40c029081b41c1e10050b04d45405003014040d03000e00304010306201e81e00d5515404644480d850503414440500c50212086c50017400082c6112080303072007425410000c1000900c240c014400c49641140a8004c0d00e80d2900e41007180b0415000718005480c00c80d2145000651141c504003d0614107000d03001a107044911603015174142d50480100d550010089001006900c5071052140b84141e440a510008103c0906000c0190011604880220307001c80741c00b091070347d4000660030100710003540c0c207000c48020607505e0340803400b044640e03028582103501070030503241c030980c895040b81542c401c00107245e0b078a841c002002c101c006c035030640106400160308010751030404081e1000382200403000032 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 873619901 1250 873618651 873618701
    0x8030d2409140a05190c2105040309050f060d050c040f0b04150509090604020318030c0123011a0a020123010509090f070506070c0302030114060907020c0607030e1c15 73
    0x1461908800c400b03171607540c0d59511928424810112425194032410700e2450340481c0545943c01040c050701c084000c225006400202d80c141000d4480080318000c0045041c4206100034801504000346580f59410040202007440d8082c0032211018250748070001b07440718107007050620b42204800985090120500088459646d42444250b0003507003920b0140c0c40391541c4d0368010007010030b9003124a05000104250305441415401304803001c1205c1917480200c002c404c41010010805c0c0a0200380c0035802e405c0c0681407060b00010039664415100005030014254034000c0a00046110300a09401610042043c0e01c0d000b0401038101c000c05014001480c60381d100c56556901c13030311400d4003440022500c1004c0c46042e041910007503801800034801140342030205807401100300d034030764030442c14000403039440b505c000782e040c02102015284910380300071902c007a1080006c1145d42540201040c2c80114003251b0030410b012482d206048050244040c20008020342d060400c12001c9400030700c03071a070 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 873621151 1250 873619901 873619921
    0xe09030a120911062101080d0306170c1504080a1211010b0127030204180302011112281b1d130e0705030a050a0309090608030d2409140a05 61
    0xc000b05a0813101c0c40c1c0e41d00307503901d1030f802e0b0008031030882c8a40d80c0245000207606100403a0030080301a042e542006401d84683e204448150000280d000a41c081101703a00241044440703000440940c040940c10642c0e258805481c02030601c404442d400280c026801800342c00c940480300c0e141161000380250001100000c2034044200e0a10003c0f558244541c520281c031502188003840c3c01030014080340300c100303240344040d0020304801c0f4015860010074511014034841501c1001500c0a400c03001c0740c681e240c9554242c13003009d44000d6007000005044c3e9841b4024843c0740e890f503c4c01c6801081c921000d20001d07249041c45201ca2086034140e4440c440140d81d10320003644403600e00e1200040c2081c40702c1300e0034036000e100d41060b90148140a440020b00c030300003d1030300195100355540090b098079040c403007042d1802c40c40765210030b41c4140101d9103244800d80095810316900300e0403120103005440c0c240a81c000540c0543d280710786c2e85170040e2612044000090f8464a02481480b06041902c1c04c0 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 873622401 1250 873621151 873621173
    0x627080d0c1e031e0612050705040e0a080a140c06040c051e04052208040320010903060504021f0e183108070b06040b0405010602060a150e09030a1209 66
    0x102d820142d4440440750312060451202043c0f09004608000e003c4e01c916802c10008030300e0805442d0b610410740001501d240c1030080400078011b24016005615281e503a05141e504050000c4041c09501d03a039503c6150620f44c00342800410700c100500c00c0c1c1c20700c3d042c00200c28900741c00240c015801c07818100e202d008200c0002c106080c0940303000526940300ea404841c6001100c8450802c400c84c80c1c0c2c0542805200b40103001079900800b460b86820b00000c1c8112a81040c1c0a0036501040c1c01d1201007002c2241a40800c1e8414006010b50040100343c810b01049101240c142001085910b091100c6c1801c01c202860481c404100c41c0042c0360501c4070038500c814001000121580380304a025221b400f4800c0c080040160303001850544682a03407034404c2c52080c04440c40c500892410300f20020f28505405503e040301d01a030050300c5144c03900500180a40016090a05074240c5800005110440007045504c00c8243c1cac1d02550312890a0900240807030840841549814200205000032030403403081 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 873623651 1250 873622401 873622457
    0x100305090d110a1a01060f0309050d1407151d010501210c09050c0d0e0a0b07050c010905060906151f051305060a030e060a020a08040627080d0c 63
    0x120030030900703106501901d000030724a8003d004040e080d1030440003842441310700b8162403840c0c0b903403000740031420400c41c1100d4003070704060400d80c01082404150b900540c0760360314060440601616002c0140c543d4451036101494465960f40d031881e00c0c041c080d07020a143c06e8911131400091005501d40541c41c0050b803d05041032088402d1000c5074405c10280303284620003003202d0304080c0400c0c58107982c0d0202c0da40043c0e09803001e45042002d00010314070013040005e0341c05e510003402d440d1a2548403048409401c641040300c199940d4003100c41c041801000030504ca0482e00009010500c3c04c0d05202030780c4a10208294000c1500c0300402d91955259080c2c0903100c841d40c0360440c2c4542952402001c0b0003001c1d800141c101500003290006030383e25410060780008070904480040d01d8040300b00d4200e1180d6030b21440000d24100204000450740d03001191204110b00e0481c1c006400d075082a0b9001400801c120750005000440e40e02080081c0682412240581860054100c140c4079440340c042180030 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 873624901 1250 873623651 873623657
    0x10515090406020904020c06090f071a0a200f1b0d020306070f020a0204061e0e0606070312090204150312020613060f060b0f0d180507060f0e0d060605100305090d 71
    0x14009144c0d44490303040e2107020070484c04590403810700c414815200d10010503452481c2c02070050100b80c0220b41148400400c1180c420146400342c48032085030900311817501d81c640c500341c072010401c0042c0100302c1c400000c00850094010492036040e245604101c0c2c01029008001305182c010140c0e4022403940d074004040c0c142070088500061080342811120070300294003d1802c80b02154464600c0e0050203101d842d58550030019840d03038081c41c6211800c0307880f03541c0b06104222400003c2e1280300720320700d540c540d074201140040380c81e070000d015119986c0700c40c40d004280100420611001200c41030862103540003501880c14010802e2034080d684c05805850030b500ca90404800c000c10b50300100080c030341e00389483e0710f40080345c049010542c083c1c0c1507100900d0030020440351075082c24010101d003d600100500500c0d00c1d204050f01c40040402000007481031242000d0599244e84c1d134a410076a220b8480002c1ca42e00b042c0421014400480254080501e02002c02008580010f00507440c2c2c44281 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 873626151 1250 873624901 873624907
    0x6050409060503190816060f02090405072a0807080c0322030807111c11030f0705090109050414010f060e0106030207020901030b090a0501020c0606010809031e130b160501051509040602 81
    0x210b80c144400a4846d006089600d01140203896455039400380c400f040040790240b1854640407001c8030000e1015000c03100d4100403041c42d2201280340c4003040012072050ba2600d04228454607a040b40c0c2e0002c00384804140c00006075140d40c1c6002c0024296080c3c250190051100d007107032240d5405d0f018840e0700038000060b680d03c1c000713680d913104000074000e0701d40001c0e0444003085c2c0c64025012000c404144c1d0080c442e1903338840e41600003161a000fa0b035805040700b45240c0c60417294601900d405031003540d58601c0790405081415080c0984141e085415030082101d9140070148074200c1c4050340f000c0308151040c020440180d50f0b00d00000d044940002210100d81c0b04d2803219410b06c900075200030295031001901850310031000c2a07007032080c04245c880c82c80c10751701d0201154403840340035501d03c00180c00300990001640c4200203491001c60201000d800151a010f02c00d03081c0e0b002d0079040e9040e4a0710b44e03980040201c2401200d61000c4e01103002c1c201ca43c06800412080740c4050b100034013040d004 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 873627401 1250 873626151 873626167
    0xd020406030b090703030e030d05031902041e0303020d0305071b03111b09010b0301050112051512101d0d030b030c0a0f0819150b1306060504090605031908 68
    0x203600288091504440d1100250400c02840c41d41c901440c072040b00441c1121082000c10b1078045040701402d409912510311315510710300b80012428070469141140c035420f00000ca4494400e1080541d15592080c0400b040c0d030035420061b141c20310408848040500340803c000d03102d039000f081c0c1c43e855402944071407004072880c0350035121101800c103e003403244612001c10881e05002c80098200b0602070351052041e90b22460920141c1c03000340a458042141917814100034441d40e030207a94814003410f07600721100003910000740000c0009802c60343d903a1140303400900e50308061007148554891340039000e0401c040a400c103600e036106078041c007061580c1d60900700c440b80c074244250000c2c0b0000900541d521038640c0c07000b4000f140c030382c09003104910440400d001c07403001520802e20565001003240190070140310000c00078090440304140c00c07072800c41c160200e4001c94081d0b80094111625010388070380c10865800c0071100707554083c41c8260b0059042440c002d00700302e0130404da41c0d0411a00780d0b85102c0 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 873628651 1250 873627401 873627409
    0x1204060905060901030905100b19030b1b09210f0106060e0409030201110a180b030c1e070611180607020d032d21140121200108070c0507050d02 63
    0x45041d002e001c902450508d4100318200ba880842400303821074450f8640040208604201030041c0030040a485803d40461401c02000080255628803110f95600d002c00f0900490a2240c0420792404540000d8000f55000030003800010003040e034810080024604d40f410050840c1002c00714980a01d607079440781c00505100390020148240451f400c1da549841151008059240c4108002070107030503071202280c9161440101c0b40a8202c0e26008c60506810420410704102030200d90000c000c0200060740009045000d800c10623200104d1440e20f131103145292481e64440301c21034a2040c00108101ca0050f50390f08071900745540c051514028100301c031101c1c0c00e00300a0716861520710300102030940e1200781e80085e400316804501c51610742e1100c4002e0400c410368800d4240c0c1c03015502100010300c1105031a2042c0800d951100311002d5584c03031107894040740307075a00000002407000c1801c0b9407907042d600054503d4000d1410300d88481d0046254071015154901806210b100301d03da07000faa01907540b = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 873629901 1250 873628651 873628661
    0x8010b0c10110a021c05030c09010516030306151704080c01180f060c0c022112070b06180906070f0212030a0e12090a05010302071e14120406090506090103 68
    0x2104040c10402e041240321a410150001d24144005100e2030032400308241080c4010300c06600709880c0c81e419174580b20b02400c81500700e485003504100d001d0040c0300036101410700c013018241c000d0f18000b964504002200b10a80f0044018000744001000d40026800e03502103543d40c070580105a19494540c0c1212082c054059442c141e1500e01c2c1d0007120344103100d00d41c003a01a10b5481001c00b01b10041c09014240c4041c01c4501c4080c0d401042c007640900b4000c607144081c04401038120548401010144041c0c1c556080f55006690303059440c02080310505100807410aa4420522a014070b8a440c8030569502c680040c03910042200441e1001c40c3c80d40208401031040c03042d10b10150701c80c98940c000100514441c0741d060301c1d6100d051200d4082241e2201210702000d40601800c0307030241010019400b83d845564100e410703030112001c049203040c40075000c500c00c070700c02c0a12400c5c0d06102c80d5154076003000002084400039080008118240d0458146821140305a6010f80c9541131100184c0041c1 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 873631151 1250 873629901 873629923
    0x60307031202030309010c02240403020f070605070512040b0f0f0c190201021c1e02101805280212011401030b061816030902130905010603061b08010b0c 67
    0x107888400115066801102541c0310f007845000070050798403125400c99880c0c14a4540940707101c40201c1e1002203078140850301d5442800303401110034106d41c9005a41c42d0191aa000c1000140d0101c0c0a0701000000d03c07600754a2100250b4050410f810700b0240e903202e20a1445850710b07141f00281180707405070880d041d0740c5000010025512100f002c442e42c0b203003034485918104d0040c0594803d1803000c0441c10380640c1e81d000c0f42e03524072004e0407074055200c0020130803144003000d5206440c6c1e00c103c244514040d52542d584800c4807034500422078542a031508202c01e0150100701494044418805c00c008201400d0f150101c0d00d20750b01c6001a680d05004003044403d202900d952a000030040c42003040f05a4080e60040d1070251402d000101404283c0009407003e144c14819a4070703006000d8400d81203540400c0c0003c003140c03207030424018150200c4408500403100381e51560404c00510440744110384101c0c5404224480d03035050800d0041030a0014082d10242000c082051a010082000700c03034004 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 873632401 1250 873631151 873631163
    0x7050105132d060507170307090305060a0e0d0206071211041e06140a05033c0609070e010503070309031124070201150b0c1c030c020f06011d06030703 66
    0x81c00e50802100801e51820664a03080c0d8484840001d03d58031403800c58410a4011241480616100f814a0350381d50026140d0400c1181480740800450001d1002501650200c0b10002e50a5010184941003c908030010415500040c0411000e140c00070b6540b44900b50340030001403049000356100340140030b20341000319070703208484014403510442d203080b178240d541a4036950413964004004031483e20540c00480000355090002c0f840c21044aa0340341800035012601c84420f107500600034406044480c00068009100c00c00e110641c01c01c40e0f01150443c5581c074191100c5500d10340080c1c1640f02c0036102004160741e0755496001d15200307034503103049800401306554188000046560b500d0030001c8e0096000c1542d000800c52981c01445075110f0f04c04c20003a4420f526103801000505900800402c8040740240145481404101c20601d012102da03034400081c3c44008800092401a5803404503c00342e000340018000304400720768644030410307a00c83c4a0b01e42e80d0341c940400e0138100c0d00d900083c90 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 873633651 1250 873632401 873632429
    0x70b1e07060b04050c0310030b060f03010213090501061404150e03071415090f150f19020c0111100f0e010203090a021c03080105090601180807081b030705010513 71
    0x4001007a00304018920b000c030b400b48070301e0310340f940003d56611082d510004010403a1070f0030000102d14118440d400030340201014015052003000c6800ea074031035044885003100e4440c080c8015142c6106042c00362006107401c09400c016a00205a070b88501e003d01000d03411180c04031001148200c003c00308003813015007030b118066560320030003202604101d0582c0c2704901820596000f482e006003036441140004103004030013108441030250390042c403503464848800422811002484030002041843e00b0028221036402c0340c64802400d0a01503074515041221110280882c400300095020903240302c003a00003050b603c10300c1e40c40010081d180070101554008401c2241804d0702007401070402e4029168204030707902084105030380f0324070343c01c004001c101010700500650412410306a405001030408510700701c1840802d03540c5242c260300c42c0c40950b200d44014001c40c0c0b424000c00080c45405054250a2041c0c600002e4590342c1c00d014840c104000480d003800f034101c1c058403060003041e8140309004 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 873634901 1250 873633651 873633653
    0x9060f0e0d05120d06090902060702150706050f0a0e061003030323041406010501111c0908030d0b040c020d020601050f033a0921080c03040e06031603020102070b1e07 73
    0x100d54105100c42501d4a02d001e01c0006c8403441402441e104950040526242c0705071a400c0000620f102d21518000c84014041074000404610440d03000311124002010f00c2d03e402040e240a944031342100d400c8a03041075042c8505004d000750010282da60504004c5420049869210007001c5040025400401084113200a00c5040603042010700381e42c2e000c0c2ca0080e07032104015501040c480b100d141c0a68000010360b00b043c03c0308040126851302a1605e07440d626610003003240b81d500001c569824540e910703031440c0202d240038070801d00541c09a0002e00b20111030f000307001e911400c0c14403450380a000c1400e40310700135035000d00140e88812454410117070768044002c00c000340149400d4000f64024415140800d04500803103d0000301c42c0b20700e030386c1520b14402c4005100708030ba4119013180d0307031081403021040b00d2000f0700203400a44050300e811115442e09000b01881d01c0e508019101039031020490610150b6070200d0890243c3e00346d48501c45d96501c3d1300c0007126044901c4101e001e4680c8020034014 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 873636151 1250 873634901 873634933
    0x9020402190504081e030f0c01150b0a08010e09031c0b04090b100807031104180b130c0b03090d0804330c1d012312010e0709060f0e0d05 60
    0x940e2281421190241d81140703122411801441c2081151b6006115050030744480b400203100080c0c0c2c030f00001c240130301122400b40703020500740c0190007031410101e821b80d880d0340d02503411401065443d004032007904005081799100d00c0760341800c00e1490381c414841d0001c0e0302d080d009440f40501c003500401000e100f500f80030001c41000c0d00e03405603d1601d5540050141c0c4001001010750b5084a041501c10b846403080000420b010312501e11171003010340c80840408c01c0e110a035440f45030250390070300d0300c8540d0b4034040d501018580c00451031024144280028a4000652809001e0040c02c107030340e0648540c02c1801c48648101492005500d1481041c4d141c3c6035449400c02c0f425020b000e040c481080443e60684269103084003d4084a03101c010031303003040d84034001002000b6070844a01c1c0180d002818625801c0c1c0c0140c858007801524140100034001d1480034860380f0501502c3e1002c203143c00c1500c014000342d42d0b282d1441c10809003910300d18481d91000b000c103000540c41000c64103d40b444261075 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 873637401 1250 873636151 873636157
    0x804030203191e1a07030e070803120402060a0504080111041d040b06060f04240f1403010b0306041409010b0102160503061807080d050702030d091206090204021905 72
    0x124001c1c02501d40c0322400c210000301c09a401c0354001000681440b1492090b80140c1e240f14060b41d0000001d04203101d1000c001c04041e028010541d804141c9a4008600e02e1904103194403089486d4400c20501e42d00030014441c454000e40c1c1120613603a11200d15074111001d00072600300c0310b125480c10068811a1080174001d0044031405845044142c81d00103051a030300d10b003100d010703002c0a05580000c0043c94420018110395071101d6500f4106600e4014030802d03003c0032410001e1021100c00044d20254024420041c03200703084c507041c0003d440a0310340c604c581c00107110781401030402101040e0b840d40d07150851858100c805406071120300d003003510540609000000310b409030061031051490400c405c0842819154060010080c9850307054100400b0301900e0a07406150003126000b044002c0306101800b5031423081c0e550152281508c0c0100f50a02c1542c281c1c82c001e1104044080001c0030440a2003481180c01c4000060194024004039003e407046071840395007941201541d8009d9900706000d = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 873638651 1250 873637401 873637403
    0x111150403030c09030b0414010e19050610060210050a020906030a0203071421100e0c0703022415010309080412060f05040b040f0c081204090e1c12020412080403 71
    0x1d1100440700c002c2910b03003134070314003016203284030941c009400b0501e1201200360105104000084843c513500340c442c100203040c0200041541c461803c0e400b485000c0008640141c2040404910f003032600c3c2001e035540c0e178004a8030402c15200d0700007507269101581a28200c09001c2c0602d42d983c80e0030100780000f50b1088130340e40d000c00c000500e076030031a03804102079640b200a60340100342c019040d101c83c00015100140050320380b410300100458034281c3c4600d424003840c1100c0c107054942c003041c038013b030420520701c2001c5501808202c2035000c40107220030158008101e0084504100d03040ca004034040c00d807602014200d078100080006001c2c03400401c00c8441b601580c410080031101d81c44210075600c0540d00600032903060404103011030191610740c41146c3c40713402460001a51030402908186542c05100b01c500c002142c02c01c00c030803642c0118820080c10401a240e801d000411010512102010850400201c0440503120034039950440d400b40818011686002c2c1c0f041c54881c1c215442400 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 873639901 1250 873638651 873638657
    0x609012f010c0324050901051509031b150306012a05160602070617360a0201030b011704080d1808040f05061806070f080307080114010903021e0111150403 68
    0x140441013614406400ea040d80d0b0001d000c00c9050b460076041260035074020101d558003c5080250880580d0b080204060038250b42c0c05103007662800b041003080a11030f100e504070680d03a003002008203d07070b84540700000400d080541c03d800c03102c0800c0c00000d50181c2c404005c00c94032420400b0f04608611581d80801c80309a41d080755440798440c1e808480070071440002e048001d01d81300c040f80c4180080b2415400b00c100b604440e01ba46101000708006503901500141c00035044500e0300000c0d03582c9402020003040c0c0c213080001200e00510b2829a4400c0f0060014040d003001040707141102080e41c10046680c130981c1c1404101d0021400d00f00c00c1507202e8415441c00b030603031040001e0b507410b000d0180c031546400c00e00100b48103540501032000c0c0341d014217000c8400c2141e0428501c0002c0d40c0c60065405400306541c1d01d0410742c10480c41002c07442481c000c05050001c08041000180d40ba03145400030f030b1518041c200340f10b03920540107940428801c1e092404034025000c6003500d014400b10220300c01d03400391b9 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 873641151 1250 873639901 873639941
    0xa0b030c04020a02030412020103020c0312070914030d140d0924060506030103080a0905040f1401050102011109041512030804050d030612020f36060609012f010c03 72
    0x10100400c030b03c56000b142015030000d200802c40c140207807144131509801810b0142c6000c01413a0b01d00e085902c8980d000d81c6145001c8140b03d074441d4440b50170800b0341030310391400d0170440703034040082c3c0d03039002b2029010200642001128030100789e80b030983c2c0903034595500a010440036884c0c07002040741304469000040c0c1d2100d00d071084001250040c041200c0011301028696401d588822540b5801000008180003500100081c00d40720752044031076425403841c2c0002d1500c00b03c0d40c040c5442e40d0607440301e811a030421209002c0c21a02d841140e011100c21140040d0210030110300103a07511041c2d0011b091408142151030034107410076400d500c0340c0e10620564049402420060701102c16034010b1052900d4140161070050a1075000c000754444001e00740301c1e54039941c4022f10311038101c03946c1000060742050f20321800c901a0040c4160420001c480090a010082000070031700760280700e014a0940c0c3d101210a41c010450000d80c842119500080c4020011040c0140107000d5101a03641c00d10308503 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 873642401 1250 873641151 873641173
    0x3041d18010c05280e06030705130e01180b090a0b03010e10021911030d0905030c0d0e010905090402061e1b0c100503240105040b041403010b0d0c090518060a0b03 71
    0x100303c041c3c080703c01e171101c2d016991000d0510460b034100500c540c0c2482000c00c0100041004020008000c5c03043c0301410116605040110201c01c2e09104000c03d00303400c0043d000929074503203110301e50154190000103a5424118002800340c040682c108009000d1105505480e8120350010504a04041c4414480458150b0100d4030410b0400000405410034004545050b0643e080350004600a40443e4204040c0c5190300c0c0c2402d55041c2c3c3d02000c26024056200c0950304403912400420044070301c00c0da00d00e0581c010459605c41c21842d000c8500c031443c1c4061541c026001951621451040e0132105201c030350f40c4070f90380e549020300382510680c0d0109035482094410811a07126805c0c6c014101403070144402447d174000c01040e0032038144542400042410781c03100780544020800b851140c1d03800340d002801d043c211040100e80a0042628039602c03008540c1a4650800b2610b041e0400225541c030751300c3e182e0b458a4103900f2124240214003e0081c000200c0d009480c1c0c441045064400703025070 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 873643651 1250 873642401 873642457
    0x905070915140907030615080103020a0f0e0604020903070b030f0105030c091303080901060b071a0f0709030807030c0b0a14010603020a0c061a030102040f06020f03041d18010c05 78
    0x700d40700745081001c1d0035050300790609001c006907410802034200818001e0321500b512010110640b007000c005400e000040003586072610104004001d1184110703100c50030200342c9802c040c00203240500031500042d0200280c1c81c2044014004c007a81150a40c032030400f502100e0b90007000307103c2c540c0b0a11803481c01c204145800e403191809018807486004180f10310396015140d42e00b00402550f05956142000900501c04000524503a8440d1202c201c442c0c1d400c00c0fa0700c00e4030b10090030010302c60b044641040300560700180c0c43e000b80c1382c000d14615141c251600d0105c0d41105101c2000b030480290805001c1000d0054110f1001c541320880b216141e40c2c1c035510101c0803406070004a000051014416170041881c646c412100300b01e00880d848210512540440e003aa4000d501c086104000b042041204940c1801742c0344070380c10600d014520745450b0030b8540340c0c003200d4035111502103440d10300443c00c40501850a0b076601ca200e01c00078440e60001031070180c42074100c4421030b40c000401c03415068000710 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 873644901 1250 873643651 873643691
    0x501030506090406090c1a120a060f0e150402040f030201110d1d1f020303090601080c010f080705090409060b0a050103090f03080415181a090d08091009050709 70
    0x30010300038000359500e030380700c00307002d042c08500568148400902c0403942000703142206020310024482543c0c3d81048c00d20402550301c00800c0003203118981041445483c1610502d601119401101d00945485401510885a80107014140d10a100040010b01814004079950449000b43c0794003c0d840310301820b0f00e840b4069503418900207601e24211000c08424440c1c030004044001d0040c09a2481040002c103036090800b41000241c0d102208003c00000c00b00400781c0940b0100700035010811744000081c0c01030021140c04010300000f0000a0007541c440c00590b8444a002403081c414500942010401486440c0f074460140c0c415001c0031078194028003d00d19800d51003401070a0300a40782d00c04441c01c820180c0700f190358114081d880b1111600700c1c061042805608440145541d00610f0300c030070b41c0c0c124030480d40c0c4070081200410084250120b103403601a1001e080101059907000704040c00c10ae038440743c011500380b0301000d1303406200c00090442c05440104a04000f510004007002e080da031 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 873646151 1250 873644901 873644911
    0x14010905060a111801120608120c010501050d110906040e16030b0105060a021b0604032301053105030c010f1506051303080a0e0a06030c03050c0405030d0c05241005010305 75
    0x2802c000200584e552143d402404c501480e2080060035580790342d004c500700414a50850204c8801142c034606464082c46061300420080301e081d4058120b80d81d42e0005080e2024420348540c0c1240d00088180d100d40e000b40302255900000c1e2080c0d0340e0814081055511280825110001c06400110b20740c10b0440448045800c0c0e03400a00032060212505050000002c043c00e401800500000000580702d01101c03100100040711550701c10740c2c105640f401c5400007040050010000c240d00c0080e03404e180004880b91000b6809415101503600741189180300b000140d80c0b8940c604040441c09c482aa48a05018968001c22a220356640c0e04222118050001b030884a61400b00040001600150081544945c1810051551a07131800001d80b0004181e0110010a84a446400d040f070780c0340c8030385c951001044d0802820305043c20040b07036480300d10481c280c09000524070210b0922401304070725000d4200c10f10504444000148030200307803440c1a1090b4082880d400008582c1e0341c0039020b128811 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 873647401 1250 873646151 873646177
    0x60c0605072f030904060b0a080a0c08180109080309012403050d0f020c06070b04120804080405040e190614092406040e070608071107050a1214010905060a11 69
    0x10040442400e40395691041d11111240f00c00c0049018948584c0182401001c3ca0300040361a001510030203030014900602500050780740210455003242c00c000e40503080b500140d901c0d082142c1341c40009004001e00080a400d010001c070401180c0001500400025542c0e00070205004451500c144209200c5000c014100d401c424010754460340305007801f8110540c944100d0303002c04502c0000c0f0310b00d40d000500560741c0c04e8440d07042009100341270194000c0803840d490110440c1c94030343c448040b5801140161840f450f242c22030b40089100c100002d812000180010418841c0b90b450464028a940e00c80e01c540d40507c2c2d4001742d10700c40701181080381f41d24081c4071607250081000e0b40c5110580010510395111390f5540380c1c02d0280804010340c2000d400715482e1a81107090054000c0d00c1012541890f09954dc4140d006210329200d1460450803600d0f00c400f400d4030341c0703218039040544640c100355090240d8a02031140381449800030700c0e00d005003c5000c0070000c08190281110340340c8140f030411014 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 873648651 1250 873647401 873647447
    0x140301060f0b0d05060109030c1220010f05090f041103060a120f03080403051b0f0f0304080a0209040609050f0d170121060e070603060312020102160b04110901060c060507 75
    0xf20442070300056441981498070b240e03c140c9030b50300d02c11210302a4001d4800c030803611110604000041c20364680c0c0c1c203840e50b50b21004110784c0000911503201030030060f041010100d5081a2a00d40c542c8401071188002c00c2484a0b0004008a19480d0002c4440707601c60205190002005d000394049054070680050203548072113025103058561600203817046042080030030418080d011000000d0514008100c00303024010b0030406841c3c900600c40f1000345150300204001c000f203c1d00040d80c4042c546d410381e10700380c0d40c0d03a55040c440c0091500c07840203009070040c5544450f0a60012404403401403036904d804034100054165490b0000c024082c51440c83c000214254106600e4001900458400c1002107404c0c42d2141035141080b85660102021940340d000910400004080c520100043d0b84021410450140c150080c030011108010b0b1038500c0360004a428000405600080e00c4009810720565503521034000782000c4005600341c0340286004080f07403100d8460f81d9500c1c40184010a9009 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 873649901 1250 873648651 873648667
    0xb0a05061e1302160201090509070207090e0a0f0c0806070305041e02030c03190201080609041e050c030105010b040315142701110307140f03070e0607050106140301060f0b 75
    0x4148082000781a9000c070403a4502c014403100360000303142d014802005000d4044641c4005081140b003500f00034400c03040d800810040c0350707001900c6400c0b10300b152400b084000100b00c01909000c01010007a181149100e80402800f60706840e141c102c6001310b0840d00c550b80c81c0c8004070111503064800415002d500c00d4150401d400c054844000203000030160343e1207503010b6000034a480b0615803903080300748040469a0a540e00052100e90003001501d51100380e14003990344203844660342102c55004148030140e2810701c8000c201e01c0f544100054000c21107540c44001101c82074001e880100c0b00702410803e40b1240c10203a0149103001d1a20718805a01c6031505109135400410100e075800440d04075908000c1b602109000c0c45050044d100941c65490070a03a100910402046070840b03e081401c00005042c242402c1c101c079440161490107410742d020741d0000034140c2c440c10320003a00940c2403981c041210040c0c0d021100d03e08104600030407140c0e82e14423004844103144d1040c10710412080c00888 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 873651151 1250 873649901 873649939
    0x271704120c092009011205090f0c01051603110313030503190513090506010c06181a07021f0906020c010f180f0605060609100302130f0e0402010c03030b0d06090b0a0506 74
    0x40d13803005041a8607882d0104007814210752044556003650751140420702031660f030901000d2003294080c60400e1909a0059600783d44881818000f02003044800f044914840c090007a202c4c41c4c80301b07807114580a07549041460ba0b90f00a020170340c4051a160703041061040c0604203c0d00c107003041340c410300e4901c0e1600e0600f40050000400843c140041c0e01030700400600c0318071034544001e14100d01056181c80302d0512102c240100402211b01003052024041416000200314080341c0342d10060184501044e040034016000406000b801c0340d0010a03020303d1108103420803801000c0201c4100b04008008401d0b40d80d0116850700a8602c0792249225000f2902607006135910040c06400c042ca071200d031501080d110114082d1007000643d01281d064824115050040c0c010504003242000b80c90030300d4039108074a0b001600081c180301505421008141c007940041c2c141110040c82440507240c6420208040e0500100480d4000c2018000420302e100300d205aa004031400751550103000b041340900 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 873652401 1250 873651151 873651157
    0xe03030a09033c121e0f061a030417030103050c0306062403090102071209030c08010b0f010c1a01180e03030f180a020d08040e0a271704120c0920 64
    0xc01c2224946644500c65664021310070860620f150050510170307811110402ca601000740d82844906000c402c000880384d2451818074510304100055480d1624502908aa030341341c5007180312000b0201c000424808086240ba002e00e1042c2c040d10f88907540c4504002601014584021403075908001032079440110001843e8002c96407000145400e0b015140d400c06111f00202c01c50000702d003104180200001000d0250084c503c3c10000c3c07144006041c0003690b403452119080d030420413222031400c01d0152108004030103440720482d000455031170b5600060725415030308007409510b0501401040340c1c1d0b00002228440c104904a1440070b4a40c0d54a44a0302c5555070440c0007580304000b0484c0141ea104a1080030051007500b8207980e551030a2641940e0b004020308400e00b0030710f0502145404840403000c030f14200c0384651508070b10a040d16110271600d0a804824244c0c0001080205501c00110030a50fa107a000754941c00400703a8503050340c42074500125107581e064a86600c2140018540406 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 873653651 1250 873652401 873652517
    0x1140f0708161d150c390d110d03110c0a210312060605030a0b0d030c03051b060a1d0d0509010507381003031b060e03030a0903 56
    0x13440c2c40300b41602c0d80d9810690021000001d4a030041c881e40d0490840d66800341016100780c50b01402c100304a000c0074050301003085011401012100f01e46c008000d40e01c0b2090200400c000d218202210041c2401040909084a02621031050044920403490301d666000f0842c0c01001081e8001c2c0b152110801c460204041d04409000d0940350450900c8510b0003400d000e040d5987c5d4042e20307490040c5c7c801e0250360450408501a0489032080030109a2020241c200c044d010309003591354640340c012480001c0400c098500301800f0307100a0000b030001c180c00c803098100c2c81e102c500d604040b01800040c0c691110400e018080b9038104001c7d40a540607402a12031030f4015800c41d4081d03101c600f403410003c01d010f006a00029049001c19007c56865401c4540120409000c525044e085a0700540240a800d0b48220120420480c9404010b0340341c11034442131803401c0a5070380741c0c101000a0030141100640440105030700700a10b01f401610140b07222404940c045d91141c120031b028600c000c80008402c0 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 873654901 1250 873653651 873653659
    0x80c2221081b0c1e030c04110a0305060625150b0603010311060d061214030a091e0b071b060219140a02030618120a0e011101140f0708161d 61
    0x815407120354a41c0c06a4008056680f00350f149210b03000e00301410300b1002c0e81002c2c0300310308c0c10081e0f46449043c14240c03281d440c0c4509002425455030000603804d40241e80000c1c00b00d0b03030300300080e5400900960744406c80d28821541c54442030f51445944098800d60071000750024070a0004001144004104c050b103114090324840c40c01a0000707100c015a00190020704240b1074101341d2804000c8589240400440200d003d981401d40511005000041c284903038200f210646001a16442c1000c5203400181245c01800399120005c0c609654400640034110080c414005000184c1e540003048a0071402502d220310401c204041e0f641510b080b25584000c0c020344140b119140c0140c604001d0a030044e090b0b4003003d442c5d1000b50480c1442d001c2022980403005005202c00c1c89500d800c0303580346d05c0b4610b09080642d002c2c0c5100482d240102700c4c200f0801601030002043c0528041501a81401000355035150186a515140c5200d07120300860b07540d00000f003c03e00300d400c0300c803461102144a600020 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 873656151 1250 873654901 873654913
    0xd0c0305060406091202012d0608010c0207051302120103170c0a24090c0b21010b07032c060a0201020d020c03092b03080c2221081b 58
    0x5250390785448001c07641215015030343c03000380d014091000125003034000c81d0310081c400c404c0005c290b404440e4940d007100c0c1403042591a0542d40503095007158018010b0740b802080400f036462002580c0e0b05140c072906d401b81e4002c01c85510881018022201082e0684501c0b200592035691210348115840d8021403c5903400d0003040c1403004244180d00c606409140081464841080d00b42c8003401800c4111052614240081000034039510000003110640c0d28420386860307018001e804440707103d888010042d4458000820300024804c0030301141070181c0d5440070109841a64130a44e81070441c00305084801508150900745003c9005010003640d500c005403c2a180b548010140e0f0006164015650804100b04403503060803a559191044401c40c58031200f580e00725241034500c1612000782c2003181403800101050440070489013580030302c89109034580c2583c445248001c0090045410a155a0320320102c41e03966404007840c0a50444030040c6809846418251066550000301840380608 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 873657401 1250 873656151 873656153
    0x606090c191d03060406050708010b04051e1c031106100612090804050d0606031103010207021315030c03080309010c09080309040911060408030a030b04020f1b15330603060d0c03 78
    0x41c0459402179104810201c0c1071b0074520b2010b410804140c0040b07e00c0c100c14001089a80c0e550f444107201e2180d080c91500c0031800801c0400d041e50720802070411640680342980c0c040580c00381a16007560046030699080340c0701c08014015440032849404002601c980c070343d210a4100754000d00c4030030b01c2210200d00e440d65400104006c4500302c0015920140d84e0741040003071240c00829110001e81c214001c600d010316940c0025010405540300e1904070b9030320030010345a407502c4140d61010b1900414030781000380d603d00d420f001c43e602c1107464007529401e0140d054082406000100305641411002e1410405500188030003040f04040507901512183d00200503900c03058018009004040f0241d40e0b1000d0466015066500352010356009510401202c035849003840240c8100c00c40019505044050454049140030b0404c051085603421000a102d981010b000ca000c0b03c0c01801c42204003088046404103440d880401183c07074000030200006140742c41e008940344c035031512969100b1030700b0b922 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 873658651 1250 873657401 873657403
    0xb0901090b1302030f0106050604181509230103080904020f25020111060f0612011d250305060f0c04090207030518090421030e030c0606090c191d03 65
    0x16500302e00c66101482c840e106604042c08040403804004000f849103034603200225030b0f10300c5035214103060007450101c0c840914032b1a400610a003104404034445d01510351301d041000380040d54001600b800309030b10859078403100b0310005040720342109030903091464500601010754040402d5030b550900411500c0e0324460110140c2c10300a0005980c181205481d10014008105101d00c0000962100707041101360120010f003543d1008080c1c03044a0708002000031907024024034000400100e80c030107000210070b40d00181c1d86009500c003483d410015001d40c00d40a60f030343c08502003c1c04a800080008025265189600b0b801001840c00903207010fa998580b54100d8200b42001c070000386c00084c1c1c00c0303804000b8102d1044007e800302c9001d07030745007010355607032404d21012503a4511510f0050035401d0001e010342d0105c90407502034019a60b807001580c01c425112001164014440e103800b5002c00d5036050b82c0e80a440325240340e00b071801d280c1c00401506581e0600181d03251014000400340041590710 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 873659901 1250 873658651 873658673
    0x816060509160618060c020d02040212040215040806040204020a090b07080c0c010905031e03131706090c060a11160e102909180403171609030b090109 66
    0x94004060681c403440901448007000031a4000030400184601101308840c04401210480d1540d040034000c00c012880400c8071a42d813030001070360045c8085808800140010082440780740f0856103081c0030041c0cac106402650080e4022110150b200d180001c006044c140d0041001d40711904240c980306540c0c0104019540c400382d0211040304010654a00210040019040e038100c2400c25440c242d0038280846d550708441d10b00b00c10010665a209101000140201c070082c1e9050341003009640d4461414201500c28510015024464000020b1800300081110a9481d00080020b890400c18040482d82c422115800d41c04c42c3c0200e1803048200d0105021100062019000c1040a484c001c0348010000c40c06a0041d540308848001d4600302c41c0000105030820614405801d0721101c02402041e1410742c0c0002500305100c2e190180803c0c141c001c001820b591000495621032a5101e40104140d4104c600d403140100c1c003e5442800055802045140d010030304d00c0001444405513107461038010 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 873661151 1250 873659901 873659911
    0xc02071707080105131a040f030518090106170f06010504120c240305100303020715051c0b1309230f0106030b18030f2d13060e030c0d08160605 63
    0x48425416006c120041804a48900c070000d010341c25460300d502c4600c0c100024032070083c01c00c08001000c04281c40310f8407030010302d0440608401c000f90f84402010b8032101c120180c2600030042c0c1c40c00561501c13190450a0f21075034041e512136041600d03100d04042084040641200c0c03c2c2c1d540003022501d000c50024400400f0020440240420300011014045034009007482c8048030507403034103102113600083e03070314100c071000c1100c021149002641122030b40030755000482200740c1002414000ca1481d080b5804682040f01e00d030b06560003204510041303692442e40205002030841d001c00c04411a488031014001040d801d0b9000703540a2661b241c219001500116004581c0700144101003684000312003401020070001d52801c003070b4034a01d800034000d02156041300c1c100d02d0350748000c0c4c04013058824103440d45004000d03203820754000b02112007040d5000380300000c3c2050144005904e40010903021240010f00392008050f000d8440d25113a9100c40f041c0d042c80c0228000d14070000d006445010700c26 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 873662401 1250 873661151 873661171
    0xc0212060a05040c0e070f0e01020c060712020f03030106120f0f0e0f01050a020705060114060705070e07020c01030212040b04020406050d030905030c01020a0b070e1f051803010c02071707080105 85
    0xd0310340352500b00803003541c5401503102505038504005031b0580100002034001191308002d10031460400040b8600b0900482c11904040c2c080b9108007004120322400c124050160281c0f036010540301e1060b03960780400d210741800a041c542000c813440d24a41d211101e4800003440204042c1a140049401d807040300020721125030041426400450080c89180d4001045401c15031811a058503140e80c0c40d00f041c00b994042c1c4a0301100380c400ca9483c40110303658540e1043c150f4a9103542ca51085d8a031a0046500e88054081c00361041c00c00e40c030a00c01c6403480702417100c1d58491503c40b0380303400c020081c0040080f40c101e81d60300e6010600380d40b03511003815214802e9481d81c40316070600041c107081410b1100310f94150b611090584000510f0f0300c058a601642a2400d4054003050100040303c5810003a0740c91041c0d2009107007091030550101c000d0401c1e02101c0c01d2102d4a4124030141422501803074002c40c0141c01078682402440510654420204001000c50781c4164550720300074210b0b0420b44107429a = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 873663651 1250 873662401 873662411
    0xd0516150218040c1817010e0d0c0c0f15030509102d0e061305160303031d07060207140607080d05040b0a050411010806010201291e0609010c0212060a 66
    0x52031400380a1420000c0080c030b48170749002903070030110040c10b0f03041c010202c1000c0200f001851a0400354420b240810b510b50888229013800303007002d4220096003000303070741840f207040000c100381115003500804c940c00781e0803040c0415002c01c2d04030020500989000f215001e034111401c6041802e00408910840307012011401e44203404010042445e002c40450456083c248101d40b0450082012070f400200407070086000042442c01a01380f02c10045801c0401c04400008824154141e1010500c40c0d6283d441c0c014044200366002e503540e0041c481d03000141d00c603070030a1100c0c80512051410740403026140c58109412650fa21034150130100b1a4032401c5d5030783c0304101c10712080364111900301e481010100700d1070416440d50040c60b0641d01c07080d81806030803004541d65034801d40c4140b1070031030b150102c00c070344a00014201450440c205002e52090005041c841d101c040c041801004110009003154070300b00100300192084072042c1c8090341c1c001c40203004044040410301059106200306140052 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 873664901 1250 873663651 873663697
    0x19030305072007030209072c040617100b010203040503150f070906020304050d140d0206071806230c030414100509090a090602091002100b030d05161502 67
    0x11840510704010b00c0061401d007030380555070b0b0740410310b401569019284a44543e450b50025584540796403400c0072651310a890540103040c52441400000800b100c0900c400c542c0c0d10030440d080c1c55086900700c66a0020303552010350f80b056a0040c0e03030080c0107005581c1050380d50b40009003410b11400d154402c2000301000c20804805412030140d114015041079105141802c400075a42d02460040030700850000c20400c040c08900f9190002c480c10310000c03140003208a4400a44a14013980c2060104001c1919071510560840a10080c0c4000d0780d96203146d4201c281d19030282d2513404100c035070a070b0020041500403010a000400182139040025100c0c40d108505000350107030003180d00400c0210600014485907290b03c0d03440e0b0002003400b004120b441c1c150a10100074400c403413440703a0102045d0414400b1940120394a59003842941e810004031f40320000381501d80011158100024038108180340344444c141503600055409404581071040c81600d640c0e0403640100d02d114590405001244 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 873666151 1250 873664901 873664907
    0x30105040b01020619020306010207050d140115050f130906090c0e09150105040c020c130606030b0405090c100507020312190201111b0a06050a022503050a111903030507 74
    0x405810083c8001c0060340740414050880100b6902c2c07100710960000041000d6a2081000300301a2100408400c0055001e03d0503100404643c0b4068419509010001e00a4454100307841c017100c8000e416130b503041803050100124401f40a4681e01076503a5500c840c4080703581446807100c9a44141e5060244605003011441108402010004c080d03000c0d03498450000c1039a010741f81110130664000c034806100c3c02c3d09034204281d410090b504101d500d211240682d400785c0050085030303d151000c01035028800d0511054860450b28918a94061103c042c00f609202140300d510041a15100c1c0c2021844d60020b81000c148000c801e01c8400d0209801c2c06c44140685000c10b217980380c2c00200070b44401c0003114802c0d03001b040c1920020296695142914a005001c05445950302c00410046403420389243d85c029040890907003894840160800d0300e80000d80300d220549901521442e007003c1c540c9004440d981180b110090660107583e2618001546e0028040b90052003a100810a0315040c1402 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 873667401 1250 873666151 873666161
    0x5060105090117030d0b0120070519080a080f130602010c030b040203040507170a05060a02130e0408091c050f010920010503010905040809060304030f09060c1a060f0d0803010504 78
    0x1030f606040c411003c03070000000104881c08612140e2021908650400042e1601c0e0440b84224030034404c075543d0400c070701074003144004c00d590003100c840800c001c00c0c060302c05195803140940a0f0690000d8030706000708004002800360f080d20891070700e15100940b08600b04141203a485000582e44400e0451815a01400703160003210701a1001c500b9403809455040e942c0f1940d1042c54204c00009040358131540060016807015900881241c10754200a400c54009601c1080c5003903906031303200c82c04960490340c011414000e9410060080c180100d46040200c040700301e41d4141c0500a09807400c4000500600a0482c0f00650400004400c03049040c0026210340707403c14030308680344070101c0070801e0b030708803054a0644a0141d40021580d40d64a00700d000c40c41072160382d590141c030100c01c100805138407000084500d000e598684410a83d110001c0da2032000c5404000c02030704d05222048140003903480015409540101407401c1025508081010f60030310600c141c0d0040c03000001800242003034050 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 873668651 1250 873667401 873667409
    0x20a0b1f0303091a07122a0b0f0a111210091109130204120311030c0106033801061809060b0903010e0c0108160309080a092102100f0912050601050901 66
    0x4c145400010ba5424901030b80801c140400d00c00c1e01d44030b014940343c00c41124078183e8050385c41d400c600c0e50b0780d0038044440b200c00c07100242c1e0000c03240c000a0a604075800b510f841c13080100f0160f402c3c2850000c25038440c18004205c00310221280704005510000d034010f404e0083c1100b5030155444100b80e040c0194044480c54400540d801004104040410030381440d103042d4162030720100c14001c6801980c03c41c424807c140390950301b030a5022040c40003000324070b4102c00c014111400340e0710403001000910600080c207041703c05002001000302c0740c010500e6004012420107844038880e201c54214ac22a003154011070145d10001c80c0340c0300b040c102449529107a400f400000c19940c0c001c0b400007060035034000d10310305000160140110350580070f0b0708440c101e658412449516001080d2000300803030b00c0c0b03105000031039428080c540300c1045040d0140486075000303004001d9590300203e0565240c05690040340802c03030070300b000280c040349c45007118280d40d10840190000b03514100c200800054181c00c = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 873669901 1250 873668651 873668699
    0x12030b011706040207030c06090b07020d0807021c180b091c11060c19080901120902090c03100504020c010f0e03180f0619020601030506070c03020a0b1f030309 70
    0x2811900c80705100300038950200007190301590350702243c0b80c100c80a030424034004000508240721103080000701c8003071a200e1102907084507092007040340200c0300300c103090750f2200158201c800340c0c0010400125400d030126801e400e01c02000b0144880c00300b074013541903000c1492064081008621072a100140384128000a003070b00c0c1d032902e02a100da07102c005002110702c0c465000001d41080c0000e040c840143c3e601400142c0505800003170501d03a200d41c0c0191645030020b94090751b9002000041d03c01c000001d42c0240c08070020f03030364107403d1812981c40a0316804411b2204080000c80e6034560000b411810005000411001449222207041e40c540b4078514406401c14081040719041044000c44101e80c1168148201c0d5100720120f205071062104218280d1444820901441d4000551130304032032250b42220195130314484100c0b0124544c240040058101c0007040c000303e658030160981001003241d1410321071859010f802c441c00c203543e104030045050b4007005c02282d00c0c4400c1d90060081001 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 873671151 1250 873669901 873669917
    0x80a0309120c031709070302091302041b1e23070b0c0c0d0e0a1d2703180307120507031109040f020613211112070e041e12030b01 57
    0x1980191900c6003401044c100c1a82c03e0002401c03003202040100002c5401412000300390030701a244681c0003054003c182d000e01d0070704040c842040402c1000086014103a41e68040c0c200c4540b00f02c0c40481c40c4070301540c00b04201c680643e40e40c1d0b02e507000400010541d0b50741c1c40d56100e826180280700302070010500c004540040c4005161004040340ba180081018607099640100d480006004030405400003940c209002603141c80101d441c00f8558004c195156031101c280d5100f07002040828a100507060294100340202800c07800f0f07082103950042001000c0e45c02c2952078600041103204c20001c2562503500c9a4010828000b807281000a801c0c41661280210700c2c1940b68400b00c1c05060030020300441d030000b2000c4186490180b00c0c00500000003959032000149405d03200311005141042d42c50712045c0d4403060b503500d00081402031400741980940607440c64100385c1011200010002e44000d005e07100e1511040307c0064201005510070314880e1410440800000d0403103200c0142e03941800450 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 873672401 1250 873671151 873671153
    0x1050a061a0304050102120a020a18050a1715070f08010905090a141c09050a050402041d070c06020c15010e0603060c1b0f0a110a0b0403020402090d080a0309120c 71
    0xd07055240c0100c1c0800d10705940b615245081402441040a1842c0030031140042c803a031204907400500004100d40c2c0d0380203130002d01090301288507810740320315580a100760000700880802c090152500d00e12340710036601c10b03408012041440320003c0b40c02e0000102c84030b0b0402e68264122074004d0143c4034400d010042da19180c8400c0d9a12201c001001d042081c505803600000c040800c0048111407210b1041050b080e6001030140c16003140d03004140c0f1543c903100000c900c6081ca4030a8030121102c0310005100000c5120741d1440851018054070304010041c1e03a6000411190b00080440e10704540c01010b01460f018650380e02040c068005104010403001409000e070703030010380290400f4200b03801a986103030403240b41907908111142d2061a018044007004184e4011070240011802038140b01300b4001500d0400160149600804107440b000740010700160602d60f010309a41c0c80041d00700c850003030031500c4d20f1590350007580003d00003c1c4c907114400c003002009031074043c400d000360505003007803111 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 873673651 1250 873672401 873672419
    0x31b02030f0306040902101808160302040c020f06010b0301050306281a03070f090501150c0305071505040501050411090705070204051b1b060c040b1912060b04060201050a06 76
    0x180d007036550040d0700003001003040c80d40c03954003034441e030f941c005c0c100ca11440c00300c0740240900858440c1e2160f40941080d000030401400300707026610914000e01c542065086a003000000c1500c4c0060104610986510300c4c000344040143c2c50103440d182c1003003511307507161004052500780000c01c0309180030350300804216211560101c03a0300503100e62034085903449029038154008160082002d0b410300c11190000341460741460900107951f8040024040e0b1b0b130303c521000c10104078201d521000074008a002c400400d00c59400f41451910400311001d003081201d8481d42502c1c01071750180c54503555001840700b00032100782980c200400039039020f0100e00d0195005007140c09903100c007900403031301e600000c0c1861107605c00d010075448906480e10b40f5003d40401d81c1c1c0384007a000362032000c140b2800300403400865626055400b154103244401d8900305c18102c2c00354200c6003003c5031405004c01310f100d07480c560310f40d80178050182101484403038035035240100c02030030340f0001f4001c02041c070b2812009000310070f5 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 873674901 1250 873673651 873673657
    0x5032a07120c030e130b060a030b0a05030a02010e010f0306050d0326150f03030705060a0c140415030e030c010606020f1015030b0612010213031101031406040f1404050706031b0203 79
    0x1000b2220103558400c20321700e0102803c801007138940d03c500001108105150998001055008203550082c0810340ba00300b0305640d005402d4000e80822140d02d4000407542c4a00c0340c0b41c80d01c904c45d02d00481e04666510200d41c01300403014085020072305400784c60001c079141400600310050302e1007010f54603040946c26004078400d0607410a0040c100b0b2040c4040d240ca0400488660755801401c407040d03840c0c0304d140e803401030030b503419900f00181c0c040d401003101004c04025a81a18510007212035900c40300e600c141e00500d100c0310302e5500740c0400d0000d080a0b0710284580802010030350054040d640c941c0d000c045c00c1844000204462394a80142c010800f00350851000640303031300802005042d10b4140000d4105081e47e0640d41c42580001244008006480807843c102da118450410045000c03d0040d000d65000880010444072a0000110310f8036041d00146030004409000003481d4001341c401c180c03452011101564240c0c810359080141a9242c41000d0019040d030200041e0390390344101c000d407644 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 873676151 1250 873674901 873674927
    0x616050f040e0c03010302120a080d02070609350f04090c03110f04060e0108042f151201091103070503101d07200d05032a07120c03 58
    0x118020400340512500201150058456901c580000b03180101d81e400c4254800d010403400340c40f00e59004070482e01d00003208822035030301c12900c0c1c0c280984a100d0030000d4002442c1a00e50644030144d040200c0c03541d410b0080100c0404040032079400da081c90608480c0300040d900d98200c50200019000c0002c41c5003510241d5103103940200f024000d50b4270450152200c099030000701d0f4000201d009c02000510028402c581d0951907040d038a402d003500540310058200c074003030501104900c81440403400d0340c0603000c0b0890820000ba58500720100030400c5d42c040e003405101004000105002410050f580d0240140032600050012908002c03641c88a40800341c1044103224001c400b04079140c101c40c00120117081d8803844500e0280600720144124842030f00c0d01008aa880c4540d186100c020f498000c28980590307000b407100c81080307542150300380d000404001c3c0100e4442100c65907900c0110140072403aa642062a40b20403042c1090913400c50f407801014203200320b816100303000a810885410403c = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 873677401 1250 873676151 873676157
    0x71803020112020f0a1107050402040b12060d12090302011d0303040b0d020f12010e062b0311060901090203062809060b0d080a111b09180a05100507020616 68
    0x2040080740d6000f90259903004451440c000c5051100c0d00d1b848510b0864943c400343c2204e1420350350b01c060008910a601400020941c2081070f00400c02c0605400c0e030300301c18050400c00301c2c4501070302c90815445041510300e00142d1001020415503900021a1b0144001211070001d1107036800c00081c0e41f44a544901180c861003c18184161080b55040c1c0c5e60808024a031541d0b00c0d02d540c2d142001e581c0b402d026055950500d400861003d04000b0114000c1d040030280002c900002131502d40801540c101c4c00b00d0400101c3e0201e00261a014050140a00500c40000c12541c141d80704041c00d0030801080201402055198513203000c000a050f8085070b0000c000014a400300c45c01c02401401a1010154000840c0f80322042000080b000a00d1700c41c1c1150b0320b50322500d41c2c0809550302c40030f0468050130b044400b0041e5082c20719140c851680c2000101e05541d2400741c1009085003000202c0000340c07a80d4108080182c9184041d00500354004402d1000d80743c2d03072401007100168040342182c1a010 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 873678651 1250 873677401 873677417
    0xe01060918031b0c09050a1103060a0b0f04032f10080a09030c05030c0706020c01031a0f01030902150a0305100302090414010e120d0c11031b010f0f140718030201 71
    0x305203c10700240250f65008071803d1002515018248003078041640c000301c003a45028005403925040c8402d590142c1001080c421509181030f041c0c0e1100d0304032029010b00c0c002d003040000002008240228440c0e20a005940b030368854002e1046400c44c1034a00003070245144004022006a0061180f0f034060100d20780018440d1450404840100f10300c02d005080d0b11000a03100c00c5004000f0b91141100c000c0d80c2201c0000341c0c0c0d2801101550101d9002d264040c403161200789051a1043e00389030a50010300d400184003180c1c1c0c000440e03841501c4215010a1000903203035540c0344d81402010b03400444c0d120700041c8186154080b68a1060041001d0000840c50894001c448402c3d04500c82a174003d90440d00003da5101c6d801a542e44803082080a2601e40540c2654150007003000340303003004c004c1c000340d41090340c200040c018900520034000459560f032183c0c9010301d9071511442503440c4064800003030340500e145031203800c440d0251884051212261400f2481c101f40c0103070f101942e9081c82e001030 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 873679901 1250 873678651 873678677
    0xd0e160b04180605041805010c0504080304090b0303070611030a050a09111309020901350d1b0501060b180904051903051e030f010603020f0307051c0f0e0106091803 72
    0x2c01450700726642c40750501903040c21a404840e080c030611b0b405000200103040394514141c41d94400c0788038682503030f00b00784800c100026441d03002e8424254083d0507240b5229103652443d080340c40541403172900e05008000e20a80072410300c42d05a1044118004004807107a5446180c1c2117001e5104503440b4040700c0f07025060740e60a40d00007490103580a00714001030f58440003295075090b145c1012250342200060410402804500550751041440c406083e910200000481c1c9602c1205a450382c5520030311001e00c001007092203194000d01c0d4500e59036890b94205402543c280c86031b04055486044600103000116001141040c0407035201035030000620b240d842d0544281c001c200044040d000150104250104440015882009800c0d109401681c80310410340490240030007001d1400c0c028800224094019401440d414038070150340386030440c0d0391012109540200c00a07036181501c0b1701c51710064a402340100c3d40540103840c1c0a005403402401640103981d00441c0140402c184061424 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 873681151 1250 873679901 873679949
    0x1050105060d1e05040c09290f010203120703020a1202090315100e09010e060c12060607140102130501020118020117060a080a03020a020307050d030c061e020d0e160b04 74
    0x100c43c1d2603034043c040c0490724142c208821495002d1040f52001c50402e0181c9002c45086460780455409540d0701010780104036040c81180d401d10f030744560562004200c07000f4051041503410344a4010390b500507917508005903006101c1c40d480c0d26a0103540303006200b4090303556404100f2485511040e02400b00340d58404c10201c004d80740c2507022500c01100d040c24800405410b411400503580e54208842d080d45940038020406d00c540f030a1103200940e65000f19801e03140070701c01400641c3c000c6458080c03407045120f0840c04c90b803015806664045000204119a503020300030902c0c00302a1100e4245041001e80020f0408503400d03440320003040002e0005041c036611803000c80d000c3c0c54020103d500001c1c2919000c2d5031003c41803420b074403d2044030381c0000c0394608030400c01e50031541075581d84503011130303540c502000e0800c00246003400714103408802029819031024019184400da000710300c589103000380d14200182d1484440e0310b880c03002020711800340c441c01114101c80a004410441c4060b0580794 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 873682401 1250 873681151 873681191
    0x507031a042114070503041509030209010608150a0909051011090f0d050a0803071407080a0513150504030b010b1617040306110d231305010b06030a02040608010801050105060d 77
    0x6802d9600c3c042400400d01c040003001d441a24104a44180000c0303407002c042c1c3e08421980310003580006008018810a03101e00c010a0300504d80c8800d03285a03082c03080014424a008d40c21047ca042d503519102000d12204106035040509540f400b00103605c20340ba04024a0b1107030410041c017136850f4440807076007038880310352001c400c0c0d0b0410140c52070786016180c4403000c0c5e4401d4441100140340b682d2140305181c081e604842c4002c1d4480ca445180c035a03000820366042d00308800004410b8070707915000640c0c91020214048540840d41c88640c1c4504502e00b2968061041c2c10082c0d80010521035404c0c40c030002004507040300d030850402048880c1194040c011031141c0d0300010f05041c28089036407403480c618800342c80602e000081c1030001c002c000420100030712444994a00b025140800314410440051340c849006000d41c00106044503e18040360352644181e46102d442c40d8001000c003c200e6010048a0241c10800b0080c0081d5162000081080c02010094a5841c0c0da41032280500c403101c01c41 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 873683651 1250 873682401 873682427
    0x6121c050915091516060c0c1502041a030112020d050a202b1b0f080c01020705011d01050d1407030b030d09180f020f070507031a0421 59
    0x42140b000da11078400c502182c1002c078545005000641102e156450781c03100b41c4014000400c1c84860f001d16a4440c007011b0181c1141107014481e1600307054012666110a4204040c0076010250b6210b00c1c2c4060780000e07048501c904c00e400c0205000501605003a44204ca603c29011143d844415800741040c2d030410149402c010107285e000c041200d0383c0e84c018850b40301c240e1411911184505251109080549808070401380703920142500d80f000140100c1c00c06541d813665030a807080b4683c90b079200d602500b8540d040740007194015031a00d42603603810001800038060a180c178101c1844965810302c440c0d012440c0d82c5041c00000f1a000c00d64800ca40e01008030088224040c3c00305082490300a03008220300c17140f03180a4003824003240c0f400c5014400190480b0100e050360a04469003100c54001449000d608200c4141c08100c5080e00400040150010350301801c003521040e865441c10258690311184c03c00140aa0701d002c02000c02c0003982014ac2d80107410490304000c030140d81040b65207100b0114 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 873684901 1250 873683651 873683659
    0x17070506010527340807080a0b0d05011410030503030106050d09021c031107050a06140c0d110c031b06030702070f1d090105010f1e0504110c0606121c0509 68
    0x304004d031002c2200f0700c91000b070b45002211425200c00100c104040c0007504424008074101c000410321541c41004c04a80c010302d20f180c0061450740107400105d2400c4000406c0d0343c640c1d1501c00844880000c042c1d681c4c1c02c0060f921a14840e0707403455564a49030b000c140b040d0300c1841404646460b02d25002e4000b24807840d0f00800042a0000f41d10000c0007480803c00150000b4502c10020743d144440040c1000596500034100c240440c500001251083d03199400000494018002042031600411480740c01c03083d90707100c3c00c3d00c1300540e0a8407854030012605480c0300354880b42c21800001001c0781d010507000b02c15692a0b50381d1f82d0360f120507031510085034420b8280f04541c0d02c0003e000360008901c01421031800c1c4060080d5180d1010b45800c0c0c600a005050740300030304803010030076405a80c81c0404441c03500c080707a230070742603690700064203c881c0c651030904100e40001d10020721007810700c00f00741c0c0680e0859900410702540021960b40c0c0d4050441180341c85050300c03000364940c0c019410f807911000020 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 873686151 1250 873684901 873684979
    0x803040303030603110f03060118110a0e101407110301090515150306100b03181c090b1809070e03120904060f0b031f0302030a0b0103170705060105 65
    0x498000c0060883e440140c44074003034850094040e180071807000a4540000740141303201d03400c1000318035880c8200b110344540582d40b007005070540d0301c0800c0581125039075501c83c02d02e08811401072100001c003001d40c02c003c001c48100c040ca0b2a40c3c40c90143c07402c803600710030740c001c54a1000d03000c03e0050003248005032561040428003080c0040c64102e9034483d040007847d50402824100a240e44e4a100381d8296100100012040c001d411003400599800b242544070103811480145070705041403122188250000a40d1440710905908040004010040300ba040c1d0b1500b44403041c0d1300e00d00d040121801c1e00c50400302c8041004c3d81c0c130404040c0b08c0003100505803841551041000b0780643c1c46995180d0083d03003414070006e2181001c003146c40854041100403491595800c04403465003810005603103c40e0700283c0e01101588042010514041c0714410811555055040c98249200f0503400c00302a050304001a200040003ca11b0328116141542c181c0c074062040c01d00c203d00d404514000c1c0200441e59 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 873687401 1250 873686151 873686153
    0x6050703170a2406110304080604120c0c08101a0108041203022101081e030313031b0521031603050c1b061b0a0f23031f23091008030403 60
    0xb00350b20104c540c152201a00c04540c19003964a9001c1c61040761300d5508a01d0015010504402860303000f1034180c585800017181c507580b90712000358075400ca03902a6120300c105070040b0485100e01145403070182d041c4c030b0a030003090000071308650340140020500a0744042c44041d484c040d80560b8100b401c2c5034083d494001c0c2e20021418481024444d002c024032030b400e1808240c12052510081c1340d4040000746245644107866104040600b020450411a140b40200003d81c440303190014118400d801030300070300000c9200021864190803d00d00950720400038040090f55420f0480d0388007156083c00701e510742e10745000e010307240600c0c210740b254441d02030b403030300618040800c0701445117800c040702ca0b203541c445402c130b80c80ca070062050500105100c1c42e041c004490040700c40c42180d40204820410700518510105000d82007503440d00a00200011010100481c004c100740140035070b817041e08005c44900407800411040c4031850390168540760040703500011490b517064080e20054003140c2d544c0d50b403 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 873688651 1250 873687401 873687461
    0xf0504030f02102a1205010b21100501140903100c0e0109050a170f011a10021612020d0213061401080603030301061107081b0a09020306030c011409031c0906050703170a 74
    0xf881d20a02c1c031603400c1c07274000c1c0c0380200403003d409a00d420150709042402d05006450300c03c2510220240501c007070118480d02d40d400c10031410903810151700420482034000c00a4013944609010754180450345d4014015034440c404c442003100c1c680c003246801003d13108800360501100da0100d4a11f5420840444e80110100b001640441c5050342c0c10944d0040c254001c80e1a03d1404151460040b00c04a04111040c07010094001e0140010302c14039540c0b02650000e03441040444204040c90317220b20f400c115103158100d03540702400007030800342203a1034880c000907241d100501690040c001003914803041003408000c0700b005444040211000e00f82030000c0045450f0b6040d00702e605c54410080041080b8005009581c010600a8000d0a845c040000155513110014502c03446031001030001c0301c40c60b42c04010340e0280788009034143c00303020328200c001031144c072003a0041310500c40e08001e002e00003030380068501121006c4445540c0c164072844d08910161460b0144942820405032003a600300a03 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 873689901 1250 873688651 873688657
    0x181d07030c091d0609160e01230a081005010306030b04080a02070b0a02282112090b0603070902030c1e07060527010b010504090f0f0504030f02102a1205010b 69
    0x8541024041c2d440100d100106c591000b059000038000341c01c1d00c1100c0d4001d5078002802d940c1151083c403016400148070920390089a21301c000a00e50505020788814855200d0024140a02c1d0030321215003161220009a400540000c1c400b510020710381c501a80b080c0041005032124030407030b0342d4075103002030001c0d030340c003109503869003500158103410075050305070307680e0317410141d84024040d0f21201c0208040c41101071408400c800d00c81c1041486c2e00c82c040c0b41c41144125440380d000c03002141402401d2600e0b040c240e40000392118410014031488400c01400d41e009a095181d12000038084c1c185400704501650784014040d6007400144090001040c0620700c0160b011503001c4a1220348200090036104080d900c107020500810050003100c6880c0c02904902490420101d1181c40f2410030000300c901c1190141c0018500104040b14641d040c04688406840d54000340b0201d00c81262422004408640000c0d401101819851085001e04008500b00c2c40c80c1c4410003040da9682c1c03009545034 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 873691151 1250 873689901 873689911
    0x30c070b01062a11280603150506070c1a091503090c0f0121090f03020607020d0302040f06030504150c0305090f0609031b0a06020406181d07030c091d 66
    0x2c5a9039101c4811420018543c09450b0700050b0b955407401240041c02908001c0b40142c03002074001000300c810b885480380104c40207151941d400641921000f131044c60060355604a01d10035041007025001050075418001c0c1070720859407015500124010302c12840d881a001015080381491466092031101107014510986c0f040d8140c690700301400c0108400b65240c000e409003ca400c81c7e100300d2203d0003205004c412800740c60320008111090b51502006a902c100048005034420410840c8944d418070a504562106040c1541001d084c1562454020390a004240416a0b128005801e20944441c1c164203074044540070040208980720003405890100e520705170f0384c802c01548418034903001645c1e51103034500f04061814191410004101140c002d203a000c454407400f155840407462074402080103145540302d200c0b02218503004d66a084500d64020114041c41c20031481c4401c1c80d00d841694401c92034580000c20340280d03e400d075020507094020710101c0b01394040d050a441c0c070141d5034502417 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 873692401 1250 873691151 873691187
    0x9050f06090717070e0409020d05010903030b030d14090a051207060801080307020d0b1305160e010f03080702150f2b0213030f0f2f011d06030c070b0106 67
    0x1940c0d8020042c1d49840f04041054824000c500020310001e210f40d8400d442e12100401c041406001a000258030412515043c2d6403a591900c5900815406214a820318882a005080c49400045000d4030455841900705622400000e50320499502d00ca10300c000b40400520741000080084c140590720b0b0064002d0b0404104410700104940c2c2000082d40c540721b500a1108045000c0c0c0da03101480e80d2400303410845864487d0350500b000034010301590010040c05000d01c10705a2a01a00348c2d080030b01070307001d0114146910005c0c80402e110008454071950103550000c0210005c011a2080d48100710300c0701260311000c140201f02c079612500498030301e4180429294000c940388418012481201805c0c44a0340340d0307000400008420303a002300405030050703120a0854241381c4a88881283c1044515280c40306071002d540c0c080b11100588466020a1a015150b401140011700140b01d8681a152051402000007403440b6409003ca0301e4103540036006030780d039594800018000442c140001055 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 873693651 1250 873692401 873692419
    0x130b0403050f12090a1a0c0102300f0106030c020c131a091e1e040c060809060103110f040b0d0b190b090105060a0c0606080706030e16051909050f06 65
    0x160a403d000d07511500b03030041038203d2461400300c11558424249060f0110f0190512408203000401c0c03025010008036a9514241e0118002c86c0c45840321207410605c03080c600b01c80030701141c0842c0740c0d5207a05403101c1e0f041c002100c605240b016481c08000403005544425021031081401446030025107040c0d000321840c2548419840421244040c01c44811104117903080ca01e40c0c000043c02c40c82c641107540c003001d61061011001c9190381400c3c0888003601c0c4983c440804000059000000a07402061000a00441c0d411550344c051008a0810024480c00e00300038031030859601d5500009008900802003c20064249405001c20404480c2d003502c09036180111407052510780140403400c0f800810b4988243e0034101041120303080840e1900c02c005c0400c0612000801d14400c0c440034060320b40080003500d01c0d0150040c1540c0004400c2c0700c03190402c01d0400031900086050318141d030300490300c81d403503044100030390320b48149242c5c00240038900349024001903081c2d803201140104001c0e112401 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 873694901 1250 873693651 873693673
    0x7151209061e0f200a050702010909020d02040e01050306070e01033201050108100303091206020c0a0b0f090c011706030a120509010915050d090c0504110d050a0b010c0602130b0403050f 81
    0x8965014008144c2c0600c0b04010484080744100020840b051050410034001d80d150428841260040d281d015070f4664002014005030305410754041c01004200c0082000f443c051034006e080c1180700990070705240d01c90200a000303901d030030040941d00c1a40018195003522080110001040a104d09400f1032b0760040800c03000744150310321005981d05601c480100d5403400c0340c03071284154098000d07150690700340013113207045809105035003a1318001c1c80c131646641004001c9004c900c4000d00702d00e0f01a8800417094503544d81200c8803060543d240030507951566201c03004a400c01c80107010082560790155a145085904103014044001c0c00380c0c0e50500f1741f501e5141c551101031442e005000402c02c00d00a964200d8019007001c107989104648081c146680c40c0d000c101640d006001d00304880e900440c840400e00d01c030348170305075010703a01030b0040c07016041000020f0504043e001c0c02034030080c0c000400b1088021043e0000380103201c00d00c0342e08e0342c031607072820038544500e4481c20074a224000d031704c9100 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 873696151 1250 873694901 873694931
    0xf061b0105040212060f16050706060b0c10020301140103110c07081509161205011113092910051e1207090803090d05010f06060e0307151209061e0f 65
    0x18860804800c00c1481c6c0d4071800c40c1054650078034403030002000810004240044c2c854040c0e14003c290090b5821345030418448041c5c240407048102d20552881800104841100716280383e423900c0c028280007170300e1601c0d03501d00701441c458a550861b0340d1083c0400029102c0c2c000880643c5c4420007071090440e610748414054403110100a0b03c4401c03500002d0600c1520311b2410001403591080c0d00000d118002e0300100c1c401e0340c000b003107400940d0880c6601040200c24901075501c4255043c1c0300440c001d10f140040c616984c280b070754007500810f96806100318981c026012681000355450007607840c0e40c400d1942c14981d502104000444011001c0071038101c90180c40070b4400e81c0c061001a600f0309242005000c0384c0385040c1c4080da1290740303e42000740058454420180030345210b81e5486080b803244010705242000f51f45c03281840e007030441c0d8400c1d0041d6220b1040740ca080031400000c40d00c4d0040d82040c07406882241140324600320b010b1449007040f016948079100c888030703800c000d001e0b00400344030358 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 873697401 1250 873696151 873696163
    0xb071b08030c0f0f3307200c030a03081e0114010e040b1f02120d0e0d08070f05090a270c030603050303181905010f061406090f061b0105040212 63
    0x119081d0744c03100743c00540082506141290b442206064400540d103d8600d24544c50000d075206e0340401c5041c52000302c02001080380800e4600104001c190101810700465910606003d010701040403540210344040c0c6010620f4010014171504101d02d941c403603040342200481207030854003095051655082740d00702401030a1603100c000b4860110620294007000032030403054403d00c00c500078410300000e0181e200010f004c0150f06444001011446001810301e85902444035400344100134041000441e03010000a038171041e203252a82c0c84001c1070700816210101600b094001090030624107600d1216402c41c9445495a000d09000035954a2400d80884080f400b01074060340040002424100b40485e02000c0c8444038030444043c0340c2c81440606181240c210304031070603510740710300e8028100705014407406007180c040c1068240d135800c0d000510602c44c0034080343c0642c5215851a0003076444c0429554142d02c4032410407000045481040d0080800725001c034802e031411402280800000641 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 873698651 1250 873697401 873697423
    0x32d20010908070320040b0a0f0e0a110a0f1b0b01170109050d0c0312020f03071713110f030708031b030a09060e03010e011a03120a1b05120a0c110103150b071b08030c0f 74
    0x109140c110dc034141142d0510795010240148030858440384510f040c8001c0c041c9105000307010354404c07541031041511981c8400302c20401960704020303409000c40c0e4089070088103503c050900212000243c54180e900d2075a0300070328000a84003248134100820280700451040040e55070340d00b0545c00403030545483c0b6505682c541c814040010b41c80c400941c4811541d804104000c00c2440307040c40420000346032120a8000a03400d400c0441c81c08010910392541d1000c808445002c0e504103102440d0062a10119200d12402c2018590016515840030361002e06000c05441c002d010707424000000e807000004890701240030380700c0c1c07502250008140c0f805440160b441c5030388907400d02040c0400c803000b110b5100410384060148a007480d041c0c042c800020f25003090941c68548100c069428404036400c0542c08450606060001034083e5880190725101038841650105807610720340e003000c0402030041da41040701e10300c25400120762800000003602c2c41d0007804003101e8030640f80c00b204c80d840e1000400 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 873699901 1250 873698651 873698681
    0xf020606180a1104090204170d030501080d12091a0106090504090503030a0509031c0f0e0a02091f210c050307032d20010908070320040b0a0f0e0a 64
    0x100d00140c500d40c10000c0000c03c003001d22820f054444000108070307801a4030400d8804000c13032030825034940502030b003101c034200c1b41020490756250411302c980307071403405141d41d0412200e01000741d41d4000603841100640e0b0840c071355018902042440828480b020302a10303001c120300310340001e103030b203400d000da00c0a4a500c103026505589aa41c0c05901624010b019014140000e00010740c001030300130040c41d007003500c2e008003046c00b04019000c0c03402c135400310340342c1c0e071058121080c0c510141e101c1080c407503080129694041c1404004824000c101c0000f03400582110803040b8442541c40d0036442c1044c0e072140644c08080740e0a43c0c0b802090765501c070070320005000020228602c0c00508599440c0b00300009403154108110700141e0714508404844180980141d400c6a1114607070759100d011000500106402403120500710346415031280c02919004007281c42c40a070b0321b001174407150059240420040c124100d1076458442c0240c105d08240228088262080c0009500c0c0446006002c0c007103070100 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 873701151 1250 873699901 873699949
    0x2040f0207230d0203040b070c080a2d031b1b06080103020a080d021b0a0b07032d05180a1a030406200f130e15042004052206060f020606 60
    0x900001400c8d00049020381d4101c0145400241d0b0080600c11801a80c0c410080c04200309400c481c4603150743c200403a203540242d6104c4001d8002908244855110982d140030840c00c154245400c1002140b003408544400701c4003600003c10b0b50300140d007581664421114684010b885070351280e5134540010440c801a0300c100d100c0b1142403040c4002200c4891301504503078003140caa11180140e540215400c80001c0ca58801c20303110984001609d480c0051614146801e400180e40014494080e10481102c0c0700c910451120443c2d0f12180004010a00c00395070744540d03040d01400300f2032600101e0f4156041d03810503414090720b6482155200380c4e4481ca403003503420001c0c000718914242d00490b091904050803508040303850090703403082d50b204002141e1a0704904d15540280302c1a2910002c510080b800e280644400450301c0c0350a81d400e403803040e240105203007400110103503c16554940405464940000407405662117000e003420388091360200c07240f0b03880d02ca080c007035100b1641c8080d40b00a400d43d = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 873702401 1250 873701151 873701159
    0xb070507081e04081b0a170a05061609090e0d030c171501092c0702100504150b19151413060e09150d02040f0207230d020304 55
    0x60006002014091600682021202400c064030881d40400c0510700354004242044110b0007000074803031244c1404448040c414695001c40d8a40e0b0480c05400011a0204820528a0390810102c20800d030000d0403030b40700c2e05101c10020f820744100c24210001070100c0034041070300301032801500c0c65024010010841108016000c80042001c03000340c20030803292018000c0000c04003449580183c41c4040312400d0000200009405c2e244568050f2440d82c0c00b106900c1446160641790315004200300024030599075500301e040b400c092505125070980c5181c4403e0209100c02da0956240c48001140104450040d28003080300c041050348840d880c0c0303c102a0144004558141d0710360442c051810040f855001040c2c42c4101504400f855008913000080304001595000c05008480c1205943c00003040c02e00700414004990640d9180d07000b406020120821034841c0d6200c0f60241c285040c0440d12001d0301d10f002d0b000704d80010b85002502c072503c1c0c00e408604102180d4408450aa41c0055140500e0 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 873703651 1250 873702401 873702407
    0x4020c0309300712021e03010e0d090f050109090f02120106031b03050115031a06040621290621060108060339151c090201120506130c031d0102070b07 66
    0x1d110b000702c0081b00b911242c00842e403002d0280c1200c94400d10094001d81c0040f840c02845425660321808603816812010012660041310707500c242c5840e40400305003c0c0c04405000040d2003401c0840c2c2038241014000a507180c2c0c940e0025810750a01940340151000c1d0380e00c2203091f20001c1c0a03103d0004548558072072024080d9200301d4580b00c0c11300b06008802014000a50380341c00551100c404200e42c0491503d103504805000340784413003100d00400000389030240900521a00220380000040c15040a031561b60346d07003060300d01880403c070b4200b81c0d00d82141c0c480c844100040c0c811034042400d08020441c50b1030049146125244940d1070800c1c0190401c05801406c82c072100e00180c1d003103c01c030368108652100350705911110a1100b81d5652070760015a14900c0c80c1e8204031981550b0715025400006030f82c489481c4083d2000800c001c900e54451b200080c2d6480c0c80303040100340e4036241080f0707811100e0b01074208911300903816104181151800c81228240d1042900007001103000000240790640 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 873704901 1250 873703651 873703669
    0x4021003091b0b250302190813031104180201210204120f1407050a060e220b031b091b0c0102070615050d0c0504020c030930071202 58
    0x8090100d4100c07580c01030b40e440b02c0d040a280c014180100001500300703400101e04021a00348000003020310500d01ea40d0718025250807011007050034040f00d04190505011807031098400141090940c0855969640303000c0c0d030004565030200d40250b003800c0b243d12331180907800020b08550107031100620ba51070b0040680c001c299400069901039802d1002007080100314840d00746003072041000112904460401004000f07029922000c507500c91542441961100c05508084404c24101100c3d180040320014070b40f07942c904620002c100b0244a1101002c0380c9400c44c2c1c103070f43c40682c20b07038418100e1230085504200c6955001500444c1c2640801d4181e00c1c2103c00b107001d81010458181170804e0100301900b640c1c081c03403064a030300c0d450b0340310360400075804040e01c402000100c0d08900400450381e27588141071982d100702072051382e021403990340c070100905c00c540130440c00034090b80074810402304c99000c10000c240f00c1c45032240304509440d80880300043d964240c1e0044c0c0c417010391070300d040c0d420001503803 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 873706151 1250 873704901 873704903
    0xc0b0c0c0f01020a1a01090e07081002181012050a0b0105070b040203030f1908010e06131518051f0612050a060f0e180c0a0311030a17040f08060402100309 68
    0x210031507082002264080c88080d421845c66201e02240c2d500d07060045050303d030754404034400398000d8001000341038000a020440ca10b402d140c0580c60354005409a00c55284006180c0c0d00314a2014440500c1980051440382440c1100c60800690310f0314080c650031036006403003803404180d04002c1200400e8520312030030b030b025200404583c6050000401d04140d03800860001e0300e0b404080c00010b0710241c025202c940502507001c1c5406151400c00001590480e00da4141d402550342d0301201c0004500000281018161600e04601450800c0144000070042210009800d5240901c20840d4110710b0f81e01404440107642d83c0d240c901203401943d00208009801c00c603000743d584900050040b080c140400080c0390b1142000600d01c0c4c00c06400340b43c803408c43d40b030100c40d0b00004ca20a1055507841c02e00400d4a400c02920ba00c581104004a450b0030307080c2c1006804c1ea521303c021080e100d8904c1c0028015988030120f003480f12503a0f0356555a4541064400039030004040000d452600d101e0340c80700400c1 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 873707401 1250 873706151 873706153
    0x903031e110f030c0c03040807090606020313170c0618031506281206051905041707050a0515041403273111031017031b07030c0b0c0c0f0102 62
    0x440388004600b8519070040d80070f24403c1d0410002044ae00119214a50040082c0d00146140103408a2100d404507042c1c010201e1060701200340074070040080100d84103089000e04060703912a650b4400e80c0e4a2043d090025120b481392558111600d641d81010f10700581c1c010f05441101c4403d4000d464013100000190040e00b008204002040102004803240071400345900080d00d081002d402d407030f511141c0040003182c41c01c1800707110001c0c0e2190814a450902070300d01c1034a17a610352900354104014050003610310310075145502c80b000d494a1056000710b11504041d0030380c85c3c00c60300d16a04c030f01a40714010000071140a44100c007058080850012260081c0b510390451454402c00c016003800341140d01a15060703501c800c20b072103454801da20311561505610350071490071607030780e030ac11403d01e0180703c16803281c1c8080c0095580342002134176500001e0000d60603079495410b048640d215440d01c0150b03410210040005040c80c6100704a88500d20243d0151620504280a12441260702c010b83c40c11 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 873708651 1250 873707401 873707407
    0x90c05490b012307020d0b04032604031e0e0406170601061d0d0312050f0609100f030813180515420a050c100c1205040203030d0903031e110f030c 64
    0x40c8011001078481d510a80701e007200c175484101c40c94048411200d2b13420f4400e540a062201117034104c0a9a10f14510045030f020300c0c04000380e0115110380c100d60f010340c0c0040c04c002c008624403c14410160050007298126080e980c1ea032142101c024811380b0703000d24840100c6544d0100c1c3c0c00c00020030b01c080d0b1b009040c881e00c4628000352a0f41100c82c21560414103035100340a12196107055422582c00c0b1030300044e0403c0c000d0a26200001c0300d6400d01c8002c18008002600040480004013240300034a1600f0b60b040440c1040c0c0382541c05410100e400507a407801c040404042e030710309240c01c43d031150102080d581100d42e81c0500d9a803448964140c40f20b0011400c1e01900c82d800d500002001c24903850740d211a2120200c904484c0b41504040034515002d04041c021360f502c0b03034826003860144030001000300e050b03240d500100b411449403402e85c81d1030900b0101248103040d0190448040c0064001d000080d40c8584007001040f111900c4030401c0d003040400011504404c82e201030354104c1015a4558a = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 873709901 1250 873708651 873708653
    0x31e02120a0501050c030c1b0f0d051e0f0f030406150f171c0807090b07030e270a02090303091018090c05490b012307020d 54
    0x40c00d1118204a18140d030301110328401007190a015050b000051001c100e403e50410100000850049030a00155180d182c2100d901c0440c1c10406107520306011130a55403d85d958a03030061035640591300c10306440445811408055440d1004c8403481188e00308954140f0a0005000c4020313400034005450141e12130360400d46100030400e182000f040010300a1350014500031242c0741520211040c414250040400003810f403881c180d003006e80c4142860309031581d654007101030700d083c80541c008140103034020a0348420150005c408021400e000c03500c10b2840305082d00d00a00302407140e411004c95520120200d40000c600f50058041141d0083c266420100800f01103915407010300f0380c8400180e0705040c1100240cac2e160302c544015000c231100a00c507404440c070002d81103114101d848129200c00c2c214120402e02d954001c02c06881128201c1c0c440420700d800b031380e030309500d103400900e518516101000b811513004004080e400d01441520340c01c8100c00c4a5009040c1c5c0000c0400c0c2c2e044280c10079418 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 873711151 1250 873709901 873709909
    0x706080c07020a170c0103090b0a0c0c080309030306010306080307032708062e0311130603230c0303130e04140a0b040501050f010b03040b0405101517030a0801031e02 73
    0x1c000383c090400c052401081913031107207240081d031342c558a041c180f902883e240460150030740507a0201c426070010540c4428844110795040301d1203c0074144250210500c00040e601100950107980240d0301407105603220003c0c10f48a20444400602089114600c1d24200c0152060815002c0821060111144d52030358010706104c000c80f803c0c140752440008140360244022100c045401c0c1c41e55001c4070003030940ea50350303549110069080e4441c0e200f40034502c0c1118803a03040700e0059070344103a00e0425250394091411100010b82460100d600079033741c100c07903c7e081c000140c8002141e2007070340c214030610f0041c1d8030480a602500c10307074501c074a4000114890000308201e24880340f08054820342446d090400034210360b00a007400b04070a018400400610940e141601e411980000e1a0b1a03943c0700c5252240c54000000d02c1c00c0811410210341440006004044134200c800c04092403400342d0410308119102c1c0b080702400808151003c0c014004143c1c80c0d40b520703003d8102105403200241e000d030005 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 873712401 1250 873711151 873711169
    0x602101e0e01090c17071a0702182e0506030c16050a0b0a061a090f030106060507050f030a081b0d02040e1501030c050d020c01091a010f1202030706080c0702 69
    0x203107003691103001840c208a08812150010442d441a810206010190041d1a101e41d446000701104610140c0c104800d440d00403500796540c010524a0016240c022003945035030101c50410a091070b50159140c104428450741c0d0300700e960030b0400e00040e420601040f25503007010b0405800c401080c0010121343e01c046000c403108a0040740184000c0d85a480d00c0382d4407110041c0612122810900e0800c814078410300d0186002c069001c419884030b50000100384030944c00402e00b8ae1640c207060002455580110003450858001d4050709c0742c2c3d020305201e5560b01d01c525030740b00c0c00103214100050603c2402c8820791810030100c1c01c80d2031500c100901c41c5416a080b981244c02d001c1440014004150b240509481c4444803e0030240101044000054400c1c00751280f0440b0304c9400040e6100700000a40c80b02e09060381c4921003076682d03018040041d012140174040d03140350b840031f01400310340780c00c41e9450348140d554020010003800341400021140210050f0180020180c240b101030f005039290150 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 873713651 1250 873712401 873712421
    0x15040f031a090102070503040306111309060602010b03190b0702070b0307120c031e1104091e0e0f0601031502040806090109030f0e0d0b130209040605100f0602101e 72
    0xe00320781c410145454075a4181c0a8816880350f80704200c0d10340080c80120035a41281c2e040000001d01d00d031a000c22a003a0302c15581d0409000003008004a4072061a0b0f004805030b5407168020800e4510300018180c1d5010030f854a40320b10500c5805a500003004e420100d64410080c2c816203a000796656241c1203241c10965a500c00f14266907041c0231428094400e10041d4a194901400404148888900c00c400441074414940e40c943e4101c0041c4003422085500615441c0000c06c9103040e040003c0c6800d42d5070039070401c080e60401c4140b031206034001070601c84011407800640b1a0307074650b03500c4a41800d03449110302d0030359800b44400145c400061040b80d21031040c94002091a6920345802040140024a8a000e00c0b10051440042d42c4441e1003924030150f005070401066103801207407801c1c688440200940c4130603594200801c010194203c14061401300341c4508145844100e00040c0c2d844900800700181e0007110380044048464000214502c6820358280361a4942a2284103488114007 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 873714901 1250 873713651 873713663
    0xc0203071a090c0a0e1501020c0303070f06150803190c140d201f0e010207080c0601050a030308220b01080a031805030c090a111303050606090402060915040f03 70
    0x4200302c46608240448415810300310350000400741421800c0b45101e402800d844c4c0300700008014000d0704d034002c02c1071f4011200014110b03074451101d0b10700704103007031540d510868078a03013440c1118409203524034035801941c05440195040c03500d15803028940c03003110300390101006039040c1034001003204072400e003100030b410202a14110107409030140808444904106802c0000c80c00c60003400c0c404a44440100385408400d0112440e07070091001034421074003068019480000e50508010300d1100030030703a0050710400c0c2d940380c6c0ea0b0391040003000b051610001c0c002c00d1312a8005a00300d04117a02c40411004649040b0303000c41c40c207845548902000760041120341d80881056030926030081c1500c2c0c190b50040318103644140c10880841d84401440080c680500b0709600407482d08500c0b070700500c202d45295101561582d081c0c0b00329085040942c8401d80f103030301600000c502070f403c1c0080f41c5807080341c014121a182016400030721905040c0b0310100c65a109003480007181e14040105540011070181c0c3c = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 873716151 1250 873714901 873714953
    0x30a020403060c0309120f0f0507020406090507080103051b010e090402030a050619060806010b04090c0203280e011b020907050915070615080a0308060d080d0f0f0b030a02040c020307 80
    0x1103013049009040030076002c280121f402240c1140f0f80d00010710424008203151444d00e03206144041000b92101d41c104c241e42500342020016020750140c00c0904030b900902c00c40300081c103090010000c04c030b0701609860002c1d05401d581d000340e080120307580303030490710241c1180ca14031082c0d203070b090802c039040c0d0310907810895081000da0507085900401c0302408260f00504403551400b108640c0701d2003a8403c2004203a1a5041600e155000388203640c06202e1100a6401e071340d0f4000c030394503004c011059040010821200d41305401c3e505c0303000400038885050210810020f80c0750200700601400501030710410000308400309054844404110b076002014980c10344950591400100740d0b0341e21060400b090361040010004040000384401186416042481d400d45410001c0348405141c2d0801a01c4803400264034410146c9a5000c064240390170030781086501c14a035014030644003400c0144d40d159000040c0e0b2009803826600c0b41030340c00c1e1940100e070725203841e0f5a80d02c103418540c00d0b20102c0c40c0c810b507 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 873717401 1250 873716151 873716153
    0x102a0c1502120a0504081c08090d0206130203160312080a05190e0330130f1506240e010e0f01081005040e0304090501320f09090f0c06070314030a020403060c0309 71
    0x4100c2440d02700742e050020389450014240c00961301c0340000c101c1c0300105850ba04034030564070213000424001c00708043c40d8a80d02d480f800d02c03141c018141401e210009080a002400c83e0480d4420389000e03c08a4640d4101c41c40c40d20840070280400800e000f03240d00042041422003401c0f80403010400a4800300d5403a0350041c80550b800b0540d0041c4070b101e41c074211349082c10000e0740c501d80f9081c1480e40301c28006501ca0f0b6105000d00201a40e80241c0f0140c040031038094800604500c0a0205d03602079602c510f83c0803146001100c3c4851240703640798100b101c828841d01c080d80100328050b44004180d640501c1c0170381d1800041d05072115200341103000d800000d000d014030b2010f0700490740034040d81911070844001080c0701080e0011155500001005032003160f0109503240c5106071a0003e0080288805007424498aa280d904441c458101c1e44903c0003003040500300401655031141d015241d00d40540800031498126030301c01480c0d6000d0f00c1d8200000b000103080e501c40c0410070b60b00c9030313800030311000d003 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 873718651 1250 873717401 873717407
    0xe0f0a1502071712041814011d1b0405060706020d0603060e1203040b0114040b09150a06140f030711030c01021e09030c102a0c1502120a0504081c 64
    0x40b058140c4a113401072032003224074011441c1190201ca62012280e1588503c6090b4800149400d02c2000d038038014210000980355040041329100040041024071952281d030110200007c20380d85a4540090612040280313152201c084d1040600601001d881d2880413001c0004440854100300c80803944c5106401d03141c002006000ba030b180c10143c80e5855810300e92079440004074144160f00c2e040b012105000c2e1180c4840d000414001d2007d00109054102039541d001d07041108045940142c00e040d100090085c4150398031550802072108851801c4a0300c01100b403154401800c0c3d00c20300c034644030180000501040102200b902d000300058440c0400c59040d1428103030400441e086800038807426405585c041500049039008440b0014803445100c130681e07540040e100740c1c4525840c40f030b40013101c441000c29071060088c13003400008400354686454681d0040c000c24180016030000341216440c2e20440004c1c001903c050901509140c1e80b0900c1910740000a0103020b121121300000d00c2c01150 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 873719901 1250 873718651 873718679
    0x2120f0103051c02031e0403050a030c1101020d1b02150403050a0c0f140d05120403080408010b19060c030509210c03120d02160c0e0115030c0e0f0a150207 68
    0x881016951225a80f680c002562400f80f042e401d01c102e042031408400d4105060200d0340195402020b4426000060402138132061a5400c01e40c0d401040740100d50b515032010901e0920303075156454515181da4030b080798000d20070b200c1904030b0b0803160001000404e00502c4010b00020b501c03070f0000308100140c40c40c00007245801c60b403007501c400125110074040c484901203514820b00c42520140618040341c18400c6c50070b105080c0c14180480005404010300c04000f0081040c0c0f03155400178070040d44a0014460740038148021104100b941030001c0c44280c0c03180301d542c20514000d2400c0c6042c4080c0d000080d07a0580000c843c507160540c12010340c079122006001803440440f007100945007107540100d03c002e45200368501c00201d02d90000c1e6210381d100104107000c2c850b54100d00300c000c50303944810082900d91001e0160030303004038081840d407411070701c640030350300d4102c000d80d4502c1c12aa00740014010440108074403d680844000008104900500e942201c000156401040018031f010481c181c210 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 873721151 1250 873719901 873719923
    0x82a0703020a06110c041805010b030c0d1b0e0a0902040e0a030207140409060e0105040b0c2d0c0a060501050f030a0c1203051606020d0f021c0f02120f010305 69
    0x6044010100056a1500008000c0300d429080401185803c9144c2604040754401d8240e0b01a01e01114003540c640d5011405141520a000070000700104000b00b40d595403a0204190780075030041c5840d0001039120213501c005035160442820a01e45070040d824000200715a010221a0b42d41c2d4884190301d000c0c003c203811680302802410094a10340c0700292603040d24003580c210703440c0002040c035964440750f000790b0410741c01c0322042041c4089521030902819080d0b42c140c0d20025031078081500c5650300320440d407001c4050521034030480f0b41d0490340701d44003042c418041c1c06914140146005000d00f030140ea03a0481c40b401001503250304207070801c070f000080608040d000b81d00c03000c1000001402d000c84002614200151003070804298a001c440a1080c2d080019180c01c208200c00100010354001d4400c0c1050043d041c0561400810110704a02580c0350345503014030781ca000070010496a5125204088141070003519007980b00d01c040820107401d03241c540740740714081d0040041c0402401a10282 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 873722401 1250 873721151 873721153
    0x10091a0606070209071d0a080102070507170a03081b120624070f0f020d0809130b01021005040201090f030317090304050306010b0a03091203020c070e0106121503082a 73
    0x30504030340100d84c071184000c0038103044c04000110354410b8030506070760010040c00144000b4205072038502c0b45020303400c0174001f01d4180c40f944002089880e0040003407003940c02c582d070041c1000c400c0c948044554840241044490441c00012902c00c1040c0700c000341140000350b036840030316003003090a000c0c802440048017007481c1d60200c00c071456039001c1012a42e071242c200380045640802418050a4143c08840007940310090b042c5280030028018042c05011608441e1808a134001100c00000c0c0c075a503541c4103005801c240d00b00d6001300c01070761005802c1070040c074160b08001c1c0c55000d1020b816403550425004129900008000130801076402a804140c41015609080c0380101080e96000d040c0244d0401e01e50104410b84800e100e9807040d6201500643c4c008801d20f80001d000c0c00940c04403003041381c1e078050010003040c40510500c1542c1200e04036950f07588012280308a6000030a6034003464640003040c8c20001010400c45000751621848034820811801003900b03035504283c10302d0802ea40300d = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 873723651 1250 873722401 873722407
    0x203040b0d0504060e030a0801030c0803031015110d030204031709151c230f07080a0b03011b050a08010f14060903030d14090f06090706030b0310091a0606 68
    0x24641040c2651501444550045402e485510380302014043c990b0031004540b2001c9001000a43e002c2076442c100d0703015a2044c001c0d2a1583e05090f10381c4412200c42c075440980240c2085800b010f0b010b1083c01c0d40d41c40c03500041c1c0c80310440d030450030b11960714241c60000e5001702d41842400400c00e0341c0180000300f2020f0518200b244404079a660b010040d11100701c282c04100e400039120740711211110601e2400c000c000503040340c01b0081181c0380107000524144201000500d214048050850060540d92070304100703941d49683c3c00300941000540640c05540311515405040e68902007581c144c6031b544c50306601e50b80040001000c192050340b00240d00b04c8620410001080030900d000703084641520060f40d104006800f181c0b03144604c01e4401c13850b074038000e4040e09020310002c0c0940503104010a480c2c0d0340303206885807541d44206550100e1a604451400c0000c20b00a900c108600d21010702503603165121000c01400b101d981e03840c2070710600c45e14015882e030380c1100e40e59250300c110300300c44080c1 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 873724901 1250 873723651 873723659
    0x1090f0e06091b13290306090601052205090618120304030c03050702060304060506040c030c022805071707091a010c141e0c01170403120f0e030c0706020304 69
    0xa910409001c07040080046980219415103407048002041461130703c0034080a45028801034001c603000c0801d0504010361a0365500a19001c151140201c6c3c40130024041a428401048401a50307809000152121404020544001c40c019144269072040280402d461700c018000c3c0c40e500300300816800e5070081086840d002381d070301c0e0039a50840d41510b441442040286015212403003070910295200d400881004208603031a004544555401d503401d200318100d004096003034985c10410540503070081c005040300c071041310400d801c1001d40c0c0e80403110965000c1c0c9a0302d0510009070080810724822480403c1c03c02010002c0304010a02d00204006500e10320401710309502d00b80f001d440c10050040d0340b0206108844003040005154441034035505807451010855017020701700701c48141e0140705091140b96024881c030032114480120803034030340c1e981c550b800c91b1030100031112802120740d1104003040031480d07403003015500000d00004650b1070b0a018203a92800741954050f80441d8001c0100744 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 873726151 1250 873724901 873724903
    0x1407060c0b0c0f090a080a230d030b0d1a040b0c04061d0102010e01020310030308090d0206010e0903040312050405040f1e020a02031c06050915010c0b06030c0901090f0e0609 76
    0x60740c029900c100283c1ca80c20851110a00e0703115070012a58041040b05010511040206004025030320811120121100021040983c4040f50341402400e4004030804035525001c1d8000092541000345a1004803006075102c0d90092189420016a06409001c00003084881d8060075000400000510f00746450560002c00c42e00388682141003000c03101c055406640d000350052043c4181c4039000f59100c1c80c2a800a000d006014030003038000560b40804100c04040c041408125001250702521042e828400100303020030000c1d00b8011341c0c2c4810040040130a07400030a465401ca01903546c0d075a00e0b8540820002130b2036010410540c11464440c118400091442c0d03c0b40308108401e00140e12000b9842040c1e00358020034600404080101800580210483e405034040e1007080303444802c01d442da40203070400b1418802002d07010030403812500f40890340100f22294049001011142c80046000214130340c1c003c203901034900c80741c55100708810301100e070041080d2904500300420324ae180c90448a = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 873727401 1250 873726151 873726173
    0x4060603020114030c031303180b09030c0103021303060203061512041a07020c010f141303030f050f12100909050114012106051e01080706080609010506090f060d091407060c 76
    0x1f0000c845451411501050b000d82d20100301040e41c80c4007103480b10341d1030004450aa2102d202e0034882e000f025600c0d901507029109503841001842841d00d9420b05642d5140001d6101509050b803040b505551b01c465000240300501d0010002d0301d203841e00341040d283c9121140003e4149003a000b9051041018071640056156158442440c0000711108560425150300040c00d102d6046118001504940324102c5440d15040303138800c1e61250140078610004403002d0068141c03010b13569a0810207410118038807280d01d60002c107040e0110307000b103566036a60710455240050440e000e03511080280449860200340c00d00420105101022521001820b10403249000c400200304541e20008035908044440c955850003228002c1a1040d507121110360796107094a111341e100150000f000203155041217500c403812030f00c0140185051540c058100009034220f074580c0d80e0807007001d000c2125140298002c4400e0903002d0081d00910800010005003041c805402410078040d00740c01207000100ca01c410 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 873728651 1250 873727401 873727411
    0xe2409010806190905060312040e2d090615040204080d03090807060e10060b0406050f0703020a0602030a1413020105030c22060306080d020703080a032304060603020114030c03 77
    0x80e09040d41e0b24000a016050b0840c40d20b21025a006408203048030036512a034064441142229600101052408254800c50060030390341103030903000c02c0b40d802d0f00b82d0315440c00318021070000000102030400f2039140b00e01103d1118103544907030184088503d226080a01c1000144d40c2545400d041c422802d0795221220b004200701075840520b0380512207417100340c5072803683c012001d0280711820128141d0b6080150030f004841c40ca0014001103803801902250102c07500f5842c1d0382d05000040c941c41850f50030001040c0c0a41c010015000006107540c0700641c4580c2a1020001c0c00d1071040c1c401e6142504d0007050302100c0c444007004000941e8008013179a5110241040080d91907502c10302d04180c503104041107880c80c60400b40082820394040c5c01100946884400f2103030414600c4038102c2c0d44818910002d40404400c01002e4901c5101e9005000a1180250040116034140c050b180160b4000c80303068603a2a40ca000c24021980d2252000d6421664640780d07600710704040c80c08200611000d08 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 873729901 1250 873728651 873728657
    0xb19060e01030912081b04060e01210e0d12020906030105041503060f050708060d02090c0a02210a0221180a120b09070f0b0403120513060e240901 64
    0x11810030507882a0480e92016502909004250844603400303042c1040945d80c0800c03da1520f00100c1d00000030000f55403c84000d584d61341c41c0e0802c030f6401524000b014051881c0803c0c40c0703403d4140d0340000d9010b0400e00180c030000a10071002ca214004064545000c02840c6c01b60042060300e141e60768003002c1d079041d15004c40d0005145031181240b038009c00c0041d80000d0010f801c02900b00c44418095014511660300c1d6101c55119950300010030500100801000358800090030100c3c480501d80800713414100b051740101c8900c600c410308000b10303106501d0400a40e030980011107c0c036250703040c0316110510303107204a900c0b425a18007220072480d0146070300004510081900c1c40c08140d41e02000780008080400d040003001c2c400d414008000320040f42d020707205114001c00040c400002c1e480550448a8105940b400d140c203555400318910010280d95040140138408080c1d0304110701103101c01810301d6202c28507c12510000d2008a00900c0c150b1241d40d82c000055441c003d00c25003c4601c0070100346 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 873731151 1250 873729901 873729917
    0x316051e07170c0315010612050108190606170705040c020f061501090e01060c020f01020c0f0f03120a0f0e0301060510050d0f1803090e061c080f0304150b1906 70
    0x115106140c000a644030300d03818819505c81c8000d05034a50001810b07584140c2d00c0312607031031171440c030301e03003a541c0a100c1d6203000c3d400b49500460a4254218030741d0703507502c20072021540a5407100011486229403a044a240e042031504210071b14107881907410500752800541608032245483d07a0b12204020b14044117001695240703d20750381300d5480319001c0c040f01d88440840b035071241d000030201c002c10b0400320b00414a0800380903081d80001000e414000c0000d000740c1c84100800248004100c0d81c0b03092540504ca040c5d0b070030340710780c02070720103070880c0540e0341d9902c80c3c4248840002410f08400c5035070b0702d01903454824184410b4440080e11b0b2649280350a10603038920040700300b4030060210380107420f4418540074006901c07000401c14078841074001c0e0396600c54a80c5801c5a840c401030181c44e0b5960280340907100d40d000030f61800c031b0040d21030b009098180c00c0080f940811001944115030484000000481134008072219100d100f00c03040041e5800200e0307640314440e40b82060751900490003841142 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 873732401 1250 873731151 873731189
    0x20c19050d12090305032a0111090d020d02030f0d08010905040309052205010f0612270c080a03090f0b03060120160305010605043c020702030316051e07 67
    0x150f21604011540081105e030b480c0031405c0a002c0f40003a52414081c000c155940c00340c007165050103001c00400707000780458601070500080190318801101e0032600b2590ba04641d0001d0b03034085c0410000c0780c2c407540c05090f81000c10440100b00c00c00503080000c1e107500e42014000429801811401a1002911040400e0f01031031901d0800305c52159804c90941c2c103041c00400c0302c1481284c4042220569165542944c0c803d900b0303031050b43c00b6003500484480a5280c031080d01a81c001d20007807040d000d00341c50121141c480c0001400c00c1103107070702900483c1c03564508100306403c407400e100c000c02c15038545604504000e0300003003403901ca400c2c008050104045d0701081c42c1f8024081c03001c540900c2108992615070302d260840c080c1003031f44107044c420745c41c00c2055010b903407149001580792452031400d8010b051407110701801c841400345a02c5d03a1203030f09101000043e1800c00c000c10b007403038001000c00c00d545124039240789010f103c0095190617110303001310302c0038000c8002004800d5842000303559100f4111 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 873733651 1250 873732401 873732407
    0x30b1305010c0c1511160f0c09020405030c0402030702060f250c1709130203040507030c0315060803090a0621020406080f0901090b0705130503010507020c19050d12 72
    0x92010040d003503500c0c12100c84807198002c004680301c10304c28079000340c8241c1d040100340110340c120344c011550500100010740f5100c1d03001c640d1009440c8142030102c0d040b015919042003442040e0440c102950340050103129074030f01040000b1414004072000d524610b002240252a400e000c1c281031038034000070011405508400c50724880902c0e000074402c0c541c2e1038070a80106400700c480401e83e1101c034034062800001c4d40e12412203a2a20340036001007900742080030a18002e600090050350540035152000c0002007407440001300450186540c40030b08041403c1481c100d40c510780c0049442e038001c00c007005c0c8648400c1312940c112845800e040b55500200c01314051080038072920503400318070020300800c102e6007024206000e600d00100c0402c0d0b5541d041155822204a0000640807403013080000300c490788035600801b404940256800001c0c1c0e50344010a00b541c07810765150015820090500c50141001192901141303141e00220b013801f403410000c0384c1d04191303615004d0f000454011180300c2c3c03140 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 873734901 1250 873733651 873733681
    0x30206070204021c0e01090b06030105010b092b060209090907180b0f06161403040605030406050a091a070311030c0f0c120a0c2a06200604060c03060b070c030b 70
    0x200304505010945400c201c1740c4c028034004504032054241c01000c02c80b103041c144030b140c2c180c0390001e04080c50403103290100a00d0060031034800c003600071044402c1c070f16161686984043ca9129880240e11402113600f00542040020a10a4035503c104801c00418461825100c1142651100054035005210214800d204040c00a9800060010300c1149004084020003001d0b1f000e00c801d1a150060f400700b2a0b22031140b481408000381b0148042000300b4107507440f56402c484038000020380c801c11581d0302c120110f210000f0300e03008520b00f400c001040d505802160349001000c0c61041c03640c5000c080390510341c09a90760300f9070010408a070042e43c0301010426882005000c4420503162002c0040c0205401d144841c12188100052a00c00303c0c0f294120356000a003062303c440e00c00c460b0520004a40601070079902034224411070000007140c603420b10441e800381d40103c00104504140300009801c0d18941da01090044004200302d101180405011009032540402c20500350f4607604c000c07040724a = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 873736151 1250 873734901 873734947
    0x1409010e0a1d07170f060f030607020f0d02030403030219060b13020c01063002011b21020706050f180a1d07030605100e06041a0403030e0301050103020607020402 71
    0x1584400700420380034289a850040942034840301c140316a40c00c40200c4224060003244081949101c02242100c0094a1510340c002c81c0900b591a100303801d42c0020346840d10654460000d40c0080c100c1c1d940600c1c0c24091808000454001946440e1940e50000d5031059250304c040d04c9406402d000da020032981e40c01c06072006100411642210103910040c00c000d5101e501c140d8850340c0380800c00074000c040312407100d99800f542c80c110782240900c1c200009800d202804124104020003403110b008412507060365241e540900312141c480780070082c003441e210169015100556010800c00c001d9180e0281c211154820a11001038039a0071120b02c2001ca222646203065000e41140408108445402e0304080100110b0b001c501c00b41c0c03141d090980c00c0704c1d09801510342290204540600e00c0c0c0c011000400c210314050202c42c5059900d41c03030360b00718082c0041c14101740c80c070014003001415409007090211034011802081507514542c00580d0703074890040020302594010585104441e60500820281 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 873737401 1250 873736151 873736159
    0x50f01020f1801020604020916030b060a2a020907051308010204060503040605102603090306070207050108090d0207120813030303050a0e03090d1707061401030c151409010e 76
    0x412031401030740615009402040490156031481015a40c8001921809142c01420050b516100c4184241600320b541010905140e00c8083c8810341d500c6d51401042c080d04281d492100000c0c241c480d072110703c101c28035000c03100c00c4076100c03046c0540d850ba0600d0350040f1503070800503680c15003910600b1000ba001e51050032594030206000503019001001184110721030607040095503100303d028040784146024400410a01c001c181c2d4612007000e0f0341050020b006400c80b420301040d1344c000307480e01600311082d10058201c40c20800013540c10075803140c0c001411002500072a42e100d00b009551746410f00c01c40e0b9840101c92115801c0c07020b100220744000c040070000041158503421302801070281619021ba038a80f0f007018455820780c020060391049080146542d00000c86078032034280070440190b01c074041110420a01001805500c1407001c50380012414041b158035508103183c80071159800358080042d02407403404826031054001b06110454900e29460310407140040b140030101c1e141d041c0e00 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 873738651 1250 873737401 873737407
    0x60a1103030c1801030c0e010f09030c180e0f151801020d051803120109090201110604060905010b040212271009021e0114070f0803010314010e0706020a020409050f0102 74
    0x100441c58010090540d80542c03c82c14000c9000044080f5111690b0300400601030000041056205400d0071a0b050414500b01044035200d44031464550010b612840e08000c6070181c040d007030101401041041e80c0c02d10042c01c680950b00c5c10054503060700708812100008494001490300c01c050300d042c404003000304000c546841a104042d8000d14041c0c03841d0003c00c0090b0030400319698004100c460915015803585010707445e120250010b81141a012414400003c4069004003000c00000c0e101d5801810003062009403810071908403580c0401603402203004000741440c09000070700c1903800c012a803048180c6031981e1307107000e442100c1d45c5400024a00484440f40300c00705071604080d01440c001c842c41c521307c44d070940d40d000500d030896403a00d006c00c06850310b080ea26504080a042640c0c026404021002c0b0b00740e58130b58250b4000d8100326455581168001c00c600001d01c1144910b113001c1c3c0041142500301440a59a0f5840d201c00034882c0e40c80c0c0000208001c010300c400c42d00079001c1e500130b540b = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 873739901 1250 873738651 873738661
    0x1d06060429031e0c01180f1412030c16050d08030412020a080a2f060105010c0302120d02180301090803061306030209070e01020d02060f060d050102190801090b01020f0c060a110303 79
    0x2441307282d200300642c000b9281c0318900c8507003801c103011942107880240b03140305a20f10708400d5460041000c070f4141c1d4002180980402480028001841d001c280783c0c3c05060780600304900a001d20300e464116500410b0440720000009a807601202e130080d400001000c1c85a074a201c1c03ca14100d04120002c2081c180420700d6510306800148141a206c15920303103c00880c00b24107400c11070f0083d50700321140d6605c403800410113940504400fa079024000d1050350106604161000340076880034103040e002c01c0d400039084195110704a40e071080503004a00a111207a429192407200e0b00000e09001d1042c2e408030045103240d8150303804007006648c003902440891800d000c02428400401c804103026004640e4100892840842c0091040294040c400c16580b118820304c01c032a42c242c10300303c8a5642c20040c0000b050103504600388125029680d1450039810b0100b01002e840031010030030305540c00818010b41208000c2403500b110402901d0198962060301c0045880d41290004c00c5010b000004c2440 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 873741007 1106 873739901 873739903
    0x60607060b0105160b060f031504030e0414040b06010e09041e080409150f061404140f09250903080318101d06060429031e 54
    0xd0401c1244550120100b0f5007036415190b04010a04101b0300303151050803a40e01400070343c0a0300700000050402400b9030380181004084c40440d120750005611030340c1c000d18aa000580c0b10805a081ca0300740185500c60588400780001e6002e40e0350546800c01151050050340e0058140c82d07140d103c0100b200c9041c5180200300c5800c1410400007425641e51702990f036040d15400d104504103494003460a4592010780d101d141440340160101035203000c02c0d02643c00700e4400086e080940e642c1e40000607844200303426082d41c800d40e06006d100d0240c21110120103802242c0c004103119402140d0161020480c500c03000b0001042040010070500500c8c042002030440c0108440c0402c400400c42000d440c1c400d001c10342920014900d01c2c0000904105494020ba005d41c1c00704481513650150350300c0e0b0703c020700c1d4074a285040500c00d035549407070410000031840e220709240c1d00d810710110982 = true := by decide +kernel

theorem cover : BRFrame.Cov 873561151 873741007 := by
  have h0 := BRFrame.cov_init 873561151
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873561151 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873561151 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873561151 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873561151 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873561151 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873561151 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873561151 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873561151 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873561151 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873561151 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873561151 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873561151 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873561151 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873561151 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873561151 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873561151 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873561151 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873561151 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873561151 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873561151 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873561151 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873561151 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873561151 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873561151 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873561151 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873561151 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873561151 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873561151 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873561151 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873561151 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873561151 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873561151 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873561151 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873561151 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873561151 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873561151 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873561151 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873561151 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873561151 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873561151 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873561151 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873561151 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873561151 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873561151 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873561151 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873561151 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873561151 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873561151 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873561151 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873561151 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873561151 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873561151 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873561151 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873561151 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873561151 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873561151 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873561151 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873561151 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873561151 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873561151 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873561151 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873561151 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873561151 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873561151 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873561151 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873561151 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873561151 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873561151 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873561151 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873561151 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873561151 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873561151 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873561151 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873561151 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873561151 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873561151 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873561151 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873561151 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873561151 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873561151 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873561151 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873561151 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873561151 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873561151 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873561151 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873561151 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873561151 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873561151 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873561151 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873561151 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873561151 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873561151 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873561151 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873561151 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873561151 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873561151 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873561151 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873561151 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873561151 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873561151 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873561151 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873561151 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873561151 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873561151 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873561151 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873561151 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873561151 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873561151 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873561151 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873561151 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873561151 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873561151 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873561151 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873561151 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873561151 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873561151 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873561151 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873561151 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873561151 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873561151 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873561151 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873561151 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873561151 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873561151 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873561151 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873561151 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873561151 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873561151 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873561151 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873561151 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873561151 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873561151 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873561151 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873561151 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873561151 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873561151 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873561151 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873561151 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873561151 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873561151 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873561151 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873561151 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873561151 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873561151 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 873561151 ≤ n) (h2 : n < 873741007) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
