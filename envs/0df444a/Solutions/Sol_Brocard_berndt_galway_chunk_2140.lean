-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2140
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T05:46:03.261326+00:00
-- url     : https://prove2.me/submissions/aa776d51-6cca-4012-af6c-69ec474f6004

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 384712230 ≤ n < 384892086 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 384713480 1250 384712230 384712243
    0x212060f0c0f12040c03081b070603090b07080403110a030507060e0a020102120a0c0c08030307090b090d06020d090b011211030601030201052d030a020d050c122410050c 74
    0x40c01e046505201c892094980760003203070450018110b01401c03588079810701d01031020030741e1b01c0200310740f000251203c1c003600e009024824103514101030f1410240e43e41020b4084d2545800010b215010380700004d00d8040c002c1000b0b80c4c0141c00b81c80c0100890172a000c0700c41c0380002c28202500490b00114420041200750f000e41458107104c900940968491540042e6032402c20140780360340541d020902c0510301c0d1080c00c108580f1900701050340e041d15620380001da02c030b50058038841d00140c580c80020801549010071940c141c40c01034660401d12241d1340710b0741d0003500002d80742009a80c0303914009001c2100b007000a8040c2243d6140e102c04241689800750426802904c000d0094129100410260381c0040999280000701c1e200403102e440506009c40c0c5a00c44a070050b11345207004000c0c04a0941e07954064100090028001c21042e103d54124403454003030401d0b10601001076a0002e03804100c031031a026004404c44c240c040d40440040002604400c0c0000040d0000d24041412046150100800e = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 384714730 1250 384713480 384713491
    0x9050106090908040608180613140604170711090c03010f08010b03030901080613060b19020622050f07180507030e0606041a12060711070f030b060d0212060f 69
    0xc004103000b03540c0c1c610141c06244544004e1102c00c3d40059000c81070080c20b4401c8905400036146c0c1031411008034010300c1540350341601c011075600c541c101405400a01e1502490b005907503203200001c100c10308501c59002010031206a0b07502c1036005017136240d11a0b0180106212000f49849605080d2541d0141c0516403000d1103e81c184644145203850120450f0484e250030310f852605030342c44402044010254142c8040c040f072901c440060622440400b500071034091140074801181921010bd99540b800c1d0758008903000b8101c0320300c40040c810240c8942491003402500e1351050300d00c0050b400e20203240c0c0004c00c4a20310b960340d01104a164440c0035881525420108001c032103800c10b150392118010522400dd5540e0312a80003420320002c0c0b00e0009072030051129044c001c0021406445600075203015000c43d440f0942806100c0c000b088070410f0b6107019003e52607140c5961502c0190300c2d40036080b9030708003550341c4074880035803140240c00c040404403400030a150b0603d0f600d10314181000610 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 384715980 1250 384714730 384714749
    0x150c040e0106050d020405060a1205070e03250b03070f0905060307080403030b1309240b03120307050d020415080c030714030c0d020a025205040204060309050106 71
    0x1051040318250350503181034400300d182c15500c0f002050116030091060b5006581d000d20042400c0802562202100a05170744603402400b00d9100e040c829507101c200342d07480c140d258100c101c2a41d204a071a4801c04d10703800c401044203040340d43d940766441c003c2d481610a1000a0200c0b1000614203070418002002408140c50162840c501400e0080c0203910107803000f006c05445141c03034461952144200011000c0c2514100800c0b029860407119403d2492440b45003c00ca1101080d07203055588a142201040074018082e242d01404103110142c1c00246030905010040c00013400d862031501c06840640b00d4400e00c552103041d021000350210314002c044041002c1c04008004e1103641c010b00503034000c0b04912050b41c403601c07500c00d188194040c400208003201d01c040389420009500141c201e0460943d9980d03600c20310100101028120402a4005064080400c0c42d0120f0300c604514020141c8094036584031940e00d403800201a81c1c0598003103070000f511202410140142849840f00400200c00c = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 384717230 1250 384715980 384715987
    0x70e010807030c060e0d05031903050a06050a0b0310081915050c090d080405060f04240f05090d020d2d050703110a0f091a040b0315060d050f150c 64
    0x40d2450724050b83ea0250000300310305030180741c03803039194641551552940b080560341c0712240c00039025a4010300d010748030300003030074503011031000c0c80c06101e000306a0340701a008201d014240221820341d0360010f00404074410280e000040c0612040c8040040d03050074003a00302e010000c60070402010708840b40c10705030f0149058140010310401004032130b150002580c91030015043d50a19815501880d070001da04030000060f16611410103200070710568041c041c0e0640c034410030303004410300d01a5902207940412142c0040c8404240600013600c0e502000400c8003003030400903404200c0d940603c2c0022a10401114118241c0d00030b04150020038000b060340d821490003454a600d0340d500010f21000e080780e042d06042c00c85580b0b8a10504000d03120426252011540e030b80c04400c010100304440707400084240c40040b50070b203443e00805807d1840100200b103250340300780780800c5400b006807800794003090000100002402c180514200901e4042c0500901a143c00032803d66200080011200c20000c0 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 384718480 1250 384717230 384717233
    0x9050117010c08150102030d1103010312020a05071406160308090607020f1207060212101a07081902071203030504020f010f08011404060302130e0d03020c0a260408070e01080703 78
    0x18420b0313101100f49404034001400000503419403044403144000d4900b000304007406410200d0046048034032403c1d038130b18a100058000c0340c4481c40c1d010000c00136003200100f04100c00c1c500120036210f4000804461510a034001c980907900c49040080703011603a828200a20210180000c41d800ba40f07a002a00188840c49091501da849010048555503008619903040c001d0b00d906a9030404900d0003828034600300107a43d25071001c054030640410f0120307800701c00f009101c030f003050b00c17404c55001e041c1c0341c140060740700321000c03102c4020070010031480350100002c2c500c00a200c5642d80c3c0c0f0b01a44000619041c540148101c114004804a05125940341380f90701c860740c44007085044450101c05800c02603210000140a081240c4c00650700240c11f507600c4415900c80c1c1d010420740c2c0d4510044409800c90400c0903026405075101042e0240c200145550101e03424640d40340390f4024200401c1c83d10300c1c04400142443d0840e41002a080e48495001d000307800040c0e01c201e02501055000341020303480e6 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 384719730 1250 384718480 384718487
    0x60507053315030a150e0f032215030b0102150a0e10020a0807080405010e06010f08010506011d0607050106051302030f070503040507060f050c01050c0306030c06190503180102030109050117010c 85
    0x35808010145c3c1d0f4640080043c80340300c1d52018040000d400e06072a1900e040b802c0950b901d4105103044010000905003c03100004d500c60044226110310491811800400b042030300180007409002e4158015590400341c00c4070907103007840c4100042440002c44413200c6003550714000c807041c10a20700034410484810b803243c00508640e8415628030301800b041ea03d13450036602600000b017914885219500001c1104440328441e1000e88000740020807c640d684401142d860500c1a20440007026401441109041020040c0b011a00400010916039039690110b6000c440e41105220015408414414000e02c1202001e802200b80e142050650400d62542515400d003071042c00144144400003100301802078080e240b015a00034001c000520301040f01d0103c907442120b046210380110904e02c08a0310b040c000b070341c80070800a019481c0724110307000155000e6001034803e10b0184024200c0102494007400214082c20800001244c29454514a0380b000c491000c00500581d0404d010601543c0e0f1 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 384720980 1250 384719730 384719743
    0x30d0606030b061e130305240f040b091204080d020601060c1502031314070306061203090b030702010b0607050f012706050a0b0a0f150305090706050705331503 70
    0x10380428a6044a0090200c01a02c900640440e45d0f4019000c00810b10601144990644800013100351203842030154034146101c2c02c841400070300030040d001c030300841d50010007668490806400c0310350400740d4007400802d58005902c8065954050341110280c1d641c10700c00f1500410007030602001000c00d90307958000c000c0320007004440440d408000200000304140c940c10405420040708140c10280951307171030300e81c0c80710b0005035485401e04000040545007043c2044881c0c2d09030351076440240c10300e00e032240d003540f0240c4020215901d4101400860fa03d000007054014801c00080128990481002e0b09507150300841766050015800740c0100384d40085040048158420000038240e0348101142000788084c0c6480d503006101e00d880070840b0380d800c56429080e101c0c00c009001d940c07031824108900751002140c003018160042c0d0310400185010300007800a45100c2c805460008050b11400b00c408090040001402d01901e114903480011400e4801d400405814001c4068520301c03000c69030f10721 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 384722230 1250 384720980 384720997
    0x6010f0b0a090b25060e161a030402030c060c0304030314070c1509090615080609070c170702060f0a080a1a190806010605040e09070501021c20030d0606030b06 70
    0x22400107594001e0000a02800f88080003051805446062828001c008000d081b00895042c4188100c000320061120210802c0710345403c441c423a016401d02c0c003503a4540001d00126054420300d01c0d89411540c0c2d0002400030008048015a15580746027001000d81400342c0c001441940c00700800004215800d1a010590b80f01100c142d03c9101420303011201c0120320750100304160310f80302e40813491100e225910340d01328402d99680c01c25901c482081041d043d2060f68460007007400462018001005a4055548050010310f9a810080301d500420390903801603049880e0355100050004006410202054021401d60400c01c0455039030001103074220211003082d4400c0160174008941d10442c071040201410038036040c0d030000e5075a440007900c2c5401c40d00614200448000000303100f010001070610031078005034000d0407498000801c0d0341046200c4592803003000f080c2080010140e05904070a07004d140003000550350342000398950310844074036405c10b204250412641d0b43d010350340d0340306031100031 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 384723480 1250 384722230 384722249
    0x906141f0c140f0f0714010503010b0712140a05030402011106090a0b0a020403050304090f05011e0b09042304020f0d0314030907050907030c030f06152f06010f0b0a09 73
    0x1482805242403a000f40001050b64500c584e512100c00100082074100454038429210316015541d82c0056503103000901400f802c2250500101c804180b442400f07482c0306586e403c02c143d0300440c01008440940c056800344021940000034001156405031321074041c0500c88000c1c14560070a12010354907001000006010400718501245961341246e044900860b03000301140d54482d40d800040c005840c540300e81c4c4246a180c1000040c2c0714a4440408031225141801000c0142c00c1c069001c040e604003005051304581d0b01c040c4200b43c1c0303424140500c1031254a01108005152902c1000032502d180042d00e13018084082040c400a80c1043c2d2845600b6050600543c49070394401d9054903103603d55024640c4104c50009100b01c0a4042d4005082c000582d0303810300c01c411020204030241d030354500c183c00c1404403085000f082c040c032820504038958255100f1460510201b0b061142001c2c003c1b11007402908198010400105101d401d20000c0122a40080c04e02541c52030240080d005449034a006 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 384724730 1250 384723480 384723503
    0xa0908060711070e220c051018050d0302030d1a040f0b030132041407031b0801062315031504150e0c0f13060903060b0a05090705070203070906141f0c 66
    0x1000024203104007d170134094028041c0c4901c1c164010551161201a207040c0e6a02d140045007501342518502001c0b40c158006601d82003041008900a0400e0725552010864885c41d10707110307035510700074041100c4040e100450f0001d0860201402c4030a4840301d000800904800d9401482e001c42d00c000b499240486210645c0d0f82c1e5051405100c800c8030101d4145c5c0c0183c50000c0704000c0340e411070202c10341e040349641c004c480c2c84007000d6088844c1d60217280301006400214070202d40718070503100301c0204080d0044d41c41c0c40c449050710000307405c00e84403c411540d81d00c5a22200b42024400c458a050300c581c4452201890118410044a0003a203984402c0c2000581c1c0070920350300104564030414003803645c02500c0c0da1041c00911041c168002200e031182880d00d1141c0514221440b8420b80b08020100d1a05480d03000c0240e030b50390700c0b08030102c1e094022840c1c001014046403003040c0062500c2d0884c0200e40c464a030400c68000d4003100700c03001404449100c407007130562181c04c0002550340280d2507000c = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 384725980 1250 384724730 384724733
    0x6052101060e04050105180304050a0902030a020c10270b0115110312040b0702060403020601051c020a0b0702150f03070c1109070903030305100e0a020a0908060711070e22 75
    0x250445402c0680c00e42464001d01081000552003a48100f04140c0b03240307600400b08042540301e2080d80b00d00f90740480303205000e218050a580c0110341080450400500c7c01d8001c0d070180e410030000d030015003000c1c0d80e00c1184141c55080340d0010b0811ba1070141120f11050f450740d60b040d02948044c0200c0135005105404056428020381d46100d003405c420003100c0e1100469004200c440b00119022a07951005d080031843e01303400020a6402194541c01030705d01c503800c0106011043c00c01402c148000c100c404207920241c0c6071010480040c00c201726486a688041d40184043d10b550140182240c00e020000d404222910030f0075240c0001070791808040c04062428201c90196080088907403000840e0b00b07000b2599008208502280d10a407406d0029035910420181492294807440410400c020001000040140d00401300d204841c204003414503112500b42c1c0c07038800101c0308040402d0401e0004a400341081003144001c051030041d1840034039000411055054045680094174888112080b0 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 384727230 1250 384725980 384725983
    0x31e01060f05010c060b04020403170307030c0305071d031006081c1125030215070314130317040816181506050904060b19111b09150a06170703060521 66
    0x80c01103400c102f5807011188058030710902d90307009a070381501080ca01b00300c44e55114080d0040b540700b402e4684400d0090000080c06021060b590f0b0607441c1c1c0f501540c1e03d0402440c120b4031800000e8141000140341100321142d20b811201c100344040014081302518001d1164400500a900c49820810140340349400070b07041142c01da06600000d41c40600042c0c151444050380703014002c006d0003540c61410852410007000380521880340c0e8081809442d51040c030101d03a020400354440c2c04c6045503585084e42d201d00b09030500c3c0d031204001955130300c140f0003080180d0707407515481000200102c081180da0001e0403c4100031540e84651003d10070040341e050380644c6c0d281d00500050054044145c0e5480040007003100d0034021071030b150003250702108407a0821900281303c007510b105005ea00100b90600c101000310040008040860400c0450b0318581940c0742c90380110000c0204d5158640b408951404984444200500e40410149000020031040d80c3e0b03074811840040c041c1c400610402c0c6a44a042d = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 384728480 1250 384727230 384727237
    0xc0c030f0a0302090f01091a0c0f0a05150109020310090e0102070f23030702030c0609031032060916050c01063503030f0a0605031e01060f05010c060b0402 68
    0x1140c800e90114107607850715007540040c09692030031141410030003403141c01900e2500f0f450041181d0342d500352644004500c4003d000f080a001c0110803203d80c2010409050302e0a034070301000711025003003030f242d400f0122024800d46003d007a42117000c0d411860200322059412606114400c045034403400010b0300710f4000e50417070390580d400460070a004445410512401002d1a5030f52241c854201d00d035648016010056925142d030050260200c101c001c400c000302908071443ca6641801101102210074200b4031581800c01091500750006030310382d0a621001150007214041d0034500b4208004103941c80072040f40c0e2009503594250814030001008481d140140d00841c040b80d03181404c04580d1000401d103045000310081d40740b00c0b04007060003040445461402082040354401d1001c102c0d07000040d40c1107a0b00050035500000c61603030721700009242060000001017560b1808041c0203003404207000b1500903042c50010f2500d110300d490700090201d03e40d010080c04884d9100075080c0240e03070340d0b0100c = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 384729730 1250 384728480 384728497
    0xb0f10030b090109060b18040b060301080c03150105092811090f1512040f0807120e190b0f0405030a0302030a020c040b06070b0402040f050a06050f180c0c03 69
    0x1001428000000040c004001d401c0c10507102d10071400000503600c42c24090f00301600d01618034103040800306201411820510901c7c1640f090700ca80400030151190f901840c020301101d0006d0190500c91001d060500800d408038007400c0041d1001400301ea194120555008010150054001d0010000f0514800105114244010300701414542c03a0700040002c0d00d07504504603076460502894404005c40b04441c050120f4152109100340c4c1c100c44076402081c0d40c0a40240303034400041100c3d0341c4018480d40f244504072801c08041e1032041c0c0c0c036035105e12625902030741a00e0759901c4040b50b01803c0c1441869210310305800d000040e03040500841502075800601d0050100c0d0000010b510b400b07500c0303802543c0034030014400c3e5964104503240902800602c201c0180009207040f03003980305d140080c0f070014000e070f80040d2a4a24150740c80e140c0e10540c4d200d14240040020f5041c02c2004000d0741004841c9a14071139104454110300506031000c8041d00105071011480c3c0d101142200c407811401132105 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 384730980 1250 384729730 384729739
    0xb09060313060e01150f05060703021f0207050105010b220501020709020702120d0207330f0e10090906060203031b0702010912060c0f021c0f0c0f060c020106081c030b0f 74
    0x3180e01d050300d054200091b503401e6440883c4250701c800910106d8015504041d0050b03010105218510004501d81040824035800c00352a1103e01d4442900391138081c1c2c0800c0c061540020591104070380f00740111074800e203004543c030080d4a0800002d660f81002d0050703220840e4001144d20440d640d4003904900c1e96203c40a0700c4294880e07040c01381d111030781485038a0450210700403008603641c50180c480007080d000b03a5400c040301a1994111107400460711400144503a5400c0c954085da20f169203509082c0407640c0300000ca5040601c1d4105440c5180d0000d404d541c42402400b15507080188150f0017004c081103c0381c1c807000680012140c01d046540100c04503180003200c034003448072a8100c1c145ca50219203400b001b40d83e421000300d07904e44001c00039549010b010418078201a04c15501d8203414a21842e0218086020b9102c1c4210513a105c107007200c2e211b55440303c2c2c1d9079203902802000c008100303031307000f902145641c4d06035441e15031446100c50040640d1500c004525583e074200e0390707451a10140 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 384732230 1250 384730980 384730991
    0x504060f030506061f0e0103060b0d05012c1f0509130501150806060d06020405032b0203031b0c0a0b0406020a0305010506040f0b03220b0109060b09060313060e01 71
    0x200c19181124001594903006003800141281404002c02000b654401070001a0001250085517090070810320b0504068952400052104594010348118402e448000525515011902c080442c1800060f01c050076541105071030010b600d590139600c070041d4509198900e002498902c41c18005d80c010903880b65102c07080c40395164440e020400c085208030000c104222502c1c401e03d010022922440105074008000205541440090142c5940c4502c8000d03040c552210300203410002481b515404c0c0350003020a100e84c10803811007514030719036a4005545582810380002c85052400f80725035580c403100003504d503c81681049030005854002c404a500c030305151402c0d00c00f95204241c0b40c40001c0c200703000400c41d4070b1b16208480c00c4461500100c14034604e030403d440e125820041541c01514540c003414107225610100108096110740b02041542d810f1078400400c4412039040000c03081818412740310a03071201022290001c0c03440051903031040e003520700301020b800440c20204a80d402c21 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 384733480 1250 384732230 384732239
    0x1e121401060f09050306040c140d0b1306051b2706040909061a030c01032703030501030506010b030402101b0c0e0a0c02060f0a05040201050d0c090513020a090501080c04050406 77
    0x110700a550840360b0f95801c800302d590304109683c0c1e10060340c010b4080145a441000700c4240725001c0c140061001d46488407650381500c0310005103c040b0303040740c0b030240341c40c1010303042044510441d46d115160305c9400241d041002c503540414041ca01410000c0c5412504510b0010140345002810280007030005982d02d855160303100141402400859500303040c1458036250400c410041c0b00764100142c000c0c4020120540114003070080910b01c002407483c07000c54038040ca903140182c000340c180640ca01182e59451490f0080c50190140d01002c107000c41402484016541d8251101c00e80c0c3c218038041c0611200e20102880026201c4801004880070100c00902c026a129007103104141c502002c00101840c1c0304181c3c0c07202c41c00c503000d00a9074010701c00100184001c0d80070b560802d0042c0f410b1400e00020008110845218402c4d210116840c00020407840c45c11505503285558506025424840000300282c40c1d50710700c1c0102c505001c0b202002545800014095500402d07004006004044e502d = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 384734730 1250 384733480 384733487
    0x2010b0402042114060a09120206041205160506040f020f0d0f0206071e05150903070206041e0e0703140c1603030f0e011514010c020a060c02040b040c020c01020606011e12140106 78
    0x2080801c80703501020b483c234800c0050000c1602803161ba00100341804200301c50008440035440700d502c03c0900385040307490300c002c03e10400000d0302c55071040030380b0360710024140100041c4100403030404c3d100b950706841c0c034000a0030020400d210300d603040d40c200b0340701d4000d40f41c110a52a00b01c500301c0380c5c110b0083e42190a001e0001101030402620006003a010746503442213548a219080c40650450303c20031040003045c814001c02d0344000024165006190740301c6119542c81d00d0140c070b6010001f81c454007400300c1d600d0001905904040d601942d42d142a60100c24920607111750710014092558985400c8400c1c0e003160080c401c03000950000f003120511040034104002000c2c002c03160186581001240194029120000800d030020045180780b4a400d030100d42c84440068102d13001a103840f00813820303031143d0151803003014854020f403501c0240e0030002850101c0c0145458100026079030700c04840d241010306d03481c2e000b03034078988209441180e0400d540544511038229500786004000042c107a40d1 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 384735980 1250 384734730 384734741
    0x4050904111806030304030201050708040302040203010b07200d080a090b190e03010b010e06070c030b04210e1f02121207020601060504140603060d02040609020a02010b0402042114060a 81
    0x4111144003001e11010340c08440c00d0800c0b43c80d00d4065001300801e0000d9030044001e0210700c2e1207403600d03d14140d203e45c085002c0c0d810030fa00070006030700e0201e158002c0025421300748214500b00b081c114120345141c400101514400440038004202c002000300a00348a49030304000750035044811951b0341c4480981c0c555400c1c0000c0e0400c00587c115903400d00c2da24041c05583c6075058141d403501ca050140d18104052075106c0c40d421610312019400000028503103050280c400e83c0a440441109000981c0c800040401c040300c0400308042c0b04240000b5654640383c2c1008a4848025a1443c02c2e000c00260b10342846820a114004408500642d081003105049480f82c02d0903829280103982c1e032042541c103401a0f001b03c0594811000c6007070494100398010b10ba001310001c0c404112080340d80c002c1802c451041c3c10030403009400040b0840266024000c8003800c2e2000d4404503d410316022051160040000788404081c000300e1040c000d0040035950003203c52401c0054442030f05120b5882c000410 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 384737230 1250 384735980 384736013
    0x130b040302161d070305071e0f03060503010b130e0106030209100801060f030c0608370617060a0e01020909010602010e0709090b161404030b1504020c0312070504050904 74
    0x10303003080001c510640f50f4030011000c0003280c424282207440e520000d0b0094074009055104000c040911a001a500340c0c005080b04d28084c0c90300722881340000401000d507101900118003980c108546104903840700300c403a05160805181c0020700300b20f006200c0c0d002d0711960740f0280d0300c04804000c5c000c20308041010441103802d05802000b00c84d640f801324010441c45803201030000030503204200225406648007551090004000110380c00a01d007000c541c4541200140c0c00116110704020f1215a06200d0400500b0010440d100c002040c0241c90341d90f00c000130561802d00e84c6451490082c00c0c000d406448006e100244440d1603507859403002402031903140121244c912880a00140a0429100d0823003465086400e00b0883d17075070f00401300041d004103007140080000e400060010140000050001365105c1d9240000c9418603605000d250904ca0340c030144161f20410685040ea0000000c0b9a09014104104180e03541c9152080c0c1c2c1c6400b541d44016002887e8204000412050282c00e900f188e = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 384738480 1250 384737230 384737263
    0x30706080901060801092015070501020711011d19030b010803072001080a1a06041e050a150f170c0a1116061b05010e0304060207060201090804060305130b040302 71
    0x3e5aa030411400e84014006c0503240812011071000400343d8040ba41c1910600945188001c80001524144a80c132801c1c094540365030104041003046005041c05201140c01d1034451390481c00c06a0102c1c0504a14180b00d1041500f0360b5203584ca484683c5c0b200e0011030300002c44103035941c0d444034901e85035445500201e031059080a0041014100d41d08101425001a55654007a594031100f1000500c4c03000320070003803000d09040c0c10703940d0307a5280c004001500760800c01514081c0f0700015642d071001395400640c46003913000002d0000c850f02d031340803040c8401c0740e01e4003105800e9420001c4d0f4601c0b41c40c1c802203000c044080704008440041c4401029981c2d142d9603894075003040e43c54410303250f20340300c83c0c8ca0350f070b810303800108100180c030800090b0400c21408030600c0180c02540d450508440521111b484e550f0008541003142d0b98040c03060000a000f10300007803103d00540d940d10010b911882c02401c0a0654890101d14032088101880503402da2161480c5414101420040e59030b0074548151050b0 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 384739730 1250 384738480 384738491
    0xe0a05070f1a03040302100504080d0b0604050d0605100308180114180103050702030d090b15090915041106131e031106030703140c0406031532030706080901 69
    0x3079405500c000c0c003181e0a52209101d82550700d00d2014a81d0700284c425801c510840081504d02541441500d001d03e1241410680e1080c3c0d0840340c106030f90703000070054072a00e018801084a40c036071410020074154805d600140d65951425682c8e0b00c1c601d070340c00203000f440001c00c0a14113000203290020300b040c0240c0f14403801948407260300c80c092042040c0100b10f200807042c00b00440d4007d4000755006015070040d2418411303104032120440d10380a60646a1140e04005c0c03201d1005860140351150b442a100d962080c0703426260103960302c44100c29100e6400d038004c0010180011151a0790102d82e00a040790798030384400c81d1282ca90307051802072042c130f00041190a45902e07040c0c2e407403c045a61202c1c291400c5002c01d020480d0681008003070174145034850703218000f010994080340d03100346042001203854605200c40202180d00c6110f481060020803082408a000a00c1007000041042000480011409404010070f40304841016816103c0d281d004541a030300306060b64859202c03103008208 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 384740980 1250 384739730 384739739
    0x3121309140402030c01110309061303060501090b0307061103070b0108060a06050102012007060603080f03070215100e1f0602340302060c120d09140105010e0115020c03010e0a0507 79
    0x1076941080c1e40080d8103500c003880d0200294003034014518002101030030f903414000c1e41808030307a03a580582466480c190705480c041c0104a4a84120790141c410780c2d00401c800d40c403038400300780d9a010380d0281906000030141d0011b20315004000b12600550b21849142055944a8400395a0300d400c0e244024840c3c2008004101c1d9403051080540d98502c9503800181e540c240380031b042c1c403540006d03020b89402d501e81b000440883d09140050500b403940b450000e542c1d20742072030000d0410301c1c60f10103c1c2000130504284583c078200a08034205803064881344020ba034407204a00751102d9030710103000c50b4003d0100c0c0b000810940103e03c2c51039124049180080b040314044d944a05540f01c4403c040c00446843c000f130015040500152200003804404c0300c0c2054644dda0201a07a008141c0e2045100c0d240d8024000f0401c000c45c070141c4190f10000280125410701c1400d0985c00d1050156100ea0005064013582c041d02c01c0100b481c00510241c000c005c07101d280003001c0d0700d640002d402600e20788210500081c = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 384742230 1250 384740980 384741011
    0x7020607080f1603090204020a080f0109110702212e0912050a050c071401031413020118120c031a09060402060d112101080102160b0603121309 63
    0x900c00c0245000011042e520451036805214120b2910f500f01550741440c1c0005032994801800380c1c2445460308010f1b132604112030840008160403100c80c1a00300040010010b0304c40040d2144903504030390310501459564050b580c8171443d49440c0d0528860b581c40b9040c13010140d41c40d240031940c47d0b031141e4040e00303105a0b54010740b82c844400405a0004c9802504060b2080000c0c1800c001c0d586442490841000c948a2a00c881600184030342d0201200d140d130203607017611882c014002c0c0b4807061002444c004090f1940941c3e480d5010b41070088c46030340c040c80100980449000b515410310710038800403850803e45084040c0340000c031842d0002e0440841c841e0505403c842c1700760800402070100b9036441e030034842c80da084140840d507040d450303801d1036250780c4007040600311004580800c44800000309882031641081a130181420342d00c100030888000000500345c1c009070380c101280904684910700400e1400050700f0103131120311000f0814043c10300ca0f2580a02c203c450161003440710140742d40310708e03 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 384743480 1250 384742230 384742247
    0x20108060105070204451b03050d080105030709110a0f051603020a11030a2003100c050a02010b040b300a030804030e030105010b0d0507020c0418170307230d0903050307020607 77
    0x1a201e41c000466401e00207032002c00c0c4260b181611fa40c00071480c81da00c1c0d039182d181c4104080320001107009000144540d0808001000080041800501c508a41085a1507a92090a105c0002c014070826400c0742c0b24050b20483c2c0030700c44003615a8011a8650800035240d200c0510300700c40144040350f0102c413a19000507501080e9810060542e105000c40000768924115030280c55003501480225141600091141d643c03100c900c5d4507981c1c0d40744000e840003421940740f620403520642c640100102a500c401c1c0c1088c1e800b5002902006440c0d010a5903031404855003c610501d9219000700c3c40201079210b035078140124405c0c0c4a000b92200c2c964201800d81e1401d00030041d442c2020b0100c168480800c0d04444c0d040403960044d240080e030000042000d496030f01c0200c0b600c6070002480300701008400d00d44100c11003606404c035401d600304070300010001c91160034000d6a01810000c42d00d1070707140c107500300d4011000d0140c081203050980d180c081d182d80c000316815000b40c041c0c0000220741c9030040501 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 384744730 1250 384743480 384743591
    0xa06050303031314030a0e0f01110c010f030b040c020d1404080303040b1815011a03100504021c0609050114040504210e090c0c010b010906020a020108060105070204 72
    0x9103040d0f5968004601d0341c0c00f020042920400594894042041e1007400104003000085d6500c00f10300d003000040c82401c1210601481c1044000401f00205c01c80124640d13204181c240703411154202c5560040b8060211001c1c103540c4240360288841066070001004080700d00c0c2a00d0f8000d0501c00b110742d00406000c0c078401d8045d150420800500011a0380da0030603030001052240150800c25030707600c189000001406071511590000043c800c00303440d00e03040080e003000200801d00d5450710380301d03180e030818141c4180c0c0e00442c0c0100d00c0181c1c903103ca545559951148403010000c01c0d65821489010748020b10a0390920b8910071003183da1802d150007480c0c81a40c01124a0401940c1c0d81c5489070300c90180d5451000b0408802e24030810b90b500c4503c0140200300380c000f42c9031101c800700c82aa0865280707114a90501c00440d10412042350040780d0034240c9502402c3c400b04a5940e840165100c0c494124021341c4a03151500640e03410414082c9054200107401110305141a030900d00e82600040440 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 384745980 1250 384744730 384744733
    0x6010501030506011b0b070305100303090e1315050a0c05030606180f120318030a031403310b0106050301060c1502090d1a090d0f1206030503041206050a060503 70
    0x18055540281c10154121006160082158142d811050b400e00f821181c1110340038008000d10000b143d0500a4982001c013104069000a1541d0f03400f5080d500540f02d0110b1208448000070749060060741e0341220160403822103004200403565040040200f1641140014600400805400d1085060380d1080101601c8a840e01d4845022044500c0b07072062410b5101c08610a1010b0544400454007200780e1000010741d12811034488501c0c2d080d2084a21900031b900c085241800310340d12106482045da01c3d0403c459503034650ba0074010940c440392a0314011088100c804e900745907100c0504206e817a0089000144c140d88a000440e400c1c071003840360200086030710b0300c11404129103141c1d0980c039020140b0018030304042c210204d200986ca110b0281d6104088191102c404228141c40540c0600d406000c0e104090358010013400d1002c50705000740800030400ca50078030554250344918065908442107984942d83c801151f00b0820982a0840741c960600707001c190442d04900516007034030070050 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 384747230 1250 384745980 384745993
    0x1e070806010305060d050d020a110301050601051905040305010603080c010f0c02060105040b030f150402130603080703050c0a1a071209151e020c1e0d021c183302 71
    0x4501401004d00096484010161080f0029008005d200010120764005c0c2040f062181000c08000c09045d041e0340c020313410881005120780e84401258282b0b206480d6088558040690854181c056908001c006620740240031081c0400e00300a03000300e410017002440a03035151200101502c21201e1841d002d40d001000510881c94107402c1034030100406804c03248481c886002061601030302d51511413181070342106104c10740c2081c0c1000d040107a0031031001d100340d514580e0380840724070600340c001d0100600810540c2d5000f000303004030398441703411109151f00885440c2501200540a803000000714442122a4041010320f00541c40c4098005c1000d5106912125002d0040c01c0c0101064910402561840896010f5480500a060402030044c0002088042000030a4103060140c4210744e12020104095590010b840c02d61507910180b80304810710102e5094401c480b1060500d88801425240840e140940e1510424001804004004501035603140d5034581c20314519210300680069 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 384748480 1250 384747230 384747241
    0x5090a1419020d0213030c060504080a0320010903110f010e0a060f18050d0206060f0d12020304150804052503060203090304050406090b13021804050a1b02061e0708 72
    0x9140c07041031001d048005803404400e400880101da011803624074803092440c0091040c4045a20244007034902820154541070400c400f003a076494101400070100813400034134060100780c03a0003850404c9030010003030140c41c1152901400c0000d640360004014810000d403d208904140103140114060714050701e000383d0162601c80c0030701000c0e44101407858580c3c10040d45488640e840d03549450180014041c0b4001e4108024200752010b41150b10641c20740c5d040302116910307034184200382ca03402401007a244804d014164214041c80e440316008094119182128540058904d40f1903845074040d100c10304110140f509100604450240c00300001e03000502c001f0f5201e600941e08400210f085904081c7e440c80004c01f038030480d40020070900c1d211554003c890405001054120700ca40f40705505016007003648030b10210322941e41e03034403c54803400483c000380c14035031014010144010443d81006a0010065960203055450a9000e42480400400c02210b200e0150050710507590703114098842 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 384749730 1250 384748480 384748501
    0x11070501170606070f05030c010c090e0a0e0c090a020408120712080a0e0a03030e0c1005340803010614030c0d0c02030909041b050402040302060306060a0c0605090705090a14 76
    0x514490300030f402001100c021581c84d010754010180701d000195074805d07803000024299031101c2141c605110744203100388400b000e050102035020110303000010380c00645007907062400c01001000b54201c80d0b20021710002da030315038000740181c80405080b11011682d0b0344851000313229400d000341c44101181000c5951500c1049502c1c0c100300804004181903e48401c040c0c240072100504602213540c584c190b07e5010070174404900820300440f90850070100000021344148140282c00c050035803003100001c40ba8180b1018011440310125501d84d084105103030044043d40280031704404a200e8a50100c02d1143c02000c0340d106103025801e04d0b040511210700303000504604031481055002c14000409540c8a2140c0c44e44194002e4600c00a05041808104480300a0340c0225000d540100b10600c0581c980404076500324905841b00b80e030340d41d000c08003280e50b1400420020285170411042c4907900d10300003001026618221140340442c1c07204d841c0f01d411070390002401d20907000b0341e10004120840 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 384750980 1250 384749730 384749777
    0xe01150216090510080f030d180506010b0d0f05190627050411180f01050a06050f0c0721061802090402010c080d06080609121309050a02040b0f090111070501 69
    0x2601e07100c5280b0503203170386075182861502201d0300b55580c408142075074410310f01e0113104c1010302c15009901d0a82d445890b03e54880c1014042c51466803c0003a942d0603040080d0321018111110100810207414402000d9090700030030001d148000f070034a1404201241d42e4240b410018151400640c0c5070044074071000f025050081046d40c0c82100308120010540b24048a050400e1007500f002e5858600200d02c01a2401d040c4c00040c0540c400442c207001c2c00e074102d0700b1101000c0c064408262070740c4a00310001e00e44001a0001054012402e550000806000800c0000c0d239100f61402d10204810600080f004161141c0203988aa0504040350155004d80d010300c11490042002524203218040f416040c4d9285500a503041d900c07210401400010034081c0d41d000981003203100d4500040380b070401580607511b0080303292555994001c2214489154111401014030750040e5455000910b803100136500060034440c08540004082d9040d40070108505c02542c030143c40e1116a103100e401600c3d02d0b5070 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 384752230 1250 384750980 384750991
    0x60605030c071b0f032603011401030b03120a080a1109060405040f06090e0a0b010b0f03040215040f060909151505091203030f040201020d0c20010c06060e011502160905 74
    0x303c02180c104c04200c48400510700509000742c015448800ca5030140078511041055000c092005001040780c025030691049803d180105001d500700e00003034140310b00d01d6072984c0300b080700040c600641a00001c00904c0b541342d144080040080403200ca094500c280e028032544108100b1061000b450035034440420015003c0d80000e1194a8105140442d141c001c006043c13036008800510400007142c0703010340902410070317110341000c0e2401510100c1c0c2c000980b00070300c98105403809e00035a52016045e200140301382c1d07580c0e03107200781c0d11407004c0c00c00704040c0070310b4020354180000710740d6100d0b02c458068115900071010707005500540d04100d409401440030386900c1040038030100c854070380801c0590f000d0384080c00c030410142090b10001e8500b9a40e00c4020091024030840440441d60303400c0000a44101d0028000c8005a07100048901d00d21802e0000c16141ca091408100d24507100b00703850695542030114508080642d5080c3e03500d07280030800c00741d13180748090144003961883d0021604403 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 384753480 1250 384752230 384752273
    0x302060d020f0d060324061805090a080d0207060522030e01020a080f040603150806160c0506070305041b0e011a040e010b0d0b1005030a051f0f030204060605030c07 72
    0x880402d00011360744e00380c1c404c2e80d44c1c1001099040342540381d50015400e03988410720401075145403451904644c10341c2648140e019075604005003010340c052000303112056005150f680c2d507030b600d00c041d80007d4000354000d4400d0762800d40022001c010254030501d1100c2880f85152000780075a900f1581c038145407584a046019000d502c40c000751261000d44410440045800d40303680c1000002021030360494000d0b4250018010104140000415003a81190b5400039030a101c1c45984020380d0605041e50000f8442e214080411004070307410751040303024511410700ca14140d0a41004d5440303000c070034002d071141c00f0420001001140c1d201010328001c20b165081072800c1c40e070344444035011107409a202000d90b660014480c1110041845030002180c800c88582980c04000f4100400c41d0000a200030102ca41c0c817000f00b00c10034580c00b04041e0180303145051145040d120f070440d817075190380c52104a00603810f01401140700e500602c1135920940c07043c040c09051040d40d449408809804048500c0704 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 384754730 1250 384753480 384753487
    0xa0507110a06050103051c05040b070c17060a0b1e010c050f030a02070f08010903080105040b0d02030f0a03200a02090408070c09020c100c230409050406050f100302060d020f 76
    0x1000041c446109241e0103410300068641c95030804074180711004610741c90380c40d82c0e18400540036401c0410388003691209000e0340e880d810b181c03408180b1100304c0d4210052801181702c0e80d20004000003403941c8201c10306e58041c01050000070a00c42c03c03401003d0300da1140d01802d4003401c500c0d449001040c42d0640a00100c4016201c01c0c8422402e40e0b204150190058000b80c0c0e007030020f44145540480100703124030003080380c54542e8030014070541d41805103610450702d640c081031a036529900a1154160000c083d901c102a007a48004d58071242c40008801040808982c840d1290341701820b5000d200c89078016002500b00ba07402c1003641c000c0140100c0d40001305000040102d810411003034090f0200500040c3d0b160048514249003c491000803242107040800c07845403198002c00c000d00404d4290903107407078050788100000d160b00450b0031074001d90b4501b004110074020940c0096002d540ea90a0190f000e84421856140301c100300c2c00003a40004d0100105d401d10480c0e0340c01090145156001d240c00d = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 384755980 1250 384754730 384754757
    0x810090f0f0212090f0607050d05070201090c2d050307060e0315090703031413060305060a170a0b010e0c040e060d0b041209080f06041401060810052d0a0507 69
    0x3241c2011031410f15100c00b0780100200b072801000740c0b4011707000d80402844d0030301c0c12020040c201d00c00c65200c0401d07581c0741d40115031841e000f5004040040e5215441c5a034a0b5240d407520100e0409145201a00d405001005a141c3c001410704109a031800f4014161042c01c02e9400d8030207a9050008940500c03034050500d00c4c0312112614240148410340150a00b01c0c42c2d030a00808210b103415800403045000c1107288540e010b486168022a141c82c2804035050360303524000b80e030340010385d4003003004003002c0c0754068000080841e0280c9498495004a1003507600d42400b42c00201040b524001860020001889201c0204d0050b562103d0014041c60030740ca10f0b6581c240215a00351000c036409600b580240c0b9810b034000300e00350042c042e124014010305042841c0d041d03070b96801520143c8140d4150307001080e40c00d000e4002a0251149404441082d0403c211400003408122903d0302031994100d80003081e4502900f010304030120181c200b060a4841540d0f107001410050300501c00d1100c503015040 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 384757230 1250 384755980 384756011
    0x61f05091b130509061804060b120106080115080c0919020f07060b03010c180e0603030408160602070e040f03050c0106030b09010207050c2418130b030c010810090f 72
    0x512112400c2c18034054618080600050707007006840c80e807150610350031480706001c0c0144207641c865004140816180448030200d0740380e14580c5441e01055082c44004611200e0540050682909071f45100071260740e142d03540c40c1c03034454407400036034800000e402203402c1d03144401200c01c100036046ca0041c80c207000c03031a12660980c0400801c5a1080d184e0303201103498a0280b181c0303038031600c89051502c0d14192560081d500d810190003210700602d4403401290840e14100261409040e01c0000c4a002c017080c00400c10101e045403280400503c102c40001c201180f040d070505000c1c40d07002c607001c1d100a40b036507002e842c55005590f401d080c5650701c800000c04104c8540d61903008840510005a0f6540c10742006814090002d24450040e404003802c5007011002d41c07008202c0c1081403449a40784c90f44602c091a00c46c5464016a0307010b00074020080440c0070651160801900c11400c9a0113880c4041c01926541030440e41c8580c071402d01c420401450b03050f40c100c142c540200c14000500340741804e0b00c84 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 384758480 1250 384757230 384757237
    0x3060a06050f091305072309130b0406140306131106071109010b042d0e040201020a0b0405060a05160906031d010f02030a06080304030b06041505120a0302061f05091b 73
    0x703180c0b41d100c205001c0801c1c3c00c024001c10f80003200071031f01d04080c1c201400b500948078001d8628007511051901c001c0c03241c2aa4010041c5510041090250070390b581031160f501c518032107400c0c5c0b0174000c50700820001000c11082c51015684500b11411105411040066035041003e00341c0e0356a620910001040c0c0d81c00b901603010708104981e035074546040500e4100c54450308022060005804241090184911030301c02c401c0b2058984010204e54a03440104c1c205480c40c04000c080d0081001400108040810421310a0305c12102c10091079541d10381648800b9041c001c0040030958202d01031152610a401102002400d100011449555243c24500f124203042640d100240d0200034080b107002ea80c01548010150003008505181c195120700d034207860f028007840d125640e03139840700405190b40c95154000703000c010698500c0e01c440607250394a60b011850102c0041c0110700004240100680300820980e01086040300c095007881c00344940a2000303002454540d04828814000d0203148005 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 384759730 1250 384758480 384758509
    0x10180905060d0b0a1d070302030c0d140303040507092702010e220203160305010503031b100c05071103060c040e04060b061309050a02030415050406110a031d0303060a06050f09 77
    0x1031780c0400b01d00d5840083e02c1e149030040d06a004084104056600007480000320801141da106c10060f03545032500e450002801d14421600000c02008181701012400400719541c54000380641e1242d64200301d90740b5100b480b0543d01d904c24080c2e460255108910f0303946600c0e0302500501e400d0303492450940040c1124104a11450780010420403c020204050700b0b07030b0b84050509010f2035040900181c4c40b40100e0404042842900c803c1b14040b5070200402c039a54203040310308210307240d040d031001441a4085d00c1d00b03940581c0e10040309c0810b42000030f11548200180380c1c100b8101420600c81030462140600192109a22440c210310b9542d00d910041001c2c2514814000110780742c68611380603a440240a071034124818020880801c0c00c1c021920001c6518583c005003d0340c4a01e000d5004045400c80e00b03101801c0806e044410316055407200059070040345e0b06c038021b480d0081c5142d40d2413000304d821b15003020710309104208030340c01031014090b401440c10045003010000705c08900f1000c0c48101 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 384760980 1250 384759730 384759751
    0x1507030806030f010e1b092205011107060b1915050d090605130506010e090a030c050a0b0c03011404110a0f02120319050a09020a0509060a03060207050c10180905060d0b 74
    0x20704140c08441001c41122220050b100d0300403030310341000d00001c040001d810f81860240002d00070b08c1002400e41c0320300c01c81101b107660b854a45d0540c2c00c00070020010322800c140540c07000301d1f04000d000c2c40e1003251812284041240c40f464443e1071000c03070b02600600b400d10301c090b4440d0000c6001640c80c1c000c07503125004114006c64102100e09105180081c1070380400a031701a00801d0007038a850208020724190303094100790f0340701031042c60100c1c42d210600201410f49a51002031150707902011000b0350494090b00c24040c60031a96404200413202a400e00a0b071500c01005140103580c060110442c2a28980c01a2510404a00d41701d10090388200c0b0091008034500c22548490100c07417007000d0300085040400c0111139269404240795000301d00401340716500e19000034105076120301c0c00c6009507910020654580445240503595141118403151123000204c03810305110784155403000070200b601c468000e10074600480a0000c0034007812241d0000000e100450124418074646401084000d4 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 384762230 1250 384760980 384760993
    0x503010501120605250507020621010315110d052208070c06110309040e0f01091b05090402010c060f020f0316110d09030308090705030106030c060e1507030806030f010e 74
    0x2400504960b40144a42e80300705d0001034407005002c0100410380b25603614100596907a03018000140d240c001d41c3c06100700c01c1c00d00034040e1002201401001e040324400d08030301210300e90590b5100e06807044217405a1041605000c04695544150042d540000301c4022800d00b25000c511081a142c010000580300712a001801a04104a1480002c02808580381c080904400c00c5000c2c0d071640309129440d40f00782d031680780031500d00c2403d003c49105440030340000c0005402501d031174003007c07113803883c0c0c01d407001741c905000510f604007440740c41e101e154140c0d200c0003d03059540d03c82c0300908040c401b100b4100d500340301610031340c8040d000460140b014041500e8100c03004c003c0c010031901c0c00b070b695074007070360051030b82c100c951504048080d0940f680341c10b1001036991080d01e09403800b203003030788001d91643c20800000140105c1401c184140c0d159640c2e6a8010400c4200384202080e4000c07070407854020402c12030b00864400e154854000c0c000406540e000e981907080c407825100e00380b209262640114 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 384763480 1250 384762230 384762233
    0x612080703120b010c02220c020a02031005060907050705010e121b0708031603270614030103030e0105070219090e0d0314070e18090c011b050d050a09050301050112 72
    0x100b0a90907030b01e40c0c001807140f00c1200000901d2a1042c07903009018800d40310002070000d05101c04a150918109010068080342500c02540c403500390300260301070300a40e2100305910190340071351403003207102815401a07038860020850352a482004160b410395a00c020a1071101000c1c0300768450b00c03135070049042d1185a405002d81c0c0050145039480d44603400310000b00314a0030040240d0b00e9121491030240101e1503d41000c6c1e908001030448031803488542c50302d41051001090602098901555a00c5043c0c002c45407005039511081c0070240100707907080b1a041e995840b85c0000d0070f00d60310152610141040000007a43e10402c0750300b0821140e41c030b549402c1c2c01404200f0140001e00d01078942030040300b400000c9001f9290780606082c04211840760a20040e890b000440ca08001c403a00d15860289829082d244d01c0780e2031141c00500040c0344021041a07401d500d04a90111500500540110207198000340c44a80c8440240024040308210006003981e0030b110300da008010740301d141034008015 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 384764730 1250 384763480 384763487
    0x81803180a0605120f1806010b1908040b0c18041e0c020106030f151d0c0a060807021c0207120506150603010b030103060216231203090309060d0612080703 68
    0xd0307810000400c0340c02d00004d1000c00392910a2a0803400986820000761104600300c0d42c04401548540a91721546000103540303107034540140115007444020707400d80002440111440caa007a9009851100304c500400d040e203d40c000203029030355a2121094040e43e1300d00202c0c00b61001c2103c2000070083c03100d40642c8600484c001c084990244c1c3c4002c1008a055a43e4443d134803500b460302501c21072414441c0342d4440c00030750102000c803103c84410440b2441c1055400d55911007644c0881c00303441e039018002507850081924070301541454010340640080802210204000b18103c5000c62082903000036804c0201c1d2a0080c10600405c007038050f915186120b0f0341ca115103049a1130181c4010401045000d000c0002d0f241943ea21000143c2d40b8950110f42050000c81914041e1100c0242240101002a0030b8481e4510011100030350701880d0b203032000050f2a01084480e910103400405c09046541703010402031102c000b99120000e0001d0b00c502c1e40c9684881d60003001c0758801d10014544052540 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 384765980 1250 384764730 384764749
    0x150c070602010b03030a03020903151003200114070204090b13030915050f0a050405041b23090d050f010207061d0708070509070507051b0f040204050a030308180318 72
    0x4603000a005a00c90100485d5591058601e08010140e01050110b425901800740c0260520303181c0c980d901e039081c144001c48800c00c02d0311044076240350304160a003050074450044258840305840e1802e05030040e9004003460350041d503040341c0c4159517100c1040094014641e081c09122131854541414030b45140251040209400030101c1090400d41540041c2c3c2c4001114080200b0920741c0362a5200503500340d501c4d014940103d940142050050781d009400c500c5c465811f2110340c2d5501e0070001003000c6c442c00c0c0e45809070101d13501c540208401d05160030f0100c1d481090504c11003c0321144445500c4160072a0409081205c07015201c804424401ea0065002d420b580e6041010f05003240c80d026800f035582503588900c03405800301600241100e8001d40607206665009800c3e19a1404d031000c01c0003000e624401401d20984080703201c0380c43c44c1010b20940e02a00c00160509801e50300355101520020401800d010700ba1112011603120b151080c030203880003418029104a412240c031040090f03105 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 384767230 1250 384765980 384765989
    0x1808090a09050f010302192d0621201201050f0a06020622061e0c030b090a051302030f15010b070503030a0b0303040f06080a05060f010207090c050702150c07 69
    0x2030511060100807200d6854081c11039504403500711f14011006480e0502d98001d80c807a024001400c0c1d5440d919102102c0741860341c143c02e40e8000c1c81980c079000150b51040d058850031058000131509030760304403101d5001100c400c04803c000c104501c04001c100825a000206ca070380c0e01c994100c0100811f00b000b6a411003039900031500c0c0e0084a08040009546200c001c03c004494a2442a400d910440500d000880c240c0c1024040c0500014180c0c0042c83c1d403010f21a40100c24a0007040a43c0b081c0709100c0c02e0040d0b180100340b81c080da02e80d00c18650150030040d1071070249403140100c203801030b5020402080c920482201800900d4001d20741484844c005034441c00c4c40751010460900050310100031207078030140c044000600c4030403140c0404d00d54001c0303800044a2986020011540395040311000f40720301184071007440b0036170340c070020300c12001c441070030703a60141e44004802c2c07014025036049000403407040c0c50014148203454000440501c40020380300d09414002540f0b61b0110820b204c03060241 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 384768480 1250 384767230 384767249
    0x6090512060c0304080d0615170604060b1b150f04060b03010506010504062607093015150e1509010305070b13030c0801150e060306070c061808090a 65
    0xc0c40c0c40302c102100c80c800100005c0140e140064140124081540043c01404661100035070703098507110085c1120007100d420700c031100f0701040080c6040c0381c42e01802e000c0c2d406e01c8a070942041401803007418045079441000195015000ea089104800340306060310070480e00105222a00f00750030003a0484840304c2045000c0d90501c000c02c07901c0d980102c11a07080b20340d03610700b481d40704011140518500071141c050300610285072061028040e4004080c106880c40101e030b41120568502c1008000b50909150000e4005038031084000300d410304210621002e030100700130a031110303030304d191f50302215054104801c83d500220900401121420350004004000d840031419541142c8400e90307030702c80c0382c4210180a10005640760038140c02e14040c5009590190f0682400c0d43c41d100d0b001c0c0039004038901c0000f001c1c068140000c4000403211071500582020f0041c000c542c440b00c3c03045a0a680c021010344540f40c4a0785800107005450300c1034a125401080f00030f032584100c2040044841c841d92094170b40 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 384769730 1250 384768480 384768493
    0x50c07120e0603060913120201020a031104030f0b070c0f03020d080a0524030a0b01080f190b0a1a061204020f0a180e0f0706020601090606050c1903021606090512 71
    0x116100d1a08070784e0441000c0311a4a1590344448000f00520300c840383c004c080407003c000c0b603246c8980540290500c2c401686003403109861401c4d401d2894003841c03101070295202e541000c0040f40718048404d40290300b6187c450140d40c50350f161000c8000680d1750850069100031076426005a202400703a4014a8158003888a402c150740170310010002681d860040e500400780c1800ba654040145010540e40483c40414542c0d507410b8040c0c442880c40d1001b41c2900801c0400034200e4010508508242c0d4400141e4516488003002d004c000d00c0d28107401010b4042c00184000f03d61340c0c1c40301400c440d0030001d0180e240b40c6058030500c400740c00c6c5059018080d4000180034000401e80319800d50003800f0445000440101845900f80b410214481b500b246006501000c20352960101d0010f0680714640e5003408034a90310b10b000c0700c0900c42c1c450800f000f60040248800c41401c0c01c00c1c0c8100903806481180c441d90584204007001f01441e90145020a8501e0b504000c1400c260b01c0c03401c2c502030102e018061 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 384770980 1250 384769730 384769757
    0x415110a020a02040b0a120506090f0c0a0e1509010b0901030e010e2112010f08010b0f150a02070803030c0a02010605060c030708210a0f0e0715140904050c0712 70
    0x1503860124000a12a41d140e64401c10203031074605c0742c0d00041c400c0d660000c0c2e12007c581041c0e51169416941c4410070f004007200c602007083c0c00203884003140009440c0807a86890320940c804480d402502c1410052940c0c07015580c103a440704c006901030559905140d40d82e031846800503044990807103400d80c05134106000800342503408140307001d00584030300541c28624010102c03541c851141c00700150680c0001c2001143c1d100c00103d4110541e0283e000800203602c51764100301c5045413100109a20401d0390a5141c403400940c00a006040d802d8011580103507211a0014155001210031810351140071070310a081c1c0d9424055030000b004203540c1149010b03641d1803080d40380d100307040e406800301000040d40c10340005000d07610564004110030001c8c1c181084400b4201800003140301d044010709052807030b520010040380319401c8031898201b07240f0409031480c0640c5d81541403070340551901414002c900321502c442c06014800d10411213419500d10091a2000c3d424155190400411103020140300 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 384772230 1250 384770980 384770983
    0x3140403120c0f0801170a020d08030f0a0204050a0303030b0303071a0601120e0c060318070e0703050f090c0103050a0b0409150c050c0309130603050114040210230703020111030415110a02 82
    0x1415071b40e03042c03440303100114000c500307925161140704000e40003001403c8000500995034050740c0a03943e140ba90203c13a803111413042043e40941d01400354000d807802030410020b0f00a85c09100441c6014051701d05003d040c0d11200c09180f995a0b80d518946118410070150b580d01070a0303c1048450810108284c14500e00d2080e543c202402210780501d0002010031074040141c00743c0c02240d10440221580941c560b058410101c0b000c1c5c41c064046070400380458050152400070314031a01500740144100c0111500450151001a1100d58400e0350391070721110a0720b1f14000e008103107014280012011080600b80800c0b40d0110001e1420050180300c0c030140748a01008036a5003910031180c5550184003401c03818014036044c0e000a1066103000c10903038150780381841942c07066000311024032010003c1c24041c3c5903121031030050300440072200462604400400050049103010380b000103182c0544801e51344081e8810755095641a414000741c503994201400740d488100c0f80032544908241c00d076000603 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 384773480 1250 384772230 384772247
    0x30b0d1b08032502010c02030303100e010501050708120c04092903030909130813060f0908060c040611071220010c0c05040c02010e0d030e010e01060302060f030703140403120c0f 78
    0x2528601c0e0750f0070714400d6a1003400300304d81e082e03001401c0e80c3d0f40342011402c8010850203482818055545034000007402d44c0103c09680d0541c0d088884546420300d0155004014031008201e103031016001d200120321341c005446068540d541e20f003c2c002d500002080e445210085040100384a540104400500da88440e00603a811111150482000b4100d51801c2c09090084180840703070100191000526030382d1201c010f494000641d120000042c0e29075203c151101000c650089244900300003c000e01032003004c01310381c034502a4080d03a11103511211002d5440d404000192030107107400c400b000c01c203a901010011585c3e801d08100360400c982d560f80200c000428498140302ea41d48170719038400c06000b034000c108052241c20958200d4995050007500400304844404403940c41c0c030a13000c2c0c0b8140144039940580e6001440e150415007003079001d0b0030b2580300818510815489201c004445142c8220352405548291203048050200c0c0503040e084400c0c200000d420481d000340c40001580c3c1040c00c5 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 384774730 1250 384773480 384773527
    0xa0f05010c06090503031509180d0c020102070b0307030203011d040b1617180f0f0601050d02060c01020406120f050f0c030a0605031218010c08090402030403030b0d1b0803 75
    0x10003078001a040c16402400c0829010b0441d0100100300700a407242007010525080044940014984502000c528003c80d0f2411070304455200380500010b42c0d00a042800c585841441141c0f1107030780b203c000e1202074005231100b00109801000521035254000c0a00510248020000700d0618042c3c882c0c1c0c07100b00000d4420a044c40501580d10080b520460a0500420b0704c220f500440d814017402c01c00c82d1044000e4400744a0042e05200304171290701003840081e0055680051403603900380410400805400c1070200ea01c400200f2004400381020300107040109020740710320215010b400413201c1642d0048a42c080036900e00410400b0064500080d1078201009a100940700c0e660080c4840041800c0e4101650500c503400ea508642c0080c20028a102c0c0c089141f0311030407d840000644660518002c0100001c00501030b620a505082e405141e2050081c903012844c0e44580380032030701c05449040143c8082e41864408826001c4503081c05004104d030300003d618004401103034041e0403000429 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 384775980 1250 384774730 384774737
    0x918050a1b080102030702060403020f0c210a0b01060f17061003090602090a1202030f07060503070804030207260d1b080d020d0e15011505030114220b0901050a0f0501 73
    0x207001c0095007204a4028101e0507008641c2c90600031006980c2d05c004035030132001442010b03500400003001103203010500b44042c090b40b40e4612141c0c801c0303020544114126050303108268050000c109801c03d558001e00050b26907030380d003901001000301400c600000003060312811000340011754880d080702032000b0003580790000e0255080d04d01800640302d50492130794088103002000c40c1c03440c10510b198040c2442101160008088520110b4540803984140e90200b402400050411030165040a502c144a881a10350454440030620442c0502c1d6120325002606070000031480f040421000c401080207041105003001400c00505000d440e140000340311800218103a1107420440d0165a0340c03d09905090250340c040c07040003944c0e2017103080030100785040c0c103000045400305022081d00046403981e4040c9103038240428000d08010191034160068189007d008108000e42d10840115100c5400448c2d40302845041245600068211501c81c0358801004c01140103800100c8041341c0080c01d = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 384777230 1250 384775980 384776003
    0x90c03050f1b21070902040501080a06031113020909100303121e09050a050a03030b030d080408030a020a1e020706030b120a0605090a142d0d0e0604080102040b040918050a 75
    0x31403058400030b071603c4a095100304c0c4004118180c058001e44240c0303c081ea5600340ca5a6a820003c0035244940b00140045c0d205100c1584e640c28641ea440d0648600c09101511348891030010410704241100c0e0b14a07071003c00003091040592054001c80078011075907051081a44400c0d454014504080b640d4a5042d5620200d40411000b400320351203182d08901a501e03c00300034103000d0f01a0039034052851003805101350100b40345018860541c002d58000078070b03d00715a607074804100250721403030352041446001d0340460402d2448044500d06001113501510826182040103420350b84ca001c00070788138254200e4450743d0b218000403038a447c5a0840c001003110341b606181d10b42000c292281c060310a14810503160015100001c60000c0910140980040004c0c0c1d41d20b50880800040050b42150300040c545e000d105110f10641c00d90810010049840c0c40d944040f02e0382203074003903445280c0352180820b040040b41c4403407040d50000e10100200b207060728007550f070303441d201c0c1034400c0028903481595 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 384778480 1250 384777230 384777259
    0x3120c0306030f010f0c0e12030313140a030c120f12051e010b090108010603090201170730050c0c120a0e0a060503061e0f040e10090c03050f1b 63
    0x3082000c0d40c0c40c81000082100ca004090380b01c02800f03255035a02c01051f004181c4c08104e080c49407100c854054030303101031810b64481c1c1d0b8174903a80c5002008182e411101246032140703a00300611254822610030f440b40510602c0b01d141101c082c4c0d02d420010414000300941000307038290468078420f09524040c600040726034486c80040f48101840005104000180b030011825482c400000c1c50155401d89604c00305030b81e980070860681d00340513070003030019131101e0035044001c160802468100700f440c103040104848075102500a56201810706600d007184d24504000035241d1703c02d03580c025150303200c52071802c4041d11100d0707900d448104031241841030008804010350710542e041d0754902002003aa0705510746e143c00041064006a1b00940300d4400300c410880f00d00850030030201c03410301c041d08100c10003282204120040842103014a41400789500d031031110303070302ca10400396958070449403289000c3c218104985001e1158050f8401a80103100317491000d004541422140f06040350f02c6d0614240340d = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 384779730 1250 384778480 384778483
    0x210f04050103150f0b032e030305070c0b0f0d14070c02090403020a0206070b010602010b0d23011d06010e010603020c03180d02040e0d0201111e070c0b040f051203120c030603 76
    0x80344e00401da00880f140010030740c480b1183c011341c0290000c0d90600d9404034440300c1070001407800d14640e640e070f4545e034008100090007800a080c150307003d21080d8842d56075900207010710364440030004201100000300010070b18841c0c0301c2c220740c2c3c125452004a103490310385005010b803041040003a1140b900c00d400a01014402c101100340b0359800342402e5142c0f0300c1454001310a5800b030003114059401e0043c802101d0410300c0105c441d007604003661400b14441c908003000303240a41c45d1701c96565525507141c191803146d0030101c0290b400d5008020101985080c048400c42101031f000441058010001c0010b40c090020070b540c41151a0381d14a14040c0300071000035044454180000c2d001801d2420444c00008045000c1c00c7e914040c0d00240030b5820114403914039881204840d41051402c1c135038116084403000007a290b41d0388100e4010685603203440c0405066042640416041d0500300e900303110b142824a00f4210b0310b0494070040d0b04240740d821b41941100f03c000c20000c81600d0200c00505e035580c0 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 384780980 1250 384779730 384779771
    0x10f0515070501020703050331080c12070507050907020a0803150604090f063b2a030603100e15040305130305070305070803030915060d0b0702210f04050103 69
    0x18402d00841d562001e5150103000e5404c22a4151281d002200202c03559090603440c802000240c2d5145001da10116030701c001c3e19801480a210f150301c5802c0502c0e2189107005c1c01416031900900c002e104042c40e0408000d0500d500800440854000c154140c0000b2042c0d800d5a07040318428110701000d4a048021a00c103020700e920410740c850512002040c0100d456100360141c079103501000040c01500c41d212080d0481d440408030a20544c00b05194902c0d88901106802028040c6201032240030b04103105840b101c250300c1038107404000000c0c40307140e103800c20101d800055162414005200300b07100c0f594a0300100001724410b02c199a000808151007441115000e019040300c40341c180e500e03070170301c15940c0900b800304442c0e0b0300c621480882d0a2200100741e034490b112400042c91a80445280c0b8011030700b01030200da41044144034090700140c540505d1f180b086200da0b00a2014070750b00c030112030b94048000301d514080d240c2040340e116006a40011582580d0742800d0104040d6541d10b00c00b8001c00 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 384782230 1250 384780980 384780983
    0x40e0a110d09030815040b0d0605130c030503040807060903020609100e04020f04030b01140907320a1b08091e04020408030a0f03020405030604240608070801060e010f051507 76
    0x14035016402c4101034101d00301c0b901071620030101c1c0d03400b002554240070071111035030300c11688242000381c4040060b082d50040d96116081132a10520110340da62503005060082d0070443e15a00041800d0024000400022000f000b8030b1074107590700351441c0c001c1946c91180d00c2101d401034404410060516001b0012200d14101c058811581c68400c1300c111065a0400e0004481403141c1000008440301130f01d00b0000c25620050100a05858000c01070b0385091042c0d50301000c40b04075141150130414011030382d00b0210a00c21805503194007040380100302c101108404841c0800a190321404145003805940000000351182400007407580e5800c00810000452540c0c09800010041103003c00480540003080c1c0680700c0000c91480301c01d0940c16405203000301031301036000c000000c002c0703960240d801a4143d1f500001001c68135541070004203070340c2e1640007030307140d540b003c0030403c0340300400d01c80e2200604003103024142c00d50401030804070914041c450b191040c844402444408442041280c0c90503 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 384783480 1250 384782230 384782257
    0x4050f0607021e0c06030105040207030908060f060a05120d120204091806051008060a0902060d021209070503030a080c0a030204150e0f0603010e042a0f0504050c040e0a11 75
    0x740390215000b50365240700e5403450350301c2d40e5801105541e071000044140500704000c0c181d501307607802c14080c4802508050070076020001c000328000782d669814071405014480000f80409285400f506000c0101545e80c415401404405060090464041443c00b036a1032185403074042d80403a00f204034044e0040740c00081c0c4491800c86550006038408503a82441c44c4681010711450781c900c001041311500301c0c400d003001a0000d00028150003400da00c0701e441148000c00003800c1102c50f000c0c0c0300407a04400748032401901d44909100b00b0000c2000884010f103c00c0b4011880c040300d4200007000d41d10098480484408c0c041414090140a901500c1c0540345e0000f070b00000c100c1942004003c0d1004046c0c5d07030f0164580c051060402c0c14a5400c0702c0c1601c15200500344030780c556540c2e00f07180d80c5000d00d01a800340e0610701c2c8220210405c2e142000207103086090304003010305010401c41202d0300a01059607203e0204000c00c00c0d0301100c4440c41e03110082e8000050808019050910f46208103400c2d903144 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 384784730 1250 384783480 384783493
    0x837050a0e1614010201020c1005040f0605010e0a0f2f0706020f0a030e03070f2303210907050a1502030d181b0f050d0602070506090307051c0f0804050f 67
    0x110070700401c4042110b0408400610307000790f10b401039080f440b5040703044050780c000e0f43c08407402c8596074001c00d42280c820f2642c00c00c04241c13510781804135003081e0489040c1161500c18400c1030320450003030400e8a80f0f10b47c801c2201c001001c6001d40c981180c0381000c10f01e40705141002407100f0b942e2082e00c007502d8106000f555120850580c80c2e00c254000900307030001c01d141c0403884403e00d00000036604c0f81c6611080700f100c0040c10352200d449001603d800d9500380c200032070440f0000c54042c8050000d0318240181c00c010b1030a4081c20b105901307001001042c090f80f1003001009699a086a8907040fa00520306101c010300844808038114410075500e903100c0d44c18802e06560703013101c0e80c0c0d00c140728600802e26049408292420402107080d42e00c81c6420200d02040c05021500d00b54042c0c440403446400014034001c00c1d80d4482e0704103102220f003600150400304d60342c010b02000703104080c060200c4c282107001045031064080c0882c45039080c001b003040110790000d01000410040100480c0300c0b40121a034 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 384785980 1250 384784730 384784753
    0x30e031b01020d0203030601091406090a0305010b0a1406190c06050103031701060f0e040b010318080304020a0f03030c0609140f100e01020a0504050f030109120837050a0e 75
    0x8480305a401580d0062203080d20f41d04a1501c040280c078040c55050752003890152401d044200f030003104040b1164802c004114020042d1348111038200110300c1003001181c800d10003001c209145005500001600e0703501a08040150b0320307a0104c40342402c614817500c2c040340580303000300d0300109030b044010100da180500100605070014461880e40b07054050b214940d0307072546803c595405007561100089030703409160340b005240a400402181d80f0601d8001500310860300d540b80010784d009001c8d91082030010030b000550521900074000390100e40400d11107103146980003000c256961001814003070742e03803100c5810007407500b0100e841c91240808850b40303225800309954a070401800c428800515007000c0c100303d00303818025268281081c0e141d50703080a03d001300b48802c1d410700d400c61301e0b4075541e1000700c9000981e40007011200300320a0390f00e101040c03500540100c2c004892008401c02c984d80301800800812043d000040980c2c0c501c40e0104568030341d101d071213000c1c0c00c5089000b4042c1c06134120845 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 384787230 1250 384785980 384786013
    0xc0705130207050601090c080a0504050f03070b0906010909020a2904060302030906160e0d061b050714030324030a0c060302090306010509040b0612030d11040312081012030e03 77
    0x840b03a4001c00580300d60340d1742d03032241d642100c20b14010341010940c52000603103002841d600c40d983c0607019005941c01703140c0c50000d19085900804d412140003195005002e5107810070001d00f4050a060b440c104601c01c1070b0380008010307802ca480b07541e1361186008100c581004640308413220016540007855155070300c1c2d200140180d04111031101c0a0700c41d00300051004201c20030184108007403512040584c402038820300a441c0f090810a0301d80c00d40b00c4a0102c4003000b903010b00c10203000700e41e65080d2038805920b03240d000f880e82e40c00d4001c1030790b0052003031010017020795000c2004000c1c1c44910385160500c10020a0070030070300c6d810150003c0d0900c1e0340011442d8040d0010200c136001102030325000d0385c03202c04001e82000242d40251100d50840c00003a098100710600000c002906c0b02201e040c82501c1e106074068451103054a0500074010400304100300804480c00c0e4058207a081c810715038900030007644850342061042180700381240040c1c4007810b00079440114a14005000e03524404220005107 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 384788480 1250 384787230 384787237
    0x53f03090c04050c0f0a05120a0c0f090f06080a0b09010303050d1103010b07122706140307020a02011d090c04030b090d120c170f07020d030e120c07051302 68
    0x2000c4034080c1d4020300c0c0c19480d040c41191300c20116608941e04080030500704148680184510100b4800100003000c1198071080d4054402d4082840101c0c0840f40804c000f06058808580300090101c4010280540181100a031040c1d560b80d180c00b03580c69440c0d00b0040041d2850301506500301c840c540010003030550200080910001a290038445c1c6110001c114905101c24498442c401405000c0480022110041c0c084102081e01d0300c0c40e80b2140d49480b50740b000b00b40d05100301e00303120902030412000750032036041c0140083c200c65039410361402c114003944690f03000000034108401000920000c0c00d00d040b2180324804003034155203076840c2c01c400e240242c1d8000d00050341c0340000304001500041d00090324544596080eaa401000d050040d1540c0260070f1070110081440499410121802c000104681c81100d510b41401260b090a10019081000f0f01c14280101800d00d00c4a0740c0c41d45000499050304250010203d42d120030318542d0b64100180764111035400704604805510108080d00034 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 384789730 1250 384788480 384788491
    0x21309110102060603070b0d020a0908120c280308060a1703071e15020904021902011e050603070e0a0f020301031b090c0e04020a0c14030406020106080a053f03 70
    0x22501ca64644104040c0c1d103400e517220b10044581f0130480c08100070711503005000c22002c1c6041c41055152030b103a402d4107022510400b500c03103c10120b81040085020010f034912070000454080000325000b544240e10600c031900a418000181c01080b096210750f0455402410040d21820103002e000003001c1c0caa610001040d1680e030820994070402805803402c2200059003c08124808801e00c0002400b940025481e1a4025801e001c0c110f1401082d101240001195900015600030242c05400119408003000c04daa03618101c1001225100040d20500b5070b03024140880c019540c1d5640c0d500501081c01481c951540088000400c00c000d850081c0d404400c4031480c4151103480b4001881100c0c48407841a0004040c0840703200d080c2003643c014510303410703d854545001c41c1241c0781e4202200400c406000b541e070001030100080340c0d0a200c0e1002078103a100c00b90090b0300840e00d441e0781c0c4101d4541540c12085c0c2640d001981402c548003810921a03500d47d1072114201c0e40c9ca80b0469a8008a41 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 384790980 1250 384789730 384789733
    0xb04030c0b090c2713050a05241602060c0702030102160b040c0801020a0c030c020d0606031b0506090d08091c0c0306050c0a090b030a020d02040f0305012304020409021309110102 78
    0x29200500d4002a10300c0e0f403181040c60040165176800c1100403040452000c241d400780120000c0c04082501880841c103940755080c814101440500e6914071000401820400c2c0c1c07801c42c0c9101c8810950100e1625000104801d8854a440300b5000003030080c49142030144514400085543c02c000450800c5441b80d4001c48a0307141150380c610146080c0e1180c40c030040d0000301d0643d10030300041c0c001c1072104c010600103883c0c009034288681d80c1c1d504560b025002519094003000310700c82142d070004403140c00303800c0950301942000b040c48045180625004c40050030f803007000c02c1c18241602c60110822000c4405201c0880400c01800c003159031210700d002c03d0b02c049003042c0000d402d924100381103480030401a80d6440380b0324a441001011030304050849040c182d001c1001d40c13604501c5001810140000c2500f0031902465441c1031401c5400ba01503401c40d148000d18900c84019003000604c1e030094050700c02060b055414800240c001030640340442c400e0745440d10030020b00c4503107606008030b85000e80 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 384792230 1250 384790980 384790999
    0xb0708151905180403090501051b010f0e0c0109050307052803060c03140402131a0d15060602070608040f020117090105060f0a0b0a03020c0c03031b010f050609040b04030c0b090c 78
    0x4243d655045812503028000c204c030301908108035482480106411080c0340100301c2d503580041a241e0940b0042a41c01507880d8607500ca45a05102c00d1000c07244c07409090800c0c07040c681c905404242c40390018401e0318810000340705c400b607100d178414500c04083c4200440d4080c1c000e40784d191000c005d0445814080000307281c0402e60880d03d0084020601840d0003c0c205001d400c40010307000301804020034a0340718001c1c0d03684e040255440e108480034180d40309145019200803400408400c0300c0c21544034508640c052a8200280c903001030300c607500030ba0040e9070031001c5409400140c40280058400c0e081d00b0441108000100c1419804a03000d2401180e5508004e1841010081c101c03034940101d0460310b02c00c1000c1e490707160007540140030400041c4181c80e201100e000001c0d04680040403540880300b54808016069442803066800a40008500300b002d401e003180460004180244001c0c1004d0303901001c2014540107003046404990b0040303a00d0194540503210036210201c401e0210b00661020 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 384793480 1250 384792230 384792259
    0x501110f0a0b0f010f0308070803040203010f0e03040512030a0c020d1407140f040b0306060d020d170a08011a04030201030e0129030708010905031206060714030909060d0b0708151905 80
    0x20709405003101e407c5080c0c68146080c640b144603250380043c0c401c0740c5c55940e0b84200b2420442a0155014402d4207002445d101c61619050040100701d085840e02240c1040100c00c240b1034005c4109114140c050b500810b402d000d07480c2480d1604c85090305415540318103040040c0c0c1900381108580814001c0e00d14a4072481c0a40071b00c825100729109065258119000141e50750034080c5c2c90140841c0001d11201140145898060900c1170382d900b0701c10812000160003001030b4104149600401c1050a0300c0c0075000888111801401603010083c100741d10390741031840170202504031160055030381e11600f5101ea100035114000c80610344c0c00c68001d000c0c2010002e0303130701c506102d05014181c01c400a14a040d85450200121160082c1120342c00b56060160300e010500740d2001040c0180380d00029a03036079505108100da220ba0003485240f1403d000c2c20801d0004812075101030300500356003440f844645441c01012102d02c0c10035420364004a80402030000401c10100d444101e075400c1e13840440812a0 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 384794730 1250 384793480 384793499
    0x31e0a141609181506050d11010206130f120905120f060c040501050315120a030f08010e040510110f0d060e010e040807030c02180a050603070b040f0501110f0a0b0f01 73
    0x9151010f4041e030418000382d408219243c400303c1600080b072a0000d0034503160b20010f807291100b03c81c00d40d411010521203d20700d5804029480e085007446140108444559071801c08820103080c00078500301d03040000b2400316025006c000302602e8014095082d200c40c440c0055501c2d00c4080781006507205540c080b0b07050180520468003610700680d1414655507400c0101c01c000c00c01410580c2c0c102d00c0b10001d41010b04000d020355560548666500a040f50440c0b1b0000c00380b50042c0c105d401c5074107864040c40002500044e80c1160701002d1000411b0707001c85030b4404041030140302120355100320001150801c00c1041c0e03200c0015542204035401030340c0d807078000f0f51240880c01c640040c12420204900f0300231a00800000e014603200030101d4000c3c54290124000f0f010081c0c40e80c8034803607102d5007441100e107418003203500079100c04840681003a142160602c420556841154184040f0b02c98620b40d025050004100d5030590343d00b2030300103d01e1458501c4000070121030b1004003003950000416141403 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 384795980 1250 384794730 384794741
    0x30204050a0b0903070e07080f16051801020718020a02010e4606020304030f180524180907030912080a090b1603140402031e0a141609 59
    0x1020300804212801d29505544a601c10003500d031341440790180010322000d0100380c4510130801c0c0c1e42c0d07200b40b9007844100824114800b80886100e803d5400d44500942c0e0700500b84c414a5510240c8110103021440050342001010780002c07008501982808800b41441d030000c08a0301c007240d00800640c2840406203403544011456000c0c03000801c240c1c010022646849400305144c202601c6447c1440529210b20f01140729000300c4945402104000a040e009018826420f02509107000085101440c01c00d0041c0e180c002c00c1d01c10310101c0303650500703401c240620743c0d52101c0f100e030707042c1d682d12200d50f10305101041031070401e1042c100c600000c0c050500c03034011852241e030311032829240c00990f203c090320701c5140140f502038401e81d22200e500208400f249900d016003c462404590415010b5000b42651000042640c485078000113120044e02c000a40005044207d811403041c2d01c04800c5a5041c40c08094004c2c0411811911040342d510010030018005414a550f00c109a503444001d81d00b42d54 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 384797230 1250 384795980 384795989
    0x1b090c0f0206010f30030309032705150903030d09120207030314031518071202090f130b091e06010903051b1c08090a0e010803180a0e01170d030204 65
    0x13030001c502000080310038140d110390355030b10081c07221111303202c003001109402140000f17a000949440c4a2814590001105a091424a0b04140c0d120500c0c0c0000c60600d00c3c0c500c940ca0003203441d4120701c0a41d0038003506a842400f03004095960b6107801844840192043c00400d442409083c4d8050b420300380001101d10490380d068403000b0391b01d401003840c5030064000502c0900803a03001040240303d079440380e40380300742200c160b450341c0c01d2800d00311070060008800d01c052000061042005401a070340e005403502c01c140003129100c00140b07240060320003130480c143e040c6410201030b9080c85140002805400b0040700c40300301d10509941d500c03004440b5409544000381031900201070b41c028103a07896103107410401003d00382c2652240d030094000056801d10700143c41d0842c001c25005014542000928000c1181c050841c0c0300754188040a501c0c1c0c072070100d200c031000140d451040040d441b140c21003401002095040c20266135508442c180040c42c00500724100e0090a4950320b40a01030310944c0c0944 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 384798480 1250 384797230 384797249
    0x10e0403032a02010c02070b0f070f051e0307030f03020f0a0c030c0203061807151b17130501020d0c050706110715030b03161a03041b090c0f020601 65
    0x544840e20305a00400300d01d09800700c1031049460581055441500b00408650141e0001554060031040207003000c1f90764011100f01c250400021658200d108155050300e50417011103540c0c1e01c003a20b41f2525040303e8400301201c01b090403808a1107000048090701a09000e9220652900b60b0007908400300d200c5d1040c2004650f10610031414040e100c2c4079615901d078440e0804401005031034000074a0613000f00c500c82003100100ca2483e04d520428820300006000341c0404514101410002810709042d600003410414180103160040c050030800030030707a150f0135556607651100d0304188608102c1075070103110f003d0312400b0719802100384521080c5107010341001c0980f040c2801c200d01140c00590280b10401c00e4031481002044001c4080c4038522132402580300003a41004c1d201c10f0600b08040d02d04c2480c040450314508014034040d030b05100902502d02c0401700d03642c0c0d555150002c41c5000e10681010703858000c0c0004551104035a01c1003606c120180c03112080c11140e007030100d036510000d02907100903 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 384799730 1250 384798480 384798509
    0x20a1202012a2708010c0c020d060209031204084b0a060212090c0a0e0a0903110105100302040e0a1511090d050c0907031815150902040306110301 64
    0x2c480e031111045040c00592401c0b400c1103110031200080c80008103090110850a00401c011803a0248070b103405c05113190402441c00c0340141c00141441d8410003002d4111600080c0c245181e5905200c40c1d00440c50000207584c80300c3e160640d090743c410f40010400c4920014001410088070940d03002c5107010f4103490134070f46500101140040c0c0098041c250039262180c0f60703514002680d1400030b84555012603001c520f452400b100b01c40e10306038210344054061207040005001e18042030010300d5000c086100c0118200c902450225020040c152110006501c0d00301402005d040c000140300c00c032070088500340700101000e40032589414500c0e00040c00034800c0380482609030010b03040080c80d00990700d0300d14240076404000c10030100004bd800c490380d4019205070a21071914000081e04034503103140412600744407a20380700244038036020190002809440812101e281c0d038006101199525016410459540300301001a4000b408110ba12a09103040d88040c020940156412181018000e001 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 384800980 1250 384799730 384799781
    0x5150a03090501020f04030b04020f10080a050403020c180603010525031107020418061401140909070906081b15071403070204090f02040b010903080901120f0c020a120201 75
    0x41c05485800c55003950207114280c0180a00400b420055010b40080c80716440c0070700c1040b4540159004403031140900c402d0203040c8030740c08000142e210004620001c2c850f00c6a080503460000310b001b0301540201c650041403c04c2031800c02103401403100740d000340310703e48903810b951640c61840c100380d540a9558a071880300c0c0700d02c00c0d081006143e9141d0760161414680350081019100182031a0512141101c00c650400840b84140164620b01d120382c10229410600c101400c00501c0c0006031003194003201141014000740b00401c000d14200c2d030300701b100594440c422505d038122801c600100801c4501a8034150601017018a440041c0c001d4462810445607202d090030f10321445102041c1c4800e0003042c005032150300c15407041501030300c1542d080803010320411090300e01c00c142d414108850030700308000068103030094030507000e400d0070680c4c80980000300e181c000345058040f8160190403c002c2d80c0a0b1500440d4401c07410307001d00206840d040e440ca401340e090315424041845d640c02c02c80e04016 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 384802230 1250 384800980 384800987
    0x180904021509130e071d13111f020d17010f05040908070503120406050603010b090c0a030209031c14030106050d0914060703060e01050f01021213030b070302070c05150a 74
    0x480742c0401000540e0030941c1c506100201c940f035a410042540c005c010500000c064031061014484132030030024200d1414801484402086410007803180282100c0786003180d40302c2038070702e000754080e96030a111400340c00002584c0c0c0340103091801c045840c8980007240729101c440014140d4054940c42c00c2150316150600000741106101504c81c24424490381c000100140000c2420082c24000c103086d030300f410708210089900c0900f51511130b07031402c0f4924026440d802c01d40c40e0b02112500140d500c54070701440c180d0107403046201c429810b009601101521243c4401c07080d42100240d90740480c0c14454000c141b071540300a02030000400e109004061041c1c41c1500a42c05542c41100703e101c0ca200301009003440e0031000c1d0b409001103a1158400e01c030300141c0e0b000c01401401c0032038041102c00b843c40c002030340f0382c000c1c030807191075045001440500801c03032030340a00002c6030706c8985c1e1100f602e0240b4005001390010380741180c29000c11140001c003440c003c0c00e07454980b06504501031a041c283d11095 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 384803480 1250 384802230 384802237
    0xf01090e1615140705010c020c0f030c0112060504020d052202090c070602120108030d0e06150904170403081917010e1510091d040b0f0c0409020307051809040215 71
    0x410031903c40003240005081002400003144a00000708a01c40d100c0360181c200803020029a005001c0d04038240310541d030004450a040800703080008011100748000009040d0039009290000d00004002c030b0101c040d68045485000d81080345020b192854004025603601b00102a40c0f01041c14041803140c00c2110013060264454280149080020181a00e0842c0244e001001540000c1000c110500c6507004032020020b4a9010301004d20346503c1d0810711254055116003d072203640001820030000009030101e0502010415803182d40d82c1c83c01b0307602c0d5070001101c0c11071001a22641184d6070300901c0c1f1080c4aa9100381000540c0e800c000026400100060880481207071080940e00340d602c1d06003220500c100e240d501c2034141400c1c006c000142e40341907455500400b07944003c010101d4000c42046d80c2110140d540c84da499207460304403540c50f000e29081517210510020501c480103400800800c081d12031159901c40d40c01c5601c0400045074412180a03400c4154058426505690312008 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 384804730 1250 384803480 384803519
    0x612051e270607030501150212270303130320090403030b010e04060303021e03040b04030f0c03080406090f0e0417031e0a0507030516090e1e0f01090e16 67
    0x101c40c11070040e03801403468040259000307000709540700010303c01502940f2042801b009a8001401a907400c40007041581c0306903000b07184001d0b4001da4061002d80c50103d9000404002000c0304c1d02d074210030f851020641040c1c402242d00040f41e400310084100180c01c41140704100501c450b4031076032141c0b01540504400d086860420884820341155030340d440c4503240c06140a42d00800705160722a4030340d0120ba420521282041d407003403004001245680d400c403400e580c0d0184c0102c0081d0b00503e8aa010740c5015000202000d00106e00840d03401d6100c440c8008450706904a0103a4513a03e4514801640c003d640190010320030a040e40c030203840c0e4800450300000c4900c10668100b8a0018808880400303841c40f141044c2c40781c0c11710581d00d6250080b550041001c03088181428800200a080710f68684030b4100f003c1410130001d0047c000e40004010032040c1a050040185044e00410708501e1003405440e070402d1402800c410302003000036072000400008002e100303089090480141c182c2904221 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 384805980 1250 384804730 384804781
    0x1d070c08070203010e0a05060c0717090a0b030a0f150e130c0f170105010e0730020708070b010608130803130f05030703030c141206030f070612051e 65
    0x7003040142c070300340b28045100240c07001800e01d51100b03141030350400030050a41c0401100134031485010448a01e5000c078940d000d2103030345540380130123404104038500f0781d406032050b40400700802a00300c0c0142c00480700d46c038581108018034000f0302c0c6d8500d01d10100d406005070aa00007030010b4001d1203081c600c007010901a203c0c0d113454a5446040d0012084603400c64a0420002c80601002d00d03030900505024041d4146400700034079042c180148502414000076004460007c24601c0b4040da50001245a2480c0039040d50390b0038842c100000203a100c60011070b0411012800020b0301d9104e103184a0007a4007601840d8000129034035440e525410181204c044c1e920b50221040029106400303010740e0714443c502a5480349175508010b4100c8100070404400d00c04a84044401030543c0002c03600303031115541441c002503c8010100303141c1061601036a449200b048000700790180c208804280b0032921201c11302c02603403281002c85498801089481003950147e0220b0031480c03240e20103041c0900351701c0 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 384807230 1250 384805980 384805987
    0xc06020a1b06120b0f0402030a0606030506041103161e0c020907110714060c01060303080f0703050403020d0804060e25060905060711150d1a03150a2003090c0a1d070c08 74
    0x1b60486e40b00780d80400505035203100c10480203070103001e496484041118100254215034804500c184002014501c9050142034258002402900065000303400c50049642a00390500003070030100910a00307a110300302d43d0b00050310b00c5105402c03414a052220014140803840c00746120742075180b00c6426035020030305006005580c5400d00c101c100442c040ea0f5105801c5c140000c83c0900d0b6500582500101410301d8104408260006000701c159402d51409807203030380e29821300e18002d011420241c5001d000c2c2000020380d940142c2c9101d0003886030310411070304540d5503000555080002c4d201c0c45401100910842000c200c7c0725003a540042405403a03110721001889407000c3e82d07400201009061a0b44040480200c4561000920319203002e40082c80080705400f11403541c00c00083c001c00c0300c2e039250a0361b282560b110003405640e030002c4a0003240c90303007041032040d07440364035002515000710002100000e035024200b80310300500f2121060792620362907901d1f0456110b403544c2c00a8458a0007003 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 384808480 1250 384807230 384807259
    0x3120215130210020d0e150f070b060102010e0118080c030f03040606031209050d0605070203210402030114070507080f09063108030a030b030a0c06020a1b06120b 71
    0x6280c816144507501e41115440d910400c00010a8480740c00110760205000d0807010b5002080101d002e81c00700d0348803080119280c447d007414801c04134480c800400224048082041c0c80c0d11290040100340c000303008500c4c44080035400c035041c0004081c5030070720260651001c1000600108205103103442030701c1c6410b0a84403030101d031b5407081d0380882d00325030303a0b407070070400c0c0951a2820b0540070300610344410001e00e800000f03840c02c3d821403c0588455620004149064000c2044584420710706942212801c1c40b07020080400c03000315026030080d401d0002c0c3c90380300616140454030030f6440383c4070541000301c50303100c10200e500b1a0006840304402049500e180d0f80d20000544001a00c00100ca0044600b2441642c41c52008040300400318019003801e00101c0340c0402600c900409a1400144001c0c3d5007001901d0841488030250030650020344c0490345030740c0400c4140c2c1080c06400f80296119411550300031031440c80c85002c2c0081c0ca5090034000c1b080701900600145c1c14024011841420b00 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 384809730 1250 384808480 384808513
    0x1d030403020f240703031a10030f0f0c0c05060108030403170703140d05040311120a030e0109021c030f111c120e01021801020703020306060105160b090109021513031202 74
    0x1440041103c00002080040405515015814004408408000180d4510004203141c001072041000c28185c48103029410503110303070f1007004100c0c1480030600110700d802d040a0101c00c54511306845038011200040784003200081210101c0390301608010030b12800070001080d50300400c03401c030208142c0a828100004002c0c000d0000a440d030080020315052524018040001c48507140302144c000031081402401500d060318038070301540c10045006060503642078010224040000c1d485840704080710341340021003103a4541030f4460384a2514044841704103076030003644e1103d103c510340c2c419400e40345000c00405030903005101504100112030150020f031300588007958600441a0360108020032548009103280d035a0030b03428000b4051035402c0d9004680c0b038403c020301203814080300288510000c0714401c3c1000c0d0450300700e00300585d10305102030224041d059864007688101c0e501d4103019004042c400854500d020940315152005181d662408060000380c0d0100302580240c40404918400 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 384810980 1250 384809730 384809779
    0x80d1104082e1503060213090608070509100e0604020f0f0324010c050a060c09081b0f0402090607030c060222050909030a08010b030a110406030c031d030403020f 71
    0x10948111900818680b50507944003101c5040061010f007001c020984420400c504041542d41040c80940e070792001c2c448217107002c8070788d901000f041498103000082141c0046102001e4401c200c4800c0140d88800c2200034401c034580c0607040319030b004400801c130740b80752a900a08882e030f000c840d0b8a08200020700e00080503002112000382c40c06040e074880a010380c0e810912031054000742059130089609894150355520040f1004200c01d542d5114074031211701802010005000100c1100c442d26240d200100c038020800c061103004444c1b42185010501d00760003070702c41520010b0616030520360107446c00c60b043c14a2100c261803955082050f030580c0340001d0300c0d0b6095445d4412101074041e1402062103041c8200034a40d00f1700303070000e11244002ca640a50b0181c111101028820707180e1f26000421001051034105200b500c0400150004a25030190091011b44080751010080c02801c5000c19240c9080c8900c52551908200014001494070003101d00100c0c1000d040705c030f0403420207200c01c0482c22 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 384812230 1250 384810980 384811003
    0x10207210b0708070c1b03080304030903110301020702103b0102060a2f09030303040b0106020d0e010906051c090c0314030a090302120a050d18050d080d110408 70
    0x28166229003051142810125400540a24003081c1c82e10b080c1c2c6000700f001c0741085005007540c0f13203c1d001400350500c60103e5006160014200c40d40c900709440d0242c9000b14611048030318001301c00a84240d0b1a043c400d4402c0700382c000c0c043c181480c2601e401100c0801419040c3c20801000a203010000d61200d84041500d0f103050300e03010001c840c03060001e840d0803030043c03007070403442d08003260705c10b0707c0140c0851041c1003400856400600c40080c1c1d16204c0900401d402c150b007501c0080208410300c600704407158100c501d6034003030345d00c802001d00c400c607200c03c100143c460100f03400344000c00c490741c818401046480b41c80d1020070a5440c48001c650142d40d0a4842900c0342582c0380b000780140245400b442418443d40002585030181980001d40364000a1201a00c40d499080101241460500504218650140503250481c6031518040c01002071007082458505514402003000e0800000071503407241c0200d20366042c015100d020f00050300c1e0304100e40e03000c888144000200102d003004080c0d00d0381d = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 384813480 1250 384812230 384812279
    0xa110c060426061609050321090a091503111008010b1b01060803090415120b1509041a0a020403150c05040e1603050f0f0a0c030b030d050319050f15010207 68
    0x18016403070082038010b0b190052482074111907494403005020a11238000c0048062005455003101c4000441110040e40045000d606000301400012180c91010341a07901c43d440708602e840d0201c0600405421000004020a000703100500171244004013034003081841c10b001c01c545184c0341e080a401e40b1142d902281e803d50011a050020389050b001c0d81044075882c03400c4015040c03030a0f030340d0842121441800b40400401c4404500c9081007030241000485e0060203003040741c107282c03500c020b030080700d00d00c05007940e0b850401040074003115000b02e5041302e0700072004c117640b4170300b103000f040040a06020315000c2c4070003003000140500d01d5008451103200211414102c0e0301841754050700795800100001000c0c0c03c002c081001409803071441e036801001d62280090100c0c0d81000c103600800703d01c0301c03080e418420801c14205641d88940210701c00e80803d401c1c030b480b900c0300708414015100199050781d0b118021800040c0008501da0108070000014812180c02a41e5049400d194505818109422 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 384814730 1250 384813480 384813511
    0x20106090513030207061b1707020102010c140d0b060d05070809010b031906021b0f030c190309030b0c040e07030605281e05150a110c06042606 63
    0xc00118880e25600c0502001031a582103440e40e002500d8900794000c99041c400003100000042c0030002144180316480300c4ea51292007005506680c0300e401c940c000302d0040d0700300070000300a03a20440301e80d4186600b41001d60704001110260001a10102000680043d410b1055280782059401154000c40154841c02418141409611709640d04494454040d034030a4540c0c00b00084140100c20f9481c7e044003005803600d124420052200d480a00b00e00e2061080d07401030040c80768048001d18600a40c8000c44409148100c42c1700342c0b84d08148009404a40d89100800109203030450f42079115a909221a240984a00030010009025200d0400007580c881d028406801c5c4a4004103c2c0c03c860944800b80103241c1c1c0401b5040021401005200c0b90541c6604045e0b085518820002d000002c01000c00811164401240f54010001800000d41e481146009481c00880c6040315100b0240c80585042d00b440f1990402c01c00342ca0903160030740002010b440b0b142d0024000e4500076060042100706 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 384815980 1250 384814730 384814739
    0x212070c140a241e020c19080a03020c010902030109031d18011505160b012d0b09030c04020f18060309070b1305041d0601060e0109140103090503040b0304020405011d040f02030c060406020106 84
    0x34180c0841500340c07007507c01501e9038000c00d910100f07071175000d40285405640c03000025402c82c00341c091100000d415601300f0002c901099000101001c1c09619084000740a14080040103100080410800b0460500381b0050041d401440700c1d28a00b508182450381c07409220028815a01d01c181800359800988880107200c54045250310800456050b0b60a035041500704008030902c120501c28101c0c0000000b03848402500c05000410b500100104115221025002c480002e40e1060b10078418404903100e5032420340ca4140241e900540600b00140f181500b042015219540320024200144400351030010b659074590007034203001c2484501030440100f4900d0f00914080301a0419404e004164001e41896644202c03032400f01e4012500300d58102e00c6c0003005030001c040c00900982107000018000c1801048800214056442690100034581e40c400b1008110fa1001e21251000f000860200e400b05c0d011032944203503680000d0640b02010103090005030b0030703402980f045001d82d464607401c01 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 384817230 1250 384815980 384815983
    0x609080414100c02031510050a0305010b0f030304080a0f08070c090b0111010b0f010507060e030301240305040209041410240f0b1c0212070c140a241e020c 68
    0x2c0c4407039052210034481550300290322440c0401100c0c040340f0007000003035816444210707030b0001454040c02ca404071130340300d00b04103000e0101041003038082d5400350784050441c240041100c0c02c56101d6030180c081244169102c0b07030206104074060b80c2d0040709010010119920f52403001c0244514500051003468160004d446030110020064503a45410003218141e01e0701c064440c000e081c2440c1441d981d9071039181410080540c000d06082511000c00040b4400710740000c041c0b9046031a02d42048031510301c2d042201505d00c2210005e4103c08800c010800007440c40300e0319503940210100b507404203c0003a9055048a00240a6504424800701c20311440501901200c01030400c0b0b40350011a2428203440f1002846018640402800904242840c086065050391580e0540c1041c20358070717013000c40d0000c000c007070851019200000700c0c10041010304400250009641e50017040c40030f414000100c20348000100300b1882c44003a445401c1103a6205075110a121005e201070700058440c011070038004d = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 384818480 1250 384817230 384817249
    0x4030302010b040615030915020c0607021e030d0c110109110f1503011a0d05160906020d081602011e02040e060d0302060a090f12120b041e090609080414 67
    0x780180d01d090300500017030b03040c40b01025841035a8100484d04120925083d20030609010071011130700e00c0482c2103044000003043c4240a0340c2e441e03089511410340d01c010349180502031582e11200354410480306403079008a41068803421898108030091228410800c1e0035241060412158183c0c1c0360204481071411015284030f89106440c90414221030050841e401d100c10302034090020051000b014451405c50304450886007048000d110358209202812649620661114080340d1151004034201c3d100258100c182c1000c0d640b5a0400e441d540d0030160b43d01d0340014614119522032044150b207402d07003484c8c4a05082c44490050380e680c64041c0301d5011040141c406441400725862110200340d0020f03505030000800c80300050040180c1c0b8201c40b66514090700108421503641c454580c55030402000342c40f00c40c0181d024800c04040720204000c4804c074041051034509000c00c0b000307000d402039110b11442440b031a00010340d1041a2100d1095800581c4091000f0000c900f28070305c0d80c140951781 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 384819730 1250 384818480 384818501
    0x406030b15031e0a18021504080a06020c010b0111150a1d0f07090e0a080c0c0d060902030106050108090a03030203040501020f0318070608250201110a0512150d1e0206040b0403030201 80
    0x41004800c1411a0390710705817070400c06071240404c40488144403800c032040310010105d01d012161804001c0c50006c0103504242408034080d40307040387d00b00032035000b5038214602e0001c1a01402c01d2019081110010100142103d580d855442c41140c0c4812550740c41a11291101c1000301240350304030314828a080c1080d0010454603060240c00d030500e440000714040c080d98481c0102d0f807114144d8524514040241c80e0581d8064401e007058820b20400b503100c05450f60098000f072217a03948070001950580000e03181d441c003941c40180040c020074460350280d6003141c401e00c00549040010004108590000d41702003040403400303100d416a505040043c01c00800c400d0070a0b10141c1342c081884c0e500030340000b0f6050b546210140404656034404e50091000d94048140c4903103070510494002d21940040c90ba0740d40085c1494085801c000c800130550b58131000c002c040c0300408007145d840f03012a0703940b01003819100c40b490243c040107075a50b40241c006055140400c0c1d80701e07451410000e0940c6c0e5003940 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 384820980 1250 384819730 384819751
    0x2411030a1e0c170c070602030a1410240207120803070801080606030c0402070303020d050703050108070509060f010c03020a0b04080a0e040903020a0201050f090904050105040b010501140406030b15031e 88
    0xc2d20260702c0d030088100e40e4071405029552207141d03a803ca900341c5902c65000c008004901c00002c010b03004025601400130030685181c1d0102c2591443c2074450651464007a01d00140c006600101024103403074403c00421500b03106445015a4951280441c84110f400495420b43d002c803c109085038000c43d00c5004100f030030f0061580b42801c0d40407907210b0b80da1000c00f6015a400240100605029030100d0701b08507a1140100041d190840004000341070a0161260f2405800000101894038500380313400341e60010030300004455698010740c1e5440b84814101c003036015000c2210041584280e00c544110b0050040640c0c0d00e0101760002c01186880310100d215514050b146401b0030340c00100410401da0a0030299615101c16140c090309004410701c850303010020800700420008190491130042d4400c40003d0510b90f00c9038019a8801d0594803800800f810600041009511a03081600c4841d406002c0c005050984a1744000c80d0340112220805d402403080980d0558604014941d4016030180 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 384822230 1250 384820980 384820991
    0x304030309030f06020c1506010e10120504061d0a02041b0804061d1e0115030206120c07020d0503220b0f031f0f030308132411030a1e 59
    0xa4014000c0034182c000540030314400030080d400c105060341104c40140201c011145202208a010082a4000c907903a0340041e5130319480c60386a0810310241e880d904c019132607040080c000c540d400001041c00078402e840d16521000c841000b0107030340b882c9112000c0c000c0d000d001140a20700501058500c444030403e590780034012003041076603109803000d40099022001003421081074582c03c58000c000c0c134028800d4094401114032083c07a4009000700300054400921003281280f95458414101c3e201c069000603040150030301f060016404039601c00c0304030311010309004881d000710f035074114060821110396000180c03403076030f1101f884042c005a0104000841506060800301420b500503005030314864940803000c1a911410b200d039290026031401c00e040c614558540d402c040b109940e01c0b040d008140d4900108400c041c40c441e0040e8101c4e0820516404a00b200040c0b01c00c00c07000022407104256500c90404141d8201e000441c020007181c44e01059481e2110010071401e50080c142d440c50754a0712 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 384823480 1250 384822230 384822233
    0xe0601050306060c0705093c061002120d0603110a031502070c08060c04030c090b061905070c090606030606030509060601081008060a0f0506031f0b0a09050c03070809030403 76
    0x1141d61224041d01d03e43e441320090501c0d41d2078410b0a40195921610520401440100c002c00e80031410940610095010042862015110101c0914070b01c96403111000035200741000200c204460307980748103e821010300348a4044803508030300c0100711500d80782e140070014002d072040440640034040391200102841c55640ba01400062242c2510070394000c40c500042c88500c48621008100e4081a254031349880055200907510902040702c0c52420b10901107600e0880d07101d01150524064062850941240b4140c064401c0e44040b202c2005020803514000812a41c042c10044c80001404241281490406000d54441d1707000003080610304400c00c0311340c10b00060b145402c0a020308040c0c545440d4000e0103d03201d0703299042403078644540018400b030411a51320501520400d08000c02080c1c642c04205a02d404002501e0103002030a0449613094007002e50150b05405802040300b51915500c41c4e440040c1c400807074100051210220400402c641c0050101d81d0068061010354901402d6 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 384824730 1250 384823480 384823487
    0xd0920010e0418020909010506030127080d06051f0807020a2f060f071a0c2704090f06060b0c0706030507030f1b020f0105070e01050c01020906070803010e010e0601 72
    0x481c070324503114548900d4192004a070315154410165009442c0c3c65440c9000c07070000340030307120960702c45001390300c3d0885008a01c0081520fa4003913000803444c80e101d184e8552a107044642007a0001c100ca59a030303c00005150f07450681c0c09000c2c4031003411000c1c036844400300290040354010800301c150340058500384002030111075100e00c3c61026480d04032242405000303800001030080c02082d04103500081c02650740041c0701c06081c22603c04d03110904000c0500c020203205a10585000350124410321401042c0c602c0c4403803001160a884035a0028407008000103011790700c541d40e095851034031420407030003400000e0103074502a200c49a00da600e4444e0403907005559061510400c03080580d030704d011410031071003600010818190040d046c0080c503680080d10804404e4603041c64094819403113201e220403010701030b01e0b108610303684644000040140041d01e19500c01c100b01841c0c0d5508100b26101952800c0c0503112060243e00c015840f50b04120702c082d1340c1c13007068003d91111a034190821500d1b0f80e0 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 384825980 1250 384824730 384824747
    0x6030e012702040c0e0d081803061e010b0702010c032003160309120215030a09020d0602030601030e011506030b0a0f0e01080609030c060705090d0605010602100b0402120403080c0f0d092001 83
    0x144101f4495588410b566940c400010404500e07908d40154001d000c4107070740301039020f04201c000d1076180080707903a030308082e8425204148009022420608840c0c01107030040041030300311000c1944000347c009001507002e09640c003511075a002103005982c00014903500c0689880034221003c0006c20f00c1043e600003401d98611381c2c02001e0090700020005409203a95000800714903400f4248442580d0314bca03211000e03400440d42d60340002d1070b08071000018101400b9a40c0d00e94000382610440c0c43c14480d0450241c00f03030051040d0881c07145040020a950450741c01d030000d000442d025600355050030501400d00c100507103023a0543d0310030301000c186450b02007079050f0892206c1c1469541c401241002c55161288080b0147c4031301c3c900f4000003002d5401084101b84000a007070304101c1e0030f00c0c0350700f004200c0c040c04452900402e148400074000030f01824500760009040c080340741c00c00c201d0151049081e407019a8408505441d0f202c01c0c000c000c0c03805a440080a004104800151030200c0001c19000 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 384827230 1250 384825980 384825983
    0x30712110306040903110604111f0915050f1b16030506010e070e130609050106050c070909050f060406060602070609060f0309080405030f1e01021306030e012702040c0e0d 75
    0x555a0300c1c404c4c105800b54003024180058175059034854034060810411481c106100303140640e2414032160020340a940340c2035407103c901c1d1a00004281030441c0e281d504014201d034442404010001c210207095800040c2510106c2034110300d004034145003000e0b040c0500000c0c0c80700d0500c0e5000083c000110007007031617815643c228075407400503550043d003255580c1c0f07070414054220707044029a403500b10300c58018500395075204005101030f136032764002200c0ca40310701e01a0142e250090178051280100c00e4000c00c01d190700030780c101c4540000c98442c090400c40c2c1654201c4506544610801017140c0510107170703000b40400c0c100180c20b81d107404d2000d0507415030f1000765010565035000841c1008581d4055601910002d0121400c5108854800f6910b480e94800a012100d070400d069400340014000c880585007591041d501c1540f60117415000b0303042c0c5404481e1103540303409124041142000d100c03c0700d2010b44402e5805045a0300602c8100c1d10700601100070010440502803c64076507080340180103 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 384828480 1250 384827230 384827239
    0x60603020405090f070320070b0105030606031213030606080f0c042702030708010c0e0a09060627080102070b0a0b0108060108060f0103060e010801060f060e1507060b0a0308030712110306 82
    0x550314071408030001c0c000702650011107a81801c50201e071a07d440302130301c015841030012140a03600d8104040e42e40c03a048a009a150303000c050f10703810104224000e0816070464124200c000364490352540c00707568003900640c00641c4003c281c400414010040711440c0102070394100410782c0030418032188080c004200d0b9800501c842c012500710b407820410b6070300a005400080080e03002c2003400030080f000082080e807003100f01810100e06017055214420456170320b611208803039419aa07210705814860200b2084006110f100016402028001401070070f00c501001c00c46c5140240700b040c11100400340850410190004004d03150742c000307503034640041d02240c401d002e01c0da01c0e10040300034040d950001c0454400d540000549100f054001c0425240d403174404402c4e5680f10700c1c04945605c20482c08540c03080c00b89032100c05042e0042c0c0100030550180201145002014001c00d451201d5139000f1600728100004210440d03500803d000001c0c51980f0041c0306025441c500765040d40000780c0920310a = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 384829730 1250 384828480 384828511
    0x105040513021e040b030c0a14120d0c06050106170601200a0c080601120c06050306130e07030318030c1406090306041109070512041704050d0602070606060302040509 73
    0x900d682400c40071142540104120140e0301c82503201e5540030011544140664149103500da0603203008149142d61100150010240b0703444c082c074281c01c140b0009481c64008803543d003000700040c1c0900a2202848050b210001c1204082c50000304942050380040c04000083c004140c005214014280d00301600b40f070680d45408250000400038403024002220070300c43d03905901d0070048805000320403102d083c0c0c2600c0280c1e0360350702505400070111200400000d000a0103100712030107000510b070414000703000d0400d5124240001f00485480e122403615541c840d510800405510020841108200002800c212407441d903c0c1103104606001b170700a8015103c200010035159001620190712000701111083d04007401c20140c4107401b0340780c240c002c081020004880a026400701e4403580c04003c0c0c20300103030b6219110020740c2001d50000c4084034408100025141e074805261820040c0256001a42c40d4905d140c07002c211000d560081052500510080185540fa509682c1c0c0c004041c1e141010b4 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 384830980 1250 384829730 384829741
    0x7020a050c1e09070216120506070c051e030706020403061e1e02070f050304060c0b130b0f060a082d0a020a0302060c210c060a0b221404061b05090901050405 69
    0x86c04040c40d030310000368460090028280e071414080c40c48281c000c07025502281c0310040100c072680d40030040070342950310007074500300000604402d0141c0307004510141ca013030010340c0d9541c01c20b0741e00690050300d0b669280d401030302d1810110401564200c81281003000100784001e48003460512445c0d82555090340452041e050040d01051859080c1c4e00405072a0b4072912034101071704819003440140c5d564800c0e10700181441002e1540c3e030740700580253b02207c0c2c40c4d661032108117103003900800303594011511040000d0a40f00801ca640d650350240308400103240000b107060540d111a0081100c059803001d0b5895015866512080080e260190703a600e90b121075680d0501d140120508a80000010010320f941c18541c8400107440c0c400b8a00c01175400355103400358203400369034020f86c0030b40e802121030034401075081900c01154102e800c03465000c144481443c1071426607010440b0160740342c94580d4480140d8640d100441c07015401281011403d000d0010081111030f01305028481c0119521000f240303 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 384832230 1250 384830980 384830983
    0x31409030c1201022d180d0b090705120601030c0e09070b040801062c010b0d0b0312040f3f0506041103070b0405011707140307020a050c1e090702 64
    0x461001c01800b181110b0340519909030007944640303040810543c0210b40c42d485201032100344503810030081da2030703810300c0c4112036600302c0c1c020140790701a4400c41a0070540c0002d0054a9400d1040c03152501520015280006006001c50740b40f80307070001c6802820040c0005111403e001040d41c8a040e400410f9139211150640380c0001c9800c40d5038100300c041000584001c0541051040d2141000d40c02450410f040c0031000b00c090310843d860320310001c4001403100e407079440701800b400000c140d00818480c50f070340086400c0607402c000d80c140603100000d041c050121040629002032042d800d0784000c000030300c5090000c0c00003940d500c0d0303900e0141020020503101c07504030980c041604001540ca490030103161442c55816820071740ca02030300070319400054409038001690220340e410f231150800c404111100c4100594020916014082190294080720140d60042d61040c03400790018200c260f40f0b42001032914803000320482c481c0c0c044c16114108000385004000d04003800380c1e1200040d803540c1d00180e = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 384833480 1250 384832230 384832243
    0x150504050d140d030207030c0f020f0406030308040b090c0d030e041d01020a03060e19051b0301062012070605040c0b16020a05090f04080c0a02130606020d090303140903 74
    0x95038401c469a044005101021800502089a403000c0300e800c0060074400303800368090b021010340400d4481c100107010540840000405500c0141002c1c08140f40c01c0c0020300700d4403690420340010346090100001c01548600c41030700101400000c05207100804000b0b00b0340c400f000801401c012071607584014a85694100c907801d9055881052400d6007448c4400d4001d4000f6110440040c0c1000800100c092001100c107020308001048940078001c10a1070030060304c005011185a1000c8140c480908980318002e103001c0d0107181d0310750601010040c04030317100385200300d140780303054000c3c060640740c2070000b00c1294200d41d4041d001180ca07a0300c50611880e400d00300d9111000e21540051583d41c240c504009030550148212000d191682d100c5080c010803060840340340b04008a284041404201c052020f0300103840260120390139070030151302042c064895080d040040603100c0074184801078041c0700144005d9018600580841d2a603280244810440030b41907540e0800010302c11115141403001 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 384834730 1250 384833480 384833489
    0xa020d06231609061211040f030c0501110c01120c110109050c04060f0821040b0f070c080604120315031a0403020d020327180405010e01111201150504 66
    0xe0030764000c071252a52480000300c842c0110300b80003110007a10030707004182c42c1003562016601c56013075101c4c4c8001e1000404544032880301c54501800f002808c01079001c1c601002d14800d0104910840c6002e00240607483c172481a41000c1d000785405100c00e036030001131b02c6602d8281403000b040c0e444e2001c1095860720540d2090010315424000e41c0c0c0184400000d005620b01c40c1a20f0070420b8680c0c641e20042c8056560160311016048140040244041c00401580001104e015070b0701e4035665030000b8039154454141310720207a601041c070b102444020195140103103d00c0340500041d203456502e1455a032030b80c9940c1002c1c540c0c0d5840001b0107020800e400d4000d10341c00212040411441c071050625a84111030880040c400c42c0281090f0502c0401503460b0704100383d00b201120500399800d18841d40d81200b003240c0090754120b03000402c03281c101c28640070328015000010b6000b1441f03502c03801c0d902a010b0041c0c400c07404025160520309104200d0381110600c400600e41c01e010003201300d90500c5503a11 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 384835980 1250 384834730 384834761
    0x21905030607110c03010614090903131701180b06090a06080d020609070f08060403030f0f020d0902030d051e07050709110a230a2106080a020103050a0203090a020d06 73
    0x1048181600641141201100c3c00b0865106001507400c03d400e0359411301400010000d00403c1024600302840c0c1203400000c1481130740e0402c3e0030f01601254542e0741d90711051200c1051528101510001c1c0300300e00444010b0340038007001c81c0e403075220403005a601400e01401590724000080740741d17a03140c0c01400640030301e80a5506c0103036241002943ea03082910401c0041c052010001880039810b108141201c4080024112594454070240e006104408032081c031a9154007542540030004d00c0200070001c0c2c4a8800a40c0b9100c0e0300502d45007020106082d000d101041083c1c15022440f441c0d078544080354284001ea03280103619215043c200709900141180d0b0505020281103e0742c074014000301241a0b1300da0b005e415071440840d9113002ea410b694100703c00c04100403554207101d5680013210460041e2200018107079002d02408648103984040010303080b40c40850f08543c0d01d402034640144014000b0350640c02c000e030f01c4039100c4e165040000d1150845500d104208111a001802d840407503c4 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 384837230 1250 384835980 384835993
    0x8070e010b0a0c17040e010905060d03050d020c0a0f14060f01051002030c0114061e130504110d0c0f12050c01111204081e01050f041101090f0b0a11071202190503 71
    0x21000c1168205000765060b01446d02c00105206d4810300c580c5204000003000c0c0d40c0e0305035480e02d080d126540100160300d1b80a400b00700c10b038103254080094855840c80340b000b4000c0d05540d4203002024182c855443d080b141c0250041c400515802e96605d030548408480b410700241c1e50301010380c82c51085d651411f00d03550a0001c80301400c80c4101304144075a1040e654600242c1c0c421240111105a100040c0c0d44010300c01d00c0150102d10780c0e40061340c014895a4004400c40b1801e0010b2480c10310884120303040b0760075943c10301a256000c3c0040b0000d003102d08808848000580d1290b0300c0b40a0303140318504100c4140803034041c3c2c030010441142c1e011076a10150b5034032a112140c0c0c03502e844007000c160400641101c2180c50100051060600c1807039003050080581d221a03481202210400c81d01d00d0400c002c1e004085104000900f0b104000c007545500103942c2e90707440d5806070006070074858402081d040103008000da03080e503400606c13481d94100c1d1034044024201107032030700d010456000240c0510804 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 384838480 1250 384837230 384837263
    0xf030708070902071205040b040b0313060513061a010206061005091c1a04020d1b05060c06060a0e04080d0b060f160302100218010e030f0a031808070e010b0a0c 70
    0x907402445054001c904058018003145d400741e90b14443ca200e41c00e400c120420080020301ca44001454001e040c41d6041e45101805072508000e450701520380f1804070840140140030449103118070840322091005200c004040000040e407100360090078240600304405503184020312540464084001c0103001140110202051600d03500035100100c48100000640441d105642065240700e0b660003401b407139030244559aa00340021204400c0d000d0300040303c1c0041147d580f04409002c0400c1c0c0d00c402001307140750031b00070000721056580c0b01c400740c820400e060101241301b2000322391401c110300b10040f4041100d240403403454400d84030000108500461280005072400c144103010502039403c50300c07240c18401c1d10000b00c1c440c002c1d4403120012115200304055015060348400c1640084c07d40b22203061224869051210504044000410038501500c80c400b0b4a045040580003100003070074107d0400d2071a04c60480103000d94846035201040c0c025081d0b00c202c8428801c1c03a071243c0a00c1054418 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 384839730 1250 384838480 384838499
    0x318030308060a3639030203010b04030219080d0507061401030515100b0f0d0c0201060803041701140903030f01090506010203090f030a0c2304020f0304060504080708190f0206060307050f03070807 86
    0x3c12030f01c80c1203820540c20b1703601903032080c003d46c0e050304c42400000c2c0c03400c6d1540d0b08110701c6603042d00d40740c80d01c0c000c03005c0c1c0000c02003402d11481200541c3c03a1034aa990b840c452415408481020703002c0d00c0074100d601c005002083c0b0000707100241d40115600034070180c981800c000d10ba2070540c0c0c005503521000046c8100b071900c190016200460f05954207020b80d03800f2010607400d94000780200707200c0717034418003042044410008480c00c03040000c00002030074404884c12801a690120340d013603241c1c0e10000a11204240c03c0c5e00e454010585210104054104800000c0d103078469901d40600c102c207a0001014903035001e010510449902c000c80c03104099417140c4455800d0703035211384442d60142d00040b0002508240c000c86a85603608050285141d90716920400100800342c030580d6014814410003000640d403074024083c05030511441e0007250a0048000c01e1441e0400108086401400501040c1c0e2000074942c000d03620304840103410401208003203460180716501c00e26a81c401d282001459111 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 384840980 1250 384839730 384839801
    0x4170d020f0703080906040224091f110607120c0306050904141207050616050f1305031605030c01030f1b080411030a0314070318030308060a36 63
    0x3180d210240d4070743e07807090415181c030306c125030194104020460710020719408090012910514600742814607000f0030100366201c1c00c4003801511011150818001550408605e11b0035506d41401418503241180000705042c030603142482a140e1a0311494047c54040c1d00070101802010f0012102843c0a0502c95582a080c1c80b0010003801050300c2000500801000c07140019009401480162038a06c071810345c0d0340e6551045010000240960409201e207880140203e80781000304c000403c0c201410141001004d070194005410080070400c01a00c0201d0390154400003407c0024540490340c01c2113001e440c200c841503200c00b0600e903403284c0854200a5607401980148041030842d4a40405e15541300241d40c80540030400d4a0700c0280380f043c60200030130340f881c4249000411511440540c6210f070143c0e4100702c010070000c0742046002d08055082c0740003440e0078195030019050400320800c0b0b24122640f2649942c45100902d0b1800020f60032071200440303004249289101c545001c40202079 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 384842230 1250 384840980 384840983
    0x904050a020a05090f0a0b0f031b1c0209040b1f020717032205041a030d0c0818040b1e130504031409120105090d0207050406030b04170d020f07 63
    0x1898100400d000d2280d61094034080300c201d4036100c0c0f5080d103e108001c1e100d54280109640402849008200380018602070080c035583c0c2c80c1281d880f4280b031982d07444c55095051b40c80110390018807021500c0260140c80702e00b80d0030150030043e034804006004c54094142068a1030300601c0d10b1b000c2e00c41603050184040d48140d541da0a6600352038a80034008032248544141c050254802e1186045104c03650101c4c110354501340c20845d016030b96880101c1c055a0b1201151071404030300c1e50505466042c00d10002d0540400c07403810100301c01702603136040c1060003242d03c1161000316001c010441030b180c40d4440c41e0204c40041c40341c2010302110000f00c07141c0f440c8501490043d0060700000c01500d103130340a95401564151254500c4031000c034444412900b0043d04150b01004050210a0254007842100d01803020880a0021001002d0b00a841c0c60300685c400360045207415002c101045040302c0981d0043d500600e00741609080e0b601c0c0c0140d0307010b180c910940036880000d500040d40d13280c178000c1001d00d = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 384843480 1250 384842230 384842239
    0x8010504030807020d2c0405101409040c03080f0d0e03030103020f0909060f060a08010e0105011a0c07030602030c250311120d0b040603140606010e040506012304080d0e03061f06050a0203120a0209 86
    0x9003150a01800b81810394cc010000040e01005000140154001d800e14113030100311640ac10150705000c0d0b0aa41030800e9200c81600000010b1080d410328244580c40300a081e2035480c40c5080c108403c2c0d5a0320402008031502818030004030329103035a11083c09004043e40e4009206680221110340e000302001c1c450b204200c46074180201004c090541901d02c1e02c00c10b1070282400901d1621810082d40c001052100e07030b100c04105460240c04c60364589401d000060340e80000480309490050701c10103c001d41441e003907001e04111044400007804583c01e0b544040d10101c0c00340e00200114000d403030300b07800003400a94041d041004124002801c144101030036a1064a0001010141f00c115802500c07550700041011000b1076001ca045946a21100c611075400e510342550758000c0b42c00c016649481100150100e114500c03140307010040e02c0d820440c3d080c403400c0f94500f0501980b801500901c1954248100460103921850080c000d8a450300410f030980740080c500b24403900f0095200c9444071740328 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 384844730 1250 384843480 384843509
    0x102130503070623040e1e0601140a0e030c041b0815060d02090f06040f0501200705090a0e1006031203051b1b0708010504030807020d2c040510 63
    0x601d00000d5840031941152101119203074000700403c241016a50752420400c410400010301c5081d130403c80c0e1003000a00804152640384c1401d0a44005000c0c11181c10005650501c40a681041e000c5900d118403a080c00da040e803c0c414042814203024a1400d50322901d0180050281001511051202411b81d0b41d1001c4540d40c0484c42c4a400c0051000d26400010500c0340c0b04814420b54000c20302540c0050488005000c001d0005500340d01c9500172030340e125000304080140e540c03c410a031844a9240040391a507000300b0b448256034aa4501c40c881c4201c0203200070400041c0e040e400085951503440a079071428442e40e81c1c1402070034207484211a0500e45060800d038446c8207208541c00342e5050044034600c20420000c01c44c0d40d403c58a41d20f442c03440c050680400d585020030402000703084000001c601c5242504000c1c101a500403d13040a40d000440c4e00d610650780039a080d00b207440c001c01200307000d00039404926100250740803c0c9400c24984424025085000910f8200f1111412440c84a = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 384845980 1250 384844730 384844739
    0x105030d050304080a0f120e0d0f0903111c06020c06061c17031005030604050115050a03120c14010c1701080f03090609030a0803010315050601030e190320010213 71
    0x5680c4400c40c1c001d000614140a0800d90602c10264040030650b1481c0152210b046201f03003070f045039a00700b01411aa80881c1c0c03103a02031904204503040111b03075801c0c0400c0c02403441d141c581e03c88281408040c8105020410b54a40b140308141e00100300380c001c01d00315221f00c6940341c000d580f00c500b42c0c1d0b014070992840c40350307601059622014896495100d030040e036040c0200711014401d90009451aa011220302c80003180f580c80800840340b00700c0c050070002c621000414400c0004100c02c2e00144d0040251007814400300320f80c85480c007840b904a14040003400000e09055000c100c0c42c401d84001c0c0c1d401c28413144201c41c4d208042000d803524009035640b0700d9a0f58908155100100a40d01400360000e0001085c0c502d480f0700a49291000074040c1c0c2d114206a43d03e00c050356100b41c1046661058103814a8410202d51203241d91100707080c01c0801465070081082d644c0c0300b0f032503015044c045040300d07440c0e02014400c0c4202d20004645a1a406007a806400c15074041c0d0003c03110b8074007a4005140008 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 384847230 1250 384845980 384845987
    0xa0c09140102100902030f03070302010b0f0a050d08031f030b04021002030a17061f0206150303130b0d0f23090703020a03030807020f10090201020f2107060608030a080105030d 77
    0x94030344140c0060885040707481d015000f600c901c08007613a060140c6440d90300b4804080c401000c4061207503000140048109042181a2858841c403a01918640b80240201d40321910500c04064000b801c035a01c0e0795400d00907a04c491a006800302802401c4040041048407107000a40030b14800c58a4510024034108201d07500d002d00a55040000c00500c4180009030f10b6014454225501501400040040c81c0209414129940c10303000140d00c14030421540a09030194002e40c001c0844c059807402e0b45845900660400500480346450000241882a0031071548401c0302801d811500b4480410300c3d19080d8038001d00c0d50b414000301d140610000301d002c00007040d01070a49600400c0750382c00605680707040310500401070091b400d40c400d04030702c031401d64020081880119000711340801c0f0001640700080c00d0801c2e010203010207a000d42111102e0ba02c0316000107040b2410a0260354483e401810b1003000342285a110710258000000d04107110ba500c002054146d850683c101d4050704401d45089 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 384848480 1250 384847230 384847259
    0x703080f0c0409020a270314120d1e05070801050111060c0a0c0813030809040606022d0a020603190c051c0b040e030a23040605090603041a0a0c09 64
    0x1c060103103042006105004040e406800340148a14094280c8280c2c4040c000c0004104d103030b4902611102c0800700b00f00f00c280d80c00c860040c28060043d00890b40c1800118405000b4103114a084035100c4520b1901c80d0341810784800c0000c83c080342480326051600000d40000002c1c004d5500054909400d8040c0c01800a09507000e017001100700c034074003091844125907050042604503180e010030410000705144030f55844020f50301800405644a0000c8108000c1714050b0b407005c029074210301000d000c404011000f610007040d00300c3d5500b220f444049000c0f41008481003000b984400c2c04030500401d818a4000351130362001d00a001c000c20514107406403042c2c01200070a02c041c44c803409c60075001e0b4080380c003d0a04030001400205003289588012070464012510300400107100c81014042c0e2840482c03820b03101d8000c801c440b450300d814403500511500c81c03007280c1405824000b01080421210550000004002c520110a0390801c41e1485000e009250030380c00000310002401b19000c60040c0c01c0 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 384849730 1250 384848480 384848491
    0xf060c030711130e03031b040e0a0515121903050c0714030106090506060a0507050c0a081c0305060f04021e0406050403030e0411120415020a0509120601030b0708090309150703080f 79
    0x15421036032010a1f80320344116003543c000250409020000c1c2c0903071a103039403500a02c00c1b0080419240780860510b80940c44540146128a10b5051100040200410b181c400304080b10100c00740c0c42842d0034142c0c1d03039103d072802c03841d40e41c482c840e00082c14003070212603d050311408400034490a81d440c00c00c02e01303a5900381d4070280d10010400c07242e880c4a00440050402a20075402d4030545030350800000c0351504503611290307903504050340b070724107005c2e00482482c0020481d0604102c5e904020011075034800f00d0031a06030060f0707800902c0c60411684414281c840020f03484669940d00d4580307034018020f8105100c00c50200d2071100c40c2d10030f140b03002d010390207c440102489500f042042c0d40340100e890700103001903800e44807840c40f0112038810380c00105160750392511000d82d035401d0b9205010219003003074a5023110b40c101c3c10050000940205405800042c64502040070307840e2181c1150461180d0803001c0e91002d4001030020800c18500c000d070150c14000d80310345140d9a04c0070184000c1d0304003140da = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 384850980 1250 384849730 384849733
    0x32c0f06131502010609020406050a0e030d2c0406080309120304060c1203091205030907080105131202150403090e16140c070b030109052203050301050f060c030711130e 74
    0x81445200b104411240a4201d58400861219a901c4011089030b209402a0000410000705010400c1c0c0028030507040e1f0070190010161080041d00080030f500800015400050440032045031003248440c8884a041b40207004014651307071070038165a2540a24403190046140b44944012200c0100036542255402d4444ea07007004955650194030600ea282220f0178195114208000716089010408041502c1e45403a5560300300b44a2003480d18490303a0284003568188401c0060340c2d051182c0880c2420b41c80f10790350745c0c441030819081e4145511854010980040c100401051544c03102c0c01c1340c111030410340803c1e596150600000c5c003003400c1c140c0000c0818100b41e03046604c1051600100f070905820300580320b00c80c0e220a074400a56000381c0c040040d1a80700c030140a071451600c01c009003021424640d40740d2031003069901821901051044622880940010b05516100c5200300d607142c61183c81620b0760303614180307001905c60b044000c0301030041c5403644200e032841c81d00f407190001c0c0b08420070 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 384852230 1250 384850980 384851017
    0x40305010b030d080c13030803100f0506070f080f0702060a0203120a05090c0108180d110118020a0b0706060b030702100c05040f0e0603010204080a050604060b01050f0412032c0f06 79
    0x605c0d08400c2e80035884c51705d4109080100040031070400d401842c000d02c0c01d100c00780300031403514103414242071054221911450040000100085490380481141648880c0c841c1c0c0b01d500103000400b0500a03208040d4100ca0005041000b245c1c0c08401040c00101404944842c0d48038a89100c00f00e94084507001d200307503c10011010b04c0d42c06400a1a40310f0b4204c1c20315010685801e840d641890b1440b811070010070a40c0c4151041e070002030040326a82c0b00030283c0702c010840b898000503907404c55441458100c0c203001642c0c409118040d0000409060017032816070745c03818650030095403028080301d8900c1252400f64052100c500c41c1d000c440482e8100034204411606000300b000c03079018060180f551566081000003140c03c81400340084150041000d04458a4030342000e50540e002c0400c854100101044100c078410712010039076080d1683c0058648222401d86015100340c840280500d0034902c0441403507c1c45190440340380d568000a41d01c00704c00c110b94500303002c114021214035007040d45406 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 384853480 1250 384852230 384852241
    0x10b0d060b04140f0406030606080d021b06031b0f03012309040201080c180d0302070e09010207020102070e04030c200a08030702091b1c06140f030709020a090b030903040305010b030d08 81
    0x44d01103640140003000060055031b01d580d08030445500c0d074483c141c60340020407800b0803c0d405024149a5841c444204010022608006445440300918005e04280c0c03008442d44040c061100380c030404800a100b465076540c481c041c10300d40700801c1d12030b00c0c01c1500c00c04c0e80e84454105055540e004940c1a16103942c03c3e00d07290300b030b0152908409040725011200c4003c48215650b00e5101c1c2b10264042c0d0094084181007895141c203440d001440000240e00400c1101c00503640081c00e0ba00325003190551082e252500d03d001ca41c0c81c1040b802c003038401480c411203460107452548401b032514500303c555075001c0307a0f00d420198480c003682e40702a500050180c0059500b0a1502e003100c0445000a0b583d80f1b0440f2502000c4804194a048a03540560780c1c0c0c414440300740101010410402c040b5040101c104010b0300103581c4089900440385441d801044a001e020700521000014140d1012402e459241091403190740e9002407206460540c24005900d5080c100864181140049652103814a9880c03 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 384854730 1250 384853480 384853489
    0x11706150d09080307020d020d09030803100e0a0f060f0e040b0c0c0607090302182404020d020d0203100506130905070c0b0a05181204050d020d0b010b0d060b0414 71
    0x80081140c0080d800c1102406407800c9104000d030491181070816200e04200c040249801e10100510007554001c0301c01391800e5402848200444e80e02018455413503072400796001000d03115034420f582000710075082c400c00d0303551500404256036503060108996580c501407814030040314416103054151150210f004201d18058607980186441ca0311840c06060aa000303240c0b800840d40100003e00b21441402149807036240702034441c1c03940491101505120401c0c003400100014000b000403501070040b40140c880703405681c4103145041c8215100c0103054100c0c0040c1d0320488600c0380080c40c030343c0c011078035103084025070b085003146092440c411030401c2c6410000f040c02030b02180a0261000840d40041c503c8241c251007004100302c082564101220000361107034008000b0301c0b06800404101c0c4083c082001030700c049400844410403c8080da001040c0714200302e6030090507403a00a000802d046020100134115032000001c200312840da01e46541354030340030720b0154403045811100741d1003882c6417 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 384855980 1250 384854730 384854749
    0x501060f140403080310082109040b0a081c0311040303140703020a060203011211120607031505040510060212130b18090414010c110613050703081201050a05011706 72
    0x3010401c003850700d5281c0c2c44160385608110380040c030302d49903100c044c05165411710841a80817003140502840790040001e1031050f01601e4203443c0642e945056520380d9a55042c2550020305884081e628a40c1d0f80c021504441c65076001c45c003000c41d0914048002d443c1c20b400c1260101c81d015507809002400240a01102d6400100254118030460315103002250062000f0343c0202544043e100110310f00b80f501c0140c24040c4409184610383e41c1441d0900c2d8813001c682e659122090380380004415440c400c0310280380f0125001075410629141c2004242001c90303a0100c283d5282c0d40845204070030211607d904e0707208800d0b600c01c04110880040010503a1407002d0f010142c070105260708070340c034508c001ca9034544089a003a1101840c0c0e92007255410000c1c8500711013804285030031545091900a41580d403000500140e20300a24003d000b4140201444141d0181d13902c5100d050351012419040a02c504081c01200d210790b140e10000100e6600643d07050304150610303030700b4200549e81c4c402080800344 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 384857230 1250 384855980 384856007
    0x6020c03131401091508180a050f0f070f0f09050a090203010e060103120c0c0e04030302071a070f111b0102010b060a02010911030604030c08030a0b040c050c0d030501060f 75
    0x40240032036400c04150408400240c0a03840c80310151920395000142920344aa11041c15110b18450001d00546d0200d500d41d4015081011000c06107003c0c5050752900c1950b5001904500179604154484030010910161031021403003190880b0340c0b940f510100c4400544240006c0e0721800e0010000f150440d00303c00e90288600a001411440f1b580110342900c510a410601c1d54024030014820883e03011045a072a086038034021440e01081c3d82d81c0c0208081c03900641c1010417030100054200b510a4040b100220380c080d003207100400c040c0c0700c01000c074007082c0c84910100b424105040e0b400e40c0b0555254402e540380c54024090646203c01a10011118180c4181195201d001c00c044c1c640703c0720010a01140690b00016418140341080580d01880c181030394030030b81155080c4808a035003c0d0100040540144450741c0d0780e160b850000d4014103079404102e0700582070070200c003946500700015203181c810141c01d0710101c0d40117580c100c0031501c09010340c201140354940070395011880761168106c0403 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 384858480 1250 384857230 384857233
    0xb122a1f0804060902210106060201050907090207050c1f02010612020a15140406050a0324032d030306090f0507090605090402040801240609080316080702130b1804020d06020c 77
    0x2402600450480c11b08681100507520902d00b0302418440d0034402c42001744103a20003007020f41003859009803500d2031803248003070306074010551a0901c00c0070b0110901001004021603070186903200e1540042d1405000c1d00059441c2480000e4101102c141d16401e550b4010265107031b09040060f2605005643c4420302c1c10030030080d4001c2c0d8407001c56001400074205544070316440e880e034000300030b040e9407545500300e0300902d5500d107010780c00a05084000a5903480080042c00e4040d00c40e644c01d20032a03c1d540d89100680d078506000030b0540580c08501501d50165007841910100c000726420703540140c44d03c00008100c1c2c501006110b1090b006414400ca000b04003514056450080500303507803080103020311011441d2400211405041c180b040180058140200c10030702d04110b581d02c902a154000e03800701c840c6100e840800035480e04882c15181c0c0149035100c00085081c080c002040040c2003240501c282482c4035841c4c610003031a803481198010018000b44442d541c03140041c4d013003a00d40c040035 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 384859730 1250 384858480 384858491
    0x16091802070f030306081221130602040f0f0509090a0809010c0c0305070618150f09080d02010c08010b130315020c06070c1a0c0d0b122a1f080406 64
    0x51002d119401529020b582c010482504140c440d03420002003001c24030105408001507080d40803980c2410580f842121303c9503e01d55204056040810300c1b181c0001c01d061304c0050046542c912001440055452400c0c40e61051512007090022a10050729282e020f603004011a000042101c8010400b0707050616051011101c0c590305c111014450760000c0301c40c0e400c010f83c14407100b503211040c3e041c44040140d503405e041740b500c0c01030942c100b42d0848007005c0141ca804504504c0740140803c00080455604540b100c8004100c024000d0074590700038800038404800000c0c030702d1440b00588107480144105140e20500d1075540c0d95620740c9040081e120203800344049802c1080074841c040c49281180c03603100800138945015002e1443e00001d40904220240500c250030a003071055079004980c0d0140000e081e5100c0001641550400c030001210340701d540e00c580e1a41e0703500748201445081c0d520807000c4000c03101040040a90160414680760916198212084d0748580e412640290007200700050 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 384860980 1250 384859730 384859733
    0x50a020405190603080909060d020109210b070314010501050f120a0908031305060f0f04030e01111009060b0901032402041508072006160210050411091609180207 71
    0x50343d000c0d03441611240008910000e02c1c1c185885c4060380100203c030200307217501e81580042c2003540d003400303607415403054140030800b5048041c50b800881038006400013500c2c900380d24020050980c5207108042c24040e0b01c00050f8550050095810f0352064420060410b04610064a0403520092049002c1c41c0c80d040a003000c140e1a0000310700640402100e06c404210f9030400c545005005050710060001c81d104002d036080c111404e05412990502e4071a15403408500100c076481d03040840fa454500aa1b070460700032341410303480010660b118a500344405080b8804201d06224241710141100307131003010880141c0d050500d85880356050240040c10251103042c1e000d60f0003d00903500e404a601d01061241c408e400100020000781c2044100f170001804c041c1460b10717102c0103014140000b080340fa5030b80030320340240101d4201c0241250104020300d4039040540035207022034234140c0200c10040121341c42100e05529182d13140710540350340403114581801c440e511003411880300c03c016030a01c6082c0 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 384862230 1250 384860980 384861031
    0x403020a03050d021501050a120501020c07060e1302180f010c0507290a140c010b180106030c1d0d0201030e060f0906060a1a030a06080d050c06010f03050a020405 71
    0x3000303140500014080c94568500103850f2013035a464841c128458100108a59914032952000f0f0f03920200014404030325031b00d030040c06406043c11a100900401c1c0002c161a94480c040350450320085858003483c141c02d008540403441010382c03200f644072106e150b044260070240c0ca0581c500304189480c030126041074403103034104119a04201e607481380d100c0c0c6200715051408a02c5144a40c0d041105180100104019100d4422071005001d02000410012446402035101a00c42200a0064111800c110030744042426090003400082840d2460a00703c29200e01451564951780e182c001d5811803241041049181898808030704040d2101040e04042005116560081030021050780d80750515a22060501c0b1006217404e000301d0048c1c80800007451003810b8050300b010003200301e540e20740360725100201604842e00007101d284213001c00859440ea01000600503c501c003010348610380d807078041c8400b02c440980300c0039080d0f43c0705078940b2000d8a032070791000e9046900c501e26a0503a918113407041d13 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 384863480 1250 384862230 384862249
    0xd1103090f120604050f1606081b040f06030203041202060105090c030406091a04110108091203060301060b070b070f09060504090c0e041517010501031a100320040e0718020f040302 79
    0x2291545c010f404403904455003000540318060041e44031291070750502d04001d0140000402b80d1100503c0d8408280e01005840100ca024010031480400816210030000d00650701c19282264003810710034401c90418400f01381e00707041e83d0f0020a0180e06407244441281a0780020f0810307140300c0c2c0d9981c0c5030000501d074a40b80c1601c0c10740c1d40a1314007042c82c06041c101c00c00101844620305101c1c0b1181040340040740403c0600c01d1004c895440f644035154540402d00400c5a500071710002c4030001000d10070300182d0b40742a03215041a940d084401d0a0100e0115480207840c801c00c0003013503050000303000c1100c0c07640240300d184161745404091502550001016185a180001c8910b09152403e011240701c1c003c2c204413080450009004c2949941c1d1508104100001101583c0031130a01090341ca807810f0380014021904000d0003400030305500441c000040b4400705c001d1256180c010722035091080400c0100481d82029040c01031903c40c0d0722044042c2d44101c6a26900c00010440400103a0f0341c2000c4 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 384864730 1250 384863480 384863483
    0x509130501180c06110609030421020d030201061802040f030206070602210105031e120f1e180306040b06090901060f090207050c0604180209041811030d1103090f120604 74
    0x80c020100d1078403001824961405526174540c0c1c00c03c0e410802c1c4250004102d4007200c0c00c00103a035404418003940074040c10180f681c02907205400b40002030506505401800a032600c0c49021814004160f05140c100e20940c4203000c07140c00c006c00c0070009450804090101c00d401601c000d441c080c54541303609503400c20500400f0440340c06800502c01c81c24108503481c010040d42d00390a205a40c05901e1560340d51000340c00c0b00522100194200498140105035603c0403845640d5401c084c0d00401042c00317079000f41e960042c000108c0500c40ca29454001003590040d40c0181500340070303448040a009170b1a0b0000c0c5801500c1d901c440c170010311030040b190f0313a2005180c03c0e00300580b40c60701894001c1c02c0514a9403440c0c8626418001400658000c9044011003001408010382c0d82c0c3d41e01021402130101a07010f10106648141d606003804031000d00785445803011401c0c1c07503040080707004c00d030303280014007003c4807442e8002c1c040c100c02e500f801700c1c0092400400500740e200d005c2034020b8951a103201186d0 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 384865980 1250 384864730 384864743
    0x30e130507090608180c0f1216051f050a1101020408031c061215020a021009030c0203060901151701020c0109050a11010801050108281107020f040204050913050118 72
    0x1020007146138030282c0d6917008110402c00000e0000d50112041e80e40329a13a0410b03100c0c0480d51010a1180e60704040025176012020560f0a034003045140d0808112081c4501d41c045d100103520715030b2204100300c1416459405444880c1000c0e444101102c3c0d14050b1450725455650030800828690010400360520b4100071824035030071002c01c042e03071061310b10070b50000d500c60b00810880740000e070f00c005e0049a40f040d1084010b86070000400c089180c00c038070b88544408185860780c803c00341070f4080b041440c09170094003100c0d25521420505822262916051a262181084240400d2183e286030080c08104500050300b80403440003610b08481040b04119210b6100300c0c4120f042284c11603084003110f5090a1000066141c0303c0082e00915004000300c68080e00035040d2070441c1300443e0075145a00243c0381c100325910040c141411160f2029005074800c03841408101c94500d40360080b40c05444d00502140c1198507445180c08213100d0966045820b5500d8080390301d0114611144c0d400c17024059803 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 384867230 1250 384865980 384865997
    0x9060608010c090803030702060f25050a02010516050412080f1216020109240e0f1621080a1b0606060f030c2a02060c0313050a080a030e130507 63
    0x2c0181080e4003a5000101581061080109440e00071412650108032910110003942e100d200c061214814601071b000f9001000e10008003455101b030160409450940007045651034501051424904e426906400100204001d03c56142c3c4030102d600d00303521420342141410441840e1181c20742181d070340100c41c0d02000d8108940000c1e001401c5203660203a0008000310660381c1c03160051074015417114920503500ca02090440301079070f403154400305524801e0700ca801c0200101d90303032203041e5040c468541c10356000d40800c02d5003407502c610202c111240c481c5103107505290340d600c0294002c188280d0070320101c4541d207544107400b9410b83c5400f6101e00000104603050440c041c25011200084404042c602250210600d4210700108024280441d42e1001c1d508071003c8800d031090441c01c020741000303000c00d00d030007044c4d80000502a40791030600d10b2184039846105211200030a07105000042d4041801c04005c039024078012a49058054112800b07095100b0603038055403015580c07a000a270001 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 384868480 1250 384867230 384867251
    0xa080309010f150e040605040c081506030705040608030d0c05120a45020609060703030203010305010b0d050d03020310032001020c0f0d03050306040216031d1f03050601030906060801 80
    0x512503c00b0310100622a0302107a810101e60654070070008000404281c0e460001c201407189004121008201000403503600e10000900000d4004055441500a00c101d004c081107038a403074003e00003610045402141010441c2c46640c020f04040301410b0103220041001d203180541d40180284030306602080800d5804141518520300038642840d210340c014212144003148422002100c004042c206940c01030200600001d9110b100d190b1800e548580006204410141c0603009903040303a0140f0000c004110f00401400000c19501000074900c2d00541001c440681c0654050360304083c7c0d440e46560308549903030345d80d1a0802500b107651701c1c0d00070081030300700c456a041007104840d03001500c015000c403525001041219910b840010180070010000030180d0704d80780c0c10741c2c04040900c0c040000a001da4100648190072503140000c05a00c80441d050441c00e0000242010300004603e00081079003210040300280005402d180c10540c540c51410046803141c0175040c0502226000094100400d = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 384869730 1250 384868480 384868511
    0x4110a0c0f081b2109010906120609051003140a0b070503090c0d03030f0507030c090923010906060206010806060a0302010309320c1c0303091403070302010f1413030f020a08030901 79
    0x83c00b5155070800d4100125103850341d100c003030f5004a42d009d08040030603050600d4180b0103006039810a5200701d140c40100045032000e440755404407802240103294800980c8012030700c0b0359480350007401c90048940410704048c420390085501c61a0101a143e4040320305000407000803207640254006512500a000d00c02041d03c91942c01c4800760034208480c1c40b50a2014003034a41c9071007425242541c643c541441c0c000381c03450002c00351140c04100c0b241907840d03104400050031507020300b00c014890f81c0d002040d030340400201130340038900c0140171a00003441c5600440107041d00000440e03441c21803a41200c408000310fa03c2138000030214910b03001c89040900c001e890022030344101440340150580303d052440f9045500c60403150140780c00b08945240d4203145001382401000039509120001d12403003810b50652200907280c040030804d02100c0d80c4003031640c0141d0310584042d16220140014100060301401004040c2400c0e40103854028481d0340b0340d05042c1d00211040c601d60b035140c28002107811030 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 384870980 1250 384869730 384869773
    0x105090a0c090c0c0b07020f070b0408071d010b0d090501021206030d2c0105041203080601020c01090b0a2708060405070801090b073b04110a0c0f081b 66
    0x3400001040704000c0c503c0010042003107a940503241705404004184018800d1081d924000c4000c011924a65540c5000c0c2a075030b40036101e54a0b15004d07960010400e000b22484907800780220144e86002c69003841c0c504415075000c120b104404c242e80b20959800170702c0038006004070314201d10040526160031810b0500740f12900b4255000c02190080f00c0035031203030400b043d42d0514111201e10940c62071501c010f8030070b0b114640102503544440015a01010307408802e05100e42000e9080c0d65000303500c00019940340001340100603894030140300508006202c3c0d810745525000c0300c040300500c1d0306140c134040c1d4442080e41158080e604407004000c10310008105c000c00604000c0c00070001442c85456121080c00c0150842c2c04028034095490f50b20f018015032a2140c0f01c8158501349610310162008a007a100c50903c01e0207241003200511591000e042511300c040015240c2424902c07066550300c40189428901711520780781444101d00310100205800740205442004201c0300d20b210b81c4040c0c0d0801c = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 384872230 1250 384870980 384870989
    0x7151d0307080a0618080309030301030303152103021e01060f1502030403141f060e0601030603080a050708220e0916050616060f061d06060702010c020a03050105090a0c 74
    0x601c01882009100d0000401d241d429401c0903001030100d80303012000104840d285400f07000c41d1030100c103202400801000846c1203d1080c1c6042280700d002201822a24140b481240c10459000d601c00000c2c01d5004480d50359180300e4419180380406401440000340f41c2d1000c5200390360f5481405004246c4068100000f070420f00240308800e030f54280d00203549120b03602004054400381c0c0410490900f0410901a68480609091010680100b1108001c2080e881307004403424000c00410400d500911810041d65000280325250180c2d124064400342e01c03025040700c103080100070b40e81c6001c450030781060a0340880e0040711507079854122183c41c0e1000181103111107401140d01c0900c51202c80b01c200080301e106940c4035488031900081e101c0d00e060303140c2c00606258104100a1030b0301001c3c0d40800141c03a42c6100321104c00e030402d100100003007002c030341143d0001800c0006d00095802440c2242da20741c07004050216060300d0760b6900d801d5650594004105502c91903812080040f1407680c0400781 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 384873480 1250 384872230 384872233
    0x4e0602041e030b0a021318021305012d0c020303070501020c070f140112020d020d0b010206100608180c060d090b130f030c05010b1005030f0106030506060f0c07151d03 73
    0x1c0d05646400300302c0c15010385510211940000c4a202d5540b4454035640101074080100d04543c2c10300012801135800002c202d1161b0a181d0400f1a9540c0500c50750920b43c15a08801c0c81d81c03c0d1541003905d40c20b130000000304280802c00d1895001650b0030401000701d903104034000768036048080d81c1c90303261030240e4201e101074580c202c07818841c03402409070080390802c007480c00e58481484261050001d2040004e02640e5500015850030207a0054200b12040d5000b0790840e40c05a551140744008049913025200c00907119001241d01e18011149500c4d004054400303958603412810b000600c640d00c20383c81c0100150f1030301c03034110078807805001c0b0a5200d107452000c40e84100042d62620114200003c0041c140840a9600018000250321130a800740c805803203200e19a540e03c00150454104990714141a5103c0d4008038143e0702c41c3c02000d0203100054501c1d801c100c041c002002c0190006440e502c883c3c42503c20014200e900c040110300204000d0311a81c10380051007400102841070a88468000e = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 384874730 1250 384873480 384873539
    0x7030c03050f0c01050d090204110409021206010e0f0120030a110615060301060f0c020307080a0b060d030c2603010b0304030e09040c091a1002060708014e060204 71
    0x6690704603003100c2500d1b00140703002490a142e40300040c000e101003402d80c0900b040208010855011550060010800142540c00340e540d0308801100c10b03400c0c0759542500015145804040c44d40100214004100d415102000c0b0b142c030800450300d140c12665951000507410a4011600c00d001d000359600510611030140400300c00d0340c0841c0b01484184649000c01450444803c003080c880c007500303050a6401400d581c201943e6040650380e9602d00e40e41590720354a460085001032401c158134640da1981500c50128600715902c1d402c801a04402102c5020315601680401141c80703031005501800600d0301d807545034146401c00034450040c680c4450302801c1c02000748000300c0d50f409941400c4a0742000d0110700d502c0100500c0100441184101d41c01210000304c0495040c0c0214500344110b529507240c9169a030f882c1e012103003c44002c510b041d072150202804807541c048143c1d19000390110a182d02e84808080c0c2c051001c1001e4807441900c20750b6000c5000c3c00140124940410102038030780d0b07001c06 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 384875980 1250 384874730 384874753
    0x72d0e04080406210c052212060e03070c03050615090411100509040f050103031403070806060a09030516030212014d18060f121807030c03050f 63
    0x74284194050402401014440030b081c2c54480c13581d11840410b00300c0300b402280355001c4081c2c41c0d5080034451b03500290152071103001404050b800e0901702e61148408140d4559203850b400002d1240c2c00c003440403030104110460104844580c00c4005500c1500103000c1031400b090030044640b000404540f0626400041c0310100b0500340ca0584410b00c1181c8245502c1c10001060310f01380301b403101c26a001402d2980ea5244002103501441c101e9009131034071f0b0b00600341404000c88900c41184c5c0302c4040341c1400c005c201e0070300b014400b5018030421410b21510301512500c0b40d41c6071071030402c95250010350640083c4210300b4840400c0801e0000c0340024840c000101d80c11401040710303c40c0700301421043c043c0c80304a58400202c806401c44607180d0000311a120280c1c241501d03071002009400040c0100381003003040c02d0107412216004550300426042111402440203000300180610344441400303200c0320803401081c00700900951040040d50003862540c40c0c600c2c145071600704020600c0c0c20800d400315 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 384877230 1250 384875980 384875993
    0x40207290a1a0907030c0e0a0806011a090603190b09091b060406020d08061314071106010b03010306051b0409090b0a06080613030203190e3f072d0e04 66
    0x26002101810040b660400429081f10f0080e1034510f000e9000f2101c0034001790810700031a8041c165513108441c010340c0c0d0100140a1080c0c07284c000303400d070000001c000048500a44c00c005504d0014081d0010401c2c0b885280000e80c2100180d4005074140c02c0000440d600310780004105590460030f4840500741490150040c1d1601135108108040c001d041000034007590f03c60100d40d102c042100c3d810841903160b0b1041c0c182e1180c088500c6008542c0c1528000e40c5642e001400318102e40603283c8482c910b80c00e540d84d00f401f50502801d4a800a032078281c4400c50121101c01500141040180004512409003015213120001402802407a490240144807518003c1100b40c2e01607281c2c00c601c4001c0000345003c03483e40c80343c0340c0c0752540000142d0b41c1443d180d82c40041c00600704411140403440010b00710141c0c041c404151009000000740e410f407400d00d40c4028680011280d00d0310181e4000a940724880700e00c4c3c050500e8440e98591040c942040c4036a000328401002e400700003111540b52070b06540340c4 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 384878480 1250 384877230 384877249
    0x15110d0218041e0b0111100b030d020616030207050f0d0302031f0506040b0a12060e0604050a0e1c0c02060d090b09030708090904062408071202010509040207290a1a 72
    0x50348554079082c613008981d0042e0030021501844004503900500c0c1c0c441c2e440001c00407a444a8400c2c02040506081c0324400a8900d01545140c80060414020010705500a501190044401c1d000c0c1a20490079128288035181507000c2a031405a960302e0040134031041c01148114800c4805041141846103440728010b44040c6d1f440701c14619602c1116120940c2c40944803100034070054106900400e085a2000340c185c003a50341544c1c280856102c1c1c14100d070584814500000e0580c0c000d2116038004829085505012000b40c00d08103410441500803c0c5980d0004050403402c50f2100510002c1102116400c0d0f40701c2070341000785040092079075540405103e0002c1d4188a8104400414280700c0c10303611240b0040184c2244500c030110b080c0c90141d07443c01d030340304240550113850340c00941000300c10f00d182c2031030f54165980c910308500728042000940004006540002c0415500200600145450f04071080c08154500f854541400b4034010340e0741c07d135a4000f007040300c05030440007a150401d01 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 384879730 1250 384878480 384878531
    0x5070c030c0b060402040807060906030f0207111012020d1d0721152d1104030b040606050402210105010c030c0b04141605011709060415110d021804 65
    0x102c1441d0f40314030001401074012504078030400d008400000800e0390b00010f65404941042d00d061011004075a02c54089000306140600800c1c0507c00d40f6140d8034001c88050801c88050501a01d4407680c1c241000c100d800002d00c1d000c91542d181014045111000c14003c04984150010001c01d428118110301c0c00e214400d40080a03100455140308010b060840100d030141d4000c0200604002d404108662980c20000320f4400f100e10070a07004909414017400036030804521015240a145998403808400c00400998802c0d6036803801182e02e50340c03400240322202441482403800b010219848105200690003241441500d40c04000020b030403c01c6040301581020300141d1a980e42c1c01d18511031903002d2160503031401003902030b108200300141400141c40086e610382c1c0e2034280890408040078001d81c1c0e0f942d542d520000000b000200d846520038481c90304900082111041e1418064031170b00104d15000c01e03d9008100001c0c402088042c0801e00c2c5400c41e01480000032104028040742d2080e02c5 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 384880980 1250 384879730 384879743
    0xf030c0309130f020a200a11010f110a0516060305010e0606070f050709151403030315030a0506090304090b1f030e01060b030405010e0c03150708040201090510090905070c030c 77
    0x2e079005040c206a1050301c4410f0480002e6641d8800c0040c000c0070a415107441503c158404942c101800703000040e00c0340d845a02281640d02401c00600555903800500c2074038081105184600e00c041c0f10a002c100e4501c0e21810060186a000840c1d54442c80c5664102c1c0041514090041101c1510300c1c00c4190011426600c40381d0356030050a00908110030303410080c0140c031a00c600000c154486620040c04ac01c440380028410320345580e4a01c034015603504443c1d5040c0d00520110b090002070703415826802e0300041c02c41e1000c410f681e03200f5007042003c850750942904041002c1098496601807840c6140c000c950700060a00c40d4007842c0c044080c401a404100b541d81c0914001403142548481c0c081c4c210f0720380745d54072494203103800f501078a4012007100c005c0c000d402c90030b900c0b03060005565468100c400c0e00d55035541c3d20000101d4135008024000d03410800f8501e80010552503211010700d410800303907500e00c08541013180c0742d403d8400180141040200c4800b10401103540030f40d2500c0182ea1245 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 384882230 1250 384880980 384880999
    0x90911040509060f07050f0f19020c0402070201020a08340308070e0112051005030f0f10020301030b0103060c020c04050a02030f010b0a20010f0c05070507060e0a0e1b0c0106080f030c0309 82
    0x1f4580c15813409224a192100c450015481c4441800c4108090300c0c90402d9003141c0300064a1740130700003640285d0030001c0c09a8451613448000a003114040c0038504030286c11030340f03101002ca400c4898aa03d451412400c1c10202840c6414164010603040e44480d150a01d09600d256140000740300900b03100101d1a2255110003044c075502d03003075101400a01004003203c0702c0c0c034440e040494035a107081c240d44000e1f2048007124410350070103000b6a81269042440c15180d03071320703503100d4102400c1c2190b402c20840c000c034088400c0c00d03603070307482201e010300c0c28500c0050300d0780b4000c004811000b0042c0c1000075200d4051044c0203280c2c0d44400d02d40c900c4100006030441e0380b8511041580540400f5030501c090301d01300701c2610041d41c0e200c0090502c06009000b180c0c2601da60700c002b903603042914508543c01c44c20124007444a200b07040c065540011070a20030601d40000081d402c01d43c0e0700003482d40440c0780d444160401c28a04100001c540070031040700036600d00100c1815180e942d100b503100c030501811606 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 384883480 1250 384882230 384882247
    0xe0a05040501090c17071719060e030f27031b04060b030403020123060a03020d050a0b040503030a0b1801050d020a120302062e06080c04090911040509060f0705 70
    0x29049140c1a603400b8006540840d1a1411702003032000503c186040380c45010b00c0000e24450103103400403500c400078040d002000c00001c40781145040d405040d12183d8981031600300446040005001d841100c6941640399010102e04400d0556586111004120140c0c0034090a40c2c020444042d18440ea5900ea0341c2a078038480410b0240106510115180c01c01000300418180c064100084080200e4228011482e035545580200341040c0c07402c03a0054540320b0140014203000000006c00e40c059421a15514600da541142c40a81103c080300c10b0381003c020b00c5501d0080e0300405041c000100e030220300c110100b4811010300001403041a01c01d0103170303030b842d40305540302c5400c042c000d4444003070349480d88507144c200659242c106445080401c0c03044540d0290310b02083e01c59900d018102160700304847d06d84102112049400761101008840411000a000c0101e115034000c95101c0d21404991400044c2080200d4100614400c1079402150800c620410b012809a9205489040c601d489080e03d = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 384884730 1250 384883480 384883483
    0xf0503040b0a1a0618100906020d0f0302090303160209150f0409020d02091e07080405031804022a0d08040c1503020706020307020a0209091204300c180203010e0a050405 74
    0x18410b154101c800056901d1210302e400c0e40341d1700700c06815140d010110007200e0089640c1d070300c81c0c030441d00143c008a0b007154103144150109403901c0c08a140150034000e0000c00a425644462601c055064403a0f00038030840c00c14a40d10740d8420400c14045810740307200c4e004180b2950071440e511340701b2551030341343c80c0c1195104082002103d4005c0c1030041c9502d0144000803505090a0403021180c81820000f040300b4031070049188900d5000c0040c0d4101244071007911810403446201e1540103809104011464035101c0c00001c0590344414641c50003072401c8062810300640031090b40420101c0700030440403d040360074200c01c550020016048050241c002140280141c010040001e130000040c061990b1340024650400c0380200c5003226180c40d4403101c3e942e1030200d402c0214826806000802501144202400300c12407009040001c010004a0b0200e8159140300100c6184001a03001d1001100c044010040004d100200310701e107504051801030001001813081014586510009082020 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 384885980 1250 384884730 384884771
    0x103110c1e011a0d02010e04110d0603032a0201050c0304030b0a020306032b11210c06070e0f0f0111060a05010503100b090708040c23010f0503040b0a 66
    0x100240c5407802680c058107040d804154480703020300d60078242c503680041e00702c54408440c600c008200741a050030580c010b46420074001c90403507110f42c0c1c540c9142140b02d203407001045400f40107071002451905500c0d01411080410400f83e00c0111030701c2c817035404440010031300321416409080c05904c48803c1c4100c9891407203560030080c0103c60110501418414980266010b00c00031426603a0806040ca480400c14018481d401d254060b0b039054030003c0c41c018825003528040400565401c030146084080d81171042941410750724000242024007071005000c4150090110714107450003180c07140c001403118a5550545104400d2154050800da00507c0764482083c03802d0295680c52902608500007808240300d8580240105000c1c440f5240085c0301e41c0c0c8e640203008011801d962218402100ca010000304100e402c0c1d820b1a4000c40c0740ea5168140a2800c201c01e004940307280708941c0010000300701c00c0e207481c1c2880014005d200c0001e04050134998001580359001031030098510100d0f10503074 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 384887230 1250 384885980 384885997
    0xa03050f1c0204061d0a0306020904090206120a05011d010308090604031e030305070c020d140f2b0c0308060d0201050f04030605010914040c120f1a0402011806020c010311 75
    0x184580400a0a0314282c0141007244c00301c0d00c07111648030241001c52441d20400ca03000c0d134881c1e940d040520015501e5405005500c7d030180c4000759261090703012034010ba0144d8042141480d00100301702c001d410b140242805098021a07500b0b80e02c8070840b0711040c400041c00300412101c404540081c498030f40c43c0c00da80065800085510fa0807500041c640d01481c17241c0406d038002402e14001030310a80c01088491120395001d84800c2052b6640d80313400080801c5018100d216004903a24507140c0c5108201020b560203c3c031340d42292000110a140466120a20b000030500040329000004a508000a40d9101c40d007610f400d0b48002561004031660300c9058003040c88010041408024080d050340040c1c142c459000e810032100240306071410380903208442c001c01c0c803000c451050180c034041d1412042d40e039129441c1d9031030502d0300e07075607800348000c140001f104410040e2080006560340101c0805040002900c490032282c02c0c078070000e40f01d101c4070b40d405040c503440f07103001a20003404004070f40020 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 384888480 1250 384887230 384887257
    0xb2e1e0c1e06020307020c0603060607061808030c0433030e15090d02010f18021009031703040b07090312050a1404060c05211605010e011103070216080a03050f 70
    0x51249006002500143c50341710052040480e214460700300401100e0080c02c000b000a410559580da412016098031303c01d1480000070400c1d5040010501c40255010302c050802c1191224180b4403d00a00700c1001d400980e60004000ea0138420040d0410b541c0c422021498082404021045841d2800e46803114900e5807108480400040d0480400e10380d40741344085c2d00a011950011072200d05603035149502c0f0060000340d03002c860041c03030f01c1c5208544203582410202c017225a251202e8414150140858070982000010403040000280c42c80742d024a1506010340c0207411501d40d000c2840d8000241030501034002503d824090044c2890960b102854641f5076460b81c481c18003c05920040707400700d400e40704820f542108411200c40c051807203000340c000c0c6410107a40544400c04089a03800a681a55803800121032a410070f0154001c01401d80d444c03e540d86c100080002c3c03400c07217038416a01c4400150102800210408100301d0000da8040ca041d5454011801c600d0200b84600052040e05 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 384889730 1250 384888480 384888533
    0x510052703011508060a0b120a0609060f02120c09060d060311120307032106080a1b14060301050d0507080a030c120305090d120b2e1e0c 60
    0x24668104005610800550080c00b03410f408092480110500380503018254000c4d0b800690b0385103495102806824009180704100c5c1e034901161803c00403443c009542454403111480c051003858001c101c4000004081180707013140d250004040504007400300c4026000024a48440b6a1080203031014032014880c10040b440c0d0740e180c034000c5524140c54450154980001c0c5006a580120941e603002e601625680b4404450803d244188890007c094060950352400880d019500304040309620388140803e081c1c1025403103c400024002d54050000c1c180d00c2500441140c546c801640c1c11140280c4400c0090031302d03480d21600f0314403a90828401e51144100000074980d0291501070349a00461040c07500854040b0110242c07041162011510741c841c58001c09c005100344ca52100c802ca0194000032854003420002d000500300c0381801e01c070340041030040c014603550000c0343c51b1005032a081101110740007103094000707511000010010b00ca0780c1c8444105028002001a608900e0368000360070 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 384890980 1250 384889730 384889777
    0xe011d01120f0b090f0c040e060a0e0405030c010608010e120904060503030c06070e0d02090705030403170705070519020319150212040b1014120f0102030702030c19020109051005 78
    0x102003060000c1d1203414510045280200c0002d40b886c02454061202450b082c00c00a030400c0c9848081d00c42504480b858500148212004030b40d0350081c2e01c02c901861340c0d80041d581e480d0030f440c007680121110380d1411352110054076000410908141580d25220b442d0f64038040010000c041c59480b0135054000045c0050468801007100d510503103850311204c4420b84208180005a09103020007500a440389001c01c402c50b010b440515405407007481c00c0900c402c8000007110148109840c0301d4003007000031540b2410410180041d000111410030a461102003030340000c0d980d5081020040c8104113804c0a0781c003400020742e42980b200200d55401d5641d5802d45d240607514000c0bc4805899a00100e40031a140700607000c490300031240619035000303030255040b040161014004540720300c43d224030340c1f214440c00c2081c00558498040c44d0051070721081030141850810001c0340c214100f10740c0e00e00d01c0f500140e130001c04c528103640e01500e003102c0d400344280301034a030303449034040103803c500701c9608004 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 384892086 1106 384890980 384891011
    0x2406060d09060603030206070215090705060313050d0203031b280903300807020604060209040608010f0501090c02030f0904090512030109020403050d0e011d0112 71
    0x90365a220b5518081152282c0d40101c2c09a00510100040c558040c480d0122103c01d00700317241c0300c52805281d05503c954442c09884d01c242e00100c00b14000c08604036160400342d03841070856121b880003001c080d5a980003110a492001040200c020085400d002903800001c5040e080310342c48460210304107c4000320400c09000c02200c1600000426905c24500000441c500501806c0076440d0940042c540e0010b41008140102c110034818a940c0c00110254080d410200050315182803030001000342609500181056003466078904942180d640441e0486416410402800854400a0382c590180c0010036018000c01d02c00403820741007a41001c1c0303805100700b0568910101c076034440301c1141c00a030840700310340750301007401e00800c00d0400c038205683c840e505000300a545d40e0400200075200f00c462441c041d15002003921030f50f0340a0b01c002031480203100000d00040d065040440c = true := by decide +kernel

theorem cover : BRFrame.Cov 384712230 384892086 := by
  have h0 := BRFrame.cov_init 384712230
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384712230 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384712230 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384712230 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384712230 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384712230 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384712230 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384712230 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384712230 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384712230 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384712230 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384712230 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384712230 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384712230 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384712230 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384712230 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384712230 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384712230 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384712230 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384712230 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384712230 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384712230 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384712230 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384712230 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384712230 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384712230 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384712230 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384712230 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384712230 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384712230 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384712230 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384712230 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384712230 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384712230 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384712230 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384712230 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384712230 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384712230 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384712230 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384712230 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384712230 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384712230 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384712230 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384712230 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384712230 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384712230 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384712230 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384712230 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384712230 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384712230 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384712230 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384712230 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384712230 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384712230 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384712230 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384712230 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384712230 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384712230 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384712230 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384712230 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384712230 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384712230 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384712230 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384712230 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384712230 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384712230 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384712230 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384712230 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384712230 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384712230 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384712230 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384712230 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384712230 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384712230 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384712230 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384712230 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384712230 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384712230 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384712230 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384712230 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384712230 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384712230 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384712230 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384712230 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384712230 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384712230 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384712230 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384712230 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384712230 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384712230 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384712230 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384712230 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384712230 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384712230 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384712230 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384712230 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384712230 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384712230 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384712230 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384712230 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384712230 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384712230 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384712230 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384712230 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384712230 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384712230 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384712230 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384712230 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384712230 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384712230 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384712230 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384712230 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384712230 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384712230 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384712230 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384712230 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384712230 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384712230 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384712230 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384712230 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384712230 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384712230 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384712230 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384712230 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384712230 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384712230 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384712230 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384712230 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384712230 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384712230 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384712230 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384712230 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384712230 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384712230 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384712230 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384712230 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384712230 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384712230 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384712230 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384712230 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384712230 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384712230 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384712230 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384712230 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384712230 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 384712230 ≤ n) (h2 : n < 384892086) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
