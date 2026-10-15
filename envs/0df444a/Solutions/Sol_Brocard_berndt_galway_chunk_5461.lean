-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5461
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T15:56:21.063325+00:00
-- url     : https://prove2.me/submissions/c250e7b2-a268-4f3e-99ca-a9107d2512d7

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 982014388 ≤ n < 982194244 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 982015638 1250 982014388 982014391
    0xb040e030901031e1802011706011d030312010f0609120c03080f1620030303060d080d0f150801110705060105061c05160e0f0310020711060c0a050c01050a08060f0a090c0503040b 78
    0x821040902302000801e076403000d4040d21050817102001400310b50200401c0c00e621440441a440a88010011601a00d0403422104a5245644440f5110740d120000c00d022040d0460040400d00070340d80410104204602400c0000c203c00c4026240203110b1a80200b403070721418003250844880403841c802d0b240b20f40840990004181d01951031840c01e2000614403010358100201241004038010328001182e601070900c1c105800f0301000010300e0b10f006034103058024841c2c0600da6007003e204000210500e8195455140d004e0014400c59081c031003040240d4100e651700c2c04041304030708200b10f0000941d026041c05952101c410076100e540c5a28000c208800710301030140503030841e0042c15065100040c14603401407000d900141c80b400545400e001c61100d40d5220382d84458042031150342c040e80400d241007403e105408036241c0102030401900c80d401042404400710f6803036400500c00d0709244402480c0400020b09041450f610340d00d0342c0080340c851aa00400050000c0200001c000c0c0c00140107 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 982016888 1250 982015638 982015667
    0x608010617070c051921020307030f03090201170c280c1e0203010e07080d08010b0405040c18120204051503060c0d06180e010b040e030901031e180201 66
    0x151107442242010305104001402e814100014a125482440814002050b00714221450381050b0b0a4500340300013001c01c940725000442e5096403503140c026000100301c13000240c1c16254482c0c0b00c90b01030f04c107074003c1046000a03070603c00351780c1c40d820303028102c2d4120f248510038194041d62180e101c48150840c400844c1e010040603032004076044112a001071940d90f000740e00030555249003108258030040500d01d82e0000303402d5800d208455030908000b050b50815103600c41c08039036004007510310458a4401c00e00c100400d10104010611260038150454081c035485420900202500c00800b5103009415512024444004c80700e64400c61a090003081e401c500ca458040284511440c0000e0b21a03601411f002c00141001840541c0b42e006904420010100c4a00041000d56007883e818041e01c828000b020a651a1031b40c42203161405209004a0f414404d004504041e10000154018403407089100190110710802201c82c00840c052500d0031000d4052400340d058580c4005401c1c106903e040 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 982018138 1250 982016888 982016897
    0x30d290301060612020d0e0307060b1002010506011b0311060117100b0a0e130b01080c0117070e100905030303041505060102030f0d0b04090f0609020102071203050415180e0106080106 80
    0x1c00040360b105550134418501e4060060f035400c61801c011000306142032041c042400007260b01c03020300c100b507170210708480c005960007071110702e402400b00d08880040303d0007030110710480110903245c0000c3c40c200d001a4840d051110784968201c10080c54000241e024610803004003d80c0b49483c1024405e45440d034190100034410300740c1c1d030f0000840507409402140c402910303050005018079600740038201c0c6944c00241501c540d58460a05a0b03c03401000e004601007100c9c0031660114041c070000c10f600c00d00b250381e196507803074040f4020050501c1c07401c0080003c200d6488404100c2d030703809200850080d441144003111004408001000342c91300280520f05540090002e00030003400b01d01194440c1d0002600011a103aa680000c0c0003000a00b0024000032070900d034140807c00c0c00d07480b03807108900176021500415601c011000180815080050000f00140410459a84404c40d88058280141421140f40c05e200c1d500d12404905071344050703200742403c40101b20b407903042950a03014001500c0c1 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 982019388 1250 982018138 982018151
    0x1050f07050a051e030f160b01030f1a13300e18160c080708030406050a0e06010b090103020c011b0f030b0a140d02010c060f021e0903070611030d290301 67
    0xc070304c0d8a90042c4030354504e19500004042600d403030705007800e841c91640020313a8029075840b400d120040360b03014182260070407101280700324a80915000c00e8820240a4001210b8599558804140c805000100758203400401150a800c40c902c2c0c0d103502c00201c071582d4500f65071134120200000b00b01b04005651500c40b03080700f408041941200618081060b905020f68043c2035458070b01c455201e80c420180221788044140810089541c2005004583e6603074140801c806264405071100d0081c4186050301c0b00c1000401e85a502940107440f21500c841c0002075201c0034045107011421001302880009004417002802c003d4252080241d4400256981e0b2110b82c1003000d14a01104481c118a00c0b074160300342c400c000c5a1140f880740f10542d43c480024800e0130005007208010390071a107001c40101c002d04404428900c00381d000e0710040303d4020700800c80b0344e14281c41524070744c03504040d003a014003080140c4c2d20914068015032007000302c030510100655a00c80346400701c07040f08101861083c0d04082 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 982020638 1250 982019388 982019443
    0x30d14040b01050607030210020a0905030d02010506031e0a05100212090106050306040f08130605041d06090402150f03041208060f0901030b06120f0d0206060a150c0201050f07050a05 80
    0x807180d0641d442907428075a15401800e080e031901440e010014019400080d0040300c13280c2c0704081c8801c64000340d00b22004c15410f08000c0c0d09981c5c0845146801d0f60202020050a401c03446803c65000e610b20b00fa104201c46944400d0304080082c09207216581d0001610319402004005d80380e8001c0085008100c500e060000094541c0700140010301403e90801c4143c0512140c24221245002d1482c40302c03202c0c0b9984c030009130250300300340f01b03200400d101c0301d025600b04c4c5d001040c040c1c41001c0c0100b0b41d41c01a07660342c1c2000504406905076403119403040c4050842c40f074be02c5004500903030003001c0c00b182c018000d0070010701c2100000d1000d0301510b0f4115180040340c84032581d080c150784e48002c01c80e0259543c1d4001c01c2040007200c43c001c0315803050860414002201040c01c0d00032454550943d0032681d269010301a01400e9445588805109031034a04220380c0f01d240c050480b184140341c01e52419450b03009402642e08810b5040c0c502e40c10505084c010003108000403a0750000200384d01282c7d04100 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 982021888 1250 982020638 982020653
    0x21e04150804020402040905040b040201081e161403010905060316081c1110060e0c0c0307081e0d020c0106090c0c110d081b070b090f131d030d1404 65
    0x390100052022880200b02155600d405982c0070781703800780040140c6e140a052072664410207a4050303001c81d282c4808035440c03002e80c0107032041261100c6010b41c101d89a85420b18800100300c462142001408161100d0020131500254003e004034000400c3c1ca0900d2000c050034014410803136252408401c2040041000c0450005060f0030296a03090300512001800d490303050b0f4004c0d5a00303850103840c0064004845c264020701c01e40c0c548890140703107a44e83d4041d0300e00da4030450401c0d16840c1d009010000028410400822807000c001a008100341802c0720362440300e400001e2001002900440d020702070781000d105401c000d015031413091203030342001d11b00034004500d00d0201078041c0352041a0790b0b4423031b1500a40720301d03a02d60007016070f80e44800e41c01041c403000d801c0d0780c03202c0b40b180038846000074500011800c1c5d8610b000d0081c142200210590200130911004403400021144c44807234810b88003507211a198264254034010b550b640384440c1080086424400e0300c24070483c0c0f990180008a800c1 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 982023138 1250 982021888 982021919
    0x2032508060a2904090903020c0315040f080d090f050c0a0f05101b030c02032b030b01020a06241a09010f112407030e0615010507020a0801021e04 64
    0x71050300c1800c07142c03103d001014091541030f44490341c0c400020005100505a071008483d28041d46c2901c007000080b404140d11b07207030504007103400341e2621404603012410081441c04104c0c4034131160707441d040c22220136034280c4050610564801030402c0e1482d05009090216109103202140c1100106080880d20060000c0c0c60098a00440210001602032030080700c3c2543d0200ca40c034080d28040c404e6180041996401403000c0b80a80981004c1500a2500000040d2914000203402c81c000b10451030407030081c802440080d0451041c00911004200d05100d0010900760f401c001d107039030011541c08200c1100c13165001014041111100c035880411940035100c840c442403a0010703240b242d0312421118524a0780108400d401000c0080780b144591100940c10681c0320001803505a586200640c220758011218030842c0c2c204030300298900d810fa0310084040081418800c1c01d010b00703900031030441c85050b080000503a500203892803007a05902c2d08840d0780c00e008540c1914003070030f000104d03056590 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 982024388 1250 982023138 982023149
    0x102030613021c05190b030a05060f0417070f06050105030c03030904020c01060f0b04060f030e0a030c020a08011d07080c060a260a0c080c0c070e09070902032508060a 73
    0x9001c0f800b22003096800c040c0e90129402902d040c4651300701109016080d8080c1035030b0040051030f241e1003000f94100440c202c507000360440d019028640e1240c070513808014000300100e541c20041d502e046e040c0f01a0402405150b406415540200040d5203444001c644041e00024071991004c0d08442140d1f074000116030400c6000c1c1c6000d0384418490000c00e015000d280c01511000c07084c000023140050048000c0c00441c3c40304e95901c1460550402c06504440002a0310384903600000a60000300340030b081026900e501c09401c0c84a103651301c150440c2101c01e50500d1311100c102c0802800c8104070108400c1001e0401680503040b002860b50000c3c030785100740900c120a0044c610102c141c024042210411040c5400300c0100507032500104003402065209411307404241c0402c0072071100048081550700c0201541c0084c540181010003490704064010000240382c13254480110780708400380061030181c0f02c00627044040002c445401c03030400b80307440c3c3c0132401c104c1c220041080603a030300c00031041140c0c3c = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 982025638 1250 982024388 982024391
    0x3070f1401020d023004091107060f152c16030614030d180b0a1715032116050f0709110a030504050f061603060803040e0103030f09030b01031110020102030613 70
    0x4408048000c0da50186d0b6101b40e8900d480d1503e8034a403c001c1000610390b00d0f100c0d05040080701800e0700302204031080c500045900014465080c0a4449136a000429044501609180c1c100909190500b401c100b100c56080e01c2c10080003002031540c150042801500d540e9000d598400340c0d120100f95141c4404442101704030b401185c09284d41c1801c0c40d4000a40303800319003980d81d1802818007510761001480b150780100c0310720b800680b50503440d00034641a20401400b0301401c1c100c1d2030244074900f103d506030351001c08040103003007040521415460b400310711640290607000c8a0021603030904229030700c09000c0728181810741c14025445000c8030f1440320913090016158480c0c0c02d0030741c60705504100001042c86400f06006501401c5140801d60285954041c041140c664480d00c1d164041c074800c01100e42403100050002a000d8600b007046a20242391080740181da0340c5410080b041c00f0fa2041d40c950031080c00c20040d50411500e40040401d02e030009515605201020a444569100e999400e15 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 982026888 1250 982025638 982025713
    0x4030302070c030506100e070825141c0e0f0d030c0e04020307180902040303170718060807020610060e0d140d020601081c170603070f1401020d02 64
    0x80d500100b10b02440d0820111400ba2511031400181e0a404e40a115060f40c41d80c0d0000390924480c0c0002e5100344141e13000d1042c9941c400183c203001800307020410381403010388aa454561a802006401c0c03901812507000040740004001004403400c00282c10025004051011865500002c04e98a1044185800103000c07a500b40300321008142966000d6100e4000004c1c0b201c000d40c4031510354109004001e1a651560350348407a10100c3c407a034440280441c540c5209072540c4600c1103420759003c0024245202c0350001411651811200c1350414004606590244045654104181d9610850014103400000c0c14043d001c0c01d8801c52289661085942c92882000c01a803840040c020b010307c1000c036888188120310194440c9800d0007241d12a00c9414012100035074419401051088203854084a00d1848640e003498103000a00d2a0b070148944280020050007440528000744013441c82c4ea404441c81400080c145101000c0c2802154403090341c00c4d8507010001001c09001c0ea00701d80c6000d24 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 982028138 1250 982026888 982026893
    0x42a0302120f040f021f18291e0a260109050a0b1f183c0914060405010e07200d02030705060702030f07021318062c060403030207 57
    0xc036544003802500304014549040c2c611440030066040c1c206c1c2d5490390380c83c480b1031504035580e0440c0c0380309030501e001400d041c0001c09854118030a03080c0301782d508940d01d00310300f03954980036000d5011b01c134942c200e60010b00306181640c03180700204e0001401c10302210740814031012900d2100180140710000381d031a004140ca440050340071401419014001c101400c04207948d10300c03030b544a248002c010135801d090341080440d03540b00300710603151032645002442c00c040100b20900040710402c480d14031000d0600c0c0c8500f800480c400c2c1300900c41d101011441071800c10815103c50f81c068a8180118145001406019441075040303500c844149051042440d05010314410003400000050490288001c0d1b070500d1a070110080460758040e0040350300a032a0001d00300e83d28468820000c145c80300030301000700185800304003001003101014000c141d2210400d5800800300007488101c408545d00c142c44038481810840c12920103c807100308000342560b29008517181c130402880141010b500041d040c04 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 982029388 1250 982028138 982028153
    0x6020c011d010f0e03030f01090902120a050106090e16210b0c04260606010e04020c06150f0f0a0315090b01080105040c05040b03031215042a0302120f04 67
    0xc114900040282001129000c642c002d20b411540d0604090600c0326500700513400204590041d00418419010303603190806050040201c400201c1e804010482e48a1506008008d15000a40170350000910326240001d807070304403020800c0e098000d410002c25a1159201c10000c1c030102c1e03030b5204260410001c4024002c0203442159001041c0080402c14004407244081c0a4001d82c0d000705440349009160740840c2c024100b0b80360b440d0040b613200c60700156841d4811007101038444e801410250600c84880440380c10603030101e41c010084404c0c42c202c0321540c903180c0c1c87c040d11100261042d05009850b90046820138005010203420b520044107400d6840920341c0c0068403042d00441000c40700d58589183c94041d00d404e80c2d0640f03039241021130214180c80d09105194404a0040040d0701c1e0191a00724a2103a00c0300402c10b4217131201804400400762114000c4403d44042681c0c51907664000c85d070b1001c02200000882e004040c41131141c680f404402c00c542c42c2e0001801a810502c55446140042 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 982030638 1250 982029388 982029401
    0xf11030102090d0f06200a110a0206031f05040221040f050a0c0f150e1306051905011409010207030807050102040909140c0d0512070f08040b070b090a080706020c01 72
    0x1500f100b103089030102030040c000c0306601c01e41d2044c4d005102011048020303141d507117144010505500410441521514094a070b132540c80720011042d00e01604054000440701c4d04202e440001606442c001c5008018000c2038103c06004201c50441c102190300c06004a080072000d000480c039282070340480c0500109000b0007409076480700440b07100304a10703e000c8028105910424a0410b424600402c0c941c61207043c10426500320b40d01c0f0102003040f0f13000c00070500510318140200f29901c030b02c0422262141307117081440b481220004000140380c4800144138080c00c100050f85400e080c030450039107071b90101d00002180d41040065841c1c0a281c00c0c120300a115507072152202c5850302c100b10040000301a0541401d81c80766094a9941c4015400d104100c64000300040c9540c0248072040030040011028040da41d0280d101002401001ea03a012402c1d03110780c01c0100c100c4404071380b4104201c0c4010200b540400a00081d0503203c0280e590b464075805070f4500140320b603801040c007051040c400d500c070a = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 982031888 1250 982030638 982030657
    0x9230a0f0e0114100c02040e100c020c030708190213050f061c03230405060708090901050102071215020906030a0c081e01090902010e060a050a0206130f11030102 71
    0x1400695940c4016203036051080c8103400081106800000789942602507a0700500300240080440b02000315049480881c9040102c1e400b5941e500d98591007a803c000f0202140300f200d0000560303407000c4201030310700098120b0342c40c403c3e071116006114400740452454080f400e00307005014048074a100042040101041e032003402403800301000072400c0c0196509019000a81d02c0144844071084220a54100c01078058040740560844e40240b24001c0382005100a5400d45241803549030000103401d90700001050ba841e21002c12013000f6443c1100000c0d004200074001003010914000f80743c0c0b880f9030503501c0503201c203c0328558880541110f0301101c6030700c08020140b507a0ad10b0011620401081142d108800203112600000d03440c0362603007200f2681180c414841103840e031030124400082c19400c01f04074100b055100d5001c0a58540102500c0380c8503481e2a0f240d1201c00c400c00c002c3c946000207080c940b1110f21031001c4404140301326a2481c04640121000749075040201c042400b920512051 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 982033138 1250 982031888 982031899
    0x51c11060a140a0c1e030f080c09060f07110d1a040201020c1206040b0a111c020f04270603030f0e2e0219081615060b0315100923 57
    0x400d210a0b070302a40f20142284104144004808040521964217148420041c0401c100810300808207014040c2c4942c48280400c1541c030700032500d404154184c000c3c902040000030701145200821107203c0c003039541d203a000e4500e2803a05110762030f1540504031425098203000400c0000c103096901c02d10440407030303041c05003503190780082144016030742d418115800d44030381300d500020807901c09080c0103603650b103985124200d00b4070b00351116140c080c42c0b52584d4419071550822001c10031f0046400070b00010724890801d401c01d410f00e00d0b40e03850803403c0f030140d140c0410b1038a24244002504500c0d041746640036850f15032501519a2b02090007101301800541d8a07001e0a04400b001c040602580c03845031406609541c8145442c220482943d28441c000900c191014013044e048004c003241c001d03144078040c80c01405083d107605102c500b2030700d1075000040600c10000030050b44244099400b0a500300c02d450700c82c0c030307181a40c0e030041c2310785e0403030041d044003600310740c141303084811650510801c0d120010b18 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 982034388 1250 982033138 982033147
    0x80a0909050c0307080f0f06120f010c05040302151615020c010e3f0c070b04240e01120209010509090a020909180d0528020106051c11060a14 62
    0x500e1030083d00101c4050703001441d40c5000650910400301d1b00d60007001c80a801c01d030182c59078010020f2005295100300c100c1d01c034081c56986114030902800000c00c00340c0d110729540e00c2c1103005103c2c8203401060018040801040602039501a56841e9084650004085503640c202031030820080d10407158659559070070400a802e540700013155284d00500404420026562601c2989100c280c076001c0501091103144030805016108100a001d0f400d58003007611481910362800381683d801c190451b500e5560009108548081480752000c1000607504100d54420500000200380240054200790401c0d00400d28070f0721a4011019100a03020040c8014020300d084100300c0d00030b420031401c2d580b0800b198404034a521002c041c80010208294014040240d84010203851590188a2804042000383d5103000d0002807600d241e03403d01c640354004904145014100400c0c10441c003160f4020303285490b484800107802c2041c1980c0e501040e5902511103980800984490894104400a2400004 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 982035638 1250 982034388 982034401
    0x3030a03050f1302030303040206132310030624020c10050909010510020a08090114071515060f11070509040c0e1510031d070f060e03010c080103080a090905 69
    0x100180e200d00c003034034034011042d69201e003e0b00142d86030340400394151708104041401b50405800522160680b0103400701c417140d5800020b01c20a0f4022100703201e035980000400c0680c9008011035038001440e18080c000c00d0705060f501e800704920f0103030360101442c1c0c0303207481110320b0b00038461342d8440f00008001e49040722440e403011b0b1140d071000d03401e203125203600800803401d45000c00810ba08030810354000c1c6101700032030341c0e0150107030b000c100118140b050100c100d05c8204907420041503244d225221a00000307401d5407086003038030089505407080c48903940b4140041e40d444241c0103680c4450b403615000c40b90704445800c0c141030890b04555089503100c020403042c0040301d00301204071100e20f844c24080352b8601603101c5c04600d00e52100c60b8400d0765400303120b6845100b50890b054101e0f1324280c92603803c181554562601d00c0b19400303d5007d0110000c200040e503044259842c50007801d90082c000e02e00040d00091003090305010040030b0280c04500c015005200d00515000381000b080704000908100 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 982036888 1250 982035638 982035641
    0x30f0f030c010e0a1205070609050a121b32011a091e010308071a090c01140c101e0c0e040c0c170c0a08070c0e010501021203060105031503030a03 64
    0x8120305200e96081c243d520074154000580d1098440d0030110320b40c809a001903007220250303c0107500341c03000340d190b001b402c012510a018401156205035200c80c44800c80c15400b074003c8034100c540704100d036446844500414030b24111000a0040e0308030000c10200051101a4407081503007001c0525803814902d0b0020496210b034401015404440c0015aa44c44001000703070602d040828810005064004000081c0440c014080c280d125a4004402014004c00c20007003c504a0b800c4001e076024045882c0d8a50301b0444d03040b1112440b0103c64034240c460300020341e44012082101410783e03a680000e0702807400485d1914054245800140001612140c009000801c100c0f01360348554038103410590060301aa045c048565444082c084214a000d481040103410500d120a03450044000200c0003a070010001c1811038440d58010040f103003401398100541c8016040a8155401520040ca82c0c0181c1c0003600c0e4846400d1030aa07950340e031007941e80c00c400498031001c1c1c0c1e090f11005c07440c4041c40d50107 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 982038138 1250 982036888 982036897
    0x41a0406031103010602070b0706090602120f06010203040302010e09150303070b0403120e0a03141c0603060b03011401140a0e07021b041107060906020f030711010f0902011d030f0f03 80
    0x12540e00b0b00078840c000c01111450701c0b01380f20f00c6015910107a01080b10344032030780103001031130b01480c0d000a03000e1168a130072040c4d034003004005040078481802c00215101d41056660000d50a10042d4201403c2d42d00181001c90b02080c91841078a030000020034003051000d07180c14240c80030301542c3e1598528988083c1c010703803c0d11304170041101c480400c0c41a000c5441415100740f2500028518850140c40a903040501c00c00100070111041000621003070302800140600540020001005450760602804403081007861178400c1c0d0410925410f1040a0b070b9000741910a08a09040c0105400002a8203240d1541c40b040c1464178540400a6543d004915008400c1e240c00140100022aa040000322080c1000d240400d100501030300011079040d41c0510081d80c0704600040c54411020301040e12600100d030f0410010b140c2c4507440b20544c0c000e004075541a140460300f030082d0f080b280d0000c0d00454030070344044004414500340b10020f541c00c1180e0f8001e00e5100040d03d1484502024040e02d0b03610 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 982039388 1250 982038138 982038149
    0x9050a0507090504080328060602030d06050603011406180d030e03011805030a051303172104020609040c0c0c230109180e1014150402030708041205041a04 68
    0x2981c80010b948030540c040c0c540300b82c1e40100c1e1070380396541d4030b40d60000c07070f00e000219400c40b07070744003c1c1040c18100c6a1281c00b01429054004644458000440c401502e101c0d400c03d40c050b1800303200400c00240e28071051911494101c4e14240c40301c401c040040885404284880e41c03058a8511040a240e0003008640d4802d0301540240b00c0060301014900020340103190040840c2c1c0104408001a445070015011002c080000608da0951340d8031080036050103101481d00d444030010780c0c1d541d04848a20408980d4500c4140500c042c54140c0018400340035502155000d181c994000080582c840d0002d40261907121000a01007902d40c0c580c0a5844a082e108505001c68000000803946c01944a80112455900c19a59800840c02c12202400400c61204001e20440d2540c00c140d08141c081c14141c840908030b8044549403651b0f4006804030070740c420500491040083c03101143e8000c1ea056402a000341d0303c412449043c201c1111340c1c0c80f1311741c0803d1004070000d00003201104250003c1c0201d0f070 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 982040638 1250 982039388 982039393
    0x270c210d1e0f12020c0705180f07080411010804111c0b0109020f07060b03030702031c080703020a0503160509130f1d06010e060312030c03040c0603060b121909050a05 73
    0x4605240036189444465002400701c0d0300f81070140c400c410f69800520035460020140c41c2125500e00c08a10b00c02130400c00c0700341c005107440400c8542c032880d103100b0f6881010b81c80d000e160b0703003403176188c0d8684c61b00310320201030401030100c0014082c44824001e01c0300225018140c08008403005000000d420070303006044400010003400000e10b013205000391180800a00a17191900d080c5a03542c0004100030390300e00f505800207104000240c0d4090213200c07460300e800e84128103203400c0c0e80300060103c8001015402454070600002015039882020f41c0d038804400d0001d4072003018215400d4800f805400c2c1040d13800743d40050241003a9000790407071038469524040c18841c00143ca01da201d0944070f5410301904960100e401005504107480c1c19a4000401406890f2000645000000f0340c0d4000c9403487c03500e00c0000180010003035840c0d00c0f14003c105500c1c04101c0503050480c1c2505074402c003030400424407501000700c4c4c1c89911200440415950303184040029990524100303407240300c200c000766441d0 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 982041888 1250 982040638 982040687
    0x3021608030c1b011202070c05152107092102040c030207110904050606100e0409030801330f0e03030301032a0e01030f05011d06270c210d 61
    0x1000c101085650180781612605e5000c445241018001d4001400aa84540046000007000d450300300c4002c0200703050280b20b0780d0303a070740904074501d04905015010540000c0142001801a40210198155500c015020000440d03240d040400304c042804080d5110b8509482c1ca00c0c0b4540503801020820310070b004c4102c01403c41000c00051203021100940306811180004045107043c1000044a08040c2000340344515001c02180440c3c041040403408218043c005011008804031081c14000500102c00c49102d142ca8080030004041107a0405000b20f5008405540340034042070078540e000075044a0700d82d81c0d00e00f840780e03007501015130880d054901d42c1e4020110481c1c0c1e21101c1c0540d0b0b010407001803d6460360b0b65020b05803403c04401c0c4d6065582c1c1511117902410090050030000301c8000600c0d01d8200940b8000d010300b2540036820400f065150740c61907400c07001c52007070701c240341c200c1c0c400003807400007454810340030b8544402e00c246000f84081400f1b86904030503000d038211081c06041c40039 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 982043138 1250 982041888 982041913
    0xb070809011107080d02030c070c1203110f0c0907090810240e15060f0a031e0228020703080c0102190f08040b040c0b0f07060b0103050c0d020703021608030c 69
    0x40c490507002030130301c000c1004103514014540d0000c6400c25410380722030b8508019616500700c0c0f21f11981180c0510006100ca441c14184d10090400130b46030140c01420350550300b0520309a5816030041140d0050301d03403800061880b8000c24803480244a09030540c0c0c140d41901c3c65440051600051801d0700102c0505140300d001d00808880041d20660407200d2035a41368000d4241031400000d0b06170398050b030f00308000d030a00780300c0002070210380b04541c601040c000c114022080b03624029002c0e50b140a4810b01000c41d030820b0010060b02c2d91001100001600c1c00441400c9042ca905a017000d803009100003030423103052405500429000200b4001410450f008400c12200b00300017200c0c1100090072403010401144000e02050341261041c1e59444041d562061208401d410001c64614080e03000b00e508406c0c864240200a00d40303109103001c211601d4104c4e802e0344503003d5005580e141c17a07808910f9004060007040859071003404000c402140f00e40c0c0d03582081e0380c4d07842200150498065103001010 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 982044388 1250 982043138 982043171
    0x2110060507030212161e0203011d031b2b0906020703112106150118150c03020a06060e0910051b0705070915031415060105160b07080901 60
    0x469542c5a4090304c0721540c08580f80105410001c5105141e4060306500c400081100c0044481c013000c00c003144840040070f0041608495a58210030300c0300b4015901001121030100864100304031820a0300d4942800d41012841c0542d15a002504403102c042d0144030080000113004c0e03607280a54485801c16121035049803200c14504c0000c09e1142d00c200013078494a000034071890588540105a0000f130071710000c086c41c0110503150f0032400319500c00990303420350b13000c049150405140b0000c86101441d10400d041d0380d01d050100281001030010100041503c203000f0020800d41100040c004680c0307406054201080075504100c1c0c0d840380c1c0208058014039401aa0b100f441e0710301c100d400e00f8000110f02e5004d0f51103c0d00071905030140b4040030581d02070030300c0b0b580c0020500c1c280c002011800c40c5031541100d40c407141e107071110b0b074440000710a410480f042c010b0b50044080c6486a240c1242c92140d0300d00340032016000f025101614101702460b503125061500c03541c1d68400034804580c4041c0030b4034 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 982045638 1250 982044388 982044397
    0xc0f241810050f27210709060302030303071808030408010605041a0f1306080609060406060806010f060c080705100903020c0f0f100203190302071209121721100605 72
    0x4141d48051040001118009082d9544151054261200007290100280c5508220743e14100d140200c0700c001c101740101042060080c00140d035003005500d007180c00080d0349020083c100d00401002010700154035618144000003418560100d90312142c540221a010f0043d0740540c0d40207610740450b5a61203000e20220079500400030b0410390920010f4020b005208410700082003000703450b1380d40002e49040410850380300d201c507400540510f0030a86001c600351130181e40a0242035028400601c14511462038050841e046402c1c82c54500d1001c2c40c09417040c1c0180b10010340030340900c0c102e0301c1c1e400e411504181d10710380c0f00c2e60a03610051030400810a04603c1c0000d0144c01900c820380070100c9040004229220391294011241800202440004042043c000000c0080e0300400d82104104000c1034400c0c442606041641100d0b007841c8400c5501d030400c51001c1c003603461201c0440ca20b4a065802c98000d038050505030068440d1007010300c0d08442c819038542c0044144450006a1f86200307900f50b4 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 982046888 1250 982045638 982045657
    0xf010309020607150b18010f080a150203060d080301060323130605060f0904031112030c0313030315170709063c0e07020607020c0f24181005 62
    0x3d052504903110003080300341000355181c2c9540d440420514594a44030320110342412580840e25a40c1003110211107184103a0101e041c0d40d221441c07100004104c9180701c100f034010070000503100d69990000139294080b1f807902502c103660000c0046401075040e04a00320101002060362a001003441e100308914004aa00700701110044140e000041c0d06a000150010300040c4500906d4041c4400120001d500f9501200881d4030107800d640101c909003d55689141040d00b06400e614020800c0d42c0719100041c4440c6401d0300c0100d40300101402a40079012000c0580e207034810f1240c80f004021000001c0030303101c3c0442d1182c48000244e904e4203004d0070341070720304911554040206901c0f619000034503145600b40320000c905200c04d404000012058018118134200740fa060600d10000707414800054404000c6400c01640076034141c42d10b61407500340d0a02640e05401e0310722016541043c1c1502200b00c8812400d0005011106c81030480c0031020035a8215103c44c1d6040201c801075031148100301c20b0 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 982048138 1250 982046888 982046899
    0xd0c0f061d1c021902040e1c1713030f0324050f030106050d020d020a0911090108090a022110050a0b0f0d0b0c070804170115150c061a19050f01030902 66
    0x14460000b4240300004c14041c03020340046000e400250701c0b41d0070401c8401c081c0005010345002181415400065601c21010800c010340341030130702d1284007000c5102c0d503101409110321034030200c2e0b0103842a40301c3c0200364410000010203a49140b40602400c88610880344140c591400c107204a150600c2090102c4100424422007a0119820b200c2c0d4441044000e03607019401b410b00140c09a0503000300003107403034141156036803401520000741000341c014100d82841c0d80f06010490050700c81183c0800d48181d81c5005880701c414110450b440c0030b61140a08520f2406c000900030383d682107070000040c0d03450440c0c40e944d01110039401e10a10030411400640345507925004038494510800061a07400c0c000c4104602c0d080d04c400720000340f0690a81040700741ea55400802d21407a28443c00d40d1701510f00442ca01480b06a0058010043d03920164050302c619035804003090000000e0480000f1740901030510204680c840040d402d4615152143d41d004010f5039045c9141903200c1e100c0c010120354001c01 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 982049388 1250 982048138 982048153
    0x171608010f080c101b0f02130c0206271e0f0c010206150105070209040b0f0108010605060f09030a05070e07030e0601230409061d100209030d0c0f061d1c02 68
    0x30814204a039400100170700002c0c120075021021182e9644000714042c2c001e02e03240031154070500ca01c440b810f1a00100040c6440d020303503030036580464081e0308020110607148280c201500b035082e020b0b41c2c14440380803520aa9420600e400358103080841401a1801a110a1500004041d4880c94200c60050060300031000080b818183c41e034010908410601d0000e00b4100507501007480414291360540d08251036a0410481c4901442018003500041e07000340038042ca441c0124034640902c58800899040200301402c3c41d031410441c1244941d0040100c0d00081d0381c5084030310702140c0c2560300c0030011b030400110040481d400500d1504851050082d0045407002c02a9032580c031400d0300449a1058a03841e500003c01c6940c0528000d60100e00c0840205180072071000d440d0108405038681402d006210443e5503070b50110344840d90600d90b0419100540007482c140f96200d503405402003419103801d001c070780100306055464601c0400d4900f101c110101d4801710f0403090301090b0b417840040e0301284 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 982050638 1250 982049388 982049413
    0x30f0c0105030414100504060e150a021809040609051608031b1608031305010207050612090a0609032319200102070b1b03011208030403171608010f08 66
    0x24010756016000b000c0640c0382c0303802440c03070b00d0400c05100d060305c4c5160344640c01c0c0400d20086100b01441001490000c008000c054043c41c15104c40050031502c41541c081020391005500c062040c0d2203400041880e201880c0030f142c00c000a100074802550680f1905141601404a1400020540b1400c500075802c00b0710b44014203004916840510340710380101100d0300f0701c5d500900001070180034001c02542c0c6a60504060800c6100254003043c1150f201c2082040346072100c1d4210354030b01c20400c00182d1f0319613404902501e00340080400030110740c034040d807000c1850f40c400d483d04081440c0b0341807156a00700300e00c4500100d00605419120780700e92110a000464080c40845a1011400c0d5900e400184101006401c907048a401a078002c81c0c20020480341c5c1000099918003509070124190071075041540d5038400c00c42d40380c8001d01c0054004089014103005d0300703005c8014005040e4685151030800c0c0081c03d174280381c20301c3d00c0c00300f80c940e0000f09000f00107010031002c1da5500e0700180130090000b07 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 982051888 1250 982050638 982050647
    0x303010e0a0c09080604050c031605150c030705070e060a0510051c060f061709070303050f1806070f1a1303031107060e061902090105070b07030b0316090b030f0c01 72
    0x50145083c070040c020300090f400030a004030751085000d14060903a007000301c0e00341414000d8002e08080c8080755a041440141e5031200302c004072000c02d080803526881c0b050744007450340c450620003800c50303c01e40c980041c42850b0f4014080c840d440540d01e009a803a9070300c0c180b0112b140000d10943c042501031000340e0040c02d568003c0040d64010360800305e515a5208100500030b4140e800c0301c40000d8180d03000d900c0c65001c0d140100e0700590034200410065255071001800d03801303032440100354210006812481c06071008023520754034000818056a622281c03810034422989084101c51210580354140c05650034003048501c562883e0301028150070140d50101c004201203a540305030181c0900003c4081202442142590041200181201c1c208260528008031100790714240d040d00403c0030000699001c2d040d00c91003a800b00e0b030210700b0b0300d9074401035014200a0002d150980b1400154003500c840d00751410044030245201040702100d044240b50302c40b01c00b981241c2040e400002c0104065215 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 982053138 1250 982051888 982051901
    0x80f040305090a0f08030a08130506060d08040b030c1c0c140a1b0305092b0b0703020c0a050c0109050108040b01050d0f0b0a1a031b0108180303090109140303010e0a 72
    0xc203000320113511a680610840b4180d0805100c03070780041068052190003410f025080641c03d1003860a40000c0c0d070700c044d0350f40002000c0b00e000342c40300540c0e18100041c410030340b00540961f124060322464440e08445068004402c58090350302d0502000d004c0c05424482c804002c0c0f4682d449034035440c005084036850343c1c05180c05000f00500441d003850040b61002c030344201d040c807a80d02c069503514844100b00240e21042524074440f42c45500d04400c0e06c684500e101c5134142d00003075005465803a810164001d010b44943d920030307405131a210b1404c1200c00319460700f407540b00742c8036880c00540b59401100e404804a400510409101d00140554548508100382d51846164400c00300d020550340e20105010503075102c3c04064580140c1d40e0b0302ca20709049440e0420301500144011520118600f007003d00c2c00400398148444480825021a101042c0341005041c0d441101c0c0d41e41025201f050080090010035100c0008480050340c1045c004030441c0d0484203020a02841c80d220740031400c1c001c2a0 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 982054388 1250 982053138 982053157
    0x90604020a09030219081219030c0c0b040302070314120d0b040207080c0d030f020a0e040b030709022212171303060c03050a3c021e0408010606080f040305 68
    0x120020000040c1e03501281c0311901103040f0500c2035118500031b0464641300031a00b1051112100b44510700b1240440451803000050910340450720b810705003c19a00980d003444050716a2a9034020042070540020b003010490740304510350302110960014407a00e406211255001240040000390030080340c50700050b8001310018001490301c07180342e4030135181d0b610140400c107240d0000080350b018150984070b241d51408100a0942c9400c01d507030b100070030b5104240c5107113210799170700c0300c8030f00413034400f0014800074003c42c5034215900c209a4001003420013218212440e800802e0f240031401681020084c41c1060307110043c0d030b0004018140855850f04401510304c181c886076040040890118054184d402c492503e0008580c00c0142c0500c0994509180705004c0c3c035040e4400101da01442c120141405039454070303c0e03a11034a05590b10001c2e03c034804c0501d12503040f501705030400c003542400a00840d180c41008000300c980d242c01c1900c0c3c8030708c00c84442c0303800b115600001d030200e400740c07000340303885903 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 982055638 1250 982054388 982054397
    0x7050a27051e010f18051003120c02040e0328020a080d05090607140d0b04090807060c20030d0e0f010c120e031624060b03071409090604020a 62
    0x5188020080881c0c00496011800c0810700c026016042490000ca038058060711101c030300700ea4140000410f10542d240045d010b0940d0350400110014000c00d5424003650f0701850b01488007010f00c00c000d082801c0403500703a108520300003000c160310900000729a0301c031415504603e540c956540c040c0300880e90040c410000d600030920001c0c0011308a074014150404082c4001405081800006141441c018204014060508440109120030360182d41d041e49203c803020a0701014800820003910480c28024066400443c248040011907085824400d141ea40c1d4400f8103111012f40e0807030000300035400822a0820000403880c0ca409401c000c003425040340c11242c41d038804499580c210b0b0742c4881e003100042d4000c886107258462901400d000b05950900450400c1c1e01da15524400b180b443c400100303013a0383c041c14055005032409002c08441d44948003000025500e40d1402d03c507a1040302c1000025076000c001207003910f801f20030340344500005000f100541d9924400e01c002984000d00720420700 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 982056888 1250 982055638 982055699
    0x90b0c0a0c0f210c0c050609030c0a08030309010506091005041d160f12080d05100506070c06080c07120f1112040f080d080a0f0207080c060702060907050a 68
    0x24601403004034001d84140070711003556501c6440c1c241e00c42e507030300f0799034080002440c042404510344000c40c3c000d4401c00c507007156443c155500020314101c120f0952681040b81d60b48001604040403010350700c2141450000d01c02640c50600300310310600219900d14452590301d03400d0101c0c0c106540308c2012141420581000203880682d82e500c2c1400d110305480c0080350000c4103019913114880542d0003041e915148141c070805903501d24410740180d80924603003e40d0b40c000111035090001e108001040054030762a550a81c40c01d00e0117800f0032500407000800d001402041600e00c06d1002c54210a400c442d640d01c44ea82ca082c0c00302da20300050704241e03040240210384c07002e2200052106030a140200f05005507150310380304a12001805591140c0c050703410a501c0d401455401078500d039072140076644000761010848210600a0040a40107041c03680041401c400d007400005446000311016003c030303041551103110640d900c1242e0302a490f00108082c0c0c0400c0300185420407020802154640e00094 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 982058138 1250 982056888 982056893
    0xf0114012c0111120d020c0705101e0c0c060503090a150b090a060803030c0313170405330c0331080114010510030902030d21090b0c0a0c 60
    0x1041440c2506501007a140a42104941c2c1207000984101203850107070910201d080d0803010036004400004014a070000340c1c4070401c540a01c181005410000e000d1407108424000c02400d0010b040042c14249003260094180c0c81e005101034074900d60300c001e00e81121810140201c581da040130b09400e5035031140710040000070304c07107800002d03c550500c078000072810300303000800c11128405411030185034904070081c444680044102c179444070742da040007030352a11890940b84211002c00c402a254106084d8807a0001c0c0003230005004840045941601145440503c400e83c00611000800418001c8481c00b4001076580702400c001c150b40c40641e0b0038000b107410031107030040d154089104e500a43c102407446801090640b103019000c0c0c6e000820124128a018864407070b01805954422003d482c50751a1b1244a0f4120315021503000e4241d59a800c00988050414640041e418003500e281e000031001814080c8200c03006290031940421940d1509140c00e82180d01807035220007003001c2d10400401 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 982059388 1250 982058138 982058177
    0x1d0f0309010c08132c090a0f0c0b07050606040614030703060c030f05040c03210f0806040219120b010f0c0b1b16020120030d0c091701020712080f011401 67
    0x410140f03500e070001c16000b01c0b5070280782005001382401700c0c900d1800d10524280020740007a0b80360f800b0540d40303110b41d80d6060404401c40554480c0307034881030006010303003004000305a06005080070740e02401001d0700c99450b2420300146000480d0035a000f03000c1000403a0154101d018804101d050000e1071800c00c034140403e0714001c07a400e0756851615101001000310301c3d2074030600e504841880e141c4185061000404d2121700205140401410101158155031540d040361807030443c0b120405072000c28008043d0001c40d45c0c08840d01082d241068440300d65009003400b035100b00d5503079034120315034125a840d0240b0900240c1018000444241e2901580b07800c0c10092a006c003610481c200002001e20004150a01712420415140322981c21014940400801d492440002580102c0c03056036140b000c541030b4880e40e0081c030000d1120550085480e00c10f500500045004119100380101d8040050380c419800341c3d429030320680518010000348241d10304d0403800000515000114400c00100c024 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 982060638 1250 982059388 982059427
    0x20634050f070506040b0a05090301020d02190809030315090a0f0603030c1416030f021f0507020a14010e12010207170306040e0604081603020703080301091d0f0309010c08 75
    0x542640c02940640a0110708000380001400122201480d25003008604451030003012403040511602140380801075900b90192998802520700454413003405590010344400c2000208000c10100d1010030090000401124421803020b89802c02c00030003101807101c1c02c5001040300c0c42244c2e540c94004800050b0707001b05002503002c0e03034034000060b00354109a6000e54009102c50f1482e8480816109241e818420034011680c014000030b258400d80c0c00400e524072a0850f100c0085010001c4c0710700743c56080000340140c03134001d4440590b1f603038443c040000103401c031100b402e01180901500401c50f240c00c8022084543c01007001505000c030785d594003941450221640607040300007004021882c10244144c02c20407081400604031410291a01c031100e10980e494101c02e409400c0b00360042c107000f009510000c507131259003107503a0741c0d4906c3e9404c020f01d91030303c000d00e502c0007140000c5202d04000550541c20712800014610f0981158010355500341d29802c1190700740707002d003d0650a41240791669 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 982061888 1250 982060638 982060643
    0x140307080d030e070807051509010c0606060908011503020a031b0305030423090f15030c150315010f05030105090a0b040e0a03080a14011415130e1003020634 69
    0xb04203c1041c0080c9070420300d1942104907030760b00c1010204925a60b200105003904018401c141c2d541d41d070b40700102d581e403803915000740120341840c00006030540d008024808503a034400081200c010350794082911400d0502c4003030750182c1001c00034030105802801c1781c0b54007042060b0034402d0f6580c03076540c203085801951100c480b480e880d0701282a90b03042c03084d0800104100710b0300c03541c3d9131801d2103000e0340c180c0024280300714000e9070380d15142094070b00b04201152070034020a00d81c5618460195040594011103030000001543e00551030594010030102901050030b80703400d81580e00b40411300a00d40300c018591260300341c031508048603035120343c07054403003000c0020040c0c81208110300380901f40000c0038024040341ca20b00004008010603030a01103064408942c0007040889034031001503040800d030200d040611b8400100003448405084041080f182c20340044c000ea55281003441035003500500c0080d410030410400b10800d41024000300f01c51078002001020444802191404500a880703000c = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 982063138 1250 982061888 982061891
    0x12020603060d05060109151a180301110c0703150203040f12021009030c030206070207080a0f02040603050601061d10080711070e070201141f03290c0a110a020a140307080d03 76
    0x12080580c5134001600c000e4004a28a142c5220324230130306a07101c3c800c0e031000d495202201ca41f41039460740c0a402054a82402652180e10f800000c070340c064070342007203110442d14000b00c0103845104400324020345c0d101d181c011054941810058581d42d000c1e80b107162011b0118051104801d855602e02c0c0701c0c24401a0181e9101003a0f05410f24020703140c85000707095001503500c00030081010003c009201903045030b00101d00c05040c0880e1002c01c010b80525000202107000b07a1002142c02d43e40114001c0001c1e43c1d02114458903a0588148110400d4440f08000003070801c4002900d414019082174482c25052030484030035a5407264000305501054a0080061b51182c00c00d100440c0032040b215088401c14400e0740504071140b510013a000308a12004181d4000240c0c032a84011441c4035906940c0f1612060301049d140500560425601c00e4901101107070042020014048001030800c01040e4080d0001c42907504200b00c43c044e14084204595141c481c0384004a0300d844140041995a800c03600c0 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 982064388 1250 982063138 982063151
    0x1d180a0b1e0a0e0c070f0303061e030b13021914150310090b120706030b040c1403040b04170c03190302122205030d0605212802100801090b0a12020603060d05060109 72
    0x444007140ac850409810066034001d82030020403274030750086800a2484928608084d81440850000c09008014032405021044009921a202c98500b032615601f218800d0b101c41c0010925011130005481e4281200d050b100284160a500c2d40700d402180802006030411110140c0d0441c03500d00c0a40058001984611203907800d803c05010341d140814103400c140300021300d42c95640c0400e000050002d010005103001280038040801c2a02090f041d0304140159600c44460010b640c1e80c0c8291000b151b081110410002054464400c0e1007100000091910090312440500030300c80d240d0148401e480d804070000750001038410001041c07441c1d40c01001140351450700040100c906203844024165810800d2400a00003010480140c003013840c1c044c0650030090241072004880318060001d42200180d40900221a00044668100c0c0c804020520100c240d141c18030a07150014401c200d00248031a81c40070052031315801650348428040e0039007210010710b03100c443c44d011003a40301d0388100e1381d20403 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 982065638 1250 982064388 982064399
    0x10090605011502031909050a0f0f0e19090302030904060e010315020f250c0e04050708030f09040b0d06050c070b0702010c1d180a0b1e0a0e0c070f030306 67
    0x80d09004203140d4918201942c0b824201a40b40d20692602c411254001e41006000070700500848001c2c00b4003074401003140340c43d40001003e00880d03000d86210098413880019074807209081840c400c1d00038a500910307190011090001400e03146204406502050001800948503445071200800c0100401d400c29407545c1081c2488d01817500d00c0291103401088a40d80352001541103031007130003d940c41c1d140e06c60034403401e8102514502100070070380c28540000244040d89140c0c414000c90090b002d4a084540d2800380694038850148450345440f020b01c941009840c20b07501a5078046409800ea110342c004a0f505c120449100721040030303456601140460a20030140803195000135217000801283c1c3c02c0e03d802900560010b005e5400c00c000030b81002c4455118002c6054682c440042507501c207040506607140030b40616503007640913283c3c0b8100e041d261f25a01046400e800009402c046030303103041c440c51019422004000300100300c41001003c00140c21501c1030391442c0e02a9900140c0c450811 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 982066888 1250 982065638 982065641
    0x803130617070507020d080c011407081e0a0f0b0a06020703051006050117070c050a03020f1605090408030705130803070218191d1005060108010e0906070f11100906 72
    0x101100c03019809800c01c0080b01604042110881c580407030f802c0420088a1501c02c459115803046504154280040481c26002c101d41c140d000d000b480c0c0301d260841e034079415040202000c440341c100d45002080080b0b4220401d035030007a0180240d045010032035255000c04141c00722000da00410060b4408801001809410b003e404200784d83d01f103041c01000e03e8200000d1012203000300854000d005c44000c1200302e4000e024004406500c5030690f0410040c50402179195003c01401c000c260190415100035600200ca5840540d50014260b80b21602c450301c8100d22504004d2481052003020000c01047d41d414401001c008c9ca920002541e850300b061040c4489803501c20710504403108903009000100b4460000c86603035001e62030001a03103c02e071501c14490074075442c60388046401501c1e00d024480b0700b141c010324031814080e01c0725a03550342d0b82d418600300c010044807109041e42007017010680591069445511550b45460210000a1100500760910041c6951a01e005a86244d15070401686 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 982068138 1250 982066888 982066907
    0x1003110321090103151202010f17040318050a06270f0306051005010806030a02010c03021f022802190c0b0c060601020c042d0f020406080103060f020702010f051308031306 75
    0x8007610038800906d48a8006505106800020706221118004502951042c142120980d60400501045041c5420003414503140d03881d40340030300b401030300011400d0300741031710548200c6e0400c0c0d4030808900b02c42008c94030040c20703031011241d521001d65000581441303a26654406107000e01800902403c100858a00c00000c0368811418032403103404200c00c6540100381070000070340a003402000409945401c03414001184000380007c0198400c59481c200780b5805802402140310012043c4841c0041c250308002c0c0b01c143c090010380c0805203560705035140003000f0711070314841c071700028000752a8818036a950701720070f103020503541c8407204010140da4100803d24200c1d001f9102004050300c0e001107900804901c600c0c080030500085120a0f00f10f409038441e4146030b81c0081d0440d20340e40c581c00010000e075806c0c441903402e140ac0c0904905002030a100b10340d000e42d816110400040080c0178255545c2d0054401483c3c1444030b0880000c00d200e0920081000c0151140100d282030300301800a488140c8 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 982069388 1250 982068138 982068161
    0x6060c0a05150108060c091e0603070504140607020a0b1c0c0c0209130b010b09030a06090506040215040e01050904022e090f15030504140a05010606171003110321090103 74
    0x4c8013050041b6808100210b400d411426108900034400040404081c1d19a0205050b005000001003004041e800400350003074925003d0602500a170b00c008100050145240281d4001002581004221101002044400d02c02010641078155030083c0c1001c41e41c80460210100e684103540008610f06036804030381c40050034100301402e1455403248903d4840c140a05a045040050b0900482d5030811085074a039600102c180000142842c2c216150441078508030700809550385000f01c403601160650b000d50b8032000b1404002e81c46c010801c4002c40c000f42060707800422204140c1080c3c801c00d0b2000c030b03c411040b40890040803441e04c0003441c0c00d10030b5200c84100c0b00c0f0150140018034101c520210a440c0d14900424580c036641071446100c40400e9440c042489249005420850190807003021103056444e005102501251001c212180490b51141440b10444091000400d07070035060001701c201a007160048441d2018412424403d2544110030b4400800c0c07804aa40c0d00d8094444c260f01c = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 982070638 1250 982069388 982069393
    0x1e060c09120106300302060a0f09080f0a090b040b0f070c03020d111f0804141c0f08010b04030201020a061d01020d020405090a090c0608060d08030a090201030b01091d06060c0a05150108 81
    0xf45520000e49801f005000c00d8400c90315016144080610f030340000c16001e400c590543d079911114002030b0031070350000e442c3c0f001056101c1c80010300c125024003030b20200c0329150700c441d10705040016041c01b40d40c0031081c1143c1e18103c1c40300c0803004d82c90f215407185090f80b00f040050038040d06a0204240b12400102114031094100440c0c1604c03070740510415082036000e00c1c0342a0808415010030300b003503070003280254087c14584541c100301c1e5101c190841c64407500d44581c0440d0341c0300d0741d10000e00d100b075000181c0540d00424104000441c1a482030b004c64100c0c1010b600d846030140c030030f242a0307809030100a00301500824280f102e4604942e80030307000001e00d04100401d440300d96800c0d00d101224814107003440000300001d80c454440749020344900b680094000d41e0f81c03820b40c8808001308440f81c000e0340064600020a0950b50040500f070050300c22107205940c007401b1443d00301481c504010400c0d03801160074000900c03001020803e410001c0d204e54080c2000341c88201c4c0020030b0340d0050340441d80c02e6 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 982071888 1250 982070638 982070729
    0x80a1106011805130b040c0303110c0a0b16150e07090902030a1e060c111c0206190e060702060121020a06271401021e060c09120106 58
    0x2040c81d01c880c41e42d9003410102c0031030259039000c8100415a40c0350000340ca903a400070100410071882d0000d10003035038441c1c2c440b000c00e904d51606840d1703110394102c4115000b01c40020144203500e111000b90480c054044a84083d1404c946c2d03612900d01180112106442d403182e281e4082c004040c4210000303003803004401c00c1045015000241c4e50075044102034070f060f002106a07c2d6603800180003d540540215041c082e410821100600d072410030041828a800380d00002d00d101100070707044080310700069005001903222200c03161400301c4030003060385445983d40542220342205211040c820030b000d4026050a625001a21007014903440361010f00d5080b015400b80140d540e00c900310103590705440d110000c11f0305442910b40c40c00100c100302c00c2100c0703258030009210000b106502070340c0c0b1081c0e0950300c4141000d91002c1140c101c0240240c1c09810010014903034001c40805800344601c001c00524107000c1807a6007900715041c0e41c01010060100300f620b40c1320722214040340c4a44403030307500c2c051401 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 982073138 1250 982071888 982071899
    0x5011110050c07081603090b1206120712110109060906090e10080a060b031b15160c0e150a050d02150f0c1f0501030c0909081204080a110601 62
    0x20349802544a4001559a4011840e103039010300980f00360700e512010442e603134910502c602820710281141180010182000811001050020358844200d00c0b2240e44507a00c0d0203081003018601417001180500c108880040c94154070408100d14a0142d0080c0c1990822503000411504180e040f400500203a410108015079000e0b410204603181200d42404039100c00760b10521454456000080d1803240052a80610810b50f111140f100d100701d04035003441d064850b2110151601d11401913100e42e00442502e030a00e0740340010620001c14000003e07000740c90b5030341c6200b00c25284e04036003100d092803800c00852040034010504c840c0800c48122090310b2912000400103000c03840020b004100b0001a5400c542100040e10a202c541d140c415440345041016559540d18402400050f203420060851b031107600c03803149506a940008688920504049181000d408041300855044030100180303000151207200c0716000324490155280c3d544051600108140d03607402140b401c075042803004101 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 982074388 1250 982073138 982073143
    0x5060a0602061e0a09080a030c030f0501080706140c01181a240a050a141c17070309080706080106080702060702060106030b220b210607050c0c030a05070f050111 71
    0x1d003d240e1030007042d6407800d003144017038010054010400c180201e0b0f0307610415056080440d2291107a5400c003c282c1d10082c02c40f0aa030400c1c4600301103a0062001031040501c205101c40000c00d00b643c00d01d181552a454043c00c41f0f9030f180c02c50000c8201c800300d4104000c4004c4951250341d8620141c1805801d20005029480e0024407264040c502c074034100c00782e251941414000180b400420612015540c2d82c140381411384a1004103105501d21007070101c00c00403901c4a10544e0760441178003c030a0444074403101156101e011300740c041c001c40310400101c1e400208071307c601070003d80d9201e40032949042000b030320049000c2e04030019500224100800168009402c130704450032440c010952012001c00f10f1240c6404404401c010340344910b03480e1180245800001460006403052803044419035040840300f1300044004d0b080750016000300e0141407003078015003d021280019105500c0c00000000d18001c0001e0046500d50040c180800c04120807440c0030740200420300344540c510668075091038 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 982075638 1250 982074388 982074421
    0x2309070203071e0515010b0408010c021c031e020c1507030903140901141305031c0c1502043c0b090402031008070803040f0f03020612091f05060a060206 67
    0x72100c034039614400113116080221403603030758030403468201d5561079181d009016800f0380201e103119030a048409011a1001078250008035203544550300d25070403004214050452402047c41304070050b22000c803004454070080048a5400006090507114203000d5074040200601c0c03001418501003a80340400e4000c1401303480d030a010032102e0b54506001d00184d030a6407046444040c40500810030140403135101d14008252082101214000341c44440100d410840d41840280080c0c91240d03080002800810050041881c078003000d4100b03522503117025802021080c006480b1404008a1409200d481048807080501200300240e100d040150101d26446a40702080c0030b03550010010b03000c070003810380b85406449800706076102c407a960700c2025a45c0d0003a01a00703001607008800016110a41550301d02101e60140049080c004103030104a00b200c4014101e4110b402009802c078019107203012840440a00620002001c2c00d0040600002180342c4d00220259800038081c0002c07000b45c1010344 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 982076888 1250 982075638 982075673
    0x60e010509130501020d1503020306090f1c05070b0f06090a0b0109210b0c03040302070b040f0620012903060103230111070c03031205101707230907020307 68
    0x101c2c2e4004191400e1402486907806407074039140350190018020ba61b08045508030b034001c07070072038003103881d2868001e84034403104410503c1a480700d1515000720f070410005242d40140380c10135604020b800d03250003012030000c0711800d100c0c501c204100981442c10b110700c281c0021006100b00089004030001130030040d9680214684440c0541150b081a0070b4941c000c0c1c9099489000441a4100a02e00d011250029074045015000b400c0c1e021640061180541d0100c4440ea02400c010900c0c081c0180c8890f51421454600d5184420030445d001600b4000c88980d507502d17990140700c0e8040c030214070031429a910740381e51082e0044801080414900c2c0c00d403c65044089000203041d12401c0050f034018403210041c4405520041050014419554003005c102d034001e03243c6669520144402e0f01c1124002c681008000c881a00c05106451610301016000c80141c2c0460340095182d4103421442a509400044100c6490010000c241030201489030400751038001103080c104150760b51464210200100c = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 982078138 1250 982076888 982076911
    0x51014061b010603050606030f01021e0a120e100e0a0203071a0d05040b0402010306060c030c030311120108070303090506040f090b042307030c020a0f0b07140c0d03060e010509 77
    0x3081c51071189409034191042518000300001541c0340392040e00c0d6401180c20900c00d002d204948031040d0010b0007120001c015008a2051020b40e1141040c0300e600403000010400c6060301103400d04507880e10031180e512003408010f04004c00034214060583c0d108103443c00b0207130005280c200041e03d0014000d801e481100c0e40c001c01c8049451508911401034420901581c0c1c106418003050049120401c2d02a50003030782e062150680340c820035038100c80c01d80d800600054200d00b1a0f00440d20a1784003104036180c0d4410381c2d141c140c07504582510741600380c202ca107890300801c20402c20540c000420780010030003518214282464a0808480319500f0300c102c0ca00a43c4030000825246da550307200713802c1c0300c1506142801985078003c040410300001c03100400403e14050000200350300010b0300c0b02e0059400340403c00860b1107559582c04429024100701d003401681441401d51381402c1c406401c03500306010040c13a0309858600000c0680c0c000c0c1e03007c554603101d500014885615662281c83c0e101051000 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 982079388 1250 982078138 982078147
    0x405100c21180c030201170403050a0c030908013e040317190809060c0c03090f0409080c0a050c1f0806011211070c1406091c0b150405101406 62
    0x40c07010141821400c0d15640215005402c000c102d50340c5a04402c0e28000c0e40d69060340310804000c8801c140b820f4074041c02080703040c803034154024840e00100110f40d119141031200c550b0780e00051400d403a86200740150f5032214801d690400c3c4028416100b240300e0504000106e4020004943c000b40f00b02c0c04051b15212070b00c0c24410b1400c010784200c800a1060035581005440380c00c0d001065801c06070380c929510b000e0351001c158040c03848025100441c90300d1000d540b81c815004100224810410032058200c2d403a46086804602514081c3c451071141c4005840d0702e0200b46012802c05025016182c4a4000300c0d15149000d420780034040390300c0074a8101600903880e29001640c0a0880030b941c000040c2c1001404459a42d0a402509803e4411a000355045840b070743c450183e02c25a03940160044070038091018640343c11421907444181c3c03c0310514040c034098a55140c03020041b07402400040c201d200107101810a0f03c50658440c03d0241003401c00c6003019886a0545a81071105204400103c4c = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 982080638 1250 982079388 982079447
    0x1112802030c100203060420032410030207020a06020d08180c0a0303021006050409021f1209081201290d02090a08070501020712110112020904050f0405100c 69
    0x800ca0304100c84840440c2c46a061103000f1101075030003203415901507410b102801d2000100c02d191004c0310174101c0c400c58115510758414807039071141440b8540c0510003040c1d00c80415112920a070420501b0303a6005641c075000c60040c4004515079a010354115406041004816139010590b0b6410082c00c42800049020700c5015a00e071612501c200396001400c0381e40001090b0300012109000c181403542031024550760410031007102c0444e40080e410802e03680030041c101482e07000c6209101400c1c00c1502503071210741e0401c4105c519000c3c040343d99010002d001400036907207480030340c0141510444541c660100030b0200000c444c0c81d400020a1144c0405c1c0c2c0c1144100d01c1d010f4031012036014010075850345c3e45081c2c0c2680c541c0360f4404d06000d070081820204d046416641c0d0041201c0c0c00010b46203082c0100790046480c01c10700f400b081da110f0b41c00d2042416582d01d5005060145403d119608640c1c1002c0c10128245000c51112241803440c1c0030860042d560016400394802d0900705191441c004000c = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 982081888 1250 982080638 982080643
    0x62315040b041a0a0b0c060112031103040608040c05060301060c1121010f0608060c0f07320106060807020a020f1c12110d0c060207020409050601080f01112802 70
    0x4a4a0542c000d00304500f0100ea181e680c1c00300d64601404598420036107a031028208580c1c490003c030300145400810041c44031015119404806500c00d26101d14031410240c100c6046030400d4000388001030446040c4401e000d440000180544400c0b5415455940b50001c050711a808101c401000202644008046642c0d1170300740001046000310810302d03c0c807800c05064006d00b814034030313000440e107041004581c01c00c00007081c6100d41490b20001c0c0c9020036910400c103250304903c200b02c54407244c07080d06101c00b0501c0b031741051010307500c450200550a40610007078292059a0440e00c1040501000c000380154006062000c2c035405403003144d60082c1907408200304042340b00002c00fa641c1001034101c01c000807030481414000480d500c072072050258021247c1c5400702440000d0025846c00d81d084049201580207102203440140001034891f030580e941810840264409000707a085a6002020300038280159142c8050480b1039030b04c2e028028411054480079810700042106d444420410414000c = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 982083138 1250 982081888 982081901
    0x3080a1b0309051506280f12030f020d0806040c0903120f1d060a0305090a140726030403030806011101050f1e0403020c04151d010306231504 62
    0x300505100e0251200c5030241c05000404400c841900c0f4031060081c1500303103880418080e5000800f888208440c42004e40000000c00c204402d50540480c07000501c9814000420018034800d0f480f40100b190750b0030040c1c08404000545015500044a02c40b00343d6404612030350300c01c1040303500240d140c0300036104841105142e000106040a03d4410146481d0480d00000c4210007070343c1e0745d840b842c0d21030f05140000029050f016802404c20b000900c900c038000d800c0310764041c605004403050403261f07403103d11540f240d1030001692500441c40c184030444a0600182520304c0c0482c44020720712101e0768950380c0e81f007140700260030000050f01280280c0c1c440e18030400d174100040e00030701031820711805440c800001528429940c0c203028034600b00c1d105400b000c140c416074168003d45070384003604c0c0a00c800303007070001e00200c940025800c001c5201c4031000b080141c0c1d51a218030000c0c90f981036241140c102c1e90003104100ca18903288030b41d25030b05104000c205e48d11202460344140c61160b11400304003c0c1c0704 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 982084388 1250 982083138 982083161
    0x70f050a090e0a050f100602060f0a0e0607200f0c040504050c1905090609090613030908031b06070e030a030509063a06050f0d08130f031205120403080a 67
    0xb840c0103100c0c00b01016040f840c05000c01d118000310035203030300d0501c850f0820705118a10250b0003a03800903210994900b00e05610000501c030105441180c41e40301410071508450303000103c6d00d546030b0544003c1865040d50704c03017000380000309901000cac509860359508400719094803d603240c800080410405108407a1142c4024000e0f0700500c2a98410b02d151b0300302400781c103020350426400940545440100c081c0106035040282150b900c8190000b49900c3d400382094043c0401c5030b1000034044002c1005040031200a113481801d800f141104508003c0701600840800c025030a00b0603255601280c20390260fa4181481035441c103800020450a000b400000c8802000822041483e00c481031a81c00b0440c400d130101100d012469480d04d000c98500b4099180c0010700203030007842c1414078030090003006004005171414642480e4030758000d00030325006002e640148150400800c01c0d0400425442e00803428510f00381800c914550000000082003c0e08012440b00450f060203a02d0780841c22200 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 982085638 1250 982084388 982084409
    0x20a0f080c061305010c0f1d030f061008010e0a0215131a0c010518060a0c0302120106110d050c030313140703120e03011a010c0203100e0d0801080105070f050a09 71
    0x3810102c3c00f000c030150200d056030a0750038030004d030304080c1c4100b0f1440109841038031a840c8040043d882031145024400445401d031117102d402505100c0304000c1d80380304810100802e40b00ca814607840600f59150007010b041c1560100d0b81c0c1400603a1855000c030303503c0420100340d0f902e411040029a0f0780d42260740c403080c21401c0d5030a0712000300036240014280002e144000b070040d9191022107800c61850071281603015000000440c17500011604a62240000d42c900941003104001841182d030b502a40a4400300700e034042c180f40e10103010300087c41d81002074180282001d40040041d5182d00c0000c280501541310800c44804001e1a1500348a251402000b1501c0481d1a40344c80d038660300f1440341d0760010507401d607004a0203140c140610040e4078000103010201d1402800191103803890b00004990602800c00d455174600c00f144110408001817400030311604001510190000c3d034182c000e100300780d040c80b0806c0412078001e4684c183c9800d00b8a0490b60b25507148004440d144900d402415155 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 982086888 1250 982085638 982085641
    0x1090e0a0f064a0a0201141602040e0f0c03030a0f030c0504121101120c020a121b060b040f0225020406090e03130504140c0d020403120f0206090706020a0f080c06 71
    0x24400d0049410300421030b54000040031440b07490f1180d4940b02e91000a0001c1d0071040745000844519018021000e161030741254014200d130300282c1510704214902e146c66002d590785020541e01000145c0c494601540503524040700000010445082c000c029400d2503220320b8007880591160084030001c0010304c8000104001d5407402528400000f1000383c005803402a6060a8000b148201041e59505400400c0000d4480d60392641d2072440001801c14001841d50300102a0f8007005000303c0244100c20000d000185141000b007280e010061011044d44180000715a48003401000f00000c0f030000c8903801000014030008001d4415500020100307410f1101041d0801c1d00080030349050750316a074609019946440a00c801c807840d5010785150341402101041c252416440205040044080054613041d160745600e012a880010950009426900c0581103980c1c140300c5107400000c040e010b042e00a2402400070350ba201300803009428009150341010811481c00100d43e000200d0304c069440c02d = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 982088138 1250 982086888 982086971
    0x403080d0f0c020606011d0f041112130f0201110f0313030c0504090c0b07050f030f21010b18011b0f021002030a020703030c020301020d0501090501090e0a0f06 70
    0x340c20341525045800c0d003080e84855802d030000c11000e2207504180c1d0b4018600340c17040014074811010881654000844007000b03001c40d103950091101510002070403940d600304209116071003a0300104841040b510a4a00c800001c0c91100fa80c680c06409107810160080c0c041c136500e0038480501c152080d603100004041012840b10052581103030300448051002356514804d0005840c00c40c44001c00d0188428814007001000c140038003041805038040790100c00380e44200360314507071040c5003803415176a022a5408081189080322880c000388003540c1802c951501c0c800c550240550080d011081d140201d20b405280d204e8100c40e8144851150200d400b000c45d1308080d0201200313800305a0268070034000d0112502d000000f01c4501d00f00941c01040820700d0354070219101145040201c0c1d06540800c0004031000890098601030030300f150700041c155161120041c00c0710040f00c0c0041c0d50f504114550360100c0ca81c080001155a000030022a41018850190240d031001a040303c158212100307000d4030 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 982089388 1250 982088138 982088141
    0xd0c060b18220c3b240904030320130e07052803020d02121f031e060e15100644090102220b0d150b07210806060d0504080403080d 57
    0x203105c40181000c0b24883c00030a0811880315903030700c40e8020700e000c030100303000030b00c00d03030054030b400090302a84d0102c9610030842031a668002e00c60307a41c0c1148052024440c02c1652564039401000300d04206180840b04034041d4014881e01140c0d4105940c2d07101400505402601103441e00c0340c950b4421075803a11401c1490b6070a104c26201004440007103045081720302003842801040e070750809101d418003108009040c04040100380d0445940361105c0c08103800c07040c1003181d00260700780d02036444902e00e003044600c0c200042c968040c0d002c202c10b00221062581c0b03030701100000c1e00381480d2480047c008090382d00c0310b80b001c444000d2400480102c108980502c041d40580000b802c440b5264028112601e080c888400190207211074090007002004030040159000c1e20014802003501d2402c05d40d1030700021501d802040c0b003074030543c6045aa1000f107000b02140310100c01000d0504403c00d00b01034010070524001c01d03003240c0310b460b40c0360042401c7c012542d090303030002c5502c800d403503654001d20701c40c560 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 982090638 1250 982089388 982089391
    0x7151a0423060906211501030302061503030310060c023c0d0804090b0a03061506091a030115023a0e030d0c060b18220c3b 54
    0x820500d05040800c4003403500d10000c80c0a11401450082c603c5007000c10f40200031728200415034103108651034110010034000c6aa0b000f103021750050401d5240c100006480c1820044041f032080c0c004108201e105200c02d86001c5c10340b101841e080f8031109417840440d046d0300e801281350100420360402c508407000071904048040414440641c0140d00140a1203510010510020019002400107028803595544583d210100040080c98126a203441b0441150742c1900450144601c0c5071b018002c050300500034200805074108682c041c20a102c4156070315020600656086501b0500707004100d42c0300f00054275001d000300c0c200344003802425610143d96000700105c03008010b00a0844605140103001001c44a00040d002d000c0340b011104c4211038094856904803189666106040d40c103881f0a411050b0300c0c16035104050f140c1c14840426109103105125076040303480c800b4082400124440c412004440f40700a01c2ca61561008c07080e900c01d41d9004510003d0030704030750010306100903417001d2035 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 982091888 1250 982090638 982090691
    0x3270318100c02060304060908070b04060f0c02030c070b090109030501060b0403060605031c0806031504060209010e1207030b0a1404050a11010f051b030405030a0303050106031107151a04 82
    0x4510140d507464040d540d464200501942c04003040c000680070400d10342100303000602c0781a030305144c45420f40d5000003090b010750b401c6d2403103a5503501c0140c1119042c803401130138100720b0004500b44201d44c200300340e07100418003070320301c040c100882c5c0e94002c1d901500442000c1c50780b050081c0201d42e00c400c00c591580d0028031090f030302e0a0419400054038140820152201030440401e44014228200d00b6191240050915030b014415083e01d031070402265034150f4003da1080502607070f01c2e010080010180c807414602541320f00f040d0200a081400d0005401c0d00701d03540b04002b6402640d40f00c2507580145440c070400513074540c800042008105010400c0110b81d84100c0304c20302003420345001111001038040080e4040f035000c10030348800c0f5001030800304003a2101d0b0103da142688403030110341843c0c52800120701003600e0b85c00500c00d480d0180075041c104c050100f410382c1003405580302c182c00200368149103c2402c1d030390712001c2c01e0450185520980300c4000360061202c070800800c901c8601000131401c = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 982093138 1250 982091888 982091899
    0x31609050f011d060118360608070e070315030b0a0c1103090402521109041a130312060614030a020904051305150c03270318 55
    0xb00d00d00c005000020a1a4076448070f1408640d640001541c680820500c40b140058a4500016410003075801a11400d03044100080240c000d542d042d030003800c0d0910300c0481c00b81c10400140940b1000059140445807282044945a180c44c54207400810035500f801081c807171003040100170700c01c011640c14010354200d1410003c0d00c4640504507082e410300c40c0500c00c1380d0001c1160b4805403030503402503d1880d00b460240701c110b80507411961208030058070f200b8421b48040c00e58546c202242c941c0520000d88020700003d654046550300ca40e040d44000b001c601c04c40800e8081024070402c1d8000b6810140c14544414481c2818a140c0a4494407202c080700022450070302209141502d00400342190950744810008284084160005410040000b080f466003448104015941d900940c2e01945850b19480e104e1403250070842d0424203121124076240039218180240342c0b84000c01c072640300d8404030302010032202c00c0c880702480c5c006001c4e41d203070705200128104d5625400011018082d150807101c = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 982094388 1250 982093138 982093141
    0x50603010e0412170c07420c09030204230906180a050a02040507050c030f040e0603061005040f06081501060e03061e0c092112071e02031609050f 64
    0x101284c0500c00405040360114030003000ca40c0055441d0003030301c081c0b48103070b4080c4070814a8440c14071000310540038694580c403003586070350032445441000c10f0015103290003d00900108540282c10103685100c024029580c80e446101c0c85000e03644101580444542c8200160034105001d40e0f80306000c0c1d4a404180c0d81c0031071820804540000c0341c00341c0c19031213000b60a8030b01c140d80810008001c001d00349e405016003041080c0301c01c41c00380000c1c09052481e080305900c1e5403c00d90b04174400c0800802d620300a40c0a0414401042152040c100071580201d0b0302040d00649602100c000c1c01c0c050b8801002c2d4400d0340d80d904064001150b005042e00d001d5955a4540c25000c07082623901c0c03070117864265202c1104410024080c64030300c1c003580e00a03c1d0901981c6440743c2d10010400660740b4030384407079426045240b40e0311442c1e028080c402000094500190410000e40c13288131042141c1030014584220020142003103440c2404030756003070101810a05040b80c0c0e40c582030005400e04036942119490140b0 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 982095638 1250 982094388 982094423
    0x30604050c0112090b0c03040302071a04290304020f01020309041e0b010903120507021f0c06050109020306100305130b0f07080a1a19090501080d111c05070804050603010e04 76
    0x41444c1e00943c01c412117001c0c0b40c032014290b450079030014009a045001d56800460042d003001c3c999402c5624019050b0341d16860110102ca80704c2d0b0190740b040c282c07003809500d1400e0b202c030b44082e03030b42064049034210705028443c00140c1c030714802c035140c50750002e0510035051560554a20545510b5001001c140040704084004680d18281804000c00700c03400ca00708184550322079809800103901c0903144c0002a101805504420f690030540000019480c1903007a081081c98010f440c01001c10f05020f60440c10f10b240081c1c5030305002d070100c0040650341c800140b1100c501461082ca89a0401d0514003107041c00c0a44c08040711007203407440041800c038408a04051218130650a40c0c07100320784181d4400a4030b808000304840410800c821100202c0c0c80860510400e1040300c0c001c0103a64024464500c6120000d08400801d07100f521003600408500074080d100044140c280c40300901e011a0b0b102038610b4260f900d4025504191b070001804800440c072504115116801240500c41d0039600e1000031 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 982096888 1250 982095638 982095641
    0x1050306122e020a0c0314090409080309010b120c2b03020d081003030c021e0405090304150c02091b040803041508010e090c0f12190c0f0602070b18030604050c0112 72
    0x101103840010599817589001c04d11400000400100d003818445c40c0a10202c00a0142c9520410a6901038000014841000c1092141040c00304040ea6104a50100c3e590040d8540c0c0129041c4d40c0034100c41110718644941c401d0b408031042d0210a078211100030340381402541d0b12400c8403a0800b0401d124046600700103950941d0b0210707545a601c0404131185542440910000810204003a00000700c6041ca5951107019262081b00310f40002c1d034a451403c140030606420002c9048141710340700340a0009a242c4c6042d9075032220345c4441d9852221441d122b016418803d5600008280c000807c3c04102c4e039521441c2040100c4041e510402182d8944141c003d2141c0161100e1006612141d0a40c0c21800c1c0b044400003201402801c88a920940312500e41c00d12440741d02101154600704103400c108104100300c0c0c40646000c5a542c0e000508000002e5603948140c00380c0f10ba4032401240c0da400d1800001c04140340c0d80000b4041c0d0f42d06041610780a5a21450001500d0114101910407200001c15 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 982098138 1250 982096888 982096897
    0x23010c080f0106050d090803150913050a0210090302060403030f080a020a0c0f05010213030b0402040e0a050a0b150a1401080a0c09120c080102070f060b180601050306122e02 76
    0x9100c2000703850340790800035039150344036080c40b085c80d40d10764a800c00030400c036002951041c1d8007218484422002041000614003006014080780d0406103811804100c001603904201a41a1070405400700f00740029607044070113910095000d180000c001c000c00d41c1c080c040d20054042d9849800305030301e980c00c40030700764082c0d0f5a0007000144100c40080210b65081c40c55002c46000e50001481d0130300c0c141642e01980056002600c190390b400c414407085003170a11540c80b00c800e0b080040c00651045a5855072144a0f604002c0c00c0e49640c4400704845080b070001030080b0340e60042c6078004081d5203130b905616100e40702e1078a03804136134608002950720790903019400454509548148140f03003050074815502d28003800c1a00d4610613080c02003003e000034070091950500a503901040b5112a03c1c20500f502c8080c4009809000460300342c078800c21112000b944c01c400242042a03c0e5035906001c50b154440a403c058914460421030401c080f0340400c084603c079460f070081000c8003043c1c840b8402071348030307 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 982099388 1250 982098138 982098151
    0x504050c070204050a1b020304030c05180f10090213031e021f0c0503041d0c070804030204020d020903011b02070605070c06030b01090e0a0b0a0e0603070501081323010c08 75
    0x20801c110001850310750f10003544481d002200280545641004444c1020b070389100a003d644005414010304c04880e00180c0140340440c0c48074031040420507a40e2028002901c0010141601000315181100508014000d0300d41c061045454410f0b03191220406030341c9100c20b6547c81d030b118840c44814881107812000c85030b00940381c00000c08400d03880c0a0000001c43c030f44410000302d0040ca1000840c1400100000e081b64216550340414441781a10700074005018400d17500c508210700800a19004c1c1600d00300d0307404903030040c0c58080a09a401c0603104030139030309906510344034403c500880c501002580300e400e551300b164200d544602d000c1e1001c0c482d0781c0020300100c4080c803003044000d21075000307031887c080185400400c0590303c0c0600d51003110190341c000307201c0d615445085400d041c10115070740200010690403c0a0170f00c440401c2e1222401c1c041c1c1410071540c1c0000903000c40d41c0e515040f1090b54002500803001540440008842510300f520301d20715400c01b00c02401841c4584001c031f01605 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 982100638 1250 982099388 982099411
    0xa0617070503061804140c22020304060221040b01050411040918150209190e150127031109090601150201060b04060e0114130605180301021b07050405 66
    0xc40d940c0003501c25810007401280c1c071800300c0b45004010a90381c4e0b601c6000d40d2103000c442e412003911444143c01c1c2188510001c0c042c08003010800744510043c910000d0129207642e005940c0e498501307041c4064400c0041026000e034825100c0c1500c0d40400e41900d01c203a00510745460107036241c40402080da00006620b005000060205000d01030599112101d60054000d01c40840042651503c500c10050418640216070110b4640c2d224140760014000800301000583c814034240101c0300e10504000e4400b10307240e00e6114031241c5031b90083c401800d200d62419071621140004080400d011002c5000445a48400328005006801c1010056000c1c0e01d41c00d0240580f40e0030000c1a1880b01d01e480d014800715900d030900041c1542e80c01e00100050069a56038000402c07403075001603c0c02c00b0400b140300d9034100801032980c40340c00d000c41280070b8a1f01858101d0b80e85004980d1529503280302c05645605520014501d00c114081c1c01e245440d0084041c03d9620555480040001710341045400e1640c14 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 982101888 1250 982100638 982100641
    0x10606020c0f1504120c1505030f070509042a0e04020304020d080a0527180103050c040b060d060f06090e041e0312060303090611031c0207020604080109110a0617 71
    0xd180161070030502c102c3c201c003010b0519a8503280d01e1501648a10140d81d818a418000d01c42e0400340c0075440002c44480c1042469824510440d0110b040006d02e128104040411101e00b26030300c0c1d800c5522010f000400d58030303804280e0314030720034117101109070440482d6041a80e2a9281824000d80707100e140c005000d00c15011141c2c5810442d40c6c45080e2803c20000c041110008242560a840744100503003494070204088801c03c1c40b03405a680c00c03d190a6540c0740c0c004100043c00095000c981c40c0d000c0d1004201901c0b00da000c52054050381101c481030034100a004507289201c1d44600d004c4070159034550480b41c0e80c4860203d440d0900b40d43c064000300940070300503555058048070b01203151080c0f03490303442111044580800c9a5058104a00040010008018455010314012003021b43c82000d540741c0030380d0401400103005c12645a0180c6900810070700b0039965000251002040307100028000741e0340d00e1401e0080c5182a03e0024442c401038130700810485d00c1a00003004600c25801c541816 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 982103138 1250 982101888 982101919
    0x16080c07081e070818030102090a090c05070b010905090c0a0f0b030705190f0f1704020d240204091b1d0f060a1701060c0b011223030a02010606020c 65
    0x100c0e402451440c02d0741c0c0342c0c44000400c0075804030040286601481c1c503541c0741c0200701001048007005202041c400e03801888140481c1da034114690003101c010610001d50796882e0311080d035140c0504100645086c0a0400004800050350031552207050718009840a0350741000030010100c255008040c80032a501105010666203200299003155290030840c2c20305042d51400c200d81500e41c19000300064500104d500c02e40d030400448000d4242900349581c0001d01240030520610b00280042d11902d003151a0405006403d04580c0100504c402c080d00190120310001003c3c0d4042d11421019600d8000400030313030000410441c04c00501e6944481c0c03420608505404c00761880f440090380b00100404041c902d030740322002000030100a86521509601c250000c00142405038003003400d204a038040740c000119819070b51419510300c20340c01120703081d8600f003c00704c0030004440460480501900340c62450800409050980f00c142c0c001c0c132903240c50b014102e03210250140403d80055010915869 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 982104388 1250 982103138 982103153
    0xe0706080117031b03070213051e2e060e030111040509060f040c02100f0903020a022b03080f091506040e24100e0609040602091f02030316080c07 64
    0xe1080a0b0201d9041c11807500008108402c042e01c4903034150700001e54641103040014604c03e82c440e580b0020003103842c10305812020720604542454440020b200015400c0110010150842111960701c2c0f0000c0400c0c1c98241c420070a9005400101c0c01da1142c50041d45414015180d60082c030951140c1000e2a03c402d01034980000307400161300040c020740c4c0c009030303807070b14826a2081002580203002001d01803113005d081b5000905070224040c10320306e210b4040707600007e40410300c642c169007920f6035544000c1c1d01424003100880315100040325280080c00c1c55400240300d4000d40641c0d85401c1d098413103038020381e80d40c144540c0a500240c00c140003d0428035040d031116041d010440305a070141340040f030703000d1514184072040068081070281400325460007840480c0241000340c0f01480e090900c180000c0d04018010801840150001041195500c0d080101d5448000388041e04488021800c000394583d00700721100e208103641003186200851240b0300060040d0081c0060078030b42902c0da1602c80703 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 982105638 1250 982104388 982104419
    0x28081e07050f0609041a01120e06040f0f0605070302120a05070906050a140c07060e0303070c030609020d02060703080f090106050604030f0302010608061306060b0a08360c03010e07060801 82
    0x50740200c050140c0d2901361174034001c0340c0d0044d0b141e00c09403034072030041000034000c0400e6988281c0c54038a003402944d19140005100c83e0080d80081c486e1b080c189107440c1041148203004001450681060140b00025400d0f80103040c042030f01c120054603d5840801e1030084441c22215440011203042040048a0040b002070a803029140303801010481c10392242100d542c800b0728031844039400110700b0040d0550001c074003141e145040340070303500c0c024050b2500340301c9440c9400080c202c166200300e90021560b50302041d11400394041c0101c1d0310385100c1e00703000e441e00500f02d0f054070394400d503c0005207084c00184121000c1c0e03000203054074105401c54880e201003214400048003036641c0d41c400400e0030002081100d1003074072140103c0081003241e2820605503190780d844483c401100b8054840d15540000c0500d9008000311020a160321241c3c15000b000c0111190b29504440001602844030300041168801d4800541c0248a00003881406c5540ea41c8544a9100002e486400600818541d001010b = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 982106888 1250 982105638 982105669
    0x1030f110c0606090702030307050a11011515082d0604020d09050601061103030708070c0606051c02032413030201110f0d0f09110f28081e0705 63
    0x50055440034a08516500a2400c001658440320400007585840e0b0320481d800402440510b003103040440700501180140042c030800c0c494582d191440b03c5000750b100310b43d0000540e000350750720b603074880200c40c03403460803900c110000d1351010020b0401480c2013030245480200c48103499400c03020070740741031011101415580e8000c0e006c20080c62000b210b4010010808d0203580502212751600101500030a0200c1617200c0c41d400610800c02101d4100c600951b01452505000b070512500d440d290006002d03d42160f44e002c1d0324800703050b06039161030182c07400162080e030480d48858440061003070752074001c07880140110f00c80360028064203a402c0c00f00880034403034000410300b66030004500c8100d400c074110011003160049040302442c2040d00642c180803d044030b0070007023150785442d60251580d00a81c1c03103000b0340303800000981c170b51200e81040200e00c0f20a100300341030100000c040c2500100c0d81c81100100e01c500079100c43d84200c5003a1602c070749040f000c020014640f80c20280f0503440c00b22400d4 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 982108138 1250 982106888 982106891
    0x30121110409140f070501180609063b24091917030a08061210052a090f18041118040609030f020a0b15030f030c0c0a0b090d0201030f 59
    0x28169090f0f0200450422101d050b0b0190a0842c24000018030180c4010204140d022890004002030b50700a150b01e820b40d110380c42d0080d41011341044503c01d8130418103401481c0c1c9031128001c454000c89901007121410125240c9031070b80240720740f002c00641c4140915185900030450980240752610903030192551182c1c803801d0302680c0304e105502502d0bc2a4074500741c1e03040010394204d207651150030750364091170444003d180c075440999500c0e03031058080d81c16400503980d140824801048010740c0ca03109041b04000c0001c03011010701c2e00005801012a02e8000c1700c010300c0004452031701841c2c2100d29000d00c030090800d6592030304d441e0000c03044916a1500142d200040c0428010092443e920480c012500450b500f03200e86401030840c074090b800181150032a00100000a40000c2c9043c0c010511069002c03c00944100003420508200c0300c3d01440c2c440095415a0420f01050051901204450810f00c15540300d0700c91040e4480c0c2282141e006161140307000040d07000381d1000f240310001040 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 982109388 1250 982108138 982108163
    0x150c0601092c0102031906080615040b10090306050a05061309020105070f030e0306090f0a030509030c032505010f0e0607060603320102090a15020c040c05030121110409 74
    0x24001c00c0940070b0360308216940000402217020b01c40d414030407000354034407001c0000e40c4c81c0220301c0d902e800010300554a8030f00850340d820199961504005000c076001401803154540700c84000d0b003101264070045034010300344400100f4155503846018440c2c40c01601d6603000d040340d030034071900070012100e040381400300501000300400c401283d00818284a41c07203810503540700d01c08140c0350000081c000b0300568030180b6410306250005c50101d502c0c50b45030a1407615041d00c000000d09180c201c01a0340d40500c1884598112001180148108500840452014661500c0c01114249140d950800c0401c86840c54055141403250040034020b000300d00000310503032039503584a4025403030600700c203000c284458551103598a03941407080030250b00d4000c605d08000c107408182542020300c250701c1c09400c10224015054024442c42c240301000600802c629190aa009482508207015250450a0300c0100300340f00c6c500c0304060241547c01201d6060445042c40402028069070141101c94541703201 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 982110638 1250 982109388 982109441
    0x3021002012d15261e0c0a0e0105031c0e03010515040b04050f01050906270703061203080f07031d0d0201050c12070507111905150c060109 61
    0x421603508141541d218140c40340301d82c0701e038050b22090b0240782c9408440101c03c1001507010040c2c240c0e9480c0c410b1901a031301c20340d520000c1c100705001c01e064a2080c3d808404442412001c00c0f0101001d50481d0f200a62a0702d906042c90500b07403d00500c0c0e090fa110703c00b0a03504200485c620a505e900c6890a0340e5090100b40109003540ea0588800308000c07440c2c003010303410340f90501900303100300e10170340d020032140c6002004151180c0042c03040d2030180d83d143c1c010038415141c01190303c4404c449010480306401c04011440341c0940102c41c804002440c244020404400c001e0146e150b0503050350340c400d0b098807107000b070b4081d40601034a030805044da80d03030b2011400018244136050546050000c0c00f120207108101a0a4440c020000340c1001c4003000314103034441d40003e42c1138018820b490300980742c0d2014078020040803004407156070301080c244075228190803800740110503210243c0300c503a16080901e00c407005500460791050030a4120600601401d10316501004041d003848d4107014900d4802c0 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 982111888 1250 982110638 982110671
    0xc060e1504061112010504090f120504030605130809040b032e06060801121217090a02040e03160b0c0906031812040303050403030e04110a030603140601050a0302100201 74
    0x485030601102280d00402060024034030601568401d0314000c107140000d120343c1014103442c14012148103a903560200028400310410025030b0030303440004856403c00040c40904180c0082c807040b5500c03410000050748412240540d01c0c0b0080e4401300c010300304003505040002910344c0c2000c00340c141c414246c00e12004a15280f914038005007446080c0906080a22040300381e443c55040207041c444103800421031460444001c003000342c4c0203000041400390a5804030740d558222503000c6910810a070600c802d100700402d268031003030320840e400c0140d0748102e241c4c903032039004200080780740d01c141e80050030200304c0804486a02c0200f229040d45420038039000900d1035081a2040c985100d813000d6401c41c20102004074600780c40289102e14186459941c00034154850341c0002410800c81317244494494683e604690200c550489240f80c88040d203000080c003c150703a00c4266041e0102c039080e1101000046251816180043d00c030152060440d024001c3d0104a4401201199aa1001401c210010 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 982113138 1250 982111888 982111903
    0x313021801120b0f040201140d020424080a06050618040e010e07030309061814010c020409030e0a0504061a07140709050402150c070e1008013b030a0c060e 68
    0x9081203141030b0078150800343d083d07038801014402801c011005000150707820a40e1900f0000014248503620001600c03001d0103400341d940500520710301c1c081e5400702100120380114803982503568440742540c1d0a00c08100303485440c4209a00108104000f8000015008031a0341400001e04041042c02040e160242152400c0d0821072613900250303003d00402d580b090b01000101100c0c9070441001080280c3c1c00c3c01c0341d480b03121300300b004014122030f05156401201950800f60b0010030405c41080c2e00d05000e8002c0a038820b0032807040b12403000101e0246482e104290645045031081915643c0c0c0135140d410b81d42c44800195003a9050324210702e61400e04210b00c0024081c00d000124403402d052041c000341010207200c6102420007485030614032003001882c50100d50301d09007807602d582c40380609450f40c480d59800040345542400840500c51346140e800031500005405610f988814013040181142d41e400f1301d01c54a600304010328110a4400e1032503600c19400f13598009414898a40301510f440e41 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 982114388 1250 982113138 982113149
    0x5090a0b03012c0f070509010c0209190f0e100903020a0807080909010e0403390614060111060a0b0a090207150b01232110080f010b060313021801 64
    0xe01000103102540d200c1c8a800b84010b026042200c50300340b0440c00130410500400c100200040407808070401d81c402c001c1c250410b5005800c0c09458181040792440e002103c8003510980d07420180000300a004034411090050404009070403800314041c035410180c01034403401e0701180300d203240c82c001007440503008100051007003903407039910881c4205014017490142d01481404e19054200004650802074035000808051065203c8504440c0100d00303d802d00007241900000e45064a0200449070f44603c46030540c40c031000710940d40701d41c0112100f40c4240c540f40c483c0d81042d0041450f100d08d42d04030001d1004014800c10855407074102c448100d80003000306030703006403141005030241e025a2140e010041402c2c42c0251292811846021850107504010308100000061a0380007403105240130014083c0008003880c542080002120301003c50b000d92403da00030034401500400051041c46011000500054115a52104448007030000880e09a030040050349001c00c901e000500268003801 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 982115638 1250 982114388 982114409
    0x32205190914011a0307090b0307030605010e0a0510051810080f0a06030c051201021309141f09020306030a020306010612110301080c040207081308060f0c0a090605090a0b0301 77
    0x81c5003030914020354102201e40c0359822003160050020000200b00e16903420001131072607030380b41c40f1040c08aa413041e00b540301134040342000c0b0034000c41d1507140d0000021100240d8560850212201c10040d440d401c0d8031455a0014000c0311407001e0380d000300044d09000b072002010491320a40c00020440091400070240001507001d000c0107503001f030f0068441c0c0c205003d5902081043c0c1566070303013040c1d10000d005080c41511101001e5140650035012148100080000c034041c203071395a450b00e0058802c04013903500d00b40440c80017a254007034404804401d08400c0c42c070301410034a0400d1010096102902c096058001d03000441c01603101000228000c2c03040e5920070000300540001c08046445134004240c90800800041081980004086040d500e0403100145d6405051503c0c201d540f140d82039800f08000c040308000f612002c08038000744601c01507640b8500e0359451420b40c0505210f11058500400c1d801c2e007040c0720807031103074015155010024040511003512b80c19240e469030001d034448480341c03 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 982116888 1250 982115638 982115689
    0x1e0702031b01020a0c060f060302040615030506031203010614280206010b070b0402100c0f141b180901330b040b0403062003010e0a0b0909032205 64
    0x40c1d82426030898a500800001c40c1092540c02d4020003d01c45440098106a00d40394860070080d540da100d20000c2d0f07070090081040c03075078451101202416244214010030324050000d00e40341030200d00024240c100100c400d207160f007407401c2521034030700b000b450f020181c005002c070f1a00036030011941501401060800c04603103402c50380c000d103041c1050300029401c880502090000440d0f400d8a10380041d8121028000d80303180c00012500742101c28005000019814000c005010641d031143d07641558000907143c0080d85485108201e800030504030750401c1da4003070398008c40c00000701c00581000d06540040740c1000713014145160342c8940c1d00303c203114034280035520a2040745000c40e9801044541c64450800e45800792607a0705008601c006807250744c1301c044030721024207400108902c04009100c100d4407540c5484040603140c50886d480c5a20501d8a003000c100351400d0782005205103441b00c019446c00400020384803040040000f6035590062819020070241d55034002548644080c85042122 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 982118138 1250 982116888 982116907
    0x60304061406120318060c150108061003020a03060506010309080c0f0601050a0305150c040806010303051209060108062206090503072030010f0b030106050f181e070203 74
    0x1510003070141031251944020f1400700c00c01c080142c59081000e1201c000300c0040c0302c808104c2c01e01c100300d00c0c01752500410410200003807460b04880e0513a00264119080c42d40d449240c140420031501020b580001c04603403c10004038141c024980c02001850007060245040d076442c0ca00e604081070071072254008902c10240b90f901089041c5c0181011030362511641d186403039003a168082c002a110074007110f000040d04100043c0100d03001011007204031401980d41e420000d0254020241c9083c1c0c102c80c40300800c181000000384507050301c1071000900416118012a2500003a400c070302c40990302ca08400d002d01080070741c0b140b035074100e018502859071130748140752042014202c07049056070b03201004074240581d150107900c0507084400c030b031140e56030f22402006224041e82c4411208919820301c0c2c80a6508803998002d55104c0b10258024400581c6520030800c001e040c1c90f602d16000f01d04d0060681c60441c12080940e0058035031490003411010f10203221050040440c0c4e040056403002444160 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 982119388 1250 982118138 982118171
    0x501020d0c02180702150106030b012c010e01230702040e0a03021525030905011506050906031b0a023a0f11010e010b0f0f010804081806030406 63
    0x120145180c0a40d0305103072036001440040044221100144002c8001481c0500801c0b00c0c1c0c449800da500a1019503030345d6000200980041508540001c0c664501540616480051000617084190f40ca0403018000c07001140e000d4141c08100c1d041040d8001680390445000050080c80a881c00450740e48141d18010700007a00c0c217011601d01f850348640042d0340841c0c4e0209408540c04020a00584261074030b480710300b101151000c0c000450f5501000c01c8560a4040d44810000d0348600b009000c1a010b050500188079918800c0c01c01280040064006030f00c0c001008552060003241c00724410391001d400914150010403065015078040e517225101480240040305040804e01c0e01c0b8460110b950985603282c143d1445141c0600801203450810140540c4c54a49006186402004a501e1003d0001d020380468414640252280b046400e064140000340f10b80304401a10369000e2364403591341d074410366031205681c400c0d80d0840ea102000d40c0d98514000310701440c002c2c0400708140f0b10150f107500703 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 982120638 1250 982119388 982119403
    0x90b0a0b040503030406050a020109060518070602011b0e03030c03030f040c0503010c0c150b03160f0b09030a12020c03030f1b010b031018050a03090f0f2111090a06050102 75
    0x5040031000d100400140e80c0000848050b540240340140c0c6500142030186d002d4050010300170441c1d420b010030032441c0516030341411700020028086440065403881d099080b07901012901031140c10010302c04001d240034844041c040c1c0f40103404c40b0700d40303154205000d080d50000d1b2026845d02001c03005110030306c12803081401c081c0208400030010000e150401070580c643d1084014101224500c402c109105554410340460320090706881000b000214082d86907105405154404909100c000c143c0d43c42003401c4c5d1345c41e80c03000340041c2628a882c2e01c6603125a4101c480d010118860a0002d80e142d443c2400904007486a001c0c1403501c400d85e03100e1784d05204200c00000c0f242a854014209450b0f80c0c002241514200c0500000803e54009181d03045410a004009031191049050b03400c03c260780411a04112907e0100400c10507032200c40540d40e401d4644501501c1c084d03070b4014030610146070200703010018131880b517841e0300600e04e10114104401c11078000d0b20071941c8140c100a903507018427420 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 982121888 1250 982120638 982120649
    0x1020609010c0e330307110a0c0b0c0307050102040e1905060d0803090709140603150408090103151203020c010908010b150d11030408031e09150a02040b04090b0a 71
    0xd111014095400600f580c0c500080103128600115941141202c40c1c2d0042115403541080401e13000c0d254103480c02e407644203541031000101c003003c03c408100307008120092100d91110b18030042c140351145c40541a080405100c0c1c80380030070000d201c000b5030241f004100070520303017610381643d1410382c0d507112010351030b010500d10480c141410403015944682903109840e40c0414410385944502401c103151410036007101034640d00d032031031501002c100c030401075100d014120100c48079405680c00c1d1100181064034000e1940744140400c80c0740358080d0b00000740b00c5803920104d500c0e00382d44c0e00c211100141d1020302500540c000c250840c078156804034130710000e001000002e020001482011074502c0901d203000c3c601d120004900841c10540c250403800e002c522414000792a41003900303291207103500c02e980c2c1c1c03420700300100d0490215010704205e0301d00c1503202c03402600c100101d5007510180013800904003a0045e07400c00c40441c900d8460f0010344050116071000080e00900b210a020740c3c0c011a4000 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 982123138 1250 982121888 982121891
    0xa2909190609051f02030a0804030e0d050109060e0307230309042a11070501050c070906031406071e051e0d02040306060b03060a0312210c080a1a01030b030304170c0102060901 77
    0x2a00215030008100d0301290030a10f0880250349e298181128100b00f0984410350044078000d82c4070034800c054118a550702e0040d00308101900740711068650702e00c200f4000806801c04407042400e40ca4841402600541002c0309403860000403c1c0080d080b80c00200e2548080d0f003844a05003074031003009242c0031943d0320504061920041418405580d044540315031030400c9000104917501c40c00a1050704000c160100e81032220540741c0c580110742402c00701d44000c0c0c81c402e00001401d40c501c9407608095a60800c88541440300326041d00301c0d9594051b07420fa4070040c10030450320702c1d070003d0100282004541c0600c0140c94070b055281190990f001e41e03001c010881018824041c855817100c03014030441e07030b01c10f012440c00900c00741c041c3c46003245080620380650f116094040000e20f150069034003640c843d69403018680d1050070031811103425101c03591440a1850346440154002e900020395004010204c0e4186a5141c000c1d1802c41c400060141ea00d030030580f145922541c04020072078101105800 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 982124388 1250 982123138 982123189
    0x12210f1107030b0c0f21090f0a030905280602030c010e010516031d01050a020415052a030c120d0c1412190c0c020a290919060905 57
    0x141c032100741e070f4064413940010703400040040c54420070200321105280001e501401d010503000d00711034031040032078008440b8003a4180303200c400780003c9500503482d43c6c1902c0310440c00e4181400c2c041c500c06d2120085480d04025964480c41001d031002d14402014103900640d9581e10802c485401d4409124158405038100800e02250318000c3e43c9503201480c19103000508600c00c0943e07c02c854038204074a2031a54a403100313101041038950001c10544d581032004040d0300e84e00e2101200d04c0d00c901801c0007800072841180d1041c2244001e031514100c28060101c80c280b00d00b40600a007450010380403400d40c444001014007480361a40902d000003010780c1401c8440910705008020284204004003c048000c0300024050940e07008005400081d10742081100300e042d500050026440f0340016032107a045c2000c00120309080816480c9440c3c030481c05400c1160b42c0c44400021a0044402150301a5210020b01004c1a441503410010002540d4600e5981c5c502030901450740304240960119100050 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 982125638 1250 982124388 982124393
    0x51f060b0414040c090e0403080621060a1505040c05070b06030703122708061015090308090a0b1c1811011b050f010e0106140a12210f110703 62
    0x10110005000b0640703002c07801400040080b256050540c025010340d0035034200307000c05c1c1540540004d12403581915580108d0080864215071005803c01d44a031940c4220005060f01641e5000700e101610b1148803e0240d5441d90300040a464221511900245010913510248050244490380014003940500039240c155241d641e02c503410440020240803040d09503440904401a20b800e400300780101360030340b840c4c036411130544070321099800803a0030200c488081f420b4010034080700c071140c1c00d9072104001c4610390750320380641c1e410000016070321010355040011583c54080041c9103c00c6071085101505080c901c80000321615480c0f011012612450340a00145410b008080850402d00b00507420712070f00611000c200e4480d003402080c600400e640c51400c000b054201d154088074900007805101d40303c503c4604c050303103c00007080d400950301c3d1040026519802100c06460b004503400f050f4408403094900102c4c0f134034070004000503201116403100e1a40004102e0988940b0300207403095070301d0358 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 982126888 1250 982125638 982125659
    0x18040f110a180302030318130b0102060112030905030601080f24061302070609030e010e011b0803061c0c0f1202090106050306030a0b1f080307030801090c0903051f060b04 75
    0x5441241441061420b0190300c04a101404000b903500030700b1240d031450035042080d0341c0120512020700038120900c07001101289402440000f800c103900801e07d50307282844075803a010390300030141c084c00620700c804aa5038600380407180c0a480c5031030090400c0414109054902401070201c405051004041c2010300703c01034a034550000c00880b0541c2410541502c903030024494000002e180384d1030410b11030700300f580151035110304a4090301c48080a2035803400640e101d160503195134001c00c021481c00c0c000100814041c1d03401c208007400e541d1900740c2c01021340086400c402000e0710b02e4034070043c0c20007500401002c8030307015003c0d207901800d004003580d0204000c200c2c1070150005008001c000a882c9460401501c50b8064200350315a0290604440003e00c12004100c004900c1c06060404900250004200c5044d00d90540d00c54515070310f1304040c000180100300c11a0304100e0010700000c00319408010000164104c21304418092a5101d1000704035409940011200c500910081001d070b50003 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 982128138 1250 982126888 982126897
    0xf06020304060c02150307110c06090603460c05040302130903180b072306040b070c141b01140d0b0a05060c0304090c0c0c170a0818040f11 61
    0x2d810191030400301880001c1e08070244640d820b2054401004100b4101d9101d1081c00e240350061041e5587e00789900c091000604c02d0034130454020108002052103c1c0480c0c1e15059031f00c056401c1010300d40081e11312110041c0350301154020403041c10036a5900750f4620720640c0c9007103500d030610900d17162842e80400c07110241040c000803040c1e50780e1144130605000d4002c000c064032150f2403481c082621a00030442ca03411180c0265494000410044440d100c15985215090111001481182d60300d644083c03080d08002d140301c080105140100700002d0b481005101c520200c18003400f01003000340c0e00d001703015a5614103181082100408210328000701e02c129030070642d1503c3e0200305a81c91002040f00036550ba4000b9401000000d4010b0101d24084041d009480105c0700070312802c100c9820444180703044900240681c4c005d03030710800c2058134032100540c00d100103509480e42850310791942c0382e2503000700302d4412000f040a0540103131440c140c8500308000d4207480303040042522482d40010180507 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 982129388 1250 982128138 982128149
    0x1090309090207141f1103010311060a170c09030c030d0909110f1909090212070f0c0c090b0f0a030b0a05040507080d02030d06050409030807030c0e0405090303100f06020304 76
    0x2d00080710000e101004100d0200302480d102102c20307071551030500190b01c60f80546040c403001d25000004400c2d02044d07049034122a00004405d0210807400104005503110b0f195450a1050041103030032008490340450f480b52240c80a942c1e294400401403504040419600f079100ea04202c02c0700e04040d40140e4188140c5000c100d0019440301700180352005031195000d25004420701182c448155040781d0180340c8408811b980d6081d465a4600f800e0050340a0160300201c54810000000d4401d44960348290115042e03260809883c400c2d42c545580003c4540c110888040e02c0754000e085600f0100c0280f01e003034600359200f1180c80d02d035031908410008090080c0c51185d884002040600c102006200041c140500030345103001d84144000e0b5032a40300c010344207d06070801000254500e800e01c280e03420306406444444050340e0f142001c40040c80003c2c00c68080c460100b4074100192168811a8801d400c100b008541c1ca040c01c80c41d03203a44250720f40c440c9103482641e403000e028440c1d0100650302200c0 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 982130638 1250 982129388 982129391
    0x203070501065a0302030f0703030207050306010b040e0a020405040e0705100f120e0c18100504020702010c03030506060f1c0515150c07180f06060806010f1b020303160c05030109030909 81
    0x600c0f401080b003440f1070991001e541403041c02c984940d503c102207a690101c900c81c5d003c44a4150740d85e0149501c81c0d00900c40c100c8041003d001c2000903c0c000c0391119803044003682c0c01072810362101c0018086a1508060356813643c060308042c81075051080f20b40d01c00c2c084e582041010000c880d8001004000080c0b06109034580783c2d11000317070f45042000024940340004084204c0a103001e004210018411144c0d4140c0380c8841d0390002d198140362080790781c03c0b07406a580b0b01c40281180c0341580500000340003503420800c10446a00440c0d118170103020906440040c1241e014402004001905c0020b485058005800240c6102c95270b0b0302c4910542c0d05000b54841da490705481c00e4464200140365028446120300b22a00c100030407003e40c4501c41401c3c525104000b45502c502c8100d80d01001260458013080c2c0c0fa50b05920311a00805175071140010f68040412104407a034042810340e00a50559904d5a1114050314204101150002c0280c101030f002042885000e4070300500070700c094400d07d100340d07 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 982131888 1250 982130638 982130789
    0x281a0d18060f02180f0f060a022103010308030f1513020a0206100b0316111b011206140d050a02040603050a031101021603080403050d0905060a0f110a0e01020307050106 74
    0x3512200740d0060302c800000c103000c0e101c103c01232002c3e4030740c0900450800c0034035800045c01d45000018003039a050b03e403c040c0c81c6083d83c2d036030410301e00f1443d809842000c4140b203101c1540318582e10b005080d407600c0104100507032100c038403a2020f4034044001d8001c02d1444105031040c04400760300ca017500c2d03100715840a00c0158206201060300c1a00210b10044c9241c0105a8a40301041c0a00058441e259085c2ea808058650b075400c1401110654000d11036a280900383d00401c034902a405450380c240294180c550041c1c20f940010300300c40665104a50a82006180d001415080f1040036030202d2000020362502d25107030100001100b0b210360060600c08400d010800b814800c0b07003a110a06031069042010400d24100726a45a00450b9803d26503410490440d5049249010b400440d4180c056420f040403030048050f05e030a0f100e002200d04600c014807a1a010450034010706004200c4446651901e10400070440d08110408400ba011481c41c4115100c1c000b8442e2049008090314003803d1204 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 982133138 1250 982131888 982131919
    0x60103050a17160b100e06090a201803070f0f09020304141b1f0e1c1707022b060f1104060e281a0d18060f0218 49
    0x85018183e0fa0500000000b10007000304111280f5150299440a41ca459101c2e500c400b1500170860440300150408040c03008201c0044460300700d4080111008488101d0056210303520026400c800000200c00602710480c140c9420203200f10702c00707049028542c2d05a6414000c100c0c1c150000e40c45031151480d80040060240303ca8821044408500d6506841107004000e09001070007150080b0340b4400d180c0e18070212103c0c0c12203a0103401c941125114000c0280b003807010041444103c1c40c4a40100e00344c043c1000006008005216014180301e080301d80300d0459005004155046c2c9030032885000420380060068425120f085428680c04040410f0310900680014098030741c1c1300c203407942e004000c10301041058000e00302c940c560300c042d549041e14201d039500701c07191420007040070b4034040884c003818040b41c41501d00b0380890601c0700f4580791410286c1005a82140c0c00d1a400943c41c039403407140c0e081000002d000e40111542c21580550900d0104100d0154100c00c4103132aa10900700403d100741e0 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 982134388 1250 982133138 982133183
    0x3050f0409061206060605090f0906180f100515090d030908070b070209090105071b0507081b120d021b01030e0706030e0d0521090f0715090503060103050a 68
    0x6030884030010302c0b4160351940340c0c0408070025441155050308250340854881d109000756103000d5001000020034441c6d03081071042030100a0001500441300004101501003c203a1442c004c400340101d0f0700722850b00014112801c821a00660300c1481940540c450100e440d2042c0c030441c04080f16102c15001e0a4078040d1204400342e07002c4401380c05410b07000901c0360107070000341403001c0c02a118864240e0754030603800c1c00c846c01100e0801c00310346008010100c8442d841002001e05100e401115040c1d0780b29655a4608040440c41340064031a400c1c40c1c80c40c90034980f0946150401c00c02c0206070b080040000a511803896401d003800c171803081034041d07440e68842e812031241c102808082c1c40100d130322510020050104500c0e0b19401d40b00f403480025a95103d01c01300c4212340311403141007040d002000400b088811024101004602c50952040da0341300041c80721000a00029041c003610898403c2c02a140c1c48040c1e201b2442a0006401000403c1c0f001c60560f4003964020100819102820f20828 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 982135638 1250 982134388 982134397
    0xf0e06061002010b030309100507140c04150b0d05100e0a0219030507020618010603170703030b01090e010b070821060a090905031b152d01031a0702010b19030c0f1203050f 75
    0x3014070be080081c01001407008280407084080c241c50510503405032210318819100c5078400d882c0e03480000c00130f20700e003407000c0d5210baa08108003600c164541550b807a41c1e0320b5641e40c1920418030290703002880d04041e4003880480c4a007040305080602161a01900c080e44503c00103105000114011504407001e440030350200001d598015840fa840320f50015404c0000d40045070200d000c0f0740ba28070790b07000c00d60145084404540d840340341c145a5a00340100380e0841c1d04004c004441d2080c00b40005955038860202549045030120b185070024036003041048070600580d80a81e08031490071440c036000c030b0310103c100c1f282805d1b40f0340c2c43c0c1002060700c1900d40c58441c0c0030341d036400d0701c5c001001805034040310b0400d000c43d251401c0031004905401810741070711183c8284001883c14940c000da44402c10008040700750303c186075000004003d8685004600e50741c404490902d40c00c021428103104200d04140c1901c06000481440d403285800d0240034481140c4901c8007400303101010030107540c140e00f00000c88 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 982136888 1250 982135638 982135643
    0x110a08070e2b060f090303050f07050408101a0a0b280504060809030712111c0c020d0f291303080612011b110f0d120c030f0e06061002010b030309100507 67
    0x2000707000c1c05c03814010000c1c45d058689083e0741682c2d401003080b140c0b02c0e1040e070f02641d0031603020b04a13001143e076100004001e400000702404100183d480e040e5554000110020008800310540d034064441e807da10f413010f0810b003440301283c040200200d085d4008241ea05881882c2000306039910b41c446154514020120010010001055881e0100f91300c40d80d1a01c03942640d108580440131000128040600e0703a900800005140400d28005031400400c820f001a00a411402101d4265200d040c03c600e031041254018001074000b00700c0318104907a0281e8054402c5160752000784403541c00502100c030250000317200d80300c0403501102c518000e6200d020480c4012040f140c0500d042c0d40d015100c1c12500344103015a001d102100304060a000c00c81010841030355450b541d401814494901c010059a286642090360b00c1c1100c250740c080500c0740064010404008181606c0c11078100615003520301264411641031007000030240e10000181c0b0070f58182142e00086520f101402143d85004201d8003 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 982138138 1250 982136888 982136891
    0x90103150512010606180e061011120406090b070203061302120a05100f05040c0306150e1e0105100c080f070b040609020301180203061603110a08070e2b060f 69
    0x82c14950a0154090030031544136403242040074400304030141142c800d038880d050303103481c40c400060900c0ca440744010344001405d08190201d290706c02505c51608542d4007045108540025040c07003210b0f0008181c0c0c005100004026141c0485a404030b41c0b9040060000d90500d403882c1d103c4802c540d201d905054104100c0307400c0b215540c4403820031a82d680302c0c54200500c42d5141001c400315210b400d005151040f0781000d25142424503503914000140120b03020764444406108012612040e0302600310300646690b440003040380141c40d01030000e440b041e0700081c8500e031200040c903212a000000710040700e4020580c1a120765040450307202c548070f030b94030081200d034050f4100410084994000a65503001b82c00030084d900c5201c10707a10050440c0d03034010358158031040001d110400003146420000b0f110b850b0200d0401955040c0400581165070100082003442007007085c0740e9030000181303028503400c0f80d0140c6d03594616000340c00101d540c004101100c40c045031801d01400304e550410305000220307800 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 982139388 1250 982138138 982138159
    0x1603081b01110c070f05040608030a0c021f05280801060e030304030f031e02060903090925020d140a050904021303080c01020406030b0f010801170708030a0809010b04060b0901031505 80
    0x401a031515000c0c041d0500e1740200c90404039090034180308e00d900b61070f0190000c510300b01b00b00e041a035010aa80388100d070b02098000415020b00341241100c050205030351542a222071701c40340016442c510b41900c0c0a0304120041c900740d0300661001c603443c1154070720304284c0a448505030111f8250f10442d080a0541e14515140104041e8004c21800711821000c0451400c4c0c01a0081280c9482060b03445401952091040b44458174108981d941c00c40307404042c0c460000f0a405400030305d01a4510010302603080280304004058001c040d4510310b50403243c0e603e02e05641c154001e096405400d400074003e0f5408142890a0071032904031401841d0030441d280d07200d02081303900780d0207544a4000d034000a8107081400d074603400c1000068140c103005854241c416070801800b520070407030440038150540309503000040c00081c10f00c010074118a890380c5000035031424480701ca081d01c86052030540030381c1c54001c04102c2207100105a80c40e0307000c246004211941c038000301014a030090303001164001c03203111 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 982140638 1250 982139388 982139407
    0x10060b0405040e0f100e070905090102070201181203050304081e0a091d010905091c05040501031407080a0c020a0c0b18090f010608130803041101021603081b0111 71
    0x201410803500c1c200c80c10b02c152206180829181c1c03442907000b115030f43c015401d04049541035003016100080311b10882d164a40d86940c203030f041c0c0e082501c0b4205141d42c00180c070b40655038040340c0071182d8440b10760340064081c03030035410302c5410f024074901804000020011608004042003150f8251f44d400c01e62401540381800101c03240c2c1d200498540106001d010005104001d00d41c40741c40340c2e40c1b02401c1c940f40ea80380900400240c98000e1a0410900400c0c18160100e04804452405000c61350303152521242044005800c960280c90f041c14680030040c108401290f0100005912201c0320720080b4800d6044030050f454501c2d0084004c1402e0803643c004034401041c000a0848500802d10304154090000180009c6060980b2401e010040700c400600c002d40c0108006c581020724a8503e8056040c1c64448081d1a0400d90381280c05151071070940d01250780c1082050514503140710506004c0d80746966039030461007880d40d003020800301403107035213130018080d449400b030034194580d45555180c500 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 982141888 1250 982140638 982140659
    0x5030c07061a1905061812030708180604050d060b01140d27020a031b1a180303310902070c0801050a0225021906030f111213051006 58
    0x50714240c0542c0300f4a80c1c1c0c0d90312914296a482c100d41c400303041145441c446030409100031890588107a0132010218055141a600300018000d0340d0084000d182c4544030000000800d6000002c103520401d81400b0501075540c030913404005807070b423001c0c0019000701c6a10061f5005240410680601d00010a03121700490803a004066052450400400403050600031304104400e50301c2d01075086607500c0c00074000112030002c0700100444c1802030300c0d00f06a8507000c10909014415000040d44c00c08510000140c038444408101120120f0185017494550b41001c0d0304101c00022844000b030501088040001020040c0c101810440009640d501c07000d003002c0640394990700c14207160358a030400007200302c00c544c402d503081c00003020f41d523189282d45207652202c0903e040d0b80c246d070f00520b0b0309010036000c5560310134a0002c203459100030034040c43c1d5410030b90880d03a01c0c00d294401c0b9042045020150750001580030741c0622445481e01703090400b810480e2a04031001d100441541c80c1460200f0850402c = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 982143138 1250 982141888 982141931
    0x10324080a060501080d0f200a0609050f0a03270306140f130b04080c01020d0e240f040b071206091b05211b0d0b04061e0605030c0706 59
    0x294810711240c5d030303030703540a0796140101d01c3c6002c0000c08009401c0040f0b4400c403403403e0140e020642080c651850702503584e04000d0b0f00181120240e036242d409104000080c8005405014404040c0500d01e1603030320090010300350008850b451102c6580d590b01e0384419544900055900608100704000b200410140ea00c2700990704003080ca2980800114075070131040001071a503512a114050640b9544c0e1081c250b600100c061701d10a54080c405051070342030611552800b20345c581e0041000a0306491003407110130a01107111450500c08c410000c11401000d0340a81050388294206580c2c0d68100c001c580e50b11025040400540c00d111000621f251250058002c0c004403810700030045c10064425a0144220510104950900400c031442d61685025542d40300c081c3d03103880408c0110b811250101c5900095050301c1007036032021100c215041c10720a0340c02400940c1800810480111240322240c803d81c840c200402c500040000d214a01401c251401554445020321000b060090301070f085444 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 982144388 1250 982143138 982143143
    0x35090312090315010e061804080f030601090308030a06140102030a14030604060f030c0602150610030507021204080312150d060c09050d031d0307140f0607140303041b14010324080a 79
    0x458070441424800c0e80547c0d4081c40c0e00001583c5044c2d0980e1a002c4203400051031581800440ba80000114a0000055101e445401d0000640b00d0602c504034006000c180c80090440d07106020780d120300e54010309030350741001548640d0764803555840b0000c0e014166580200f0090b048000c40042048010741c5080240c501640a44208214a000101c1480401c9031a69032024621202c298080d01a40c803140e003104540c8155541d03c4a45000302415501c25800400b4660000450307a40d075103909540240c120107000424a598094500003c6211080d820045e0031b16541d01e180b12245409890f65000400e0050321403a18610319040280c542210440c2003e00510782e450f2840e168900030942c0e01c240e071008004911305642e08018090040351850b001c58000f030040040c60f0100d400300b1044285050031800655880c81c03d40351100340e00085510040d00455a44070030b0084a04000851140603000c4c0f0300000c108030405030401d42c0401143e40c00c4040900568049110344010508000c07550 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 982145638 1250 982144388 982144399
    0x31008011b030b0423040c150c02190605070305031810020702040513080406050c0c06030a0608070b0c0607030923030322170705070335090312090315010e06 69
    0x10f0781c0e041c84299614501c04c8410f58184d03030904c4104a0034001d405400c140221801008140c0301c10503000c40000c1c00c21041e01095000b92807808502d0071a5100e000d0b102558119204146080000f17031140c001c1c45402001c0c4007000c000116100c44e044580c02d0012000800c444034420705584000c001d50208806070f00485c10040003c0003000906441c03100700350700840203031a080c0742203800c445039001442041d01c0c0d400b480c3d10000c000c0c1e0314540550700401c050400040da09143c070075110310b4600c182d07000d00b980c4442407006403c041d1000c03480315400046400d01262158451030003803030003070188804503c43c69080601240350360b000000343d44030b034140446480c900c2104d01070b01100c00704504001040d0303c4a2a4000c1c07040101c0c400600741c458450012242c00320782300e980725610f141b59400c00180c0c40705246c1c09032254a50501c4440c0480c80032049151618810a01086d01d903a040300000c942000000340c505201e8030304228103446180c06031801041543c5030903d401005200341e43c11131003007 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 982146888 1250 982145638 982145651
    0x1f0816080613020c01060e0f061c0c031118070305070810050a03020d14060414100b01020d0c052a03010606032d0f06120b1006090902031008011b03 65
    0x19006410603801580000c000202c542e40c0246014065400400c1d01d1030349540310000081c08185402000d4007030602884400e41c0d51030b0410074401c410480c01c4550f1001c0c040d031210080400d4209940c241520340003648010710140d040302140a10b03048070074034091030b002c02d010031060690640c000c40c0107100d59610003c0d43d8540314510000081036001700740d8040c1c07c0d000204010300d01341e401512100d204050642d01c1c0400c0d81c01042c01d00ca0101c44c1680e0784c201c20190f1148000051010659085010354200459006200001d640301a00c8400c1818481d13914141c1051040412022401c0d00030101000d030034011030b4604840c5204020444d83c00780d030a050000c66442e010f80294500d07a50101d41b000c09045041e80045c1000e003208103503014080e6504190301c8050410301468014084801c0c00204101851403c01d4120000902603681c20b44a42c2013400f50540c400074074822100301c01000368403501d8106e1040d803d1103c1d076000240175803030006460f07150690a154041c04c81e2542c1c0b420041c0 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 982148138 1250 982146888 982146931
    0x1207020d0f05030702070b39070b0f04060e011e032304080a0c0c05060a080f13020f0105090301240f08060105061606180b0a0c09030519021f08 63
    0x440c041944c1c641d015070401c5005204041d407200c00303007070b024007200039052041e9415020404003410018454402500c20189661402010401c01c0c00504620003078500d00680e285101041d409a40940707000c0007521130703000d102688148a001c904a2071700e55400309903042004081c0052016031212400c1c180c0b4000756540700e0071008400fa01c140d8100d54282d10b051030780e41048411290102c0c084401c0c6980b03180100750380c2c541c000a0300c11a12030743c44111a60138110050403507400c000b0040c08080c2d44007518540180c403072070004101c4000a0070b0042e1601e01400000b03002d0400c03400740324000e2050740d1941c1310305805042054202c80510383c40c10503c030f45411074079845920034001c4503040030301040200d5400130306481c0714821704d000c1d02d000100d840c0c0004214503038411124094420a00440511011f051240b03e00c00301d850b5181404034807030303280d40d4900c0d854055007485001c40e05003160540003552240c01c0507404504450540781c034451000f079405403600400340c030041c002c2440840301401c0c = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 982149388 1250 982148138 982148147
    0x10915020114010b0a0906080f1f09023403120c0509180a230601051605191b050f0f0609090f0a06090c1b150f0902030c0612010e0a021207020d0f 64
    0x9c1d6030405040c5c40304d644c0740d000100f5281303048172000100c1c00000303000007860343d814400341070000c002c0140c1c900505c650014031481c1c1c910700c0ca406048202d041d0b5036000020b4105030a0600c81941c0d00c4045080d504801c41642c0c1070041c04c076003580011201c014030348810080c182d60351051004410030402480520b95010781031000342d000c06205140c21000c01c0c16580100b0107890819240032242d280ea0b48180c2c1c48600b044010b140c4405d088600d0a982000c0200411840c8200b00e645c02c54200c8261604d00065191049515454062a15103038001c60b603441c0c42d801c035803644401400c0c07000e05003040ca1084082000c100c55402003d4908000801d941240380100051803640307580300011100c003007008a00110707406200b12000c06511065542d0a4954000d41049041d01c2c0380c00141807202c2c0c0141418114200c0307400f0310070709040240003000b40900c0d410380d0550b0310308400880381c0d5454400000080c42401c011b1400d8510203810001050b500041e0000380b20442d9403070486040c0050000c0c0e5 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 982150638 1250 982149388 982149391
    0x60705010e12072d020d0308090d210e07030b0c03041412070615031b03020102150108030316050c010603080306130606121a0a09051e06010915020114010b0a090608 72
    0x820340c22914a10007104d4070041190610780b20780ea204100001040e500260b903900344c020040340400c49180821002c800d0070300c806040285641000700305c449141c0380316520002402d40c43c8007255640c0e1884036815108001802c0916802100d40d134003420901c00c81c01064108441c101c6140d000384d14801c0305004042100090000380083d045e0a02042e40c0d103440280100300c0b413040d040c1c0000b03d0000042448a0101c0c00d80214141100d615a82980002401e0115114100313280da4880e00040220250000c1201d41c00315039135031041d1a40001da04100c0e603901c41c4821203803880d802c2080120038412844000c41c0200760483c2c0b103113a0541c01c901400300b0303900e8174400d03400401d440c920501c042142a4100c061440e419540c2600d50981d00c200040c00c00d507450b04040042c0d95510100048000c880360600c02000618040c000c00c1e251800c0001d103912203900441685c1c0c04402d800d9001035000f508901800a0b04c0d0748844215a12032000c2201900160107684c006106501c00080460047d0303a2036 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 982151888 1250 982150638 982150643
    0x8060f0139060b13060b03150112150512010b03120705120307030c030b090405060a0b0307051c0201080702070b07020105070804170d020712170901050f0a05030609061507060e010b060705010e1207 86
    0x10387c00c41c3c2d01c0c60650030031000c103114028103103c1040006504401c0c0c910072880c2181c94030074101000e50510040c8098240d00344892803142c4c0c034107141e1041c11355000803d1035110b0307046050310783d891072039292850500020480034a10184080144129030750560403c5950f1a07035581c042060100000030003070111301c1038402402c66040034000c01d100c08900d800c00c9044c54006012205075586c0e0708042080b25048008110540740103500c140c0071507074400c040c160010040e1000b00348050402900e040c00d4440c0c0e040003418020009118410072220b00300342d070010312410141e2018010781c0e82405031120b0614034081d0040c020b00c04040780a44d0f2243d800d001e502d40003c0d030000c1c881450448035109512001640d4180030090010000d1501c0b010001d100144031940d8450300da08110f070130700c0010040a008640701e0709103482010494000f00e010b032140e4542045d0301060030194508424010a6010314094001d0f81c002002c0040c84070540085042e908580121110401c02d280c40b000c0c54020035900 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 982153138 1250 982151888 982151909
    0xa0206192d0e01091508041103010203060940061b200c090421090e0a05100e0a0c090806010b04061409180708060f0139060b1306 57
    0xd05100d489610503040002c410304010600d99120b00c80700f08184a403000c00c00019001c2c0003004100200d500e4205205101a4025810b41c10003000081042d0401464496042c00c0850000310344d241c13444103004480070712204c02c0a4450300c400700000d4901500700c182d80c114285207081d10000741e0100304030103c1c01c5594403d00a0380010015050300c81404060802e0703441010502202d581c1c0c4e0204640c0641e01ca0012101c032003941c0220410705000c116136180500c04030440801140c11041c145550241140000003202e40d02c80384003200c40219038001c0c41032100c0300410881100e0f89079114415030f007015146c542c959941d90345ea050343d40c8000d0107034500c503100500c001c2004074069805501c0b940c455007002c504085040000c1240c1a0300511800b60f0b010321442446002034102240c0f070b4204006483e51040b0b00c44800010700406020b5000020341105240300f03c05414521a45072505105503031030382c450b0344940c00c040c406081030b1181d003481a05000300600711000d40784500b00c2125644e00c1d0 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 982154388 1250 982153138 982153217
    0xe25090605090d05011109010f051c020304050f0105181b0303090103020319050408070b01050d030921050f0303010503060f09071404020415030912210b030a020619 72
    0x2011100c42d00040031454101079542c0d8103500080081c080c4803c00c034150076025480710740003000100308a0318162510140f102c10820940148681412102400b1034a44003613541e448500c0e0581c5058800b500f264807075441c14050000e0b4007014480d01805803602d00492303078281c2e060216840d80b0564450010fa15901c1000314481030b5019030040c50740b001e991b6108241070281101c03d042a65401c4400b102c90303000029928082210302c00382940980380075039115503a0f01141e60007034101c6070540555403d0f14011461801429844e940d8401c0465210b400c0d1042c07080c0344c544003603983d082801098842c9c0a001d00081d03080c00c03100b01a51051403404020b05250346403c0c01e41300312a11110725981c200382c00304130110f00780c0c220040781ca050071125a80050040349505000c82c203c580e00c1c080d0020011120f42041c20300c000d180c103e040e42e840500000541100e44000a4900203c0e640001e4201c00041505584810105111445283d1503251044411280003107110070320408040744006216014 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 982155638 1250 982154388 982154399
    0x210021e0d121107050a120206070509030c010e121b03010515010c030c030c08040312030501090510030b090a0f0c08010b010c2a080303190b06072105090a0e2509 71
    0xc1045141003c03801c1490b2610500c4d4032141d045c218249015518980810a010721540e8100002c6620080d1480c105040c2030703030a40080c0d1a4805442060b041080c82c0c0c6468038141d403410300007146419503200b160036213010305a404112031640000300d4425481c11000510215500030702d03080d00704059544c003020003800d07901a241c3d01400c03c2d0030760070851020041000102c50303000620185000703186800074492103420080039900705070882c2142a00b03240500059140d4400202c040d40d5000e030716003080d60380711182d03a444c0403a4440c000e07041d400f071190901e080c045010000400d4564140c000d101c03104000c0f0043d17603e0350080384000d001220050003050820f512103201e1284000014125801c90741e20b02c8001d02d0b50300142c4686049100c3d44541c48003840c03e6110b000c500001c00c1c0e800c80d00306851a124000340b94079041482190354405003244020b18032403c04c650520300700a1455a0540d15103002d0b0f1401c02c0d0403101301d40d4030038460310554400e0f501c1303400b00e84158a0b41e6686402950915 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 982156888 1250 982155638 982155641
    0x909060b0916180b040e090d0309170d0b0303041217120f0601200f0c0a2402030c0703050303010e0a021c020d020f04090903090e01030507051c0210021e0d12 69
    0xb9690301510f4414001c0204900c0340540041c0000d2074618403500c0700d400c04500c0982003e0584a00300241480d00303842070b0005a1203000d8182d4034003d40011512214081c001c0c401a10f0341c460000d605010004021454100c050085600c150060802004880d8000c0505c15180300d215130205030b201d40a0b0004441000c8191100e03446101850238079a00c201c04e074005501817002252031822034021420302e5044000c104502c4c140c003801102e0303e48000e49041501c4800040c103001c94828044211803c1016500030004c481038650601c003220f211613a01e0808545a40003030168405002c1c4e1203010940840301c170700a540354810300b00c0a1494031150192100c009512000403180b445809000b501c04a5201c0000380c0010040120b0118402d001d5180040242580d80c05c411804081b4000500100754002000d00c1034803070540c1c400e14120141c6410110070107006078025030005031641c0520a481d03012540380310840d4620902c0b00000b00c041001030b21104150700040014858003240440d00c002c9 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 982158138 1250 982156888 982156907
    0x5120a02060a0f1404060504110f0904060f110a0507060507080910150f080106050f0405161d0907180b090d0602030c0c0607090303021005060108180f0102040909060b0916 75
    0x1410011304034644802a01c10781c082104d0565146d07643d5000c0000344201da503034252114400300d03400030303202c0741440c0010352161019102806041e40c1c4d8450900304d4640e81c1c071211000d5070300981c080c5c4807503500f01e0040081e0f1140e0400c589090800e40450f08050090554500402ca450054140c0140150f1503100810303510303949410550711444002446480260100064908940041451810300c0d0a0162144092900900903440e110030011f1458000c4441c042030602403038081c04442c02208000703401d5101c1d004095100100380c0503c00200e4002d405950300044405102405a950341c5503203034140101140940c100c034240c44002c000500315070007150300035101050103080c0b420070304105141103c0ac40319480401e02120082c003d01d601000b036042e034043d013024140820b00d01000001c000400141c84c480f91828002d1007100303140310071b009440500b1341c014000c5440310b64401510005d42003111041d16603d10303200c2c0010b56070074401000d51083c07580b103641301c0444060b0303002103442c0c2a0 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 982159388 1250 982158138 982158161
    0x14040b0a0c0915030c020606090705090d060902045a020c070303050705060f0c04060f031803230c0607110703080f0406110c150918100305120a02060a 66
    0x280c844045104880306003d50500b40c07240e030f070009031007500110203850704002500c0305116a0920b000c01200d40d511000f140d1190500b42ca4000c2c0f041407a14010000d80b400c00c200039070190030105800d848800d003505200001458400b511101104143c3c0d100411690102d1100f0742c0b420b019221a9450380d1034080140d0b0040080010302e07122a0201003403c000880d00120b00143c0d00066000134454100513450f040310052103841c220b400c10741c941d00341c036220710b109400511605140d840100303806540325002d4034210901d0501c0c240201d03d40200170207601107030905c0c030000341440048040c890b0000c1c0c509200c240e100514803a101c5480c1036174800c02c1807003895010312a0f40c902000281c259009041402031070901c240e220340c02d0450107002518030010413081c0d940b080c0c0310900c2543d200242e04200d80160043c8070b544139210404900d00300d490548000140e01c00782c007406451005ca03400311003200e000c1c400303076045500351221407001e0f80705858070b00780103074400c50114003a02c1140e80700c80074219 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 982160638 1250 982159388 982159397
    0x110c060c0a0506010b031b04081f09020d060b01020615012f0a05150c090f0405061201060b07140319080702012009040c050c030d0f11070f0614040b0a0c 67
    0x5641c50b940741a0090f000310715440ca01209001031b0443c4030740e15443e020080f02c41c0a080c1b41c10101c0c2a50b69200ea4000500c3e40e00b103a244011031407410f940240c64040d009816008280f1031030a001c0f01030000305208500502c82c100008500a4240600320f45500050b59114506c0d98540c0301603a40d030300111001c024010036000c40c03240c0e40700d08104e8440d40720b10401c06420228841c030800c1d031003100020003149001c0420010715046903102074200ea0700100494001034103461b6040071800d401d54010003003600e5840d108000c110013090501524600c1c0c407881e6424a00c2c100c800f10507459008900c6807101c3d40c910a5001c240040c02010a16413244481c80001a215001041952011488914030407c1080020480982d09050080c00c5c0b903031a484c20228604003176004810360368400e110200381642d0ba0307080981381000c0990040d06a100321052001c0e1140b40314100000c0d02c81c0c040740115100c40c584408504000680403504d40303d260040340094003a619505c01c08060030ba00303500d03d800c02 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 982161888 1250 982160638 982160653
    0xc0a060c0204051b070b1605090d08033711070b061509030304030b0103030224070302070828180602060429070801050a0614030103081c111306110c060c 67
    0x30b1310200d0190840074081c00369500706082c105004030032031030501c900030204403040005454548480c07014507605980003500380c0c0d0b242e9031081c0760a815072802c903001003035030b90008100d800340c1028001d81840804030139003003215107510103518450303100e541d1000345007040c1e40d00058075510780011030340124125800720368506104100041d003968400d420455103501040014414550304015035001c000e00300034926055201c80d00c940702805001444801090340002c0d0310010040180c0030384580b030440c0d825010051b80c02c01d055190b0903040c4801c01d00002d03034504200301c030402004e00c01401c541d5181c004d0489903d0f1921440c5040c0050903e82e0001804c60381d070148041d0038101e186108003403640d104050f55040c0010801c28038025403200781000500c1403580420744280781240d044039444512555a00d1b03401e03580c0f4100d80c00d5001d074003c20f00d1401c0f0845640d05484c1c0c0081000400c220650851503071141815141c620b50003490954a50242e28414118100400101150f841e00300486262 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 982163138 1250 982161888 982161931
    0x1050918040b10050402180f0a080f03040816030c0603050604140709090b0103020c1f060b040609061403091f060b0a020a020a06030b090c0a030f18050c0a060c020405 73
    0xd0620a64044030701182c003a08200c0e028580a01400150904039402d40c5040f196007036250045201543c40c500c07904400000090721ba8510102c08001e12104c03003521561500707840d04a44035085845580051b0081e0b2564004c0c03102c048040b5429280d10040a00c140c5040c00f10480081000900080e003013030faa415291183d006c0e82841910030181031ba41d081407903050581803810b0721381072104903060500500262180c640042101c0300141c1e0b9030300201c0e220900e031130859806000c85910a110000300000e000c10b07403a510003a40825030f841621034840800481080c0341369484101e03050401038001e610001854484070700e40000001d031a6501007581a160984030300d16034807049207000503034000038000c8210304101c031304140148164182004020341c03060200d070301400b0090075140500c40c0003d42541060003a401000307103104074101000351102c81c00036440c1c42d41c0070000a860910400709115107601d40010964158ad06a55407668040141d50921001e8100030f0320076a50000308603412680c = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 982164388 1250 982163138 982163179
    0x30f0e010521040c061b061808030403080f060a0b09060c1203010f0e0f010b0405270115031a01050d0903030e06040308160903080906070614181e0c010509 68
    0x501075210005455600b4145411000802aa880a000c0c030540032844031151408007806d0022907001000400d250b490015101c489290605006002030008402d02007030640c040a0f4600c034545502c402d041c035449613410020034911a108050341101c04109086003418001c0c043e082000c0d50fa021110170400d081606c0c1955002604192007202146034100020280c82584a41014020b4a10001e45d41880c0f002e4182d80b00c1e03401041d010380201d6581030811080190007580c04003181e01d104850396110721000e00c0c292482188800000d00300110b1341c490b005004d140e180507610507101e40d480d001d5400e4074003010740003409080c0e003415501c0410001c144814404284070700c0c0300e59a485014030788441e0200c5401c09481742c0d107080141884041c000900c20f001101d02400c01210082c0c0c9401c0070745400000707040f00151084440c4007007010300403007101d074507841c1d0405030008083e82c00403841e1304540812541c01c40d04288207a80004102d0146500500c0280304811000d03010480000c00c0c04030b010b0 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 982165638 1250 982164388 982164427
    0x4050c1e1e04180f0b04031e03090b0603060609160c06060e062d0d11180709090e03030f04140601030f0318060804061518060e06030a030f0e0105 64
    0x90307652580c519650780c58644203041803420190710150500301d998031004240003400800410740b40c0e49201040606024908800c3c51130505a4034109003490307180014080c042003c4219860300b00000850721614001c6000d52003044060030903a20f564500d4040c10000c00740ea0b1685040c403402c0da003003030041262030084001074550000581d40c2800d00105000001080c2075800b610302a20080c0181030b12049003c0418501c421520010b4454843c00c21000f0314440700c2081d94030003509414241581160540280300310721a484640c4629a2081ca400c180e68840004a5441d001040059442c181200c0180d03085800345031145207203c201b00c18207280240a810994108032000c24040c20968040c01d0b052071444140e005a415601e01000034204243c003400c014041611980304c2e101c1e100c4c03002c003018000c01c8805078000d03800130182e278088003c1c5814021011515554000120760b0304001070750300c0405515582d420b40c12070100c07608039102254828680d0411504100404081c440e6207170302d8 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 982166888 1250 982165638 982165669
    0xb040c0804050606031c080c040906080a030305090601050102100e0a022205070509091602010b150408160803160c0503100e010534090b070b160804050c1e 68
    0x8002504003802c00314a4240024080c511a40c08034500c01401000c8406c101e0b00c1a0340c508043c8003d403200c401080d418000c6400c4030109600d001d20018989000040c00f2044a000352020001900d50132203003a1171306024020700f40960301807103010100c40d00a44c070100070700844400345c0310012507960008000c0a203020507162007021101c0f04a155001a10419800161a00740585003008081c045131031182c00400140680d60369880d42c2d11320038000e41041107042c200908801020948440c2400103070494040c00b040c9104030303944803044041e075698034010785e01c80900650810800b9031000c51080c0380d00404480e120007c84001800c1e49040107410301041e10a08041102001140070f9421510001c0030380040406c8400e40800c140480c103499180e400001c04008100151141c0c02d40c1c9502043d400148046c4c4005048003e01c5100710486001c0c5070003070b80e40e818881c100201261004400e2341e020b8240e400883c441039151500c2080116461141c802c510119404400001c2250031000c541 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 982168138 1250 982166888 982166897
    0xc09050703050601020609011401210c150207050109140405040503161a07031a011d21120414060711130506011121090f0d061b0c08090d060b040c 64
    0x107203e020342e014015140d001d0030800081140f62001446182c1402c41131040021800304580480000c091054040390366031380001405c0395071680c90b0790301d0403001094807083c00140200351011945611a8401d14120b80348660001c1e80425880104002801c010300708403114441049050303009047c55040710f52050003a41040d030500000d814214140340f00400c2001018500300741500381032000603484020032030070720f0040c00a42da00f02e0700300c3d0b21102d0071076285da0110281d4440001d09a90703e0306a4965403040b01560714403041c2000d0b0481900843c00380c1c3d1490740082000d00610704126020b0030000d8003401d030040a1032460750104021015030b00c1c1da9000103031a4005c002e11940c010300e0000428039030b01c00801e04070208086038980d1041d014841030710208005942000d40d0b58164a10031030100085c00c4000100723291900400400c0005003685505000d03187d00c400850160601d1460380b40c1048106280c40005010080090011031080780c0c001c0d40c440c1c4000080e200d80c41100c000b0011500d4 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 982169388 1250 982168138 982168141
    0xc0702100e130e0d030e0c030a0c090e0606010c111302160b15011b21080a0f02030105010c0807030c060e0f07081b12070810050a05090c01080705070c0905070305 71
    0x18442c4400c01c400541ca440340c108084940341600000d00e00c0c0188082c2d150000701a00c5182c072030740c1000b04200c9002da06101c0c0da0494030038030402c404410100d9084d60401c00248100c15412611141c1c200c03503d0340401d01c000002d80114120302d8110703600d608000c2c5a80440e0040d220301e05c040341c01400c0c4c08900d0b208400f03036520030803d400140c6504002100c0d840c04a44002c84002008a0244601c1c1c0301550340764150002005651800103c854050800d983c22862005000411f540340031120041c81e0303414140c2c040380220b80d40c0700301c0c0d05813401a034861001251a8841004980c0005811420000d9249020703000c5511031082049004454002c1e005400c1d03c0e69130b0525101c103681141c21980c202440c111100c89a03403d80030300751141a03a01185c0401d81c403041600300080799101807540d009108950048120551103903119400c0b40004100725125805031951303410315100428045512000032130f0b20075010f14042c05400d031156541500382d0b6180e08200b01555416944e001c00700f41c4990 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 982170638 1250 982169388 982169417
    0x30a02071b0501180f060c050313030b040302151902030702191b0b1317120c0a03080f090a031206120507050307170613031103270301230c070210 64
    0xd00006119070111300c0c1c0400d40c10069101c1050640348503140c1400540c0400d0070400c80c0500070750741e004c40e220403416031032aa81c4c1071030100080c00311011401070180c0000005500280000c83e0f000302c1061721010045203503a010384009500c09801d0b071040d44600c02001d0107a145002c29040124410314400d065202d0f03003104154981801d4102201c900c5003808001c00c401c11424910086409540109403510001c81c8204d007040700155020307410a100249011001d03c0015110148902c250798091460b40e61050841c502070301039a064495400810703140c0b0210344141602d049408041e0700019035255240d01124802c1c00040b000c50385500035030420061480c050100600400e81d4064503240d052080d41c40a4840c0d000900403110540040005401e241c8558080c01030200540f0032203540e108480700400c54070510a401003d0714440c4482d1844070b0030180100e224040c00701d01003040240040c0ea0410703104d0310040200305491024001400540d41d0014080032940c00fa032600911015441d = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 982171888 1250 982170638 982170647
    0x15100e010206071b021314040c0f050a1d2e03050d0e060f0a021e1609180f11060a11061e0403080a0b03030f0904052a030a02071b0501 59
    0x140b006003480b050644950fa440304e148102c1c0d52039641241c0240e600402c0c0700b900401442e070b001074400801502ca04010810058075001d50540d6204900d00003000ea83d07108104446075980111039888181c4080214000983c10040350441e00d020b5041030348022024a071100801c030304441c1d01100d21240307001c0003844400e1113003510205082ca0301d03541400305003020400705c1c464922540350003100002c54800d050f10900c1071a8601a00400b80c188058554030000e40e11100d06480780d165041c031207000103034030704188101c10b403580d100007092144031035075151441a000d01d03174803d40741000340f0012840160303582801098240104c0d115804480700c001f01d65446e08800400008562003d038400c1c1c003000160001e802d42c010350600c0d20310501e9441d807190102411a034201a501031202180c910324601c0b028000c0d220824059404210694541d0031101140300243c1e0445410042104060840c494000080d98000380c0c500c00980340854965a0b0700c0ea500e0750345042c00d240c0e200800709020320b40c1e00 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 982173138 1250 982171888 982171891
    0x70314160e0c04060f02011407110d020607120908040302030102131d041703090102090a0311011b02091305281103060f1f0b130518040f0b15100e010206 67
    0x50012032446494002c6248215104500412040c8910308072040b40461003500411032881d005519808a42045840580740c034503d06181c41150042c9e148000f919440020020301c210155600c0b0000b58016080840051282c050f00fa501903008010100168809000410380f100e10f08080348600e0303140864960541260861714210304006c142440046020f1600d040c00b84003d00c000341d65a5252002401d00a01c00e07186d94940092290f24000184001403c0d0313030a00840a8031086104100d0340d0383c41f00c0c45103817101c0095000e032211001c41c0c082080507440f4130305103114504913405038240d400c0307180c11a00154940007518070141a02d904109410607442e801000c180c0061409080042201d18005002404446181c400c1c103117615a010150094500a01040d5500c41c0d80d100d00080740c4001d801503000742402001d048642000400d06154458400c0b0707000030301c6481c080074654031850310700005021700703007804000c18482401d80d0f01c04810403400798203038031601c40710307121034002a040400 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 982174388 1250 982173138 982173149
    0x30f130e070c080d0902030d03050a1a011b050c0d0b01030c140607020409080d020c0304050a3c0b04150f030612020f13021207020c03070506071407031416 68
    0x5080e030a200700d00d9000500040402d600c140042c0d01e600d00c01d05140014680514003030f605219110078810b0301901a40030b10b015500c03108061103284c03810000c1031070456030b45082c00d00040300100200c04082420301c045414034030a0013641c580038000c0700000c207100d43d00d031030031b551a54943d4010800c0151003113008000b0f00d04051564104007501c00010f655001e6084081d000300d0311884a0410058603d00b01c4041d000035100864a81d8807269505a07290854001d080c00346601c85004101c061508245900726601c00264449150b00848031021030601854814003050219502103003181da100c0c0500080c2c07034000c4210351034803180800203000840c440e04070400d052601c0000c0c0170301d600c0c3d600c2d5142003580545d03801580741450000700d499682c10021040d20113102160f1018020800c982003402140385608076241d5140c0c01040548400d113900c00d0542c003560400c402400902e007181e20680007542c2c0005ea455081d03036a2034400781c03c203d81d49034000b15008103458400742900306101802501 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 982175638 1250 982174388 982174409
    0x6270a0b04090c030903140c070e0a0c11070b04170a120816030b030303160c0f030e0a0e1e0406020705010608030405130203011202091003060912080c0a0801030221030f13 75
    0xc00c1342c1b00500311135070210b409050301000040c180000041004030070010004c0d1341707020f041403400309070880048c05000801c00004e1002d01c0c40115055002039008107030f03082a42020f1415103080001d030300c1040340652090a6024840c0080c0105040419080d4a0401910350112034500304800105040200c5081800e140c54011000030548000043d40c0d440644107021090328404d416007542c5021090740020070800404500c0020140c0c85804000e0044050b20440b02041e10781c200c0502080048039144040c491286115009010765886070ba005801114014500507054445500703585458014034120b070300c00601000341303041040c4030302000f80b1404011030075541408241d07102d006481502030700c100c2d41c5c2008170754072a0b0055400001940c1c0510b0411030844c881c41c03c8102643d80380c5851000c980c120001400c845849801c07240c107600c0715580c0c0a0540c0c08c66003000595003800100c10706034010132540e8010034a0800c02030036408031f214015030320b503e0520300c5d5900e29035483e04548020f0 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 982176888 1250 982175638 982175651
    0x15081006020a0f030503061801030c090e0f03070f030c0206031e01060201020901090519120303051e060d0201180f170d0905131109060403030507020306090c06270a0b04090c03 77
    0x14007080c030f10143c01d6414942a550b0f40c45180000e5a910001703005d02c44662003050000080182015101c000c1320603900c01449408020140765880300d4412200c2c101d5500108000d600090303205c800064410b2103401d001060a18036004910160004c40d000c10000e521903040011f80199025002d00402c501e100a610302403e01c40001c0110302d152140d00c2c02103044240e103415146106188102a000041c01d641c01c02c402d504000707000d4a025100c80c0c40400003241c07007419115601c1c50046c4507031409401598044a15030044800c0140c51006103a507650a034001f00700b201000d5442001021800000c4501c7c0c1c1603204460b040400c1e22400c14140034040030301300099100c0000e440d0108500c42000100300000c14026030140c8545180741c0c4d0302003030000e070200c20160010054100c182c02641121020395a40413100d03a80c0e000e4154840d44400d0511107003a00310811880007110741d0b050000d0500d40c101603400b04940d2280d81d0004240c015022400f0302c281000303449041c2505039289024040c8 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 982178138 1250 982176888 982176893
    0xf031e0105060703181a03100527040312050907050a05040218060a09080307031706040b010206060d080412080306090a110a030e0a1703010f0f0806150a15081006020a 73
    0x107440703180001010b004440c070040007486003008a0784010160b00c045c0281d59010360180f0070081c7c2c0115500200c1c040f0b050408100760601802e100b01000031000c81c0c80c02c1440c44002000034090051089007001204010100c0600040c024035000700b52503801400b0340340c106003c1003020706c510342055004134414440c0e01c03040f00c00b06080c041400300643d082d50307031407040c1441100c880003142c0240015200005441c4101540a1024440480000540c520984515003007200742c40e214100c0e240180e00c40404100c051070300341420b8000c10b21818071245000e0356410800c070f0344000c412050701c01850220410a15041c07401600d83e0001c2028000c00501d104051a003172035008400b03807602050740d105110f0365455000c001c03000c00c6a0300010350001006c10485542d209034024011644110f449280010f16075841401d050f0945001101600c110f0703440d501400780f400d0807003202030f600000080001884c1c80300000c0c00d850041e130319545c8194501e41038402e8503500c4038540c8007004642c040480b5401 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 982179388 1250 982178138 982178149
    0x120723100e0309090622060f14010c1a0c040e04050705040c02190803040804180615020703020604030b0c12160f170601030518010f0e1203100909020112020f031e0105 73
    0x902170400c4410940102c90349281484c2c0310658400055810303d810400726100e20341d0b0705420700300d40441c0c542c5203050714a0710045954074041c0100404051318895100343e6030102500003540b045075945941d042c190346603208240c13100265006c0c1c1c1d80e50000710090000381014000c0d40510076146c001001162104080d0306c41111010b00068084030000c8081170800c44018229401004550411040c80002c580094004c0c0f80701e21551074403015004642141c0390002c1100411a038004040c54185843d580b0381c5581c002001f0f1090324684d008100e80c2c1c1c10489002c080500aa0304e401c01e078030b004244904040c1c442d03214208020b00740041600741c482400740389881e466005000b0f10700450309481c0da60b2420440c032540304c8041070700c1d420117519801c8c40700e465000200c44c504020072100391039040c28510070541f00a0780c42d031b40c80e0b4150620a00c016a2a034002070803a61041c98490000c0c00c0d01000d00b000c0340c1000000c44400c1800100340100081071116000e03244140e171280100b00c0d40342500241 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 982180638 1250 982179388 982179391
    0x51309020d1109031b2e0e03010e1005090a0b011e0902120a0b0109031415011e03080705070803181e130b01180b03100e060102120723100e030909 64
    0x10b0b034817000403104d2070041c1c640c6036051550413400070145e00381d084244161844a2003450400d80000d41e1300d1f021590519050060032007481e00c15000e811300181c6150014003400d0001d011903920b21800c010b54000034001d60582d4000d20052011003040010094851504111580701c245002d00500202c0400540d054040d608940c01a00014900c0002d2006031100c1e0b0040c1d0000d48804644000c003c1c540d10041202d055074540505010303100e17a02c50001c07140d01280078100713652502c0700000034000903105800410b41d46005200320743d1455511800f452543e072043d43e000744010101201034030b03541495001c00000014102c1194030030000c460100c0c00307100b031001d48080420f07181d0711000c0499004541100000e015240036038003c3da02c8a52001e000d52003a1171144122250440020f02802a01a03050203014140d0140196400c00b44a800c4c07250000c3c042622403242c0d0303040240c0c40007080b0210380401081e400180c8803403050f0002d001c0441d0300001050805810402103201a80d0350f860805 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 982181888 1250 982180638 982180663
    0x5130b060910030e0706021c030204120222021903061d0c090a0f030b091905030f0f04240206130f080a020c0303030405031e0a05031501051309020d110903 68
    0x500082c0015001100505400440c0f00418060040302140c910350218405040030b0b131200e0100301810071180210100d108501c180550b98240c20301c1400180380c500040300401c00000800c1e01500d50040e10041264001c034081036080480c0344421443c2505801000000e0011101c00010148401080940c112008281070b400c200000b58411030b654541c2c1c060005031021030102d0104545910340341507543c6e401e46800d0741030310403028541d01c1e040c06100a804415840300242d41012200b60a640e52a045900c00e455125400d10002c03440102c48071038030388030750a804003050040c1000301019050200c003606072500c185049100c200414074111302580080d50061300e240d1f65186001049040c140074461596240c0000401d120501070000701404080e1480759011030034091a140d0514603206401400010030001d00009a56200c2e81200f008004c034103040003860070b0011018440800c4c49038104d07203011540803135141039104062140c206c1400d807482c0d019107460182c00c002a907441c402c8108 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 982183138 1250 982181888 982181899
    0x20c0d050606090603100216020f04060f060807031b2610231008010810020a0e2e0f03061403070e09100504080a1706100e030a080304050705130b0609 66
    0x4208551006c00c01041ca14140d01c02c11501c91031018151107000300580c505070300c202305401c2c00b02418541489580122408001809000d526001d401d56900c00300911940074950703281c4000402610030700b000e083c40a2155035888110b41c010342115002c465018554200c20020010802c8004200114000350b03410b100d00a5078003211500c0c02000c0c0081503200da508040b60200c0c6464aa80200d0003505960402e005d0b0798900510202030003c038040e40d95644000741d000611003085050400740c41d0304d406141d40c405072252501d80048141007511100605c0090105007403000760691511aa2010b03200c490010302541090784002a50344015018284032541c0940100d140040c042103c0049000101c6060056103403508003541c85412418000010848a800b54614507111480716885032100400380c0c10184c903050012240070680c511070a400d132040c0054500411000805948503520500003454058141810b0046103244041000c0f01da42c1400039000c40b680e00c14040e0b0b840c0b200c05440 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 982184388 1250 982183138 982183141
    0xf2a12020c030d0e042007140d091206020903060f070e0312071b0806190e060708040b0a09053003310f0605370c05091906020c0d05060609 61
    0x44c001b070030750358020b02c503072140c420003408115107000141c0326050188054200108082d000541c540c441443e200000a072441c0b820700202c0740341c03003510044500030322006040025100c0403c0c5401c0098030b605100d400400100b08034180c1c0004400004403041e000340c0b2100c2401c0200e05098040c0c50001001944184199801c00b042c40040a000300b060038101c80b03950801135a202480d0010046040d105410120000043c0400240c00b501030401c642d00d100c03c95860b03407901884840c019060f59051500d1741e00483c0490750405c20030507a503890004000c1c0111003a0384c1141e0b141318081c0c0e0400b4004087c410000040c0f1b02d6203040040b08491044168600030302c3c0d00d454148c61058500420b5170740821000d2090100300e622140c86611511907021101208961b5031100c02c90b920540352104080003203c2c2000000c60b008002900c00c141017a50500f84118009040982c0c8800c0125039038070310301d0040081e00e0741000641d00f0380e481661400030001c195100e541c0c03107202c010074440c0540e41010 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 982185638 1250 982184388 982184417
    0x21040b060a0602190f05072705072705040f0b0a12030c031d06070312061710020d02090a0e070909051e1305010509030a1206150f2a12020c030d 63
    0x445d2201e42d5a80402030320140ca40b542d4091042c0c0c0040715104d1001b00d808082d060a20b00b4611481d8059034080e201e0304000740487c40444008410300c0603102c0c150345000310010306c42c1c0720750180c0d80702c207401140041482c0c6000e1080c40545440c0707a00c030742c2030400407104450210f0707084400c100d103d50301441e040850710202c08048076580c04911080d504007038000341e05000e041d440011000f02980c984002d011407a55069100e8084140e0f2154110980102c5a02c09940403546e0081141181c18040503051030f13007042c0007a00d1141e455224106010141007040041a488540e20010b022101e60422040c20401140d00300442c0c50340c0044845c00c58030307010440200000c81103c0500364402c000380503628019650315120b802c094605804074007a500b51040ca2446402a1001e84034140903c1781740c500c0c03084084900000364500001840000024284042c800c00380014008030300340c041207070f40c1015140012030940c900e00c00c00d0454101915014055402158132030118030503103842400d145100 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 982186888 1250 982185638 982185653
    0x30317090c030a060e010c080907050123030702331602010e0d0518030303090303041b090c09060e041a06092707020601120b06011421040b060a060219 66
    0x4956545481440100020040140c12885510545e0b000038031000015407000d80d021042070718220001d0f00319400500803540310300604c061000c200c1c4030003401c4240210304000c25034001c0d200c100c01030304070080c94020982085a4002c0140f90384514074134414030704090042600c07003d4200701140052000b460410303031003508084a5903010100f91070038181010005841603000541c5074086118001d551491031a001c0709072885075882d0b5018510f15540c035990040c0b071389400c034286112108146001301c0e504003244034022040c0d100b0380300e030302c8114223251014022046140541e845a800c05144404542512030f020382a0300e002d90b0800c0d00e455607000050207009640e1071042e040c1d072211810b00c0d0403960b8080b00b140a00c019400341e0750f04d079072103001303856004003030a9020b054201020042412540308081080712402000d4166040c2280c104d01c41d020046a000e00200c4108120240300602202040c0f490304607600700c0744100392030f02e060320107500c82d00d0f002034400c0746400001030743c030500c00341 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 982188138 1250 982186888 982186903
    0x306030204020d0902120c01021015170a110904031b020f04090b01090c050c0d0c0c0b04080f0706110703060f06080601080618150c0d060308040f0302010e0a03031709 73
    0x40c41035450ba0f15100d1404010070480f10140e110364076403030704403151800c08508000210741c107034007910348100712146040140450031032a5031900b016202c0060010207044210003021100c0b006004036620030704104c5030208003046000d12908503d014800021b0b0071900c0e402c4805189140980114028000a03261910100035203800c2400c001410302084040f00105040c0c0340c865400300480c080c0020304440e0b5005400000119505c22035018080c40d0007010f1050030709200703100034281306864400d07110454100341d1103040035a1000301641d2501c8414051440502140d2400ca032a030001c5030341403a5035001d24440641406d030388418000170b510460b00014060480102241ca155940e043e5665a0b00b01c201c562191000046221110715030010900808079840300d082e008543d10f8004504035282c2c01004603501d00c075a102e9000001464010180008220f40d800b00c49036180355000151000d10102d401c039100e1201c682c420f0000035001841c1100580792101440c40035076030b0311440c0e49400d41 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 982189388 1250 982188138 982188143
    0x4060f03150f020d1401091103041704050414090c120615060d09031106240108180106060305060a08120f030628030c090b0109170c0d08031f0b0a030c030603 69
    0x140f4a030110106400c42c0d05c44080300e40c05000c0300d0380c4c0c0e200494100d81d440d106e11145440d0810201d4049400105403803824880d200c58240340540d600001021101d40b001201c00c140084402c01442c46000e001701919510251020070a000c1c0d06102e0310384443d4000e1002201c60201100c0002e02c1c0c84040607079480a40141d01086000828200035003601a1128541d68504c00c400c0050303a40b010143c12510008404c801070350802400900640c1d000000605145200002600c4180a12001d000c0c09000308415100051103050100c14040107441d0b642018100da44000400c80441c101101101d0000803802d0000b500c0b601c54000041a0780340c802c0d15000a03c00811804101140e20700d80802204d05c10408035000c1035480e591082a5200207003000d011030b014020412040365a0f50f0308800000e411000c0e15010030300d0800080c81c60003804001c3d103000340701104000b60a01d0003000c0040c0d61001c503160100b035500e481c10070320b41c600c513400c0d02c44109600d0b021140b02150103900040040c56 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 982190638 1250 982189388 982189391
    0x2030a020d111f051f14060306061219050c1c2022092304020f040903020309150705120a02030d0507260c0f032a03100504060f03150f 59
    0xc00f00e004100500b00542c0c0500f10742454071200740c4442800c642520440344d038840202001880c031000c0140d0781d00020542c030380141c1e0400c915140d00094a072460f1085c60500480041a07448440b40d0084420052603210381500412650000112804608142032000800841c10300d00901942e42450440e2184d010100700c003192810803024000040101d540280e00d04da00b40d981c0d203404c290281d800200410315a12650245040d4403200c80c800198001d0000d446400014042400b0034111a40e40c07a00741c0068201181050f40c51822010301c8070306440041c0070f2400d000650325a55180c0701c5244006c101c030320b0001444c411450080c001d640043e02800c404002920b00a00081c00e40b407030039680c50308000e20200c43e08401e030006207161402078040705443c50404100c0603034450140e201400400400100f003254074102e65021680040103441070303d420751641020791f440398001010703820545c41035081001c10b1160202d55172410b4212a00b041b0085602d00c000e40e01c032002042c0c2c0140c0d250030386 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 982191888 1250 982190638 982190683
    0xd0e070803072f01050304201201290619020127121e0c0510020f04170703110f011701060509010f090e01290301032102030a020d11 58
    0x101c4110324103d2082e01c15402e06a111482c01400100d5446180c0351030701180c800c0c00410080384468580d010880c60241c0c8095a0044a1001900d058519201050030b691166181010355200b98800300846500e003480c544201003010000356030303004034106040c0380928080813242c128801d40100b00101c031009426000d0b10282001114a0303c00c1840544140001900d404910f9206660403080c00d6422050322440325800c800898020003100002d03103417440390802d40481c5480f00d20061401142c02e42c0c103990756a151005800880d08507880c450516003000c0010404241c00a00b41e44514004540424a1002040050318840101d109040342010703428000b0800e81c3e0800014569100c09807142c1409500c000000c4441c40b42c1070160514041301701004012140c0402c0d001a224020403213454000410542029010b4100764810340e00220018102c800715103034403034000191800b40c030203185803400820f0040c3d84c3d00c40380c1440c0020009146503000400005100d540c44070f80400c8490f1038807 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 982193138 1250 982191888 982191893
    0x2071a0615070c0306180b062211040e010618050f060403060510210f0b04062306040c0f0e09040606080d020609060906040c0306240801022701050d0e07080307 70
    0x168010f07070008854180c9824414031501e14038100c80614998041807114a50340c5601c14030080002d01c94143d0302032918840420548485806141144201808407a072104c0ca0500c0c4034019100c103034071007818480704440130594400d801071500c082d60000e541d4a800c582003200400d801388543c2e8406050549800e080c4800c20310f03a07000d250b04031880c03010001d0400f114600d445004140482d80104403005a0030804001101c0782d03003050307000e0300606000402c2c5020740300040080710102545070341c49021000300511490329101c1d50000220600d0150005001008041d00300c4510220452103882410000782c1089219000403016090b4030040e180a00c041d564082e5668809a0b41c207940d078010f510000b01c8a0000040b10f500c20f40e081495034024900c1d545a8000901c0c8414501d9405a07400d0341440e0207075940010b41e0010701d1540001070345c420039070300702414251403085a03542e030241440c1e0120075613034041c09841e0000c5488400082c2803007001c200c14641060365100ca48640000b00b4020203 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 982194244 1106 982193138 982193153
    0x130b06030309030102191223090c030f0706030501170c06032e09050a2d02070515010510170705091207091e02071a061507 54
    0x16280d4000042800ea07030046c84940001e01074a00101c01907580b220300318107000305544040040304c0c0b01c0c1d11001c6840c0ca09440d120345c0350040038082507000a041c402c030442c2c142c2c01400c0302c1411030b2941d11b00d601c4078024414240401d10b001d00028a8000344550b41c0050394401c005000c84101d40c1003041155000079000401d10401e540c1c00e903403502d503502e072180002040c5400e0492540e140900c030b50150343c4002c00368800e00e0b007081004c445910440380413664107594010341202c00740e1040742001c003d004461025102e403050700032600c00e10098208840c140d0340e0a56003101c044090800c1a94803403201c036214031100307055000060810380301788040d05100b400140043c01c1880c1c40c011041c43c02c5026007001c50320f10380d204000030103007900c070015003c0401040c82c19424102542c488120407980d102c5500303910040f2000081099455003011403201e500e2400c940e4448500742852403 = true := by decide +kernel

theorem cover : BRFrame.Cov 982014388 982194244 := by
  have h0 := BRFrame.cov_init 982014388
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982014388 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982014388 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982014388 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982014388 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982014388 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982014388 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982014388 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982014388 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982014388 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982014388 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982014388 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982014388 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982014388 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982014388 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982014388 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982014388 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982014388 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982014388 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982014388 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982014388 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982014388 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982014388 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982014388 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982014388 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982014388 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982014388 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982014388 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982014388 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982014388 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982014388 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982014388 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982014388 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982014388 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982014388 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982014388 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982014388 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982014388 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982014388 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982014388 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982014388 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982014388 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982014388 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982014388 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982014388 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982014388 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982014388 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982014388 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982014388 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982014388 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982014388 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982014388 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982014388 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982014388 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982014388 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982014388 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982014388 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982014388 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982014388 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982014388 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982014388 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982014388 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982014388 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982014388 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982014388 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982014388 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982014388 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982014388 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982014388 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982014388 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982014388 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982014388 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982014388 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982014388 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982014388 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982014388 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982014388 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982014388 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982014388 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982014388 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982014388 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982014388 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982014388 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982014388 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982014388 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982014388 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982014388 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982014388 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982014388 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982014388 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982014388 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982014388 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982014388 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982014388 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982014388 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982014388 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982014388 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982014388 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982014388 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982014388 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982014388 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982014388 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982014388 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982014388 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982014388 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982014388 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982014388 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982014388 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982014388 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982014388 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982014388 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982014388 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982014388 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982014388 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982014388 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982014388 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982014388 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982014388 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982014388 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982014388 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982014388 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982014388 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982014388 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982014388 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982014388 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982014388 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982014388 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982014388 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982014388 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982014388 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982014388 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982014388 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982014388 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982014388 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982014388 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982014388 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982014388 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982014388 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982014388 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982014388 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982014388 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982014388 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982014388 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982014388 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982014388 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 982014388 ≤ n) (h2 : n < 982194244) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
