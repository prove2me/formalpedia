-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1570
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T03:43:33.891984+00:00
-- url     : https://prove2.me/submissions/bb2c48ad-765a-4ade-b9c3-e5d3e405bd7d

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 282194244 ≤ n < 282374100 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 282195494 1250 282194244 282194261
    0x201090203060c16060f1806021e03040201091e090c03091b0f0506070822080606010c03080106212906040f2607030804080f1b0f0301020c060a 63
    0x102119080d031156001c804251040248040c4d03401c00c02d101c81c001141c002d41252045451001c0c0c00074001c3d50103600705100c074024080440b00d0640010300500b0315140c04418910010340c07040000d28504055001820034601c9100e40c641c034020304504114290744c07510700d000003002101f40c00e0000001040000740140b180c00811a03003949814144031f00302498410142c15104061410422942003204010040d040290120b49001e0201308490b8403000300d8514075007500e01010002c0c14241054551424400c00420750703810021081c0003507001c694408907041c11100c0c0f606102e8142000e800d50200c810f61516462412107081c48034034030881080c40f0032114800c151040000d41c014181c000c0144510541c4240c4e0200e43c4042d40c24088514041c08884801d103280d038130006020812408241841e20a91054906020200701000b00c0e1031300344450b00095240d00054076040300c030155981407030240002e0041c014000e0340c00045543c0c030b0941c11a4110400c48044468601d00411010042d110b100d = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 282196744 1250 282195494 282195499
    0xa060b071a1503120d0b0a150f020c1f021510090c050403020306060402091807051903020c301209010b011d09040602040b0a08060f0d02011e090803040602010902 71
    0x2400030b000c000850301070280344a0014082c2010222011009500f80c100701607071841150394444104461344d640464100414115000b80c0300d805180070046c10711159906440103540080721000f006980f00512040350506851500d810300d03013030104c00c0749800e00b84e040d2125130b00c47c0c18007404608081d9030402000c85202c01010300c04030401c0ca000300d83c24081ea2100035019030289001c01c00b2498650050205818054880d19002c0341032501203c040206072017400100e800091410900447c5060b541100040e070b013820361900c80d014407901e6850281d225140900c0c158402c0c0c05000c440074035490008401030700003042d01c0701c2ca21036600205860990b00114036600e00f040350121035024496002c600c5102e190b940ba10031030900180148175078028000c0351980d908000101d410701081d4040c00f80e100309960f07100c00ea841d1210a04c11f40c07800f04100f440c4070381c0c04071aa1600603a840b401031013115500c06038031803c0341f031903c401342ea0f140d05c0c64008a08034003000c039003c503a50f941548003e0919008 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 282197994 1250 282196744 282196793
    0x51005060f0f030a060c02010908070309050a0e060f09041415160f050f09030109120c1b12080918040302030d0c030b2b05010c09141f080a060b07 64
    0x1400c01ca2000c01450ba0150150404051030b03010904a0f0301110701c5100600020075100e14550750b00800703502c04201100420241e10040c400c1d0705000c003040028045200c9242d101d42040400900c24045071030b40b491141c00041c1c002005c010624480c07008440441d001c0340c0e410003560b080111003c80c11115041074805002c02004210301c24030601e40b5404907a100d103454503080048000c480c0c0e000b488038580540d01c44402000203954584070404440c151358036552401030500c0c000704202d00241116500c4c204201003400000c41d0200c8580a01d42d100c080e060b911100301c1c0201d9031a4003030f5110b20068400f1a0304208c141a0048020148052410410481c844d0035050a80c12203000c40103150b084102e403001c00d03c900b0000801e001200b00d00164072404048541d980134252410b80c1d00c040000780500c0810440600c40c40c00801c00401d003114041c002e15444030741540f1606028420307500300208403020880c004050780c450005059050089079032260b01d41000083d0380100c400304c0401d01c9a = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 282199244 1250 282197994 282198019
    0x10909090c0e150f1009030b180a030e030f070501080606160b0a0204181401060c050a060c030c14040e040308060d0c0806040b0711060106081005060d0b04060605040b07061805100506 80
    0x217140c008003032510040e031070700c81c18242540c031000d1814100600102140c1d0801a082e440070701308001c5031140d60320a0b5201015030004c00d082c1070504003c64102115544411003c1c08585c1c0c2014203194410016240a82c0325034030211005110b211498028025151403028420160041e0b0000c1094482d412034585c0c40c41403066445040f9500f150400c00340002c0c0701d005204807441452100415400f4804851040409071110002c40d00c3c0600d00c1400f00e0350b22102a51000d400240d900c01c0a42c0410321035040c03070320348201c1041c00c03803004000808108208000840e607a8400f00d00000030f40d080308003c0380e000d0b100c07900c061755440152402d695008940c8001110503105001c0b02c284810030748094403141e40b810700152040e9402a00500c105484810040313410744991003d042410300d60000400c21110b0a0240000c4800b01c0d044001080810081030080c042c0c00f400311003115034080c0d000100d40c9200a1010245030000320020140e0160b05054015540303d80c00240c09a04222000d030100f04 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 282200494 1250 282199244 282199249
    0x708070c05060412030c06090503030a0b090601030204030b0604020c012406080a02090f0909070909050c040c0201152d09021e040602100b0f0a06090602060109020306010909090c0e150f 81
    0x3c1d441081d456240c92403102c40041d12485184020314443c4102103801b2465075141e908541048030251b400955494002041c0c0c90261a543e400807003c0c24214a450700b07545411055007001440703e802a0380008243c80a0602548208075000c00310382d20f108078136040c140704088020588202c40000340401e0200b40302c106c50303100f12140d000c3c004001c01c2600d0080011b014080d9401000c0c07031144c0c040c03640000b50b100d0345405010302c0c0ca441040a8440c40c0b10010401045403c034a00c01011a0b24107880501c0015664600e1030580300c01c482c207002092194109100c841101040c1c588110103103041c00240c180068024042c4980200e40d4426040300b40800301d00f060103148a000010b9011111954084000c1c2e4401c1080c510301600c44111000044041a003810442d400300001545040702000601c0e414003072a800740000313010030742c51810144c00003400d030201c074000d42491a035038480100401603180704140081200d5004100c0c58a08000c460b0403440d602c4207102e000e1a0451440e50091 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 282201744 1250 282200494 282200497
    0x90412080c0f0418060b0301060509090a05010302010c03050f0d02040b25050706120e070b03060a15021507030e010603031d0105070c091508060a05040611070312050c0f0708070c0506 80
    0x5555440c030803810903150038000000b1107000d0411052459890324017086c07035a801c1000f90b029121b9900c40c0c1c1d075600e4404040c48000940240b0394032a20b450080180700503030b8802d215001c080d0f011700e00390340c8a08540e4001c003d40d00c1524100d05c1d115100003130004030340c400d50015020751a0254009160080d66409490040d4030a0700003e10300d41040006000003401010340b801074005440700000c010a02e210280d00d000003d030450300e0300b040023008001061074240d07003c4006c1d2043c081c0d0300006030f14004e006983e40d1184688850380c02c07078010001d02d0710b500c40d07407002da140140003000388030446c2d580c2030240070100b6210103441c580342c16007074850705540a003080303400c0c1c1540031004001251520320f680c8010210000401d0940b205003400249103001000001d00640b0711850008a500f8140b40050888185092400300c250040c8030060200ea0800070f1041041010f60000c50039585d0118141c030b0b14850a500084000004034040f0140113180f005400907910640717814014684401c10040f59 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 282202994 1250 282201744 282201757
    0x32d091a0f0117030702032a120c0609040b0913021002210c550b0411030706020f010b010930021201020a1706030c09090309090412080c 60
    0x800c0018801002102480b144006100c3d0340b5074196402c041c403560000b0b003045145900c41140c0c1d0b11107074942402040d00c8210743e0880d0000c603000008003c01d20403c0380c8484500602c00d115070f03004643c1ca48103413280e40001c4201c1c080106858404e1500307141c4004440a03668059020350740c0040e0014007140001812030314255003441094020380303e0041d03405554043c080000403806850748607441102840c0b400c1109284e40511400690206c8032a054921800d903002c0741b40710300303c00a01321120208295140c28507005404c0f41c425507641c0c1002d60349021100c030440e40520a00c64006580c941c00304802e007038074501000900c9500745c003c0044a40030003d0040010b40b9200c0485e10354403c4a01400e00300082d03607040005214041c07a000600f0018440d0743d00d4055940014503503d001d23510440e12140039121000c200c81c43d080601c00b0079507500f01c0070400d50140f270260000c2041e081c1d0400c141c0d80c4190703004080703c0445c42d0030301d40a2800b58111000c0008203144001091030107500d9020b8400 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 282204244 1250 282202994 282203011
    0x20f070312230903071e050c03010605210a14101415010c0c0801050c0d0b01090609121703040501060302091b03070e012106050112110406032d091a 65
    0x402d0380b601c01d4a880c5100e015051030400c2c030080140c08009404500d0010b98075141c030450f000580c903107017001030400c03403020300c55442070345000e0042c030059546c07030806140b0300800840c0e00d06080d42d0002107131a00e0760024020b4101c045d100c0d09001c2c000f50000c2c11080504007484c003480100c202820415050030159405001d0031001800701d030803944144401e2980c1802100c001002035501e12540e0308580007640c1c2c50207290400910f00f80d401105004920f00402c1c2031904440c1d061810301c0c0145501e5450003240c0440f801d09548000380b00c09500d40b07000300c0d41d89a200c40e540b420986401402403800b480101d0050b014030b0001840034103a60401d18100d4000d000c9149140e0316148100c400ca00002c3e280383c184110603c40b1005038802a82d200300c2c001ca82100001d141e42000009822009894120381d0903d08120224a400401e10b081d641161140c0c2808901400074441c00001480c40000c542c0c007007802a62045051492500a08030060141a50755604201050132607030b141400c0f81d4205 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 282205494 1250 282204244 282204281
    0x1061107080c04050405031e0d061d1602030f040905040203150103030e06160b0f090606040618050405030702090408031b0a171503010c0302130906080604080702040609020f070312 79
    0x40303d00b095001240e02030301c40c40569280c1502c81d42200c0b441e000c5000048400f12000c00d5031041950b10388540c1d00035040001c81020101d44082010000050043c580a60500c04899180c1c40720f0007001620088021000307055180c079103989500c401080c048905074802e2040f4641c0303809440e00c000a82e03060b2a01552400000c600140501050342c0c0044000c1e003030040c4844000c0c010440491045008900d0095004011300306504800d2400c803000d41540c0c82146801410880000c02d0344401d1580c0310300d2103020640d50b41c0c9081450031805070000c065000007c1400f0081001804401584682030ba140c4c0c0d2000c0b1000a120482c04d0b0180c09540340200d20090031090614150340d16080d0702141c1c0011061000480101003803c3d541204070100100343c01203616215100500000030249c038105808024007443d100415640d500041c0018210060000c1c030f000079910740e90400b03005465070f000103640c0c8881030002d84405a0141000340e00040c01e00300300905141190043e003240c4041c111048 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 282206744 1250 282205494 282205513
    0x506040506030c090f12010905010e0105130f0812250905061215040e0109031407030807110a1a040201030f060e1923040302070812030114060717030106110708 70
    0x141101e81c000648250b01c00b0305d80d1400030451741d41c1000080c13014183c1d00003240d1030140789841801c0d144a01900e00081c1d0401d420004820140710480385602d400c0b00c000e03c5500c096040002440c801c503d105a11254800e0401042000307070700a038030038100028142040302d981c220b8116050411802080d6120034200045d0b0810b031420302c1c0c000c4c1c001c01251902903035050101c000070101c0f16401070b1010141d440307a05a500b03040d04a0100303110300d091b0006e09460b0100d05e50300100018030003840e140078848244004c034082c1c50301308440020150301c050601ca44102940074000800000c0300c0890000e400c0407070495030802503028900c1120030000f03042c02c1030b0f15240701c8140317403202c4c1002c100f400590341c401c414188108034040c1031042d0801e80c00113800d0304003400c00a04000454020060b01c2d48038405541c212250071044a04541c25041d039a141c0740034040c0090128450000302507c24500e862892800941400c002c6d030484040d5118030142a8100c00d0480d20381841e4890010140c202c2c0f40e21 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 282207994 1250 282206744 282206761
    0x60504060c0206071e1b091e09030207080321010b09010c0b06011202030f010e0112050703060b010e03030a030e0d0c0503030415181110050306031902130222050604050603 75
    0x5403e41301c0c400e00e00006042c070440e41d120501c420314542130722400509104440529035218148018010b280820300a02025466001a613100f20100c0c030040e0790303508500020705100740318407000b910242d02170340e075540340d03440c000b4160010b503003020300c00350058900000d000840070040700da400b00103849590002000da00c0304031102000601c418148903a014003940032800b144020751185211925003201035050145030568100305811400700400c440d525400072134000516501100e5002c1408220035004400485c0c0054070000e40b1038141c072022031228001030f003541000404034103036000c0300c440c4886e00c0c20448080c900080007505917001080480c010500880f200580c000b00c184000c2590940b071211028143e4003a581640c244c2150400c215440c608800c02c03595085040c0740003400e6080510019884285005015600c1600310104408645908840710300c24044d000c2d0440d11a0307401d6040028a0002032045016010016404603880c0383c43e01c1920140d550240c081821940c44860 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 282209244 1250 282207994 282207997
    0x8060904030e1e030f010f050703060f091e050a0c03053303010e0a0f0c060c1112010b09010f0305121306110109050a0303060603150302030318012303040c060504060c0206 75
    0x1a45600c1403883c42c4990b00c9502c04010300d08200c0c038010700000d16104200c0112003180c001901403020581441000c00c080d29104281c03106450f819040000c0d00c00d91254201211403906400d444018140810001c50042075404154401200c2c1c03802e01c810b40d58003071100c0c043e0840e0b803882003903c041c9182d64181c194003ca884011018041c000040c201c8009502c02c4c500200818200c90001c02c84104c1ca04006002100d48014811418181e4002c20f466441710410101c20004d20300410201e0f5135651000c8094200c0d506184e405084000c072561a0000072949001c54041a1690310030000c3c2c0020f61a4810116091018000b061a00f00e6040c440110750522141c01c81000c0ca6481da0003800100d4014810001558881c2d10001a240e1400d003018082c1c913000d00989000c8900c0000400240e00d01100b224008031800740c12031001401d540050310504000c155003901c0d0009241c110303071384d40b11031030085014a00a400c0b41418941e80c82c81290309100e0360140f000080c400c220007e006040000 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 282210494 1250 282209244 282209269
    0x91305041b18020a0c150207030207090507020a03030207020d0b04060f0e1902040b010203190f03050108030c0c1311030103060507020f0307050706051b0313170a0807080d0b060f090108060904030e 86
    0x1c0c044607175124a403600d10002046051311403545a00003420b00805804208140c010321540b4401e1200e40303010500a51980c540d640c01906140d00064000210750721440b42030000c0d81d002c25a9030b054101030400100400c046020b4482082c03610200e031006642c0040c1c0e50400c0c00c401103546580e464280d007480058040080011b05510040c00317010001e440300c036000a0345403900d5462060040300c00720010140e4106a101c0b020b80d4000304107025003c0c2008c200031414034010b0b14244a12039101ea280401003000d081c88100d03964010001000300051508a07a025802a60884201d04408102d441c1c8034810080d0042841c0d0091038100070003406940600f4590455150703a0400150480c1c5040c2568800c0007007500301c4049038402d102ca04d4810900d042030b0022440282110800c90340c2e0300c0c0c00c0f40b1800002804804001c50301102141d0300340c004840180f005094151121290004070210390810103005002c42c2d02c600000e0b020b0305210b4840d070320440d0160b64210104060340c0511944281e0003 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 282211744 1250 282210494 282210497
    0x70209010320090c09040c050a1d0a05120c15030108061308130e09070602030a050a0804150212040c0e0606070609060905010e071a040506091203091305041b18020a 72
    0x110482d100d2695040f414034465003981d5203855076250203808010407a44800313440c40502c607084c0000d13018207034031102c00c01e080d2000114085095035814006404042c1c42d610030347e0712440340f10719900c40340c101048a000415040d02c2d07444090384401c9030100030303020034003d94405601050008906200c404203410325035025001051508200707909071401400d8940003120111454018884886410845030740204428401746007070103a504401003140c440d004d00401000b0740d150200b8140720540075000e8000b41a070f1070465403003144c4007400744114012281910088080640004c00c48048840d680c031800b801808145000308030f40d19503009104800c015624569201e4419000403000d20070810704000b1040146030f907500d03240360f080071014545107c3d4000142844100501d03204d000544d40c0c080c1c012150002c080191145d02d40c80c43c000c40e8116a440901403103072002906c2c03a0750250f40982c2c0110301c074410a00649551114507141881011800e84d4894040146c002d40b81d03001c0d0158100c00d = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 282212994 1250 282211744 282211793
    0x20607031b20102a0309080105010e2e0306020f070b0a2405030a26030a021315081f0f140405061002060a0518160e0c0702090103 57
    0x103454192030811003584480c402881c5661606041c030f00300e50308048845030780ca0101c0010b100c016030b070f0a5101a0030b803c140d07075500341d46640f001c040c081c0c40e99a010b441010b000308119a510128580210400c0e6025520085a8000000c240320b41805988413010003007403141e45145941d40b0720000754008184107411410600c80000000c030020109802170300c0404002c42c640070b862502c1409001e00c2217004141403110f04081010340c8020620500c0290466208411800001e404840c516810110f280300303041c00004000700400c09501510305000c007580c20fa10506c0d12282140c606100d00c505840200e1980341c00102041c1e00c025840304690b51492613104015954a01c1039000152031304914040441c800c10750385c4c0c504003881610b90100d02120103030340e1141d02202c06529080050300d42a4441d0312180003420000321101994800b107039a508a50b800e400042e852090703625079001d031900280001010a0260b41d801040e0307219260000c1800000ea440c1d99604a40540c0c4840d13900e8214a5 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 282214244 1250 282212994 282213047
    0xa0b19020702130c031512060c030e060109150f060203030a1113081e0a0b0c030402012c0a060f140702030c0603070c060501120b060603040f020303130e1302060703 72
    0x218080b4071000d40c0420000401c1802025401030300342c1e20f011b15161040d174402c00080102c18a0b00c2d0400841c550040800206075441c0003049016020703034030200d407485c403c11000003445503195204c0d0515090303070148110240c0d15141888040e12140c8110f0700103070b00c28004100d000c1d265030301039440e07006840501450800c01041d140d03101c0300b0560000749aa004001d184414903110960200104d9540d409020108015030301c52a9818016055483e1024088001800c59004549410420340c0c440c003500d0b40404807113104000c20480e109a20f000d107c0c00c000002d611402994a2102125181c44441502164208242c42c82d0403103141682e052041c211113030801e446400003140600e038182e4a41c0b0409009080c210142c0f0810780c000100005d070001600046002c030102c2c2c58110404884466482d1594100680e21706900000654103010000700445001d406c052041d0440358802c09245c02070f82d0790ba03032214a1109014019400032420003201300028454400284102220000101e0084 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 282215494 1250 282214244 282214249
    0x70809070e070207051903050601060c1505160f0201050609160c060501060203130e040b0705070f0606170c0a1404020703020304090915060905041709181609080a0b19020702 76
    0x1e1050b9034110240e00601814002c6050a880348403441c0803074a01c60300000d2655035900d070f4420051003044100310f00c2c2c1d540c1008004800e2000b019681e14160284010b0030000501010001c106035590041903680100300003c50042c01294410b55008291a1095855030841a004080b000341c1c80100445c000410000410512641e40a442d00d540215101d413a0413102507070108184e00120151a414000c0000003040f15115030303400b500a2034201d44815292a112500c01034401008141d14104035010030907003246440c940702844150201d0f040702442c0c6c0306014620385280110220000c10602a0800b030074180c0040181504c603104032440c2a40d1807002c50201c4041c2102151558204a80c100e074a19441c0500c0c006441d0318001001a401d15039130f0001c03c40c001ca40b01c00f80011000c210740b03c9540e41d80d00405682c4800c1181e14242d442c12405402141c08540f02c400d002c590201408a00501c0001c2c1d03000485030b00c800102c00589503500c1c02169080540c050032106502080030f0001078 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 282216744 1250 282215494 282215519
    0x180506150607020d06090302071a0a0c0c0b0d0f0f140a0b0f0d0c0509150306060d020319030507060c031118031c080906150f0f240705010b01080f07080907 68
    0x600500001800791b8081c50001d0400206a100f0520048192003025003400f000c8210b1f44d841030b6904041c07450404038a080718006107994490b40c2c00080108003018486a2500032081d1650040d0080102c40a403c200801310f0302100e64a81402075180c0018102d100780340e201e5450b500c0000d0040e03102041c2c090009042d29890b5104907040c4002c600104154104002c10a412240040805113500f12290109076203100082504d03218071800c1103900c6c1075440604c0103038280d40a011100c3d004400c0c6042c0a09a9841010f044a4076481c05409201d030f2803080c41400e0f0300e01003c4107901d18110310400c224020014007a18583e00d406100c4081b00b0a20b094041c458141042da201c0080c180340c24100c5d00c0c14804024640d0b01103124607a10f0031040d55070545c1c00d240003542200e00c06c10502020002c1240502c03000703080755000902e04030302604414401c01502c02c4520903402400341030526001128003190980e1000b400455130408120494001e0040c00e5214070032000b115410740d5989811200e0 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 282217994 1250 282216744 282216769
    0x230610120b190807061205010302100f0c170a02192604181b080c0d0207081201060216090207030c02100e10090f0f0308120702070b0414010318050615060702 69
    0x3036002a10800030660406040000c030072403921b0070400356140d42c0218031a0140e8002a004008102d80d41c0c000302c5002c0c5d0a0880850341100d080c0d0036180001080e0f0490b90300488191025200302e50503034190807045030741012595840312400c461408014101c44400405140e24141c6500c02c3c4808562880315502440c0c0e00001c04102041c0c0c0845920f2500040b400202203204100000b010000c0c3e00d19403001b1284100981c1c4401650b60790541020b52003400355807090b10043c0845800081c1d81b0703900040c0c0d000b012400007400010155142540c20480c421000e0040100c0c0880c2544d801500d04150f082d0700c0b4050384e04021512050000004919450807007408000c1100c001041c4402c841c840c800d80060034204114030315407030841d110341c030560080301c9020a01010000014110a02c20310020000b003109159040c1c540d91200c00800d203484401c0c5505000a141003040300e50b80100070248240580c100300078008541300c04108120469030022a00d4108404000120040c1c4541025a22 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 282219244 1250 282217994 282218009
    0xd0507080d32090a030822050708070806240d06140a05090703080d051003140604050111030c0a08150a030c030b0705090315040f0204230610120b19 65
    0x100011007004000031421600305180b070801615081041c102c8000941945860f01420305071110740d90075588036074808815012603068500140460100900060034001340d44980b01030700c008940769410b0a646000c00c03116240038501801c0c0401c1c001c21106401003c804000d4141078040304151182d009a807508108916804404802c01010006610a442d00180d0140181252500e5621150312034020260021420f41e1340c1c0300858003080030701103030303800660348850302820522001981940b900e000b2101515103501784105515a4030040c0210b03071280310420a114140b048070320046495a0008040e091100c0c01c070078070030302d25070748280b0b94000a41c8103680f44115903040d813800e50f10100015045809004003807000c42110358010444900c0d070201d010000c1403e50300c0d400d1047d90042141c1010b500076244c51036100c280109016425840710100183c002c05844038014400c8042d031050f01040080e600149420182c01c031030300310343e006600c0182a294124910350010100d024035038400345 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 282220494 1250 282219244 282219281
    0xd0503040201141b1204120303020c0c030105160201060e010b071506081603030e04061214030702040c080108060f0402011d04091a0402031204080a030e180411010905040e0d0507080d 80
    0x65040f000c0080c5160721a00041e041c2c14145840d000d5201070181210003000d16801140700c0c11030345010812331400b0b800090091069003081400f01840501c041d41200055007001400314a08845001c030ad8120340140b8801c0c0c1c41d22072181ca805404029001d4010010741e05c4400000308034000700b08680000c41740b1198080d0140c03a40ca00504104602402c485c0580e0505404008500a8650f100d090603003282c00301c09107400c8103000604600c00e02000a60007442e00d40b4000c48164065840c9050301c0b0460200c40560302e070f0318440c3c141003004960081c002000900080d440d04146040d003000d081c000b80000c2035001c0c0035913500703d20090007610300a05055030410001076107000c014954000401050031441c150920f01c80e1622800b040c80042c0a200020004030000d4039120450550a03601055000c02810146410448000116000c0380001d9520401040e1442e04e4441c0059288413100107061541d00600d0641d00740d0013101040e2020401401840c204040e41e02401c0100380341c0c448003c = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 282221744 1250 282220494 282220537
    0xc0f0c040c02010b0310200409020711030c0904030e0f060d090c0e04050319200106030210050a0207032006040602060708071115060a120305031e040201020d050304020114 75
    0x12080381c0100703000e50704681c140700c01460b090f2004500d4206500c403000700800d030a03442c018400c0303182c0d80304600d40b1a40d044c001000103c1c1c5c040c96015104051207041e0010803042c0c038504140d52070380341003601948140707140f001ca800a4001c086001c548000a84021295200903000a40d1a0041c006d14511181c41c1d500c55000c2210882d002400b0740a85404060300717090907100e295803801211289040c0d0744400ca1000016401100045d0542c092401d00c402d100402c5c0725414040c20f45840101c0c050b2000132141170300203000b10b0079940c3d0300d00e450b801407402e1495615841c94500744030003489402c095841e1302e0341c06902c0380306c01007000d8000c9400800c0182040e140040c21482c0040c00305040101b00c5011145464021441c6005074000c5540031505484102c0010ba03581102d600910004010000c1982055000340165228003080c003c4050700c0c0b25409080a143c0500301c4000740140c0243c43c60800690042010b141c02a00614100c14000705154002080798408440340c00e5112000031007 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 282222994 1250 282221744 282221749
    0x9090a0f06171e0f0d050c07090504061a0109050f040f090609050312090a0f03050c070b0d0903080f09070506031902030103031e030c050318010b03010203070c02090c04080d0f0201020c0f0c 83
    0x40e08001183e010081040003410100d081d118290501550200319000a00c504c56500800800d0080e00305050100914246440c0400c010b146004451440d0b400442800b40700d07602903080d000440c2c03009042550680303205401c00000b00072034440300d082d4030340e100c9a44020400b20300c6080e000310701c54401142d0382d0004a03060f103401ba40091001a030350740014024400241595100703840c156042c2040c54032012100c000a007400301c2500181c9203c40003141e03030644048586c00c00c801c458025103507070b03c094903010340030039921b802112010a02c0d8001d40e410803050420100455000c0041121120440d03200c1c41c0440690b4401e0340160300041f850040784507032090000601041e082281020401d1050400c000381ca5130000414000070780c1484100c032900550290001d07038412500034001c40d524a4001070242c40754141613400c2c2e010300350f00c0c8006140003000000f01c80603601203200030064607651000c101c82d1907040502000855400340f21030103a0050406c090b1105824030341c094100b40114006 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 282224244 1250 282222994 282223033
    0x405040b120109060905150402010c03120e0d120608210903030f1305010306050f0d0308061201020f19020703080301030f2301050108011a150c1212060109060509090a0f0617 76
    0xc010419051f18424040180c2e002416505c200e0742c18201040c00d0070700700840400508038500210410301400c44131036080350f44440b10305901030109004002040d1118280340ea2010b00c02c0750200451200f440750104041e02001902d0ba480c030040c2242e1034040c03a8580c00c5039581141920080c9121552401d0040d0b60305402280c000d00070680740042040f030410002510040d00040203004d1140c02d90108865441d500003102009040400955803201001e01c5403081d58004113003441c00302402c642a03c141840410f212040720f070000e00550649c0d08680b50405002181401100d01220f00c8810003008d00e2039820b04911917107030a00024a640c50256400e0039079040c1c2c0003509407010310000c1211980e4401864009446100c0e2100d501d40701040c006602c1c00f81610703048050303400040741032140340e4580c5450074450b140070b903140da10307940d6181c0041e5140d00850717050940c000e110000040d04401740350311854030201c101c00040b80007540c52110703604030003060420300c001d071b00801d448002c500d203004d4 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 282225494 1250 282224244 282224263
    0x9190b0f040306180f0f0203280c0605040b0f09030c0411030412080108071a120f041a01030b0105060a0c0605011203180b03190e190302010c030e030405040b120109060905 75
    0x1541d0001000043c2d07540c004955481c0c40080440406d211800c0641d20b08001400d561814119003100c001820454408a561b10f800c4c102e03100d114503071010808900c5002034804840d41c1031015030a1400c0c1100501d659001f0250150b01881000781120300c03540d1784e020392440c20700300c02110f660b2820a8140072040003044940074050090100041100715000150301c4120707003802040d171003104084071114a00740710b01c2e000018548a101d0500c0300041ca01c410320307801a8442c8100c2c40e0254600d00c44074010764002d00c400790a1450500040200703003011030050404003c01d02c0c0080b10700c1c0f01c503541c180484100b0f8010205c02030b03500501d00c0c100b41e040110040e080c8000d160001d8054036090543c1c005100041c0500003140b481403144250203102d80244000c40604001e46600c0140d0642c801c101e210900000d07001903003000e01500b15a40244115010340c2c0100020398603080c10881030102800c0c0d54400c2a8120307401070381c400c51904081c424503807003920a500c08602c5004600301a440c1c0500d40 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 282226744 1250 282225494 282225521
    0x801050a09020307090b030114010306020a110a0804170c0d05011a06040b0f1b0a2906030a1101020a20120316021903140d030e0c0609190b0f040306 65
    0x301c141c2002da81d0024a0a0450f08249000720319801380801003405000504030300b8004115000002c4204006034000e0500241d4030381e588030064a110581c90358480a10101810030401000103001c0e14400c5000f200e01c0445032000c44014001602c08180d5020303561100743d81603596030142105a00e48515408030188044404504190800150b10021b106161804054100004400b40c054543c4100c0b0b00d007042004090354050700700d13428a00300f01d4002d901d06107440300c10750b220000e01140c80c85034107002d4440a001003002c804140c1d590300ca00c0d41c0f41c0e0713072441c19481040850800030f032291605540401101103140d41c4030f02480b0501944240c0200120312a8200740301e0f040801e50104506502250102c813403c40a260300f84401150300c4450704080c086d8942c403000c506030000c0000d81c5120b4440b03241d50801504002d04000c54845048070345060380300d0020400404185464401c8010204d50b030729400c1030460361040e101d801503100039000d20040b10f02240400a00184c0d01c1001d03c4004034 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 282227994 1250 282226744 282226751
    0xc01020a03170601030b0a0303030c02070f080d0807020f330f130f0602040b070c0e01060518030319021507031107020103180b0a0e01110c0c01050c0114010f0801050a 73
    0x66030042c0100aa0020b00601c40340b9640001d0800c4e07100c2d4129620a890243c10000c01d59241c2c10010043c0402c0d90b0180050311401c0000154064919151001c490456015002110028200300c8010700040e000c2d00c218420400e81c000056014041c181e0181001c003181c0428880d800c8034540013010440004054500100c204241561521480340e4070110703c010760b100c845c0f11843c01c08565000c5a0020f04070314808500800d03102e00c40002460194000c00c00090129610703018000803c009004440c00240148100c1c001c580c04400550340ca08070040c10f41e418030030074400c03015811000d00607070360059001d40d150000b64201512165081800c51600380b10700d1030003d03d403102501c200386000381050342d03950252058007800120314204692146424402e030609210501c081c1c0282d60a030f805a510708102180d0022640d001c0b0780702501c80c0401380041000101c0152065040b05020580d81e540b5800300300c0b903030580b400e46107010300b040d0b042c000300542c00c0030b03070403800c5480c01000400b510381f0303 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 282229244 1250 282227994 282228013
    0x3040c05041a0a1a0a0c170310140420090a05030105040b04140a03090302060a11060f10050a030c0e09030409091b0e060306010e0711010e01020a0f050a0c060216230c0102 75
    0x221322040300c9603c0e182c1d013002c4840641034946100e1005550744201b14004005c0240a40c96079244000c10860f900030060702c601940400402044440810340f003186151045864602c1d020440040c18076514024800089103594030b001c00d080d50021141128600040010002007000120003010090682001801d00711800d0b034000d040382c03000e4000680700301400305000019511502800b84c40c0c0c4d9080040d100d80c1e09042c1e003c02c0d610a010b43e01425210061803012a060a000c03421004494001e00031501c06071030500d01d451b006c50042c2c103103a05070104100211f000c1e40c20b401a0302d202482205d03100d05240b050f904a410040982c0c101c1c4100d5281c2c1000e21066990028045054405c1c0b80808100c80c4c542400c203484c403001c00780c0d0181d1a5401c0c0401c4003259a030660180c0701d0180c0988071000341c0180750b441102c003881103034100e501040120403500007044665001d00311aa4110424050074085070701c850b40c1c001424004a083c0c41132040601c0c161420a10044d9544d600c00c2c00145003209 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 282230494 1250 282229244 282229289
    0xd110702090705071230320a0203130507060e01081602060a0b0609031f060e060303070303200d0b030d020601080a0b1003080a0206040317061503040c05041a0a 70
    0x40501205c0c1c010421000400c03880000400c4010103800c0c1089080c410604804030140e004d400f0b11a82e0107a100c91504115405542c00180f041d11000c85007a01c43c81c56803a54480c030020740001e80354480046001c02c4c1200003950400541c2c0141c0b9580e240c4810a0b1901d04c00108000380061080c2d1403907811180c00300b40351743c0014070142c00c10a10390000ca404c0140300080b8100b400361001150b41407141c0207c440c10700039807000c1c0b2640800705c50020b1102544410201141c2038055a0007034055000b0401340340400d119600c041c4a140b050000d058045588103503050305c40c0c200141082c4450350710742019040780f400b0840000c110480c0d0000d8000d80d8500050b190b01c940e40403401a02000c64174000964110154512501450b8082106501c5088000e402507580700111001c50100b4140c041c4007010701c00c031410035442600c00030080440d0000c00c0c0c01603210345d0070151049404000001303000c10300c1d9480340100188a880d189050104013a81420080d0075078080c1d000700712201688001d410140f = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 282231744 1250 282230494 282230513
    0x31f0e07060c121e030c02010f050403080705161a0a181e05010f050a0207020a080609060105010309061401030302030d0f05011202040b030f012301060519030c02030d11070209070507 80
    0xe4000540920110303c03000c003580c0c60003440405040d80a4a1981072007026090741c000d0012041d2507000b0040000d201403e43d0494405603005800f02c2c030501c00007045a4480d02c010000d0010030700000305c4130151550364802d2403100301c0c0c81c0c441305504d1508010654003d4441e41c4007290b03480b40300d403182214584603c010401c00d08090340007019031018240500c0400d410410030301e0580700f800c020750325000640c0c0c1d0094104071402c03445050240c0780042c44841c0001c010b4001d0075a10080c0065900e0b05005400402149400302c4400e502e855000e110b40f5410b580c1e650003540a9000b81d03a070342c0d010303900d24004c5402d109e05413a0558605001848100c44451901500950648001a1603080b650020f031414000d010b540e0900d60030001c003c0c0440c0f0300c0c1030f845040040644140040b59807606c0050701c06000e0300159265042c103d50120b4025071003070f000f0092000e4203005487c030300301c0f640c1540300680d40307040c001864410000400b0790450504142d45644450540303000f80c01c240da10741d24103588 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 282232994 1250 282231744 282231767
    0x6130218040f02131202041107030801050d0f06090b162309060919090b010504080c1e060d1407030e0a0308060105040b0c0a0b01050105091c050705031f0e0706 70
    0xd96440c000c01e0003010083d0f045a00340c0c20120345241500b56070340d0180b05c0c00c140c818030490040d17040500c01c18510400409030f408132a8103880c1d071203042c4e080c00148040c6a00080040d07480c0241c4214a50100d40345111b075908883c01201009840d00d0700b01042c14050f109286031100f04210701003406151216082250f00000c40c100a5540d26054a070004040780038651280c0d41c00721582040d10f444082c0c82c5902c0c0f0444020f25000d1015070321000055507240071300e00c203540341038012140002c400c2c60080403014a824039070780c41d880310542c4100443c905800031240c1c1305413541e4603c08019255196000c0d59403207212403074144407102080701216200c1018000050500402e140454016800741c0240d40191100102041e116103c1e1040150b035151912410b032642ca00e00340021940c0d500c50021a500d000c0e01524980c1c4085050312610081003d414095500c4c0c0107803100400c20381c4e420b000c2146045040c9410318040007076803000c1d60444080e9200d0044d1035001303104c03c10072140c1284c01c3c0d040 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 282234244 1250 282232994 282232999
    0x21090f1603030513030501050c0403110913030804022b03030614180c040e040309030b060904171606020a050c0706080912030c070c080609011d030f0901170f06130218 73
    0x12900c401300401c0e03803c08a10f40000780300d94240810401540c04850180040304d001e40520000e404404c0284001501c080d070b03410340700340c0b100c011610201e03009000d03050304148042d02820610304480003030091900c10065008100c9045150350080c160b01d4001c03000a44206816000440c074030000054450b0b26420010602618140000d07004500c2002a1801898030154811592a00e4680103240548c580000c5a0711061030300462aa428003107502c0f8442c540c40311000d00000d02c4a400340c1d200c0d42111901b81c00c1502c007910b50100040e114000350503100015160b06884140c02d0404904080c4260071138400c001050003004850540040d0782c40d440d0007000d02584d520b440301c0c070340040e4611400f9000707003d0351002d120010360000001402c41c030a0140e04001c10510900300740c506400e14041d8903101d410351062010f12490f4420b08014001010141013418518088224041d100d00003141c00308610f41e80e180401001d4100810786416001e5400030440c07510300d0300c3c10241c901c0e0040f0402d060 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 282235494 1250 282234244 282234247
    0x122409022d0d0903120e0105090703031206051305060307150f0804060e03070b070305070c0f0b1017010203040618260c1f0615080a0b0621090f16030305 67
    0x555003000d034100d80c1000b03a2100103202c0b5500c0c40c18060710750402c280103041114540800041108010700c101c900907004c88000c0d142c60351540e20101c40302042c104642003029940d0305e000640c1e81e506000d03c04522003c0c18041200d19284c4c0c20513050580c203174000b4101c2400003060301c0802c1c0c3c1c400003212000d41281884091074545041c4607004101d4001381004d14400020f0a005010300e524a041c42801d0a80c0c0138002070740c030500200d51240d00802c008050004a4001c14000380c03608000e6540105203050788522a0340e600c80c503400103114140c604241e40d60000611003880000d0050810354019410f01e01c2c1c80913848e0761690514280c1083c03402207015101c5d20340000381d50103130454115038441d1085400c0700800c8200607411410a01d00d0f1400240740140018001452903101880090f242d250341e00c9a40e9420101d1340505150648540c2c0001c04105c011140a92289a403444c1f8a6103002541c840ca00540b815160013030014000c40c00341d000d0b08421038104a030a18640c1541d41c0f41c54010b = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 282236744 1250 282235494 282235567
    0x6032127090403050c010e2e0209030a0f05010e010501050f06130b0c070501020c090c1b070f0e010603150302060f16080a020609100c021b0112240902 66
    0x406804240aa481c1c0c071071075500600c014180d210001d03080c801000710080044d00c124000d016956840044403452490f1115071000c0b010101c5200814190240d0308050301d006c60444c006424100d0041048541c1d00f55035004605100c8241301c0c074911480a04000c00165041c480001c0d00341d41e40c4091140f24000001e411203908030f01040c15001440d4152070b560702da1300340ca1107060b103038030b075602a09005100d80000c0320b140e0f10313007400e801e070098600c90752042c9000101680c0c0e1000d540f4500b845503da00c07030900001034402010360b40030010582001c0001007941049001402d40d00220902c01c81d440c0003c42c244096071395403080b1180c402044070581d94803030b118180350941c01d080390000b80840402141040039181c0120b480ca02c200c00d48400d68003c80c130700940740411541609a808016486408840f24603100f400c00d000e0003490504100344c40c000f503400c070981a07561100b40d481c03480194005040044242548110140ca2100300c19400e1036002c028241030120b040c82d00800301540c01010 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 282237994 1250 282236744 282236797
    0x503011404021309021b06010308070b220606060f0e03070501050c100e1605011412070c061a1f020615010302040e01060203030115050403051506010302040b040806060321 75
    0x4550052003c104070641d030907615000100290454403940d212101014580a240400031402c41c2c181c0b5030082c40f0301e090580d207486042888078020505140800403e5198203c280c507140403d0340248034040102d034582c20000300500b1441e951080310b0910583c50a00349850f42c0203d49813042e5002071a141d42c884042154051a11f95454000c03401c0300e00d4402198142c910106a81500484041c841c020003542c0b84011600384120402a000180c4103100b4510095510031307800c1c0c0c00514070f1a02d0308550b000ca884100845e405900b80320b0600c80c82c41002111030500c45140e80301d41d40c660344103803407540106a02a480d40b00007094021141c51903041d1020316802681075501428043c21480c0c680e6840380b101a569600078020b1300c610030000095260400d02c103504407130070341e0f03030000180c18610942c40740701c4010380c00989044e041c10f400740804500381141801500007014210020042400c002c802d1500f0074188034010b1000c03271641c954464501071680219031143c030340b038100e007ca44040b0a40c0c = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 282239244 1250 282237994 282237997
    0x13051b011e0912030306050405150a0b0904021b0c01020d0e030a03030213170a05070504020f0d020c0c090a14010f060e0909010e01060308071b05031f0f112206050301140402 76
    0x100c0c1651000180f4090245036041d4400c105031001580c04020a4540640003200c51640c00744150b40405000383c180308060303a070005444900c102401c05410f10312040030040880910310824170640e805107081c0c40c020341c0d04204440301e088241c00c1254038a102540400d4035a045508041c040c9070700007611401c070315071805a1100074030a0a201c1d0400340300325500382c3d442e0a44000161010310070010007107014a882c2c400c0302d90401c1101d12081c0361140c03046886000e9004103c1e0001c050040b0030114609883d40000c85104103400880095480c1d50710100e03203544201031b00b2192000d01c0c3d1b6501446099046044035110382c40480303080440f550381d04456409850b0069001c0c51950a01c58000200083d480c082d002c0c02e03204000e122031200000c44246003540f03040c419540c3c140d1108080c42c2c11818507075598908561211800310f410649600c52070706859904080001201c000104a0542c401d03121294002500d80b40d00c116000349844c030000c1480c081030180c2e103402d2980c1c1c081a2500e42d510390 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 282240494 1250 282239244 282239249
    0x9080c1014030106020d1409030325020d051c03292103030601110d0905040c0302090a030c0509100e0f060604090f06030312020403031209050703080313051b011e09 72
    0x3003260342c035a1100c00013500c90000b810810049180190f8803d00a007101056508189001c0c3c02103061556804108440f5188401f03840c000e00c23a603554040141c0c41d02001100406c0c0240002d00348060002000302071499070903050010540380035201c10302106200704038000d24501010010f00111900001542001024a0303030761170300c506110026440348080043c521451098803140c50b403003024281c281d2690100c56040c00090507000e414000c915041c3d0288888031007528005062140c07440101d0001314440c1c005031a801e407042030803c401c1c03a02d0340c102c540c030500d400300b00a20585444100e6040700c0b005400c109030700f070010300094441d4031010281c0b402062502c0042c000c4512140051000708034502050300010010a002d600b00f0016008540c00c42e035055031000c0c0303103c559040c1c6900401c1ca1060840725030140031400004200254060360040381c0144807070304c4180991170114500000d0b40b8020190f00c40442103250340360b0b0400e41303420003545030700362a2000a0b1942002c860054040c0c = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 282241744 1250 282240494 282240527
    0x609080c03130501081e0f0903091e040b040e06070507081c0b10030501080d0c02040b09010b1b011a10020f010501080708060a0515120a0602040905040b0709080c10 72
    0x442c00080d00e45014100404030340083e258240d09807154011259200c81c2d00030004d112100c0140030a201420015500354049484815203090540c80740000c0c02c2c50055090039003c07245007010f0400a407a02e403081051140f0222400c10203001051032181e1a80380042840c001c5c000c020038001c0a0101d54021100c43c143c1441d4a441d401110b0441c0c0f01c0180210011f40c4d025041030010314401e180644185410785031504000e010290032158201d030401034408040360000d0b101c0e00c10219030f480e141c0000b03004c2e00c0e100504ad41c480513841022400891001c0c5078082981c10003d1500100400e06041c0b5071030001038075440c1801c01100410380c506068452032005035840c0c41e0000903036100110f24082545d00b0031054a03c0c036201d40700010300381c940c00d41d1408054401000c441030a45401c154804154986005940313004c50300381c9822040b44c100342d00410b0740903141d030104010448010884c540c4149107041c030900c02d40c1085921603980c0102c00500c2c3c007401035000b180d404240640c18451125804 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 282242994 1250 282241744 282241747
    0x915090306060e0702010e0a110f010e122a06030a0b01110f0f2b0f0c08120114060307020703080d0908040b0c07060206251b0501091205040e040609080c03 68
    0x41d40d0f500800c480c07044880310015443d02c400940d400d00b004c40c041a9043d00218245003900c2c086040017a00320085000038148240000400c3c0951601e2842c00c0542c501003014203000820035690341180480c141c1e50000c1c0400440f41c00b0b40c581c1d2090103903038121942880c0061200d03a001c0040e141042651409410ba03c1240c2803a9030b034000008081c40303502ca042050329240b02c0441d1000390800c010030b640b150b1548040c0c84085e062803185202502440080c500801081c415854942c01a0300c044428154072000000501c074042e038410b02e07004060025079100f4510303c0c1810000f5210b50702030000030031200000401302080c54681e0420380c45aa00610220b982da943c80b8036650045c1e010400542d21070240120000b0f070300d400410440c3c4110300d04408910388008031400501444018100e82d014403416240d2880c1c10003500c4545001c8512400001070152010f0400e1010840f0380d41201702089401c000500040050b84050b5810603802000402c40070300c03514010b0740c64000c68903c080c9a220 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 282244244 1250 282242994 282242999
    0x80906190f09141b060d0e011401030c0806010b03220c18050f0a0203040c18021e0705010e03131211091f05060a080408070201090803030a09060e060403091509030606 73
    0x2d01c01c0315014050307210100c3d01e85000b4801955046400d800f120340c0d1041091094811b02d0401b60017442054441000014400c03100c40281440c0e20001e030019210721070307040c9003803100303540800405014001d0f09000d0b5081d85010501c1a446131550600302c0b00001000203508100620000d005000c0c0244200b0384102058181d001c0c0002c01044480f1000318403204085108000c00d40700700d90280b03030480ca80540c540e007801030080403022440000740410342e0810400341c28891000841c6200c10041c51030643d142071a003800740c2500e00980454047d6001002091104c100703100c42c0f1022640030303010f80c4520803a6030a1040c0b50b5079400c151150003801a0080090743c104000360b10340390300030010b00ca9040a03251401c1c4012030140c01484404290f4800c00706020801820203040c0840c41490411a02d80d107030b00c1701c0b0b42141c0064a240b141142c541204c4003c02c062401151041d02e28180149014039154400411246091051040810240c107514407540c0c4100320610140d60001818002240d = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 282245494 1250 282244244 282244253
    0x20f03030f09041a031c0507020901030b0106032a0c0309210c09150902090d02040912030c020c10031e02040b0d1109180919050706020d080906190f09 66
    0x501003484580716500d00005800304030244d4440c10510000a0010500c080c0301001502c451054182d465081c810240440b20040c1d59040402d03004e180716281801044d450240041e083c3d032304041685088295a8140c000c0d607000c041c42c1c40200f40c01c2480c22000c200c44070709042e5125145504002914006850403001106104420040c0948508400c41d94079540b94882002c440403a203043d060b4038104e810401043c1c040340c010b8800414020f01a01c1c0b42c40942e400642107a0415008850700301c5051000b2022035050b03c5150710700c41c070314000340c50f800160500194a0000385001201410703980d0310714000301c8622084080791003140c408115507440e1030f60140c0c41103400040ca034110560500800144c0140c01c5410b44007400c0c0041d200401c0788214220700b000c551002002c4200c030748504c010301400e61079132200003401f05000d0000351400320704003000241002d1007160318030144041c11050050760180004c940f507028501d0070900014030f601c250308038060030450141140303640c2070846101c00d00 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 282246744 1250 282245494 282245497
    0x8120103120c05070b0a120c0f0305010503030a050415020f0f0c0306100b0d0905030c100915230703140108011a0f15030a0603081303050c0904020a12020f03030f 71
    0xc900514000c8000c0480d410200c4104407003880c0100a03410001040083e00390000142443c0c0c2e080d030519202220803401407078211502d60035088005807184a50708551034051145501508045d80510b00e0407607521005000d40c40340307206820403650300d4103203921180e10a00a8010302c52100c02a03030f0030b000f9060fa8007a0b850480c100502c5c031a019070004101404510000401140d10794502d0340e0508004904500080072a00000e0f501800100309e561041d10090042c80d40030b0600c1030340040c810a650810410308409108550481440c0102411526080360002845210840d0306401c02e0b039218141100980413003407102c0080780c1804000704501c981900503240c6520b1094030082e405442c1c0080100c207600c0c03589141e1700000600040350980e0b94110055603c450510070120700c55560b03543d03280c5560302400095282c100074900034820070400780421440c603078084030400395908168000440c100c200b88900e6860240103074004007151606140d448840c40001c003603035114bc0a40b1206a41c5 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 282247994 1250 282246744 282246749
    0xa0e1c05030a020c0f0a050d020a03230705100e06071a01090c080f0402150705070b03010b0903060901110306040b011e0513080f12130b07030c122d0c081201 69
    0x143c003445404d0000ba04244004840f194401003651075403910b0501840410019000240d030850303d101030100c040307a00b1002c04000090030340781c0305461a04010055041003580d4102e5880b034808513808000003503000c0e41d00b4401075011948190340c2d0000385800400894007000111f200c41c80080008ac811000d50f001c006000050b0703d6180741e5945100492440e4501103d00940c411403410300685410300040281101390301c68401c69074656183d0314942140d40090344414040000000d26800a00b07040c0021381c1c10401000c001d00c5181c0018100070528000244814004c0741d4408607100c60380c0c400c5032050207035810343c8a0310151203400c2000070216881803e8486070610350f07000c004bc44044c0003504050050396400500b20300d07190310901da0507980c003c2034003480d10244400003144006003140184841031007900ca02e5005129450034036054591041c4080611005a038099013600c2501d0210340d032076956065021a204440c1c03802e41d1812441903001e0071a1030003158984c40307a150803400ea4103 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 282249244 1250 282247994 282247997
    0x3160c0b0109020304060b030f120a02010b04240f0f0311040b2106060307050f09101502010e0c0d1e080d1104080f010e0d0809070e041a1b0a0e1c05030a 67
    0x342580003400c3c50f0b80c9e650000480030140e84801b490b03140031541c6101500e51444a44004102c0030301c510b00040982d05180d82d420740c0c0c060315541b10151520361130b0030b00c001480c0c0820301c540d5841c80d10500c00c903c0c00142c03101522030070034581540180c0d91658042c0c030414500400206240309004100403182c01d01c280080928070030040803510501c0d001070014111540100000a42c8400c6002e01070103c0000d0000600d505070800d01040080311511815800388440e07000040c51440721204e00d1904599400450040012078035007008200440a00b14141c03200351b01c18104040d10389089501403040e08802944145820403003510440000c004001301c40c001012501041101d034005400c9074500c0010000035441028941c1003140100191035008601d0010340b0700582ea250ae240c00b02c550f040780c0807280c1041800e0000350701c20f080041d883d004000759401c89109690360300340300c40c24030401d0700e22410703c0090050018165071700c13800201000c1136190301503010000c0d80380c29556070300050120790 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 282250494 1250 282249244 282249251
    0x23030403030c1409010e04150b070309050f010f110f070b0c01060e07080f0414030a05090117010302060301061b020a0605120a0506090a020304030e09070f0e0904050303160c0b010902030406 83
    0x1116880f0300055155a009040d00c5813601c0d141000565880600d031010581190700c4d50740010b4840305031052a0020310041a1040e556040f07071800805070754107a00800e21510a07051144520707648501e0000f171640c1c2e80d042141a03000a02e58003490080c03229601d849030710407810007103091007000000d004d21070103040080c8005a1a11510340840030100c0f00080000c0d8050300150381e000310700c0c05150b0014085c1c01c00d501441c2d4001451811580401407a2001c6400001d20000030b59100081c000f102d0900002d10307070306504590000c1c0c0f140c0b10610920f020440c003503041e4940301c03080c103040c00800740c5c0c0181030b40d02c403c0d034440b4050050f411035400d0303929440c03a010005144070700a0041c28032681e0000c1c5210070716a2a041c50b100290000b82c015400c01c0296040814039848201d04c0500800058844140e8400c0c89040106001004a203503400b89100c1d01c140000140000162038000c1c0200c1b02c04a0004280303402140e0440d01c0b940d01500082c5d0100002030042c0341a4021405140034550a0 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 282251744 1250 282250494 282250511
    0x60f09150406140c0606040c09030b010609050a05010806100e0f0303030a0509010b10120c0302210603010507030e191412121825080111030105190302031c2303040303 73
    0xc03003c600440010f01140d4000390001429840c055020000107520390400d622400d0312502c481c10394100036041b42d00482c1c0303038040620051a02c403132141d00812003444d1680d01440d210011409030301c1c0348922041404182d840f088160745d40c40d5000302c00400050200c03a1a864251683d001414064031040c40c135520344a17009410b41003005d4962180000c90729035004080c280c0c150f6500030a01c190805081660900c4041746d95180725041c0f400010310103003940703001d0a03c80d080500b19040a00304a01385840d01c120840814404900207000c50780b01da82203c5002c1050900a0174025214130036200340c081c45070105441070070074001e040074840c4103144461541da01c480d0410b584900d194a418690b200e0050f814150307407040e5a48029070003401d082c0c94000d030b680307000500352500903c1d450980e100100c014070241c109641443c400707005015003480040e103140c012076110002c7c4904480b0544003d20303051443c5010b170303c00d002c61010b603c4600d80603046040942c150340d0416201100004d0412101 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 282252994 1250 282251744 282251777
    0xb04260309030d1e020f0a03050c0705040f0b0108090c0f09040819080406050f19020306011107080106051503101809021905091807050103020c07030f030203030121030e060f09150406 80
    0x501d0341c4486c00c0005161300d0383c41e610140c0c0d264002d010700301c03114070600001280320f88032405072100c0c0d26421300020580d40c10310300026044060080605c1c9156100d080b0f41d16059441c3c0094450300e40b8107941200c0140c54074241909144600c140d0000d2445c20840030381d036081d500500700381c4501d00910703041100d912041c100c0c440401003030790402d0000361030201c04424000160b00554000342c0505001280c46103600c1c08504201c00c07a03000c40b81d903940d910004c00c503600f4001018007000018550143c554545104034a503416014000c9030b4241e45c00010f840302c804070a51180341c072070f5001002d034020034651003401252090f15008441c000c005180c00302d0780c000003101c0380918820b035810150954909100c0114025003020000c900544036245000012801e04421880504e01983c0a0365583d030403d1000304040b1580310300745040c000d0b46805140803070b0340030501507ea52011103105940304842d1042003103d0003060719440d80114256035650625071a4001031040310113a0700c4121601100000703 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 282254244 1250 282252994 282253003
    0x203181209030607050c0a0209070f0909020c0a030c080d0203010906031a06030a02010f050417030c1e070303180504020c0706030f0603051f020f0c01090c0b04260309030d1e02 77
    0x1c6403901a8441404140f8107401100034010290900e0100c2c2c05038000c0360000790b0b000c3e130140d50705004522081e03101c8030003540c004a070700083c19404409520f46001d5002c4907940c1d84c070003407010b001c010b000c280e00000c02041c0c80880358009003007041552603503119100d0b4001080782d48404c544400d2281d990550200020401500c1600001d02510842200d50019250352443e1302e607001c200502000040b55440e28480320031601101032000b1600c803500000d8043c80d205460000c5100d130b00110024441002001803004152641860480802000c040c05003c01504c15081280d01034004101400040000542e400413a00d1555040c4010501c00903044216001400042c016030040420406800b06030020601e50108102d0010300d090310810902ca43c98011100e2101300342d456541c900f00f44070740000400003074003419000034038003490f10107140c0c0c0341402040f6a0801d650482c101505080040c4103407001c001010b0147c071450800114010b100c00d1080111506120184101d019194070028 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 282255494 1250 282254244 282254257
    0x807110a150e091905150d050c03060907030c09020d0f060905040c090506030304120f020d0302070f0b12180705120d11070602060c07060f0908070201080a0c081b04080102031812 78
    0x13141042c031103202c90909000e8134005005030545d2001c10850101500d0713440c0c1c1002c0e0311740250054070812000c1d00805040c604050110055640715000c144081841007442404603540c0f00c40060795810342d1054030014141210000329200e19001d40025560025004184618469281e525020361a20040e90440c1c0003924025010340c4184420302a4440360541e04400c1402031403115014041c690002d244481d08000480c016040b001c0c0801c405980c4915441c0a0001075950b0303402e003c603d402c080c49080005041e0b4440b4001009191036103102804401e0290001500001030f00c40d500c02c0303090b6140e00a220340340004003220201081c23554049244025030b1201e81c00b8020540b40d4a0803a44a50010b0303000f52006c556913071040c42d0024280c0b04c0d2440851050354800e440b03191600001d003204100410749041207040000c0e000d05039a002441d150702062200400c0c1c0d580b2200103840449001c0c6e40c002c0c2c10258400414003002134101d0070040f000308025021100a51040c40500f1078034046d070b0 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 282256744 1250 282255494 282255511
    0x10b041b050703140c070303021507021b010e0907030501140a050f01200102031005040c080403020c01050d021209070503070510050909220312050601090609030807110a150e09 77
    0x10004160128800e01c001c00c0228081d1400f196882e00c2208000007940c410712243c8000d600040040042580510050f1508491401c0c44500c03460b007584040e454a2138529a055038000c1894002d060340c0c015210702c0720300307507003c1d250442c0c5103031000000c0d00500c428026001c260b022100c00c0400e42c80c0c40644081540c42c050440300417880200015548203c903401c080c261039021030782c0c03400c04681c244090340c800d07100408011041440c1070140012250201e07a41d40802401001300300c040381e0001781840d050a02807900594800d44001c158000740213000c0c0c400020558036040c8041c40c000000d4210584400301d041d10004c0d90380d0010008034a601100b4403010450620002481d8540003c079070703902c5101140805a444040810445600f690380d8089001c12880840300311400e5003481900e6000e4000c2c204116801d0601ea4050040c444a2100a00c200c2c00028090104041c0d02d2148040d400080e0001c0b506c5920342e40c1b8184000d0b42c1c841c0f104005075110041e03000234900924014051141c5 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 282257994 1250 282256744 282256781
    0x304050a0c05190311121218010c0506070c0311030a0207030209090102071709040f050903132114011b0801060f050a050a1b0b0c130801020304020619090b160302010b04 74
    0x4550300c0103148800b000210743c0c1b002d5224064028070106100520055100b01c3c984c651302c005403060b101c2c181002c0300000e8100114800c044000807800180a50405914200300090110b1072804440d440042c004001080c00701246d01e98020313070001941801e5a00c2103c801010340d40f4038000d5800c0b4000c8260103000b420b020303044034601e0500d038001419500c00241000c00c2d5035884581c04016a202a038401102c0d0340002400c2e6011901c01c21180c028010742d01c01c40100c1e5181c5c110050b80580007070740160900a41c820981c408044c254420000144208081108424100009401000c0910980c80410344510340540264440d004070317041c0c3e402e243c43d00d600785004440700b140c5035201601404409140d1004800c045410040d040c0e2190701c000e00d52070358604030391500c901d1070b0000c0e61007500b2580c0180103000059641c1c50585034070b420403220744141c5100010342190600c0c6282c2c0800303006800002d074803a44590708003941c840c25000350020b110104400c414031086409840984003000103 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 282259244 1250 282257994 282257999
    0x80412023a110d03050d0e010e033a06060807030209090c03060102011d030a0e0f0f04050c0409050a0203060405060108060f1003020d05010b120906010f050d02040905030304050a0c0519 81
    0x40c07a021503205540100c0c100016a000a000303d40a905031020513004540081070a03280f040c010b00a4641c1100f2590080c42885444030711560399000d6420040c6902e40445403d02100748245400001c0d42507013900700b01c00c119a00400b130010314050003501c0001e0458400282c1c0c55019000b203820b0460081c103080211340d200d003020005908050f103010704554172074422050a044001400c00580c946001540e42c0f104000e1000e0103e8004a00d0b0300d004003c0a683d09885030342e81071210b141c031792054030042840d6507041c2d510001407043d500b05040349480c14060280281c0d07103601940c0304100a580420094542c04c00542e0409001c84c0c1d00366022155102000704c5041074096040b813005203003005410050890007201c1620401d8104120040020a801100d00044c0035036640041c0710001030301c1c0e59414400c41c0b00d19903d44d4007406004c3e8844010410454a441d4030003c05030742c012060342d07220304140c0380254030303031701106d1043d9649040d9080200c2d47c0d240042d040400394445102c075090341c2c0d1 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 282260494 1250 282259244 282259339
    0xd050705090d060b0a080708031209071d0a060e0c0d0b130c0c3c17070305120106082712041503110304080403110d08041202 55
    0x4010000000c000c010710122849448a49100038040e2062201203020f4240c18103005c2c21a80e5a4403441c0c00e5400910f04222288011003144e5049020550030b01341640e41c0d44900d482c10b203880c1c0c0403000ba254000c9004148000305c0050a010703c0700510280f00b07107a6903000c12294000251041500c3d90000c101e141800c0c0c0c219800203030780741000b8184182c22640103040000b21880ba001d103d01050b9901840320422821904920702c240c0c12009161211001c0e0701c201a10221003106a0310103148440001d050061501c50002d81c1180041c00543e100d0062030010030a030402001e109880505074000314840c1d0086043ca0310135000541c13411400110341c04a00d920081d8003081c40c425002d01144055a20091030060000d803a1194448102c45074101c001800c6500240e03075100d41a106005000005070b11604031011203400c003a4031601980c10000007407140f1060540180b82ca17000080006814000040c074031203150080741e48001884c1c0c08040e002c4500c00700460244198206810a01c202 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 282261744 1250 282260494 282260501
    0x210803010b030703060503030c0d140c1207151802030d091401121508030c0609010509030f07060f091b0b13270e0616020d170c0f0708040f1a0d 63
    0x4040d140114170307146d85601081c00c507803140004044940220b05c007a01000d411140c0c26811140d481a0320385894110309000d43c40f0030302120a50014200050302609000c21a49454400034a02000300300c0030406800251946880120480c024000c1000040c1c880e030040320f5040488460b00f10001c0c42c1c040d48001100c40144141004101b1603031120440501c40507100b10002404064004503a51842c0100217450300b50014507141c0a40c0c107003410000080c03008403d80740700890340031032680c48045070b26206001e042e003031120840345440c1c900300d0f1013441240e007200c40070608105030b4841d900c3d8071082815418464800400c0800c1701240b01003103200d900c010341e140327011182501c910321100400d094034280d0b0440200005554800e40a001d00160003021030201d840080c0000c0c03040002008000d0080e1030301ca443d0000d52001076000504a400b40c80c1154005921000300320382d00c00c81c900c1c010040343c002c0c0c05540060a10810041680340001400aa802040d038849600b886070500701c20016 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 282262994 1250 282261744 282261751
    0x30102031e0c160503070c0b040b0d0216050a2406060504050d06180f0510060e0406150f0803030117010606050708030c0d0509010207020301050a05070504030b0411060703020601210803010b03 84
    0x400030200300c02c40c0c001521101d0f102ca40c600c0350018550380d507498105209600351fa600705091401003080208640e1500e841141c040103801c0742c0168840d00c03404a201d29543c1d8050000c0c0003030042120110030820300b243c0039110399089003108550070492035503003005c81d4418020f800c0850402c000500c060310340050600e4641e44160340206030b8401d0302c9110a00740110b42000c03652044110f038080100310080c4a001480d03001d5070b8003040424604002c0e944440d401520140c03d05a43d0880038084004131101040501440103803091030303554444200d59240e1091145aaa40d520f04914000805040c0140c800721110341d80d4441c1070001d00c0e00c56854651010704104200c200402c12402d4103006c2e409180e101700ca0706000161900c04600505094070001840c10f83c040346808104607400e40c0060507034007520b41080c0c59140d00e9495180c9100705511403542d141d484600440c02d00708042d40010b005040e54044101c4a0903902c0313100c1140003c010306400249094003d1005010a84424014550 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 282264244 1250 282262994 282263011
    0xd020c1207080316120507080904020c01060b03070f02070503070509181c0909050f04020a150302040503060f040507120309060302030606131701140108060106030e100612030e030102031e 82
    0x9103079a0b4002149142d2148481d00020b20480e50108144240a240c3c1c203180e504a08100385000c03103507074070110300e80305403590b02e07110700c2c2d0204046812150035801b08003c3d005a84a8540d2810520b5000d40b0044004070103100501c0f42c0c99011409080204280e0111032000c3c14a007800d48510741140300b400c44840400100c0e102c2c03012a084040982100c03180803000030b445a03d1040d0400000406403840101031042210f081428000140c5611070b400040307640703640c15142c1600c00101e08a02038401ea51207158540715080030b0002003c0749001d003038003807403041046841e030039a13504d20904200710071031001d8089041c0304010004d03035000b42c005613840b03d401800300f850032100300701c00c0d2160620380e04140d18666070388402c585144000d10840343c00e504040c10107515589014880c0b8bd550005008150805898103001c1000c0716040100440030b1249000c244081900c441c0d40e44d640c0d030100c14080d030000e289442c8240032400c1c18402c40f030044025842049079807880050b1554940000382a010 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 282265494 1250 282264244 282264253
    0x3040210023307020114150a03151a012606010905090f01151d040e0a0b0424020f0d110903032712070312090302090703050412020d020c12 61
    0x203801d8a0742c041c40d10402c00e05800004aa82e2410a050a2200070a42801d5a1500c0782d14107010200503012039011100030004004036541001190030807940740e000500c905400004440d00202c0c0f600580c0c0c60104080141400c1e640750ba0046464a111168240c1e5907403840d904406070b2612039000c1e1b070380400b060500c084000c0d40c8070302240705107004842820000c0740148c01840500034840340601a245149041c1c6440c059003601c2e0200818094540303441550744035580442081c00f8000506003d4225038040907900e45400d103840c80c90101c021060080c0304079041c29008401d18400e5400304208541c0039420241e0360f0080c403005000100003111184003d10030f0426030b0358100001c292640105940304032907080ea050204150034110141c0340f241c03003000084840c60000142800899401803440c1d030000410400a41c1c0c808126040a50401018010414440e4040d00f02500482c0309034011139003a2503020080b601c3e0780c0298a00b42c016002141c00401c01c0c50800000300000102000b0380c1d = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 282266744 1250 282265494 282265513
    0x804080f0301030b0916051525050d03051b090d0201090e0702071a2b0920030c152b0509010c1b050705120f06040507051309080304021002 61
    0x200001e8000364003c840c141402010401c030034409111801c0c00c0610020881500307400c14000880525a040c4403c042c0d140c042090700501c420761024000f8604030700f42e0386c3c030764038528182103484c3d10881001002180c20031004c40c04090034480c02d61400c80502000d2800d00b00c9510801c4041d008842e0160704001890201043c003405003203480f40a80b009400400f41e01e403030401d090751101d1040340050030707510f02881041401c1e84600035502ea4448201001000c04030007100d10402018070344000382c03501d24941720b0f00700031b1100216040010f400840881d480a8603103030806c00c040f400c2d9420b00455600a10080e00c10410f58204001e00e044411a120a4100340c9250311080341c004503204243d503915000b85400c0c60b40c12103051038036010320440004440030191142075481c441d5110b071038000d4500300c2040040e54001d0103004040b481a0f4143c03051410241003c95030340049001b110721a803550400260200140e00ca4020082d070f019405500355540c1e5000c02c184142030a811030190301502841 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 282267994 1250 282266744 282266767
    0x906040c11150a1d150709170105010905010b03090a0305090301020d022106090c22080f15090d0c020402070201140703030204030b07050304021e012303010503120910080408 76
    0x400d02189419a20300c006458100080720a96032101400703600c9074503c2c1e2030000500d40205074844120094018100d9940f90a0400c640e9207c042d4020103070703060b0586220b0185a41900107034121100003000740400d90320b96184c00418401903c007203510341d0200c12070703c0001c5d00130000381c1000500180014106100031001d901640e00200072400083d080c41441014401c5403000c040d0000c005a070200c8a62400441d0f241d0907100300214100304440e101521100c50b44168410070103080158240c84a540c0f42000c8107658040d01c06440c03420001070030016403504400280d1600348e1000765102103000e24581c007803000075400b500741a810000410070a8500842820040c5182407280e42d005075240d203981402c000c51040909000d0810408100f03020160340c0b1464070381340710843d02401740b0800c0701160046e07490b050362603604030209480000c01ba544c1910380025604070342c005d40a444070340c000ca10b120380c06446411611544000e1035031454034650301c119429680507214804003842c1c62042940c = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 282269244 1250 282267994 282268003
    0x120f080f160510050403051209030f071b21080c010b030a0b0901110310090506010c051009140607050415050d060312200c0f0f0d05030304120e0906040c11 68
    0x1185040e80c0c0140e24240c007081820407544848030f40000d0204030506090b40e00030168800e405200821410101c04609020030034401c5030381e403049250107260f070783c1010b10b0500072040401c0c0d0211080800d040c400140b4981202901e0341c6842c51b10342e0068042c02d26a11031110350400d400361055990780301c0c0c0146682d1420002c010701140a48551841850f01c1c0c10141d0a5642d00800d600c040380090051101a807003075003050041d14030079800840c3c60f5444200490f0a00a850405030440c41421222281d074440303580800d4100c1d005140c6c2d07060316005458001c1d52028255039a100251040004120000f020a22160000e01903d0154600030302201c0400c169250398000780d0304c0d00d4070009024407590b000031407140c40d0038101803041308054222101c00e07100e0201110040c0036001440d48100607580700b50f2171501c80107000b000c0000b50742090514540c0c0340c004640444507220340d041c2e0713402c0d06401856404050100204401001c1d6038000500028110344203828040c4041ba03103a80700f02600511 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 282270494 1250 282269244 282269257
    0x3120c1e05061609050d060c1b080405011412060f060717040e01080d2f0a120e0108040512070606030b07020d0e010e090c030c04031415010f120f080f 66
    0x60080c00c030303420b01503200c00711411240f0365101400000c01d001c02054403002260203080d50006c60000c4e03484843c82c1d065403410300700c001c124002d9060441c0c40c0e0801031440050000d503203081c2d0381d9803621481c22021002070301c5035450036214219008009411842d00e80501d240e10840a80100e061048a9403007030040f180d143c0300e0980d0b41a0100d820300507415201001801005824024074810100700d002030b00b000348811f95030342c0d844510648118581103c1010740c400e01c9149007281d440e0070030740c14030350038046409540200103818214100260741c4541091030040e41c0040251000b81c0080207224004c3d40102c00c100e904940f00c82001000c0390b4003e40e00307403248000c1d80161a002c1100e1000034209940c207034020341030140c000311114182d101c108003030341c0c0125000d68a954070b4076184807100660055600c0140080505402c1e02c60380400421107100f403101c0c1e000e03003496030b98031505020b0302d071100c1e03010720040000140725010115040781202c1842500a110003172502541c403807240d1460780640e = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 282271744 1250 282270494 282270503
    0xf1507050a111503131b05061b071706130f0812090f1609110405030601030c030303050a050f04060506010908160302030f030c0604030513080102040f030b070903120c1e 74
    0x80c541c682c650b040644a00c5400702072620910310350318000343c4400b09000c50301c0d400b400e03d40c03c081c0140034041440000c070740030b07050083c0b00540b10f0303c007a038145400358114211503405003c0c50000041c205090b9a1034920800040302820166444000c2815440085c0c841a60601061000c000c0841c0082008141e00b034215090644c40b4545144407500d4110280c01d48090303a40907034040c028540c0700300c0d813a00c1175680f03260340031402403042100f4003003a00070364220680c540914800002009414104441100c2c0720303480074404ca565002c112012034204840f40741840105400190000b032440d40520b80c4010141440080544c03210506403418007510301e0000040e00d165000e2095143c20803001c403030307185800c004629164105145544803080a00b0040c2070210100d0444e03103108001c2c0300d0401030704489000315100e903500c5820740d007984400c0c0b005607015038440340400c0c0f02c60310410245c406d50340c0000d43e045010041c0c20040314503000c402030a4414041141b00000c00e160706441c24500640034 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 282272994 1250 282271744 282271763
    0x10503100306050f040b06030f0304060e12070f2102010516060f0f02031e1311010903140a0611130519080f160e151302190c030906020307020f1507050a 67
    0x40c50181b480c4040a0445403081d4010914174000b1100002260b04ae107446207841e10568200c1c00100f442040384c01c2684049020b010f8010800341d2581c5916004c48688801802c6100c00403501c0c403070001840314019000501c10011101c80c480c222402c0038101d4403580c0c00040c4511007000140442d28021a90070710241c002050045180014403444241120800d202d1b0740f5090903c0c000720b20407400c00380248011011001c01c4656030084000c00021600100291140003074410b5031900c84901c04011100e0030726041c0000600058001510082400c0f55418540381c0e09200810801c80d2915068400716510400041510070003070001c10301c4100000004e00e040140e036241c0e442d0a040035001901e20322200070401c00e241004001c0e40420000c156089040201ca5030510700c040d1042e08030500c00b1031280d403411015168004074003212240aa56070b41103280c0c0314032040ba240d104088001c6c3d4803c6507208061490718240400444034050220518500100d41d625103080401c0c290058441c0d861 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 282274244 1250 282272994 282273001
    0x10c030603021504080703020d17040807050307060504140d2109050f030606010807030203040f020d0312060803160204021809010b03090d020a030804082209090606080109030e010503100306050f 85
    0x300350303100750810f50b94100c2203802c16050065140e0364148034440684038400041803481480a805010b860a00c407001d035456485440e503070f50b59a42e00d0148a0315009210320030300094628800c400340d40a403200082e00242c404420010040f07001039465090f1049820142000400b80394410100e8400801e40c8400e021145018104041c054030300c4507070360090300040100041c50303a001d58020350102460034016100c0c1c0303e50428442c4d920410380c0c02034003c88004031017414141c0103c802c002500e426141407003140d4585003296220f000b821510000042a0140d8100500d81074018000103024040d028859607004400030b1403030039080e4442001e000c400410700118082c1800030b0400422580000c01d0701d01d11680d8004e083e40030060018002c140c000c0346042c1050b129118003160200c442541c90701c00307500c034a800d5008004900040751040d250400000701c10303c06001ccc1850031905078455510502840380191070f644d0001301040c1c0c403845d0000020000030010f02c592030161707480300035092003841d = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 282275494 1250 282274244 282274249
    0x5070509010f260d0c03050706050408180f0f2e0c05070801020304050a060908071a100603060308030a09031103030a0209090105010e1302130503060439030b070e03010c03060302 78
    0x2c107544516218070031821070f24403082c60008134158412040d181014506403141411201d5010b1b456009003014240014041440350010262031400749001c0125800c1c0c105800b08000c22074151003040d0480302c01c503030122451400056140c15011800b0910000d49030b50080188020342192036030010980186450050003402c00004001c0c0c404980210318608058840680d01c80c10380d40c00809454449001c0002c00c00040e05468049500c038100340940c2040304911988c05c00115110780c06d138201c56800145103480b038011581100c7c2c0101c00c49145442c0c0c1d400c134002030040b004060b0203010749907a88240200e01000214451030f1023020058550245504100c07031050103a001c58100a4218242c1103d943d580b0343c3c4c6a0b602110401c010383c0d17808011400d441c4003606510855160280001700018080c039603038258a202a84d00c24001002e41d902040d800402146210f2441080483d20500008000b4201d56401c4190342c00e18242c43d0010400080c00d40e040ca140c03080c00651640d00400c0ac50 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 282276744 1250 282275494 282275519
    0x60206060607081801030204030614041e0b010b09010c020a030b04120e01020d120b1003050610080919050a0803271b0d020d060207140c01030504020108060d05070509010f 75
    0xc0811515240b520312541c44200d030310b01441301d4007003980d0102502d059030b582c0291f0484005582c014402d0000b16109808480ca109040303400b5900380758400041000500c400d082041440c1e07000816000503400e150100d8100e40001243c1030510001380704110141c1d81c3c0b41080c4d07000f144030f21030b603150340d280500d0240c040e044800c91260500940140c0b00345181e0300420743e80d4680e0307011f14203500c050100001c2e180c0a4252404442e8129528455005206526400880c0300c1d0009031400001343e0200041141c04080841c0c105406400c8100f035003030505615191a00c03184c2c01001216020340c3c940c2c030b0b100300390f900c20b85202040d65038088840c944014509546008400311001500c0341c0c110000124030518503480711503202e06400c03405034045668175081d40342010341020045495442510781001d080700c80d116200210310031010411210340c400d001b01c0f441181c0c103943c0c041d031649501f81031010290444408560b40e00034800089442e0300c07407441d018020100000d01103412440c008074101d84 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 282277994 1250 282276744 282276751
    0x7020627010302070f0f051203010b090a050607020d0305030a151202010305090f07050d061d010b01020f0a020112050c090d0602030105100206010f1509180501150e030703021201020f040f060206 85
    0x5050061000d2004503011800c0b542c40141c1104190001c1c00080c50702c00d0801540c0d2020030940c2c0404270001c590020484054a0302c0403060316404501c5868204201160256050080d84a0344002640300000d119102941d00002c0d1890081086120403191001030000c035080010203142b40d1040400395a850300400360062010f501a0410344c0c0c0d5a01c0542e00d0358480c0c000d050141042a082100300403003580403e0b000b00440300c0750821010101c9100303020b0440200014010310036a590110601c2d4040303400700e61560b05850340e00000341c8144200c0e001c2e0400819001c2012414070070102541c540b5180146594402c0c000180d4940c100702c100030303507414040c2c2694115441440103100d0002040d07542c0301030b82c0b400b42801c07840c084164021900c0502e580c04c0344038900c414061184011640c0d800030303411303038001503e403080b9030103a400e0071110700c10002c040a07490b42c0158410005030420303011912441580b8400076107803800f115002c24103580194042d01c40240c01c1502080a1503050000940 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 282279244 1250 282277994 282277997
    0x6120b0409050706031a272203030b0a1e030219060503040f0501090c0b0d050112051506060904090506060a050409151a0a170f030c1902060702062701 66
    0x100401c1c0d803580d903600c424034001c2c0e8080c556909105440c5910103022400701507401070443ca500b9000c0300640d00d42211140042c2c00d504a01c0d4041440c02100c3d100041100c0c15082c00303c40c21645980701100588101c2d2801c6406c520b1550340468007106482c3d07500300c2c0245c0882c1c194141813551060120b0761781000d803042201a0f0546040c448075512504498109800103180040c44255082441c010300c0c0c0c0910080c114071495400040000150026080c0c4201c00e100404c51a03903651010344081d0100b010041160300121750044001808040e1990800d80140142c1c0c140041c0c2c034040f8044884200d4155000c0d8402001c1003d185040c000c00000b0304410f88052102848030380d0345048911031348048100d0180c480c2010301c446805000c1c402c508005c011b18554405030380b460310401400c5425100e03581800b4400c454603c82e44004100d41e07904018000405881c110360720462503c2c0540c1d90f00b00d0380b142d000c200d280090394031500544000101e0070101d0107035840c0c160309911700d880e03040c000d00e0 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 282280494 1250 282279244 282279251
    0xd02030a1b02180a0917180f0a05041815150303120f020a0903020a050411030f090a0503070807051902010503150d060c030e060f040b0c03070e1f0906020604050304150507060606120b04 81
    0x145c41c140d550303540750788091060391108c0c0e45105030000600a01c2ea02c2d08600c1d00240b40c550010600c2445d0402c03000b040d405000d6014148400c440b40009541d101718481c0c42c00680d22008000103440b41140400900fa2403900240c40c4251011401c01d0382d004c1c00066002a03d17100c0103009502e40010030100801c4101c3c1d007040004c480030b0070072005008c0100460101d82280700000c2403041c05020b1420101c3c2d201094a60ba0a028941507500b03802c1900140c9451103841d18986d840140c0c01e12141101e5016102c190655540a80c11001060000c8116401c810240075000c0000c0603409020010901d549001c1585c1035441d242c24034041c001841e40650b00c010b42c0074800800d00d0400d0311604914203a040580c1ca9172205029901c8007403c6482c15041510a155100c2c0c00c003500e25022070803200d070390343e20180542c0e07540c2c12659102c0542e80500300d41c10070031042204400c4107912101c14030241c10042d0912001d0344400f4203c89a6620003000f00c1c1640040c8850f4030360038032540c0c0e0090780848081 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 282281744 1250 282280494 282280507
    0x10e011e120c030b090c0705190c09050105041a0f040902090a050403081b0f0a031805060103060c1d1215070206010503070909030c0204050703020d0f0e0d02030a1b02180a0917 77
    0x14560440140440700e211b8000900802407000900c549001000085040d071390030f81d014a44140c00f81c00314880c000c0034515003000803815152502490100d03000d0042c001d25000c40f100c1c100007100c0320014071a588140d84100c010010780701c0040340d601c034480300940003e0318a0507040150201000601159501d00300c00d582c1c4005550303000c180d9000192001ca540e0b02c0b503902c4601a0002c02604442d0120448007020300010000001036603811b0341c1c4140828000072909540a0368030000758032843c3e0418074049803071501c40c1001000100c585080c1c404a856803e507501c24400405015658600181c000380f0051003281010841040142001801000b0b402426200108003501191000f03120701d40b83d0010418241c443d4042d80c001d66180203082080742a51951900141140b0030204001c1c012009034a80341400403080c1d0b4400d0a881c0c891800e04d035060090300f5181c0e640564126801409074151003211a40c00116a10400000703070001982000d6003042c60400b003540001d60100601002107 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 282282994 1250 282281744 282281749
    0x503130e060d12030b13090302011103011404020c070b031303090501021c0f02161d0c07080922020d050906090105010f090e0a02030f0102131211010e011e120c030b 72
    0x7140c0060340c00818042c4544810102200a000550045c1398003000880313000d11810850f6200d100064071a4000f040b140609034240340150000344102031008070940d030882980c0c00c0940003003c0400c4400181c4034076507101c0020701503070341003038408540443c3d44420b007008043c0c0242a21010702400d0005180c2000040f040e1918103240d0345006c410060181000e61a09008008651000c12011040f881d0140c4031020302404442e65542b00005a0000000c034842041d008112070056400ca070109240c2203000e428040c80c11000d011501420b030142046544401541c4003406030786000c81000700d00c074100039440c02e150200150040400740d00d024010000c28032510410310441e42c0302c0c01d0200e5200040602d5070f040c10040038000e0340602402650354509138066004204410400015085058507420b0058100f081144000e100b2544145018031b40e40c040e40c17194010500500d4030340c801c03440c00c1140c3e41c602c03e00e041c980c001003504501903001d01c140c540a01a4015240d283c100140d0440800 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 282284244 1250 282282994 282283009
    0x1509141501080604080c0a02181512071a070602071a06010509030a02100903140606010801060c1709060c0a0c18150e0c04080607050904061a03151306030503130e06 72
    0x1405840c0c0002e000d806c8501c244640010107400070242e01d5041445001780ca007408003141c5c0e0345200622401e100d0340f50b1a1418058152241c108005c108850800c13209105050718581e080100d030304281b10f950002861070004080d02441030344401c4609401c2c0300144080c8030003800e103506002046c01452a1504d00040c840402c94040314070000918080340291030340900c0e90005480e44030b41210700346241e0400a507080c0600d0082e0f032203142ca43c0e81d8920882c0e0780c8805c01c0b4010f0000481c250a00c0408404101034480030400522641c46c00b44001e4101c3e03e072480c02c4804458080c15207008020300c460011650503030040469041c80100600070000c1c3c440a02c0d80164000e00c103507207000c10f03001d40846040d2009407155204441c0e65090a14016201d500020800362295007030410102d40c4100451455100610546078141152502c50819100c6d014610392607800c0300031301c140c00f60003082c0e602681d0001c50107400610380d1aa0300300701d58814003440d500311190100700d0109204880d00d6804 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 282285494 1250 282284244 282284251
    0xa020f030613021c02070506090705010815190e0f1b0702010c080906161401020f0d0f15060f0314070206011205010b100f0216050906010c15091415010806 68
    0x2c0d40b0350b0030582282d80c01c4000b1300034000381401501e042890160701c400755600403d003583c01070741207451595400039000d0703550440380682c4c0e0026902c1c00c0031079100140f1069246208a00428911000c008404613020210099000300580b0342079400f0311401c070303c82000d8180c10105016030742819800110041081d0701c2030400081c1041045d82528040c084020140ca44929004240d596208000007080c9620380010714103480c081c1084100e0b01140a05200300c47d0036101303444085040c5603141c0ca00c00014108040300385030a5855141d42d00c600c0d002d10021760050201501c3d100011040102c0003012110b2903c1c240c01c100402609005005400140c041d04503109a4000e0308411800d181150141004408140d006004184a08019074000101c01e034400c805a080700c60100142c1144080201039210740c2d0b81006290f80441c109501c03400d8241c4040f401803a40003c6030f4205099041102d0403485c0544010305142d203003a08009052280d1a48841d0f84a5100c80395410081320a0b281d200c0503 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 282286744 1250 282285494 282285499
    0x1b0e1c020603040b0f310606090603050f0f01021804090809040603080d060b04051507030513030302060f0a02090d08160b01081c0801030308060f0d02101d0102070807050d081210030b0a020f0306 85
    0x40a112007084007523000741000d04000700c8140300d00c0b41d0741e1400c9651503080d4a0245024080d420312030060480500c02c1d1400c46510001c00214441907406100c000c011006043d0f4006170300300107802c91620365016410086100d003007040d5981c50380d030448808440d19900204820031003000104295a0783d00000c9080c0007018550a81d03d00c0180303402e4505110301300300717078403030081081d03001080c140c021401e42d1040d403d1a2425aa41e45c4400c0158100c1c440e070300900354000c044079085004560000060303c2c0341c031204500c05840e10040c0e00c0e0300d209102c00340d010301c1c4541c1c016418455058404020b82d042c04580c1c2c02c4c4017909505650303010b0031a400c010849802004120340010b02680e605048014103078000e811802d02052401c8009e0005540b00c269032009800802602c1c0c55520000782902216542c2000d04001410003007000000d0301c03880019500c1d50000d10800c0a01259008414007030307060501c401042d03901c0c5107051088003100909000309c0c0c0e80b0600030054007003852001c030790340b01104 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 282287994 1250 282286744 282286831
    0xc0e1f0c120318031706090f040b090c0301060e150a0e01090207050a020409080304030315230a1a04030b0a0c052d0d0605041b0e1c020603040b0f 64
    0x1c0890050021141d510400b0340070b44006000c0c103070885841020580301c510604400c0ea2110148500010241d80c01c801041c0c6032000500420710302410340c0c0e00444084103444c200d550180c0001c0c20b40d100c4c4c0e00300403000d039045020b10003640c1c0482c6018440e001c06865070740040e85482103ca2452405104d82140188c000905101b0400c060081c8500700394024000c0285416038103104171160401c84003240802e20301040d4190b40000d40c1c0400086410b09003a0100c0040200034055030443c0440c1e1076500108034500c04184a030182400f1a500800d03440342c1502c0c1c910f035013800c801e144809802c4200d041c1c907101c41390710701d03c2e407040031504051035628040e04000d00e0b210207140c2d00c02d0b840f1a0305860703200100e425502211190440003c4a10880d4240011103100b82d03a00411240c9258881c04a101403070719103a1824589294085c842910b401101620440d070081034491b44120340441d1070075011000c0003801e81201b030405800424510305000001c1c040641d04c80030b40c2455003c40b110240 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 282289244 1250 282287994 282288023
    0x603010c230d0212191401060e01031d0a12080115052808061002061e04080c060403031b020a0201020d03020d0b040608030405030d08070813020d060c0e1f0c 69
    0x185007007222074114412004568030b12511404d0b03034403180140c0e094507000c5240100c00380540880d0140c5c400c01c0c9078240c0c2c0891302e44d01e0003030f06a42e0b001052484078181502c1c0c030134040c8400c0d0103584c000030031003403035000d000204014078082892043c004185002e111081b0014403005107407007480840c88889040c00740d50b0b1002041c065200d0025652141c2100618500318030120ba440310899009010541c2e011280c1c10540b00c060762034120403038112040301e81418034408051030300040d0a41080c0260340304c0c0c0c9000c00d03030800705080c1801110140d0101f520741c01c3d00c4e503145403861180410200e261028180503441580001d441c0da40411080081640105407801021a5a0b202d4204100c00800402040d59201070450306d0b600144125071103400f40050b80c941007405802c0461048076903940d0540300355219030345110400c00e20700c400d07a04020060b10300c1c2c000844900c00d817031199050782c54011914100c003041004810401405e0200c1040000c1d401d610b540d006001190754035408449902c0018 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 282290494 1250 282289244 282289307
    0x30203060f030f0c010809030406050909060103110d09020a0527040602090a0f0305010c080c0406031e02160c0807050f120a0b1e07050301030c03031d04021b01050603010c 75
    0x49107450541d030b040c01140030100070040002240d42480100f0788921b409540d0b00d40d11161240154030504012410411058a262909049969000805040000e0780f104042288091b5800a070b41d0091129640c0d0200d100703503c1c0c072000c000300034802166031030041d0b00010100320a000b05106500c00c05c048250105040183c0e03601640d00c0400054411943d503a901c150303121451010380b1040e00d255203040c4102d000c942c443e4109511039900d200300903103450310b0001c1c12401440251010307034640c0c032500b800c00c03001c8000c4d00040c01e910041d490202000901070500140d80d01459009850582c0701800070042c903150807080e800480d0049800380301c24040107440328104000301c24000d025420070020409014820103002c4880c0000c50381111407a61450300c02e5035280f20030b000c0034140e00c1c80403d0403c0024460800142500d0302d5004c1c103540c55091101003004c2c1d8100c100c10442d81084c10b0320310400c0c08024424a40d001030220024407148440950103815204284000740c02d4000601410340c0c0d00d13 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 282291744 1250 282290494 282290509
    0x1b21090d170a0b040f0b042702010f0507050706090303030e060912160609051f060b09040f1506110f03120a020310120602030609090a120813050a05061b04140103020306 74
    0x1210281050042c518200c5c030010003400103080305482540b800f0581454000d640400f030390390a602402600010380c40d9001034601d2210381620300c00300841044400005070090001400510706915801001c9043d03241c082c09840b0488542d0100f64000030410030f0008001596000001c0f000e900a43d40701c06607a80c40031000700c0c154000c1c110a05004216080205c0094289180c00602c0341c21040240600c0c3c01800b5940035200d5013140c0032003445002220b10305944007649104441c0170008286450600b40c80640b0540d500c100080741807181360306200344c8103005080309002c110016515045525601180704403000d0700e4070701c4966000c00040d20090714501c01c04054200e415104500d012140f074904040e40c0200c65460181030800b0100300803e0001403a0640103a00006100c50030030f010108546900d0020030449590150a6441d0080760701480306000b254021b0010300094504010305201803c3c0e42109090780c040100400c00c0900702d00c05001d880e40e0002d1a0241c7c1d242ca070900094601c = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 282292994 1250 282291744 282291761
    0xc011112030903120903071218030b09071a0f04090c0504050a18110c061501020c0a06030509010b09060a03061802060d020d1b0c0b1b21090d170a 64
    0x514400018082c0780308000003c1d280300002110854411381c0c540500640768002c480703000b8254800d41042c003480302d00600c0074000da00584401c041405589845001c1d2410065401854a0700024000d00046000c64022080c030403228424628008100c020b11180f84124401c0300d0185070345000070203005200300d0880d4002c11000f8070043d01a521922840414480c104003450281d00d00402d402e00c40c3c0004040e20840000b600140000b0f0380c030303482006420054201d44504601407400e10412542c2d070a1181c6015040c030750341c00140ca2403e80030319821aa07007103e0041c17203091420100016640c8006003201500d80c4a0030200b0048018545000d813403480b1b0000a62201010070380d070000e075296902901040e00705400130701043e010008090840a848003412002070f03140c036181404240844101038220326007a02c01c1c1000141c1c4c20364916250403042200d182c5030741500701003510440214400350040031800c043d141c10214414003403c0c81d078403a18a0040700c00b44400044c040b8505a011048 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 282294244 1250 282292994 282293023
    0x5010605031f1511012315221e1d1b090412020f0a030f030b0a060e06180909031908010503030301060f05090a1404060f030b0f190609090b010503030307020c0111 71
    0xb11b030714030780004100500729820804c0c110342c018040c006184c810386a07000842c0702c6640004019104040310060700704d0503140200d040840d0400801c1e41c030780d4464150346400400d0354880c411480413040d410b00c620200c100744500000a00b10000f0313690f154420f03811650200c0c1484215418210580c241004007900c0d075841e02403c2450420300d508a41040100380301ea035030070440914070030200035015085014680015040d500c0c0c2c411141011780c01400b0a0b02c40300d9104100e01d04010000b04030080840e08000341c0e030404600c0050102d425032040e80100c000341440302d0958180300c040b0790749020501c40d50080000d060b44020b04070f8016002c64080c0c000c054021802c6580303c080824082c62409001c0340194504080040e5401501c40407405a80e8032035450070307480d01c4a2641030700f802c40c00b40c000103240251203464050002544600c10043c20a81030200d0424100e050003415240140d0065000303030020010443c00c00ea01049640b8010402d0030b03c0342500115580b160f240c280f0080b620071 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 282295494 1250 282294244 282294281
    0x100504140610030c06050a0801150513030c050406270207060b0d06050702302505010608060a0c08040f0c0b0f09090a0c050d11070605010605031f151101 67
    0x8201c6807402110042d04d0103120301d0840c441e0b6404046915114074180440062000801880020041314042e1174401840c68420308014a4001d10740710404140e00407a140b1200c80410821821302d402030500070804400c4204503501d086542e04500c40c2c5404002107003e03400070b445002c0203210740c8000d00301480602030203900d040303a1521344014a01a50014050701c516901410282d000740c140d500002c1e0310040c000c0c00090481c040c1c8401d604000c0220074051180280361000300c09041d501050b90307001da00040f0301e1600e070142641c1071100142000c0d501e00e040c5003a40700b050b034002c0341254006500c545000e007414041d0401100c888003d801401d0f034107500203008074244c11100064100418221503088030b80d102c860180c4100c40000c501c16005c111305104c1d084600f5940d5026890311440140036614141e01613a500c821a40e003600004040307003000c014000781300c541403d00d19081500c5181410b400d814403120840140c9000c8840742040900180b5440810003900f107405070179445407402 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 282296744 1250 282295494 282295501
    0xf080309010204211401050c1e040801021c0c0903021e0f10050c0106050609030607080a0e01090c0602010c0801080712080c030313021302070c090c02012d110306031005041406 77
    0x144602d02c681113040d110f41d0b425454160a01406202d098018180c0500a0780b070403182c3c47d244c40502c81451405409090700b8400010f03208002e00003000c0c1029042400108010300001220440b000c0c652860100118080103000685070742c1e101d480404507500c0c030701143c4e138081c00010740d1550940341000e4000c01c06400b10301d071230b54110015001380d0141e9402030001680f501c0030b1090398011280100c0d4141e0107040400c00d841d01030948136030030400494001c11080074a000d902d082d200f0f4203900320741c030318440d00c0b04000c01036081c4170b00c110780c1c4d07128605000c0c42d525240010741d40388014040e40740c00c2000c00780c0762000c021040c000c403640000000c0039640c803450180c1402c81c0040b01604181d02402c11075510207100b031901c0c804c541c446540b1922003080f241c1054000c1d001004420341070300c10f66503505480100e020019052b40f810808036011f14090b0080d00b5038140940d042c0038204e040a04042c02803081c943c2d0301040c4000d4241c075903540003070281e98a050034492401e5800340d044490049100b031 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 282297994 1250 282296744 282296789
    0x12010f0c09050a0e040f030804170a02030315011e05030c120c13080a08030412090314010525020a0f02011404080a11060301081504031101020408031306020a0f080309010204 76
    0x22808031603003122000b0742c40399603040204c10034104503030060000100208880c002809840440c0d0080d014100c0910a92020036000c00603510052043d009640040b04108044412401c1078115030800e10f0082200030302c10550448100d900c00540c0203004001c000100c2e440b00c04c800b980c84050b510444124141445112036455600c085211a16250084000300e41940c0001e03504c3d0206506c1400c0310f00d59500c980300c030461000b24030000d404000f003803580040031911140c6141c42c0d051003580005440e0804081014080d0060b1a180c00c41e041081102070300140c012030291840c3c7d0700030600d411504500d00c0122066000003599010013040441c0c0461060000500c40415620030310660811885000811080b0700003440341641c00d501c400040903a0842d041a21500903110742004844154410086804da030001d802800c030030f510108508511040c2c0070101002440d140c000b44c18002403544440a019220364405444810000042500d41d02d00b58115802082000064014540401c40 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 282299244 1250 282297994 282298007
    0x31603051318140606160201050405060a050a0f1b0b06040906140f0a0207021e0102011d2d121308010c0e090a0b0913050a02040603030207150f080612010f0c 69
    0x1d2014076140781070b40043c1160a0f006801c0d00541000304242d0074102c2c2025491040709980008a042220601c40090b00b84c468102600806021361285510380542c60b100500c00984520544200705140c0108041805800c09080c00d0581103a220112540d4000100e0080c200e80c02c40103018918254000742c40503a40c610711030003030441490300c94051300c0344588581070f400b60305000f0f54420010411004040c80d60708054050310380600001c600701e030800c244c203071520160790802c51b0300d03030482d840540070b4100001e01300d03c900210043c40281a41103907511035482c013040070400184440041d80340f400081e1112180000c1c103000c4020300c01b14605040040c2000c0e030031000603004002200c041a110351260040588085024102030300da0340c0c1d40c00c4401003001605a003556a8042c6204500140c1c82d5409040301a50081d0028588549000e404101e0070034416000790802181000c0114a244d0180403280c1144084882c0342004a81300000b50050811110116503280780c40e0320f40030455000784 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 282300494 1250 282299244 282299279
    0xa0c050106120507030b01080c10051804091514090d0e0d080f0a080604020a0e100504080105090a030e0603010f0e1b19110309090406180203070e09010b0d03020316030513 75
    0x200004c00d10392340d03000340710f03600d0001c0f0700781b0342e03110700b044091b50865440349000d4085503900021500d00c607109031011400301da0002400343e69822640c01103404148481c05002105505c03000003082034a024403040383c4404100701000104000b0081041481c0c2d6494101380440d50040125503480307418602100e583d0340002d000c100031410800010710b040c0351501c00e640d21002d10303842d03500a8180301c00400c01340031f0080c036040d010310806100101e000b130000d2159500c00c40b450002019a50f00500b8007802c03110140d019184900b40410040c413001d5039840c60301d421501c207130f0b01c02c086544405000803001600203540092002001c03601e6000c1c4c003c1800c0171816840346403114524000d4200e0920303280e2181d5806a501710700802d0125001035081e034458243e0f0703502480c0845230b00003290700190400c0003130351058a043e0914400d01c240b0083c20300c105011950304071f030303520034040703050b600a5101d0243d01203040400b80918003800a05015500312040740001c0403030340a00302d40b5105400040700185 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 282301744 1250 282300494 282300503
    0x3020f27041101090312031d0a03030204050f090108030d02090d080d15091a0613050d0b070809010207031b050a02090c071b050307150e03100f0f09080a0c05010612050703 75
    0x181c03440c0303143c1d402504a94207a07500f003001080b02e03c140000aa0142402e12100415003c40c0d01c00d039124130030b052000c490124860741d4052b83c2c40b8a400200441c1c140c00c145142c1c8100540c00040200100c000103c5036090341c2214056100c11031a000281c820340000b0000c0c4c00d203840010651411119913104c581d814072003112419a1030f0300d806107807085035a210b40700e007030900c94050ba0800c103180c500c0c050f041101e81703550100c03091a1540e000c102114000d4104880448405c02800703500c540040200d0b51100c049002141030a40588008200030401024550503010226103402480400d000c02412030707402805021246c20180b5440c40158000740c41560842c0c1d840c10325103146061100d81c2c10407541e00500600c0054104444856030024005589040c0050949001899107080c811001d03107040e02e0000049087d0392070242c0c8107941e42e1182c4180c0c000e24044d00c038400628a2410340c5c140c01254a0281d20758205894001e004101680180020b0249100700804100c0b00091200c2502e115 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 282302994 1250 282301744 282301763
    0x180e0412032003010504090c03060f0b01140c0a030f11061008010b0a0305060105060a020a0605010602030306011d0a030b090f1515010207030302070603050c040512010e0606010509090103020f2704 86
    0x181c079848081a00b610b10035990b00c0d07400300010005864140c0060395000d00807401001c2c403555980e18141254a1180690a8039840c1c5488094a43e0001202c01c0c0503a0701c0b00c101850051a0501c5940f10888c812000303050242c101c009220700e612803000c410b100142d0004403005400c08024010348003442d8426020741d903081036512032071400c210f94004102c9520a00401e800e0742050200009500321a50359411842035080c640023052080c01524000d28054010319500d0400d5000101400728054019030514000b1003105401c1d217400d01c01c0400c50b5000428000c490f2078400b5200d08101a002e2605c1326407144001d0060140c05545515021350180848084c1c0301d489617005903141c1040c0e20015015070440c90b070404c80c01d40203411055000d036110103101c3c0380980710341c0014000300c2741c0341d05001940c0d07485101110107102080030b560030407030908180d410110907000041c0e034020305020090260b01c000003a0102615801a110020310420b41c4440060401800101d94890216803d80d0300c0100b = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 282304244 1250 282302994 282303011
    0xa0c090b010e13090f050d18050108010803120703060902040806010905090c090408070813061e050c0a110d0b040312050c0906070605070c020a0602010213050303040f06180e041203 79
    0x2e4940300c0e01415010f00f0704042c2c01d80c546000d6008000d21001503805414502050f00040d1051004144001e55078584600c00596446070fa040d4900395040507041c05088001840380d14400015240c020303180c02c0d138403d240d90301d055084010b0161a0f104104940c000318001c565100045030882c161641d0010800060b52004103056540c099058042e400001ca0030105001c20415001002c08a0081103002c0ca4401c031001c0d1002406102d620a0300040e005025200c82d00b080d004448003502070700d06d01a130a001c00d00004d140c4584041000030030400258032000400d40b1804500030034a40c001170030442e1407509080c050400d500255941d5100d03854500050884903061003516038419014104605201c00395071858010b1201030314020a2042e144045c000580d0f96440903006081151700151710341001045134100800e881c3c0109200f80c206100602881c5042c1d43c20744201c50003850401114440001d1030211081103401c8000034050031420070080c0700520008031052005650104803076803 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 282305494 1250 282304244 282304247
    0x50403390602060c040b030714040515071e05281509020117010b030106260c0c011401140402031e01080c01121a060a0e03030d0509010c11060a0f0e0a0c090b01 70
    0x1703c4c50080310400c581c288086428280320b001e10a1035140781900f0780d4601500d0b500007a00306020341070300c480b01203800074801e0100041c4200d0601500f2010b181002d4143c2c15544503901c03820516024920600c0d40600c540c400d0100b00c02d05a441500b02c03080c4142401620f012038098105030f4401e0b0b012450100c400c8000241440d102d03812590300003651420359080c44411180d001c541003000032001c09506521741145030000b075140c043c4141d101c1d030641d51038640d00c0440c01c2d81d0f200c2802d403004151660040000b48079041c00c19944174021070b801a1303650fa940080013020000c42c0800c54030201820004202d0400c0014180f1051100340c030742c1c07403501302c42c1c410940580d1101d004045c2e030b4002010500700141049806040007018070b04100d0f185d0150400409e10b07541001160904141c0c550043c0606001c080c030401c441000349141c00100307102d05d034404176581c40020f0200c07a09542d40d000705c0a401d907101d9100d09040c9400a0964080501500f801503000c0c40a01602c3d119504d0300340c010b0b04c1907 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 282306744 1250 282305494 282305497
    0x8100234171b0706140309031602040e0609010605090a1118030f0717150c09130609020708120105030604120503060d0b0103050a0b060406060c0f020303071703011d0403050403390602060c 82
    0x7c0c11407078004d42c5840300c00a1503010200c101c110803600107440f650b01d1a9403038030612440740300d4150300000141c854070b00000c1004100029000d00c010034a004100d040000130041101c0045061041c610481030070840405d1030001080f100254601400e40003088000e50030f1503140f007041910044541d403588240b13010140803016030300c1d02c951881c10000f224150801910011244400d41c4000503410368802240301660b010440c119010b1100051000c070010800401030301402c001ea00820051603c0d0350b45854922130802090207001d00803001454030350718601110002980b198240b06103503585c1c94440c0d40c440711800c007214003201e00000107903141054031a01080360303016922403407031121545844c2c4001c01550b0007660140010400007000c00e01052414035105d42048065130340758507010148000390603606103450805043d506000c046a840320550b020f40343c02c030707d5040310010204200d1005e1000303880c40c82e0841146110076030911541e0814081115000c0c2c003912510780d00c0c0d4038000c00740d = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 282307994 1250 282306744 282306751
    0x1b07030804031e0804020907030e0706020a03120204050a051c0c0b0c0105091b132915040605040306021605060f071116061808100234171b07061403 65
    0x10384c22200280140c9013142656400c0041d034100000c0c1c0440000c080c50070842940c12480140c2c3c04450031500b0194403104404449600c41070450600c0e0500380050148151441898442c000b0003111341114000445820940c0c2e60000c0103002d11507a42075082d8403134000c4c85400080b9464140080e0a40002140c0400c441c076605241c6801c07060041c3c2080202940840e034010401d5480d0310820302501320704801c041c182a0300011150721010002009441c03600b051120343d40c0300c020f00042010350b030000300b942c090360f81c00640540c0b6207040e2141460301130001000035086101d030105000f01101c148465902408440d5a031204207440088902d95842d2991100c1c200b81e400384000f040780911801210b2494184407481c1c01c1c0041c0e0b03820074075240412040f0fa91030040d07800075040641e07091a45e0003041240c606600ea1806410000c4040003003e10b141014048454248100c042000103d08032030b4a241000c0c4c80c00e080324811f074038955490f0000c2c064507010407031651044000d00c0e40381098910 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 282309244 1250 282307994 282307997
    0x18100614090412110a02090c0919150516080304060e010b030f0c131103010806011d06220f0905010515090f1b0d0e010b0a0f0602070b031b07030804031e 67
    0x5400f9040c410440c3c00c2100e910040300139010790b204a000503507031300b4a5030b4003501414a0b1341c1d40b581040d2007000030311450441d142040f040d0343c010400040d0b000141c1e810008180d03003419510f0700c00d0410310206507904118024071980e800000c01c000c0040c03980c800703681140c3c5403000f00904581d51090680d10200c0600507525a40411808030040c030b0010003010050800d00c20115580b562011101e0094000f0b8001c4079403900f02400603c980030700507900c40708141601084c0d91050a0100108024640e14000416148520500c0c4107140100360070a402c00108a40100325075015418918020042a1078007403101046060308030040c0390440d20180038041140130b007545510341414a56540702c2c0c070004600189401d01c4140d01107041c9104003181d084105d0000300e40c0c54024010028003181c0740d00103a8030500000c5080c0501c0d41d00080c5c5800303541c101c2001503940d45809841d1101640c2c4e0118900080034000791000030180c1c4254414000c61198540c20310214030307070700d81214100071905602c0 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 282310494 1250 282309244 282309263
    0x1412090c0114220503011e0c08010e010b0c010605060a020106051302120105061b01020d020a020d0c120e0f060703050a08010f0e0c0706140901060f0503030304080d05181006140904 79
    0x1400c00c0703440c0c0f1003807040440b000920682180d07200046825910f03040038008162036426030b2071500482034002c1550400c0c8614003e500e541c1082600c015452046c012181c503944041666240d2481c00d52200002d0f0400508041e2a54aa144001d004e48840d0081a0060b54110000140b041250080e038000344c9059180e0340c1310740c0c205414080c0e00d82100321110a0300034540c1d03800c150044288020700241c5058440941e45900c14a00645000b4070350340e41400b04000c200c1e080c00400c00030303c02207000030031a1400d042500c0450740000c06c10701c901c0c010706910010015a880405810030002e00098803981c540d80d00c26a40c50030700e0911950644034071030201002d20300151a6281d440002c00801e8842c01c0d000664038003820040143c04400c41c1c4c40d02030780c3e41d20a003d110045c82c1c14030100040c00e0480083d071441c6026544d00d140c0b401290b816251107520b17400403c86210a01011150035401e010403680d1b1703104118500310181005228480720401480484001d600302000101c1c4155042a0a003 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 282311744 1250 282310494 282310507
    0x105060f090102210d0507020303060d02040507090302150c0706050309030d1104120f03080108010b1e03031204060f110c0c010c0309080106080601030b0703050103050613031412090c0114 82
    0x14145a0721100009045004d80025071851104000c4c100b8151030419401c2e40c1c4130044020a0421550041d1640065610500402106a07221882c2d541d100360f05940124280e110084181c4a0406981001707500214cc6d100c100c4141c400080500340900104040720b0300640c2d150b10550791488196004103081d00108074200c80d0301802c2e0001c01d2140c19a0305054600782c1c1d16032451040344402d0000322041403460f4042014158041c070040d01401c82c40b4001c001051180001a10300c0101d078880c0c2403402d41c55000c400032a50140241c1e50310505030500700c420307440d080c5850801000c0e00c0351803a01c00c52501261400f144414000d4500080d5010300508404840d8030066801a0300e05004604012416101194100080c0148070050102c0390040200e541146071201408100030201c0e4105440c01c801000420000900b00c0d800c2480626a0300c5c0e80c101c0c1d82411a4440194140c1c990841c4001484038000d42d42c05204038800c004140a40340c200b1900c0340111801d090f035030b603819501030050050 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 282312994 1250 282311744 282311767
    0x50604050705070f080906040b0910020615120f06090a06050702030a080f15042313050a031101020d05041415090705040f060314060402090a090b130503130b0a0314010506 75
    0x4000600800342e0500700a04500002d01f42c2c0d01c940c104200303030440807074607010f1ba040c001422000660640040c00662600030689844480006611882142110b0b14000c0003641844860880140c10040d180c071b80c0780044245549010200301165198984400039000c5440481034941031000c5940e260340300c0d2120783c0c8501000c0e00250002c00040ca060580052a0342c5a10400c1004900050440052042c01d00802c064800003045042ea5003003400303518002680124642d41c00e10350504002c421000b00c02d0840340280941644100c20b18035040605c420721981110b01040d92891400f210b41e690701400e2004c0211100b564206240c2d407120109100710314003031b0031031040380984210003d029652515514201e0540482001003a0031603c103000650500e1000039a12a41c0003009003c0003105944d02e041d00031004100040d0f4681106410301040002e208072140c07452008424420746484108809541c1c3c4410070140c046464052400302038000790356842d040301d2004043c5070a00d20340c0300c3d5 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 282314244 1250 282312994 282313013
    0x1e0301060c0312140a15090e0c011103040e0c070c050415091d1f0605010212090d0609050303100e06010306051c0303020f0f0304230d1101020d09030203090405060405070507 76
    0x1143c000703a407503100143c2201400d100051080400c900b000c1102241c5411141d40216030b03410401c4042d0600318424440742000910800741802860001c2c400d0004100550079401a6004404401110018084600c0c1202c018040c041d010f0302402440c81c0ea104100011500c0000e1520716120282c8801c004400d4907a101111098003210741c0c000250712040c0340c505100141c015200804445041280ba90806104500103080d081c0000c020801c46081d03d05850700032061b01a1144021900e00d6040003065004051903a61101c01c81e43c9a080160380c1040c95001c0d03000d170103195a58540000c1896210b4041c410486a01500d96065802825000f05810305418016424035808000c0c009030411080000c1c15100e116941e22a00c074185460000c2220606200100c4030146011210714103440101d051140c4841034201780d201d4010805806019000d204030541c40c1502c0e003880e80c2c1c14540c010000b000b505000b120304001954641d02000110ba4003521070000142c0f0a00036107001600841 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 282315494 1250 282314244 282314267
    0x4050403270504020d0f06080f121c0c02010b040f0203060a180b2d0409080d0c090306051302120a08160804050a032a0e0c0706090c09021e0301060c03 66
    0x109925074140e240c00c0401c050703900001c5104821a501c05810404103038600c2a940903240c610084e0006020901c4101c1c1e44907a5550300040304500003400c01c0342100b000941c902030b01e0030203400f400000080140607009280400c1450b000c0d03410480e090031500e510b4070880380300740c0e8000c2c070454099017060509905041c2a000100540e941c1e15180429943d81d8440c0e204880c0c2804070b14006401d1b0201c59040d0001d2900d03001d8090740c10042c1590004036188295141d40c900c030400000e17080c1c1404400c65000d01c00b9070000d01202d2400080c0a901c60403030200300c4529000b51040040300451030b007180d50ba0040c01002401c00c00040c0500a0030341408030407003202038040c01016040c951201c00082d00120715500c1115441c0d0401201449402030903c020751541028102102c1c0515000d80f6400e0440001c1c10b28010a40002e00716080003550b6101e003115940280c0c02907103658982d000302e0000d42c0018801c0400006000a4044a0341d251080b241aa01d441d655401c10f20f0260b0380a0700c1020b54003 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 282316744 1250 282315494 282315557
    0x10c0e011d012606010215060108060d1b090614010203070b0f04140f03090f10082a12040c17030403080d1103070e012606090406180311070504050403 66
    0x4070f0010740324184203010000360612000750b803002030815800291800d1420306c015170900100008000b40c87ea0041c3c03683d41e0100d025900c40054003503070724008007a4a5801c14910070b000c0003072000b2944902682c4203a09a440040c000e0003502045001a603503801121002801044001c0001d0382d00c500da1000190407522880f144494004c0213800320317041c000404060800e9501c04200c0080c90701d072011224141c0002500e0940040108540c02461450000d010004810610302020742c1007250421800080030028011601c0d59001c2d02c942800d00c0041c1d1b4140c0300200108008038185100d4640505032054900c020352515145070f0368006a9000300b0349598000c1d54903070071108030449010056105404035a2800090307924000050040614801032507107200da41d01d140340e00fa5500100494014104403501c075050350301ca00d04070000c0c1c4000b0301d03003c030054103021440c010590048141c00240d0303440c070141c4102da034450081c0000c0320021600a00041c1d103400d01102610898500d003549014030 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 282317994 1250 282316744 282316757
    0x9020903030408190b180a020f130e07031406010803030a0c020a0f05011e05060d030e04150e090f0114060f0312030c04082803080901200309010c0e011d01 68
    0x545201c2410141004d020f2500380c00b5100c0321004100da00c1c10a150b1100760000d0b080e8811100c124000e83c0c400c00020700030f0040c240c07010041e50307a030390742600c64480d00040c080504c1a0b80d9019407064a58040e8441241c84103098211001c92150104405061f80c1d0458006e509540d101c003141800303094950351510550142c0c1c0101008540c444a202006a02520010442082c0c54019500e070514800200681920b07040500c021640c803000ca18138155014030b8444681c40700304000500401e03002c40a503000e8504000c0000c0c4400c1c028000d540310f40d080506540e40b0784001c5039070500340d50b4031a0000744507014900000d5942d1030080b04140e20340c28044c04940344506034140c000d5a591082e180b401a0304008141001100720410843c0d420080e1040544e0f0306030002811040819500e1000070203001c041000140038600940c007108848006161550104800f0002414158400e403502140365081038040d00c5031601804540040d960107940318a0103540c80078411030340a548291381410881d5 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 282319244 1250 282317994 282317999
    0x3031207090803040b0c0c15090d0201170108011d0a0c030209181509010614030303010504090f0f0809012d03110d0504050d0912030e0d060209040e0d0f1404090209030304 75
    0x101040603101810174504444d0740c40038140071091409188140c000c0c400c0c41c6503152201c0c4030128009170340302031000b5508418020181d10040c0e448007244402c0612a6521b84d0000419400c1500f00c132100285801e6401000440500d0480c0c8400c8200000b41c44550038000030001820503444040c3e01c10f00b00ca156034022884418864104055441911100c0f0510b40c203102101c1c0003031142800400c071075406100060003040200b0340324081441441d1080382e0f6249010705012900e00c81c0031a0030717440594050307048107030f241030b40303c0f500140c00c1c150008000c1846808403454010a00d0440c1c0c3c3c1600b46004e04c2528040d045000d04a82040c40c62102800d0058031010b000307502849000d140f00340050908a48000c2c0024944481a8444d070703001d1644444101c0480e420003e4001ea20b2410340d045c810560311801c00034040d00c034080c0c220f908a0300e840b00500b044440800c1e40581ca1401d540c9102c014a10b010b0100d481801000400300b89840400c810810000c06500034410308001400392403d040d03 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 282320494 1250 282319244 282319259
    0xf0203070207240e091503030301150e0406061b140a030816050f0703030b0a0e010303110f010507050d0b190816091b180308040902040311030c0303120709 68
    0x810640300c0d5405030340440014420048040c111803004400401c00002c540b008500c01421007441c5803110f409041d0020105619041342030150440c100d000c0c0c21a952540c0d03449840d0f4010321030500706000190b4046458000d40f4080c0201800c03a91a84d40d500c40450300c2c840314400007152203500b126a00083c0d20002d403442d43c10300000c40c006000351502082e038a48040d1241c03024002e1110901001010491800d02c4254003040c2c8251541501e000a00d95039090b022881c0d000d519045011402400300c000020164402d100b446112114002d4401d41d03181c01c8001826680e082d04c4c0c0d000030810511116182100326400341107d03030001000d580d0303400d010304208942d982154006505c59040004155030710b10807261004d0040858401c20800d49090301001c400320f14801414138204240080980420aa441401405143c108034119900c1390f07130f1004031000b580284401c86131426115001c1950f0300d00840c0c01d44080b84068065403070300c06090810640614028510b809004003d1b2000c0b4102 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 282321744 1250 282320494 282320497
    0x201081503190201080604060317210109050103060f0908030109180b1501020609060108030a080a0b120f010f02030c0f0309070305031c06080303060d0b070e1e010311040f060507060f02 81
    0x20b2180804002c10080700d800010701d903003002454640100e003440010400500c042c0200d0304880e400700d40305da803250f05c8a60f0314032882000056407614000703a0000401d0040c1d655000c0c504032885a40d040266015540442040e04e00700e44000d040e80302d042c801000b9840464000c0384401c0407007214120001400c0d43c1d0b5441552040d40e001901c10b84c8866140d41951b01003055980100880c0c00030009585080300c4199039120724400344003085580d401084080506411401c060800204a4004184141318056aaa00170554000c3c02d40c20708800f4807103480c0750b10881c3e004444000c001864059049401401755101820070542c0e846071035000804a40284040d250100c407400d284121608400b8030b40c010f0301c5150300007611580042081c001c540d40c0362032207503000c654032045510555030307210410307a00a1042e00b10a0340215111f005291070711341031a05100590401d80302040b00428140e80d0203080d000b103001d500d00c0e50341090402c2c0280c5008501800d4064403607000810001c110840e54411fa = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 282322994 1250 282321744 282321763
    0x20607031d0a1109010519030312020409090506060405070306050105160302160b1207170f152e020303070c060f0209040e0606010215060109060c0f061b02010c0215040201081503 78
    0x2c0e46051076090b203952070800340340c0d401004100e8040070580c4400c2404201f41e00d040c07000605102111180000c11819901594000c1c05910350030843c1590904089490718070031910180b04d540340070b000400c03244c041d214041c15600103039500c6050071800c2c08421500c6079a1001941903100741c2031201c0418000010300c1e406030014642954640c4242c005061034188040e1411041c003100380b1402c03540c0c840b0300c200c1c40e07404484146075001a850302c2c0b540e84080705c500303040c40c6d030001500030f6840d204184500542028402e494100c603841e10030100d080380c60313002c1030768000c001850460b181400b00301280c02c00c54580b050584d005182180f0040020200d402008c40202150006410030000b503030140f2004000b00702c3ca9044070840e03d0b001000070188440c90040205000c400146401800350304400f8044c220752050080105410300b0740400f607400c01c0120b00400540c20890752000c410b101248503107181285a501700103680f0b5580c019640400000d00d205c00d103140a0180e4a050ba4003004500395 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 282324244 1250 282322994 282323003
    0x15040602040e130c0f1202010815042405120c060d15170f0c090c0c0c040c050306031213031e0501060e06010e04090f03050702150316110a03020607031d0a 68
    0x2d6540926000c03411300595408050b6030580d0380400c00c2131880c068004102d0075424031385103080380e40790708001d401d40c80c02c40d02450b049850803402d001e01a0410300710342d0508107000642c5120719a1001001052640303e180b860654102200d4500e0342d0800754098166244809008a040c0c401883c0180c0388003070961040c00c40701540c0028420902d024015446103050481c05081520140408904d90f02c1002d0070801c0300560000e01081d50400a0000074195040100305002c0f0440780d400081440c1c04c140d6150380300c1d000315010a880501d00400b110000300005603881801851a103030b415084403400141300d4010000c20400e000500203120702c40c060550050441c15604268000502c142c0ca03a000c444e005500e48821900400c0b90151243d030055414980f03199940b1052011800d260000e4a00064882d800f00511010445a0382c00c18907500c0b107540c03030308203904001122aa44141c0518042c2c0560024004620042c0c460b0b0490200c1845009a0508440d060700c0340c60300c0c1101d03200042e107 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 282325494 1250 282324244 282324271
    0x609060103151a2205010906050405091c1d09131401020a0905090901091401020301050906011d040b0f030d030f0b06090a09020a0c0f05010c030e0f15040602040e 71
    0x1045103030301c0b03580c1240e506628100000445440c0c010201c1d407a002d001c40c4141156544001c2c0440030381404528503101542c18000d41d6034039403001c0041d2800d4007074284070718145400215110f03000034003e80d0860340e514081c01424100c000950380c80d0214a40c80100c141503803045070407034948241040c00b49003e810303440421000c0c0e050110b02541d0341400f84e8403907401000000340070340c1d20030380300401d44808503800a0b03d0703101c1c43e4000d401030103003801c02442d0610260096441078010b41c0a1812144251800881990f4510045030a01e683c13480ca500d60b880e0b03050380001c0e1420305600c20800514040c140c02c00310300442c00007900d400260803640c0006525a580c1c002640d6450082e140c4107201592a1400c000c2040c1c001906000d0380d00034003019039800b00b5a2048588500c04e400502608007840314040c2485080c02e901804800c10400d002ca8100362009500110000700101407030780d0b14000d4101d01d07000c118000304445019000340c46542d001d00000c100400c50b45010381c000e210b104000c9 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 282326744 1250 282325494 282325499
    0xf03080702010810080c01050f04090504050d1101060501121e0f0e07050d03090608090102040302060a09150903052805010606032304081206010c0f032c030709051806090601 76
    0x400300000101400001110150b041100605c0040c1481a008090808a4641c01400c43c0351055009950004400500f82814081840340114081484a03880d542d8901d007140d0030030b605800d95581e0300c81e2a0002e8183e5003030110300541d0f54000b00b40010f0440301d50802d068004a404107803454000b40200380d50741c400202111a00c200a2000141826904408020321a03280a014242c451003a60248602e5100081c1c3c0342000b0f50407100690746c010b02c0c160701d0b00c98040380103010b190240105190710101003042d511450003070100c64103e0f40d018008211714464002601203138411019200e482ca82020002000030340d00380120300180000f5500001c20f42d8801d45191500e03d081c0040981d10f240a6083c000070a22003421a01d010445514032074658417110012126031141850140900070004456010160720404052500b010082480384a05442c140f412030900c4051605515502070802000802915040b185e4040000c900c03010061110102c004d0400f9811603c2118503044807005 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 282327994 1250 282326744 282326747
    0x506040b0a1e21050f0406022206050d05060d1104112a12070308042003010c18050406050105041211120102042c04030c05030d061410020a030503040308100f0308070201 74
    0x140308075040303d00d06202a00305001c222250703940290000d0b000c0c130340010f01d9000015061708074440301048060110000390b585c040040403034024400750741c4038600b4000072840b5032038060542590076801141c0c0c0c2000701800020003005141022210f001c4240c140250016a103103ea105039001c0594252a9420720141f45035a0910185601c00c4019560a012000110703a124056652066005405640b030b2183d88100306070080480305090ba0544c2001c41d00e4000f558080c6d501502e105241a01180c01030700c0d0420001074803403a004550000e6001d00c0100f03d00c090b601071045d00c6034015002c2240e4400e20303801145812800340181e84407a900090b040226010100d50000d18000d5000441001c0c0000c416507440408068005020800000000c4051020a1007101c40d0030003510000c00c0f00c1540c03104001d02d84440300940340d00c01da018480b0408060b002049031403225030300da5665840c5659541e4190345005001c0d00200210b43c4160340440c085000e0713141d44000e140036291058031224180300 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 282329244 1250 282327994 282328037
    0x30204061d1303020c04020a1706060f0a0503130501060308070b0c070210110f0d03090308181c020309060a27030c090b010c020406060c020102070b03010506040b0a1e 73
    0x1c1500c03481400d5012010400d600403880d0090600c0303280c1c0e035102165060403482c00d0b20324420ba941c001c1c8000344074410350340c011406540c242c0c11300483c5100c0d940c1c1c0e07a04212850080841c0715040080070022640080d21860055500c07450215202c2c0c259034140c3c6481d0300310790322030f00112403c55000506c80c050001c47c900740380d03115135440d424034940710003075001c201a696020300c1c0c042402004560841a804107000e0050741100d854100c03042c518940b80001c0c00303000c5204007640880d590b4030104006480006500502c140c1c01c01c020251102d41000241044e8540009501140818001c80401d07581b450002c03c0001d11a941e0b80320f20b02143c07105040c030710805030081541703e40d8121040000400015145003112401900001d0380c0b910803005a074070031038108009502c0ba151240c08240d068000d240c10130841d0003a400c440300c1c00d4686100c82000e1000b0302620740d0006050108025692055000b40205003941c640000845850400302d001d80344604440c0000c250511a1094614055034 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 282330494 1250 282329244 282329249
    0xc11060906011e0303021902060d11030601140f03060f0105070804060216080c0f06030a0e010f090b1e0f0402060c0d020c01030c180e0a0603020a06020c0333100b040b0403020406 78
    0x28143d200f41441c6640103903a42d100c1e07002c10070340b28089002c9507081d903403008159484024141c0c428810485c440001c15410b6208030740300c6004c110400d80380803101d50050151455540700c284600d00c0d5403224010400ca49038001001c81c1007250800c20703000000c4045000c1c1004100e250010448089e8040824841c0740c8582c01500c0198080c040603c201e80e252101d003000c003c82a1460b5a0780c0c6c482d4040c40018004d07078a10040f1641c00d040b500c841400c2c0035481011094020002c040b06500d603da0240c1000320120303071460f0032000c10300110b00100600c10043c0e030010310040009280c914126240ea003070070f009440050140e0050269400740e940c26004143c80e141c01b910b050844011590450010381c042e500403000c00b0302c2680700041854800340d0101d8081c540040c40070074000e56440f0003c2d500c018900c1068000e014a050741c0a8040d8506424900f40900c108000c81c402240d5503000707010400201000e002840004c00003410f40080f0006101502c0b06261103a500c500b50300500041d65070ba40d = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 282331744 1250 282330494 282330539
    0xc080c10020312150303040f0806180a031b0b01091a0102072105030918100f1203030f0b041d0106080309060f0a030b1003060e090d0e040c1106090601 66
    0x1620203a404590120071101d000400e61010600e03512105080548080d1007040070ba00362000050100b400141000c1d1070080300c100d84101c521541c0c4050840a040c40c40c003900c509558402d40c00400024011041c0c140700c00d49000c41c03401481142e0f190015598001e9100365611a40c4d002c00745200300d502d40d00c50350100002e00060090a28140c070114403440030100e101010300403000d840e402c100c414821699007000c018201d90140c11002d041c00c0900340b0035100070a005213810000509400844000c40c02c4400003021280850080d072015400342085c40c1c00d5031840d680d5030514000599540c429408000064901002c074213008030702a03401c4441c02d41003001640d005002c60400c03507403088102c03415102e20002c00c03511030710071003010b50180c1003c803211a401383c0d0030410b00108030390562040b0700320b840307800300901c0d01c0e203c800c0400e485180342d400e80c1c00065410009543c00e81441d4101c602203560034509841c032000c3c2101c2c0c8074101001a110503140c0e4001500400200c55825129217615070003 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 282332994 1250 282331744 282331759
    0x10e01061a1c050f090f060906060d080405040608010e07090e0325021f0212091c0201140d0f06050105090102100b030f010f020a030b10020604060c092601050c040302210a0f0c080c 79
    0xd2341c5890b03650a005020911422200280c842080041401e0310b008080c050424451700d501c621145000e00000e100c0300c0d009109441e000900d0180341d014000300d08018901440c034002481c04031078444c44019900d41800f503014660180140c0703807803000515000058110901c42c1c1e24006000b030070200180300b48155443c00307208070003031a5249400780c0c600b20925181619640c903035100603038400c00e100d000c1c201c030404080740c94003054515070464000c660305075504101894481005540a00400030712a0040e84045041394568030a90f00c03091401c6001011207003044e182074555400d581d0f208442c601c80ca5004142c40f261250940101d02a40004940041d00c542d040c5074000e5a07410010006440c060311894201511030107942140041c2c032241c0c130b888402070000c00142e030041c20303c14004d80f16503280100040d8040399520584080d6503004054002502c8140003180201455070300350045400394480243c0011180c0001420340c600c00d02c981e42c6d05914041c082030800c0401c40392107001d00107 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 282334244 1250 282332994 282333001
    0x6030b011e0201050405010f090b0c07050a0b04200d1e0615060c1b0e0f06270609010906080a06020c070f1e0f050906270711010e01061a1c050f090f06 66
    0x188024112f0b40900d641c05200d0315503005080080c604000541c000d0550504c4105020031711180d0343c0c40d80120042c0700d0000b5101307860304d010712503507841c040009002040c4000c0740e800007010800080382014002c3c100400c05500d0750010300d0014840350b00c188042005602207004101500e584141e150801e145001ca10514002d11000e406034010102c8408403807100000302c0d00d90350304c0c040c110f81e0000e840304458181d02003448102c40700c105885003441445d401000003090754123802082c5c241c0361650302401000800d50707540c00181d0081e21805089015031000400e00340d020a0010b0700800050400c0b0030004160000076410000941046091451060f82032081e515000341003604404103850180e0058120031258101d0300c4421a42101c4445c408240928141d00c02034a4614090700d00082000d05e5810a1950807186140308131107402036801116080d41c190080580754000e524503510891f40608003c2c10112082291101c1c0382e0f2054030f0600c0450700d002c100018064030084000d044604 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 282335494 1250 282334244 282334253
    0x1e0812120a06140d0f0615030b1021020a2102010908010203100506091c080903010e06060d0209041403281803060203070e0402030a02070215070b0106030b011e0201050405010f09 78
    0x219492889000e100e0408984041014617010104606e80000007001409681c0c1d80074a402c07000c0b40f0040c3d8681c4403c1011408a00304402d410007158040244640500009664a5030b8251606010b81c0d02c0b5903000d00010f07525400040a101c02079444d030305814003a0251001602e88e52040d044482c0350707031041c000c1007205068001c4160a48404894440d125002500001c0e8007801c001f09403050043c0e000740801c2001054000b80c43e03141c40450080c011180003924095591a08440d4580d004081c15803400c09410199040c1d9003150103042a64902c0f252518000d01d581c0c0204145d4a101c200070340b20b041001c910106504441d840b80c80c054100710600b60046118034120701014184ca54001301180c1000e000b41c48540b41c130500a00190744a10340b0b0030b091402500b00d1201a4054034485201d4080070841a0880380311300c0d8001c0149c1e6650742802400c0300248461100d4030b0612008181108071602e40d10607081404100d40d00118091900d803610300e081da2412404040000d0070580840f0004 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 282336744 1250 282335494 282335519
    0x30309070618051201050a0e0309010219030e0901030b04030306060e01050307032406081005010f0210050901090b13060609060b0f211602071d011e0812120a06 70
    0x40e400d0749840354403040c42e0341c240c5441d1641c581c0305940c0b0041c0003411140b0040190000e82c440c0941c00f60810044546035610364036440342c40d1000c0c0c01030f0400d03240e4003140581030380e140d441a4080d142201900f8110004200455020b8106940d008154010082090f900d80074510203042c1503d0300c031035480c560310000381443c080a054042416160a0318180ea01100c000c246010224003000d07211250340d65101500708001601c555500300304152010030603501490300740c040c05e2041d50041031f4800701600390200418011b01291415504c1d9884036001c510070740c0038140140043d0070b0280035400c803880d2a1085800c02e9009102581c01e00300c0401a1015010a4420b60002e003025959603407101403242c1d1512411020b195042401c07202482850300200342030803540c0300240c003140c4282d80c4035440d00c030816050740c02e45841221103200500006101403481c2c19004401081017814075181d100f0305041404c105920102c0080101e001d02c10b00005003103254208400d020704000301e904002128950 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 282337994 1250 282336744 282336749
    0x703030c0b06150d020a023c15010b0307083601060f08010615020a021f02011409030307091406030403031e020a0306050a0509240301020d02040e090f03030907 70
    0x2940c4080011072540310000c06041c0da05500580d180e603070328184e0703408009410500b5070748010300c201104500c402800300381810502102039007a92010603046224a14012520b001c0140390207031340401d00c0082000e41d80c00c2e010b0300045e00c50076182e00e4003640c001c0c07a589004080c7c05d0a050a4070b4a003224010504c0d81c0c1c2e05100c02a401410000c10302605280504000e6102e121005024100080d10381c030194414070560354206070a150440109104a81c0c805880d54065440b0086910f540c10030050f0240c13582020016000104120354040c495808007101158641420342000040004031a40038850102500e048001c100450b680740c03006c03c0aa000091005041c55a60002d001d0380107516109505280c64400040d035a40c15250401400341042e4400e20b80a625000004034044c030b055207486208d18115102c2c504100240100e0000118402d031250340c15540c200034030082801c00703000130405409020721500440c18003095a52070f25030b5000d03402c4040d070010300c14850401e1022601204 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 282339244 1250 282337994 282338003
    0x110303030f01030605311b0803040b0a090b07030309061d060406020a0c08030403120501060c08180103180f0203060a0e030406030b19060e0a060e010c02150f0a0804140703030c 77
    0x500f40c0e01e10f01110fa140c1035242e017000302d840c90303001444910603560788104001c0d8401e03090589503187d1900542050f10f89405a03d0f0650400d0005124080e480e0010389461552464000d912658ad486c0f19092540300710000c1d4006038a8094800070700c260380c01008110740d04611051880820a15200d80b1264054401001e05800007802c6e111248103203200d40b419900001c5455403424203281c0981f00c8010b0451a10425050200028041d802103d0300340340785030450f00c3c41c1d252080340705203000720341140c104440c14540c0d54440030044003a1b2908000e00749119580745240712074280105490312100620030100e2904003490a07000c10030200950382100c2e160304003c81ca4255003800034190310703015050101142d50a980004003960300082c5180f000724169444210140c031008111160b21110a1040c0480c052040c2c000042c10034084100240d5008034800c1d04101002510000d10b60110100d040040c4500341800306002c40202000d018040c14002030500c1c42c40c540d0f004c1c0001580400152 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 282340494 1250 282339244 282339251
    0xa050d091a0c1609050a3b07081c0207080c01140a111b040b03061519030f06061d010503030a2001090302030901090b0903101802131a04090507050f150313110303030f010306 76
    0xc035034600400003400580151001d6948007801403000d21248481d0781d0002b0300601c039440f00010343c0880850400c81da0030040c0d40f151100c01e400c680c8188258020340c3c04500f00504610210340b155400e00c8040f161044121800d070004500100300815194040e03951403081d003000c810702842d403052090800a110060342c1070b1b120040901c1c0c41081c28090307613102412000d00725180104012240e0301000946203005001035540e035005001044624003401902e0300f40e80104614000c45001d651751091840c00407040d40421920144036900f0342d42031150440c0540d1003c01c0325021982c0200c2000042c0c0800c0d0911402d003444240000c1d501c16541e104d58065a80d61208240d042d003070320240190044d000780c1104241200e03140f4101c018244041c1020482041d40c11014483c9401d003d507407100f40d0060010054281800f04115180f0050307100154024030080406101040c0000518465a030700f00a04c0142c42240c14030462104003801110310a0b0020010401e603183d01d80115410360741c2158000 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 282341744 1250 282340494 282340601
    0x30a2102161401020f0a1a090a02010c1509050f0102210c0d05040309051207080d140d0e07120b0604180b0f060a080109050a050d091a0c1609050a 64
    0x181d04042117000c202aa9018054088061001041401341060400fa01a2900359111101292030f19082040240010001d150a00105000c10003440107101c05880000c0c2080142d62018506034820020f030902e80d40104040c46030035412007a007003518021961030403007460321491440c075600c540d19003021000c3d030710300103c0c0c14548544486006410003406960001860060250781c1d25820b1103409154460000200341151040314071601e00ea070188181814140e20f40b04103c042c06017040416550b01c0340c484005205c4000311140210315010700c51b2046282890010320046d600400f1820a0f1081a41450300000e40c40300d130a01d43c4100c0b03010388410603459040000324580c6080d40710008c2582484003000a01001041d01e800b094428812284468900e0380c098071440750a1084004103130301c11148200030b0843e10002e280c420740140c140c3e120310324542d40b9000004201c2e0000c000880e40c0300708001903151240706a801c14541c1d0f96660380d03009440050b0108186041d00c0801c80b880640d002d0 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 282342994 1250 282341744 282341747
    0x50c03130303062105010c031512060e0d050c01060e060a0621060f090501050f0307060c030c020a031a06090c0d0b04020403080d050415060311040b0f030a2102161401 73
    0x340f4060b14156403900340c0c1c0f0b41c40f820070761301c5030448141c161015460300250f807440c28028031076186482240c0b28624100d614003043c9503142140040305071038013903d40440740c841c4802485031103c52a0b0944801d40c03104411180c1c10308503440e40d004001c00315800c1061190f2a9070303000c40b1104035041d40c600b02840441411442c0c0741200c4503a901d041840c1428004141c045040c404141600c0b00d640041089a984030200814840c04000c03968060700440e0f41445854480c200c0192064002d0620100c20416903020480d00c060340e900035078250442c0d800c80c400403078201030410f400c0001107580200314144103040c0300e480d101d050204910280e0741c0b1540002600e85030156002075401080c96510340c0356140c07015019000454003164082440001801541004d105010030740f070f041007040f04aa000c1d03106100003070290269a65000c68036000700304681d5020003070b40114501c2030036032800b04d480e4004040c00c0408144503810a41d049201002c440301d03c2c40d8482e100310f5108405410340208030000 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 282344244 1250 282342994 282343001
    0x317090111070e16050f0702100212120109050a020c1c020f0111090103050610050f03041403070302011b0c050606060729250c140f0708010506090604050c03130303 72
    0x441c1d40d080c0c055024006008800a07820900c00c0100c142503000c1d985072060215800d2003010079000940c002400004054100450100000c001900449520031001862140740d07421903003482e031800080320018042c00c490760081c1c0d170300189005010350408000101d49900d40e00c041103101c0031200400500d8010710300c2040900a60101ca1000b0004001c5034000c0e103540c2d510600707185000c242004040382450505480012821280755542e81c18507010560004544e48050401e0398801c501c1001c0b91003a0000780002c040d0b191107a000000c1201a0b104440b507510840c40c000c01c00c1c0043c80d0f82c2900031403c081041070380903104540003541e4954900d094125a08100701c82c1605a8406044070f24400034040c0c0203025100c2c1c0c11380044005076a1b01c10035440005840da58000642a0001c84001188021b14540760781c680c40580b00f5102e0300c00c0c0e115141289a50040400d607441e08103000040c248183c0154200b00e05840c14802d0b0b24060005550612020300a04c07800140c114580083c036100f1350 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 282345494 1250 282344244 282344267
    0x18010f17040c15030e07060903051e030706020c010905010b0418080904150303111603110d05071809110306011505030a0b090708160216140301060f090905061003170901 74
    0x4202c0400c3e030740744980040082a00107018179207441040b5010488502072400801280d41c8000281010140103103020300c0c4480c42c27203825a1905c01070219000060031400600340358075400000042c2c0400740d0600302c0c255100f590030103004500e000414488400d03030615044006030044286a036402e680000316004013180e29410a1204540c8404810181d0281d0203400540600c0125090003d101d21480301015044c4030007005125050039111143c18090900e09402e13020302c0680740340580e01c03104564210200003607040d9060741c520480ac06c00c81145c40308a94110294028140b560500341003540707280d18042600c091140200004202c0040f60b00030204940300a0042d0165042c40304015022007030a13259610f60074440343c414100d662001821034813405064144080551038130595502e0f0132003400e0400d415540325000840c621f507100d2040030003040509400904850780f0700b002030610704090025000000c10107030810100d004074044280d040784102407666502d255000580300b040c80704 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 282346744 1250 282345494 282345509
    0x603281401060e18030306010309020f1206090d140a0c1401090302010b1206060a03150603170a0e030303070914180702150a0c08040609050f100218010f17040c 70
    0x500100c0680c0304103400c03080031100d05150070304460b02c401106420030714250a40c42400da0041c03002401a42c401e81141031400d0000d0a8011a1481c16020565001c501840d0992a5100784148445c0042c00c00c80840d04440c0c031b10b44050044551240c004880c420b000c2240100005c0400b0b86003882005505c54a0302c04550000300188810b515001c1c0c0a0480f07801c4d454402d508440442c2400c00700802e00c0e43c4030b6a40280002c55050841e0b80d04480680900707814101c4560351080031000440021118000e500600c00741d40e212000641700802d05849000898001d402c00d0051103c0980c002d40c1101c240c0c0c02c1702c0c0003030178007580940c04a1340c0c0390400d032100000c1d015a0014002103540200707042240c1046030010340340c196510b030f0300c42c0c05540e404048403000408100000303000c141c180d4015004c661190302618211900a103030140f502a40304a0740310941d900041d0b400c5c14561480100c00c2c00f00003030038000d980c40c9049102034201c0c40440d100390180340050000504202e4500d1000c030142a59 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 282347994 1250 282346744 282346763
    0x3030a02032d04020f0103050408090409081b0c030601050d0308130f020d11090c04060c0b04110405040b070305070201050601050711120313080f010207080f07110a0617060108060328 80
    0x50020b0802180107a070183d0161003070203180511948030707001e0705104030f400082661034002c1c00740030301000340b90003d0162101d107401d218030808128818040d0890f01e0440340180070800005040500b04081a440306200f1300600c645000003039001102581e010288503c08070144c00d2909101c0c403d91003000c070081d4040c54681940040142c00b0160f00c9602c4016034004c81aa5a5152600c10360722441c01804042070b40fa60080d00050000307000b195100e4441d60512030b6400580d40407400703071141aa01281c8a00c08502005243c84c1e0500c05c003640800148003c0c0014142000007078198440c002025000604111b201d0070503848503080e190410038240d00703c0340d55a41e48130000e004458603000b0241d080c040d2104010182d03205000781ca20301c1d42c00421803403502c06c100410040d194000c0da01201c20168040c808186503540c9c240710f5008044980342d0041e01d190007040d00030000b100400043c1070207031140c01c0c09029100059003440095810701101c00d990740c5114445941c01c0301000c028030010b807 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 282349244 1250 282347994 282348061
    0x2121501170105070923041d010b031c140c0a0b070206060411031b090a09020a02060a18050c0909030c01060b04170a08030f0c0909071107150203030a0203 68
    0xc1c15a0010810004480204075989455508450f410040c1c4584500c58417a010a0150240200301c45e80480c6c1e030040001a014003484a40c20f88603085179800501030b55911b42400c01400c0c140019044110641801d51040000c07032000f400360410202c0260b085c110108882c10b8010080000d082c0d075036000400c400c41072802c0f1600a5442c3c6007145c4090060f1f003002c20392a2030800c10000d4034054080074450044038407184448500a8010040c000c0c0d200c0018480054014018401440e10f0f040c01e0380504818544444140c040c2c510260942e000300d440c00580002281e070105098040403c1110760048503100c04032028554054800c0d9079040c6d518240001540254042c02841101d9441003d800341144002d10300c0c1d21021000d8001c0d104036010000503500c3d00b150202103500205414001b8100003103100401d02c000011142d2101103600da001150852100300034003030050000c000035001111041b41d00035101c0c0000f03441640e0749a004404100c003454034a1181003a4003200c41d50290b03400 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 282350494 1250 282349244 282349259
    0x1c091d0106050a0c230f030a1704050304030c150923210d0c14010b0a0603090602191d040203060d020f030a05031c1a010906080702010605060c0a0204110306030a02121501 75
    0xa0405140aa64451b14900d425807040200c1640c0462840e0740701d00d1b1070724a0319000c22001960080c411a0640000c010203c005100c0c802c0c80d00181c07803640036407084d6904061019100f04400c0d00010600d01c2c46201094160340ca48100c0c503410742c03040d20190446607804000702940402c00c08441100d020b10490886107a91001400c903180e801800552440a042d0502c58221820741d00d1164020300009000d0242e940a6005541140c0c4502c10044c5405098040c0014041000c5100c0c0c3c0002c4900824903180020312443e80829007081320214650304001c0d0000d0350340440060001e01030302c01c0c081c00c0201582d05110845080d80c11000307603551000c00003000c1c088105800c005840d034a10b04191401a1100c2c1650725030030480684400115504021054805540007400a0115900e503000440c498071018050014041d170310004110061051040000303803a80c0c0010703809014018403c0000d599030005034416826010b481d00b5800705071000c0c1c41c40c1440c100c03032417841c00ca040007000000c4a4 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 282351744 1250 282350494 282350543
    0x8060d060531151e0501140418021513091b1709070501030f1506030519060b03010e191e06090203040809121203070c02010806030a1a060f031c091d0106050a0c 70
    0x4040071542003082d11081101c9e181c007201c034071102940145c0c010841024000e0101d006080042c402c410500405564440b090140d807181081000e158026104449805400c00950452403080109080e818036124095607a0707070400744506410142c5030713404480008142c2c0e001c0003104c4460b100c01d040c0303d41c0b01d01d8050050541034592585004000050b01200f0005110741803d0b182c00c0e032112403a61746440c034203007070421010300610319841b22114420a01005842380c5a1089000c41749140303201780e50713544c103000ca82040e8040c04d41d081c0100f0030070000a00b4082250b801c503a00302d5008001409400c002c5140051358411f400c2032990003c01d2243d030079000244032001da40300b42c0c0d5000c1d07280d81e40c200b49500c9012a0800806c80b0307002101d030540c03902c180200958002c0d405803019822400c07041c00a403502d40488480f6522040b02441070601d40c0d805030740c00b800b42441009a00110102c00d254907440441449402c040060118902100130b1003907183e402042d4100802c4489c3c825006005a6074 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 282352994 1250 282351744 282351779
    0x90405010b0a0806040507030206090f180f071103040515090603240a030f02010f031506030204140d080406080603030702040f1e0e070608060d060531151e0501 70
    0x582460310b000a06090028010341703d02e170f0002c047c002d1103245509014842d0030010001e0781c89500307040b842ca41a150110300320701141c0c0d18100c20781281444040741c50083c0020b0f003a1020800064040007041340d00000325000c88070f0640c0d00c2d0480d071030114100e003a5070181c480c082e40d0020000060101000f258040000b908904012014805c40000c1c00c001c440311003840001d11b41c0307d08040e03510166002c0e440201c0456882d05000c2209224080345e030340b00076030700c3d048080802d902040038007900950f1403040d0000501501e07840c0426055846106082c0136512908042043c580c0c00909140c80500c25030342d0031a030140013804142c6500003100098061440c03507807400c90301c100700c0c0215403030310340191000709000102410710f030380c101a02290800c500800554000d40250308a40000d840361092074840c20706d40310001622504602400d030003400c01c8400188101c400b5100c90086600307103110900303d80c03070203034009980c030132081c0b0f06081c1030007032007080420500d0200009004445a0052902c = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 282354244 1250 282352994 282352999
    0xf0307050c0105090114031503061806010e060f1516060c11010504030504140d05100203071409090a0c02011805011505060414040509030c0708150a0507020d120b090405010b 76
    0x380c14407000c0044520380500e200880c00102c0d14074000710b12440d003000841d00720015510386400250300340701103032600c0130649946072502000004d0140d01d47c410701c12035000d0401c0910554803030410304d0004065803241c0f910fa070f11801d0f441164440b480d03140400c07541200c200d0510318107031003007a08100000700055a840703004580c0351a05412003038010b1041c548115455201c00341890f0401d0540440314011002050700314030705140c914081001080002040e902c043c8016a80345007034880202890300c1ca48401c94244000d02c5194043d90342c140030b40d81d1000410780c0000300d41010340d17402c03070141a0008401c0440041568180103200041d0040302d26a038260007039920407a542c0081c4040380c0300d2407289903103001414110350340d14906508050b8009016108407418202980340250a1106543c01104103912400300704180c120b16080d8070358001c8101c00304009a20301054003940360601524500d0130002603841d48051050564851001d500c400380845009103080e180990013485150f54691 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 282355494 1250 282354244 282354253
    0x7050a080a030e01140a0e010f0203040605100b070b0a0b01140304060c1d060712030b06040e06031203040b0a0908130b0408120702010507030c020a0b0c011410141507050f030705 78
    0x300c2ca01014050903117061442d21402d0040d90350240b010006001d20240c1410654071003540c055004505c2c0040d41c05075015420015042c01c022100030081801c036801034911200911400000c07852510965900164040011500c41c44581c0100c94800c1041c44014109101109001c20300c0307840d9102a006031590b403034500110340710030700c40030040d40310740700281e406082004040c000070f4201d405034807025440c2c2404603900d01d0500000d03040743c000b070b001003140c01900401c101140c0740800003030000140131580701c1c0c07840c10141c03903914542c04c005207552071081c0c0394800300041085600031204485140442c02c520b05480f0700116045a001303108454491150101001c1d0040810040700d0590f58140c445514000c1c2c65607042d41d01c034240807030590303100c0c0d0041400164000480e0052581800d07410000a0743c00205540d2100014043e00f00c11604c10740f2074082c0401c0d6509418207426000c1220701c0b101e0031139050601841d038852010020b10358026541d2201003103100101074403555110b81c0a98 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 282356744 1250 282355494 282355511
    0xa030609020a050f061b011b022404080405060702030a1e0615062708030d020406020d0801080606010302160213060330080601031b020303010f0806011404020a0507050a080a03 77
    0x2080b4103804c0c1100350b52000003007108440c0f85440004c910030288500c400452006c3c04852030501d400100c0080c0000360b0004100c65015090444da120084000210480d98900702600c07580405e02440c00390b2400751800090400c00d555080244085403944200f401c0150380242c0d0030702d0ba601203598030440c0c80e9420003c81c0c80d0700342c0b00003090b4001e442071070b17545240030b40b4040e020b92003020006481d0000302da003007031020070151000c0c002041c82440c042c0f070240c1c0d11441e21038000d16040824600c0c0d010803500000501c403d010108405800075000d01e00940c9071072846094560a00704035000030351220307812800703071030301100d50300075000302c038010702004000140d60186802c00030544403111401045244490401c0341c0101c861b1600240180740001e08001c151300d200145910300d182040140c1d101000401444920103200809040742a0146c0000e51402c0b542014080c110800c26200700c0d0080303282d04001c1e10035801c0d1140d42d41c008044408180302414403200c0d03a80001180c0300006c0c00d18210 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 282357994 1250 282356744 282356749
    0xc060f11090a0b030f04080306120a0c1401030515040f020d05100f060507080a031116050c1002070807120809091008010507030e0a02010807030f240603060e010e0606090a030609020a05 81
    0x1502d11031142c50240c2c0141c0d640307942d144003031340d4002007809c0c3d8007030308500d4204009a810800210105e10030300b001c20f0441e00307100b007a030510002246004d0406042404101d88088a41e8031b40c1c10a00059a0200d120500b124a03800a4080d480401c1c284c945844108030109644184e4203003156040d041c1c100800341c03202c5080f40d00d441550b101030180b41007004076911b421b01c2a404012040c20b161211411700448016583d03e070711400c20243d8642c1c0c071000d01c1e0040340ca001ca404003808140d5000030001c0d00d10b8588103c0e11105580700c1e540e00c0c04d08450310030702801a079000321503010034000d0910f88180791406c24a011142e03070f40110100d5601c5d09000800e180c0c02881a004c8003a807801c000c008100c03175035004451907c40200f00204050721b4960400444040780540390110381548115104407044800707c1c8034151196000800b010f041107410800c04440311070a070705680305640c04100c2580e41001094191250408417500640300319800024000710350720140c1c02920850b880408660b96104 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 282359244 1250 282357994 282357997
    0x5090307031b0317040311010e030313060b060f070506010e01061704020621070903031701060813080702130b041a0303031303020a020d03020c030f060f0105010c060f11090a0b 77
    0x50003000300b468000140c14002c04208101000b500c2072a0052560050705480e000305842680e0031400300b04c1500b80d551900700c080c01104800ba5020000f0b50031480c20341301030050002001c4020300010b5072541a0a0940c403510304503000c66110b5610141d9464803441d146560360ba0910401c4e201003840710011485a03c2804103400c112614400307003d040d00d42ea0200107055200201332704402d0310002c01041c0742228a0000d921961040e00c1c1e02000514504000e4144118640580d40d02900403005205032508120320a410100c01041201e0703250251030001c074948641d04000e58081890108a520219641c000c8086094190307010300c60506d444801840b1204886101f81c1d00d5001030001400e080300840c80510041d0003841116104880c07a000b00b441d00c0b001d010180c2c01608000c10803d503a040400c00300840007100342c0180210314007880e03401a42c1c401070040300c0c1040f5200e03035110140039440d0032020841a02c00e80c200041a010fa0f851b089551001c00c1650155a00f804002900e044040 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 282360494 1250 282359244 282359257
    0x14040f0302041e050903180306060d060509120c0c0a05041e1e090c08250303051b060f01050411040602100b060f0f1314100c030201062304050903 64
    0x21420881505507402c10000e001c00e012280e0803040204500d078400d404a01503240070340d440801a598071a42c80303541410300801001141e009038404020312500c0c0d01d41c0c0b068040102c2d00100002190f40301c4144150a00803407025110b10300b0001310765949640004200200c100c4412210113074942c0d030f14424401620002ca2941c40c0c03040106420710240c0c045a0400c4c00e012403003003050300401c640301105104440f2400c20640d4004002c0000307101d00310b010040721803407104080e040b520010520468001c0e0403100c0c007005003084000300e0b102040d50241004070340a41c5510702a5806460540d0081c511824244601c511480c01d01062414404620040701c081d150154050035102c450101010040e00905000f19000f200801c5180401e841d000d000e04600084c594009645800260840c055100c0581080d6607401301d02c00303101c0c0315980d085007680710742100d4108080020003a040c245d0041541c0d521003040460b494501402d542c100300d0410050480c202c5081280d03445c0c1049182e964020403 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 282361744 1250 282360494 282360509
    0x227041523120706020102070c050607021507110604060305070917030a08090f060705030406061d13030201090b0108030703090906061b21050c1005062803120206071404 74
    0x244070082464401c1c11641185030007800403000311055001c05860000c0341d41c82180107035804a0705c0740800c01c3c0c1c025840700804049030800d040405640019041c0c0402c0365041e0301c043e40000f09202003110043c200000c405008211a8599640c0c00700030317010300421220840003c0c000c40c0c004c00c41240d02402c0c1c80070110080021820210400826280450013510500c2d0324458280c103100d010100304001c0d40300e82c1c419030350703280c03a4245071805030700303448080d040154800820460301d0f2003655031040250740a121402010b028901c1411305030300403d014103014200e05040c40002c02e0400000004000c90341c0300c4d5503244440b0385e440201e00215001801008001214110a280420a013a00848455000d00710301d105c3c0c1e00d0b085030000c1d1003800036044070010034030100d01050316260034484000080d04500f030a001d41d1618500244002d07200101d44610b02c1e41d04120305080c0c1c25507207101800f4580c010074000d0514800100655114011151600003a00042c510310420b0f00940036901141d849 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 282362994 1250 282361744 282361769
    0x2709060c0301120c08010204080d080703090b060603040809030a0b090d08040507060804170d1a03010c020c060f040f0b09030715080708070e060307030917070f08030402030102270415 80
    0xc00c004103c5209500d042038800c0d551000340810f59000c00c0c4001c1000b4080781e4014840e95100c00c41c00b40c60707003400910b4402032600d0100764002007018002000c4c1d10140445c0e40c556203654528040456006101c0c9480d014840ea00c524000c2051104445005940b0002180c1d403410042c04203c51060088130001e0881d0801e1104101040c040c86080b50414818070f03240d18519058039071000365801a42c00071400e580c56a007080d042c500f0a400c0e04041c107800390000c1c040c1b1402040040e50795440c0d908202d00620000825142c9025030b6020384003d0f11900f002c50f8a21695842010110b811050320030b840f900a80c8800034001103494040024030280e51034004807a51400340c00d0f6100480107244e0b9060007101030b02e00b20595507050081d0f00c0b840103a2800200c0c01e03081c0c14607140e1428181858443c10100300601d00121382c2c41f847d504562603100003882d540c0e0355188046406801080f961000e004c50426202c81d080d60550505800308000303071000c00c1207500c03d401780a040d8100c0d12407034419904 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 282364244 1250 282362994 282362999
    0x240f050a03080d0c140a0905012d120609020705010b0f0a0501090308301008030c0322030206120109050702031e0c12030a060303030e0c03150403020c2709060c0301 72
    0x241e40e004012040c0b4541482e0040c080302c0814075179103071310101e0000c0c0015443d42c400e100c550307044040055000380213030521500a4003d103444000d8000d80340700ca07040c040441e0702199880c2c1c0036004600509194101551608480d15209020b030040132540e9200d40c800c80000703281400c4c006802e4044520594420301c40c0791954450070031540c052040341c0c815104924400c0e01910140c05880c1c9500070401c0f6100b200d2410811036584411990403241c055001040100b90b0380302c0000c1a038106d06c5c20300c15203001040010044041040305540029006480440c12011084211703403914101c5480f400f040c030803541c03007000890b00c9100b2120500d0290403c44c00202154034110064109158910201e4103030030340310a415000c9400c1146c000400c030340c450405208040e41401a40d14401500e0001e0042d10110000251100000d0103401108800c0700d0002c2c041c0f6100700003aa04e0504041d098a44000b01400b800341400d43e0850400b00643c0d2000c0480c4402000003560b51017080750b4440503003582d0 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 282365494 1250 282364244 282364267
    0x402120c030a06050a0b0c06100e0613090b0702010e07060c0305030c0d090609200415050d05030d0507050d05280c050c010e010624090603020d240f050a0308 69
    0x41002d400c44010b59a50b41001c1a19180c0500120103440840c0c03441d034031143c141848915007400288500d800f012220000c01607100e408001e036130005030845404051000d0718a400c0014070039100c014014241000c140304442d074041d840b40c07240a100c001a9000107403902d6095071942c1a07401d006000510400000d0b400018030300c040c010081c9206130200b6000e409848800643c1c101c41011307656100c844039080e03124039100169901e13080080c0c405104404240b901c0e6154000e981c03043d0f50042c1000042c1d102045001c4c0115901c80314030f02d034204240d00f0244001003d0b60001c20140301064907100102d060a1440d070341d0750804603400d4002d00a0070b503490304120090010796256006121040c00b850220300070a008003010309845000002e0020301e040baa8018004280b81c0340070b02d01514580c0803a9403544043d401040d0b40480c103015a40348504a05400201101d0041d0203407107803041c92800406a0001e5820304a444001b200c0130300e2a2a40304001d420281440000c140d100300704540e24515 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 282366744 1250 282365494 282365497
    0x15020709050a141f080c0f040e030c07080a06050a0e210d0c1d0d0218100b03010b0703080114060d180602070804060801060e060a0309050c27060402120c 67
    0xa41803500410318004042c022410390703e00f99000c0d03500d0100300d0064240410700320b084600070014500200710322807a030700100381c0ca0540350030524021070b00e44495940095041048804d04040c400071a580d02d55110003090b280c140401d001c4440a080801040c60380c80240035451020601c1d4000e444001c040000041450403a9a8401e60f203600500c064860600b1510880b80d90581e19228205c06002c00c82e01e0440603131004d1040383c031404080b19071001603140c1c036540503800e103445100c1c80c800d500e03111404d0190603026400100c528100000100340341091902500b54a44662603018035a601c2c1e88003500d03d019054011600500c09000140c8628929007100c1d4010052459080203202c0f00d4a8040c20ba80c0404001d9030b00a4001070304201065000d04d04a004000c1458034103000100b840006190b8442d032000e5070704041d1211071680034002d083c809240005002460411601800c0c178840c0100100c90501d420600c0c40400050a1410180200c403030101d903044008100341c0d9180180c4c0c10030b = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 282367994 1250 282366744 282366751
    0x4050a06050702030a0b0a020d060f080705090408040e07263904140901080d12050c090907030608070501020307081b1908030417091003110d02070f0201091502070905 73
    0x1881450030314004a01c2d0040080d010b100d00703c47c05a95004040030180075a440e80c1d10003030210314004010440100e0102e50751064840032030383c0744900d88036400c0140c2e4501443d08150035084e40c0c40309012219410411081845018220019440d40301c5907040c01d81560854a040a4040803040d00c1d800880502820060f0401110030003208250612070013280e400c1a0440d000c3c1c40450310901c107191070104030180c0140800002440c0c02c15070000020700d00047c248081d43ea10f904c48011510444040040c0d0b117130307d000680300031700d1407910f990001d02070704003071040600e203006000b4085580e510100c00c9560f0030b60805802850101200050040000c041a000e000c5000b1b904254004031400d05542d060540100d02c02c84c0c4038109400d1500740031689082c09000e1210400407074a05854620740c0d000c1c403800c24100003070b240780c12418040c000d2281c0801500759501c002864410030520b9242c00450a000780c3c0d034580ea090300e0394051f401016102c0741310070140c2e1014004114400054110591 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 282369244 1250 282367994 282367999
    0x303030c0306030506011418010b0a0f0e040218040e0f0a11120a081201060f0c06110f120117010903020616021002040312030b0102030406051e07051515040204050a06050702 76
    0x1201543c1e40ca0b103030704200d02a00700c0c019030400300750039607540e10b402c100308400b00c2a0402c1803001c42d4035103403030000c00780300705500340090104045000e81c045020356400600260b015100b550354060300d00c4000c0d001c0c0e030340d0b00c9000c1c420752034040c055a0203500091440340078030f0414000c0c540d04480307072210260400540d280c5603008101c6080d44002c100d081c05603030240c81c4592582078036042d06205003960090160020130401c40c0300ba134161a0b0343d5002e0760741c605c45a04058005000112240c01082c18801d00c040d0b03905c10307400050b600a800000da85a10b040310304a10000c5058006103065a083ea15210005030050f44140003107101c02c4a07a000c1d1020400c2503004071101c803a09140c051042e6000b0b5801583c2d80400d2440c070f46191034140c0921544060301740301545c0b80c981407000c0034201d801442e045001c100140801c80c03005400d0343c0c0c01c40300400c2e0040d048450003110642c0d45400401c1c104c98007081c010812a000d0241d09190082d1401c6d510000c00c561005402e2039411260b54002c2c240c05c0c0e0317 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 282370494 1250 282369244 282369251
    0x13050d05160e04052a04020a120501060507110303040e01150504081204080f0d140903070504090807031409030303010501030b030a0b0a0605010e03070806010b03250305041104090c0303030c03 84
    0x4805410350381d110000c02c2c24420b0303601c942c549070525a04210703403007568024003000c4408445203080408210700e0002d10842c0c0068a032041c616044450040900d05072044614020012800603003282c040c010785842002921030340c2001c88149a141d00440c0b154140042141c0c00602091524071088180c040076840c100e8103165590940c20314002c6058410300450000003018098007400340300910840343c1aa0040c4404090003500520b09082c48844401d02d07200400c044900781d806010400081000034400d014004d0305040500c5d03075920040e402c0b004161000c1c0e2024110f0902c3c001d8400c03556000700a0350940c0c0c42c200065002d0442c5a40c1103070301d4003400c201070300020301440745540503003411000004c256080100141c1004030401c00903100c2c6c0d100c2041044101d4002039040d0558001c14460b540700d0f1640921007107106504110092044c1c0e40c4050713680683c0c0d056100620560103444669000305080c001e20044880c038180c00382c01f40036221414000300b400794100c810005a1031a001 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 282371744 1250 282370494 282370513
    0x2010f0e250e0711031213060c08070c08130305030c10050106020a050c040f0f02160201020f0a020603180703050703150605060406020307170418050610050307170613022b0213050d05 80
    0x1700c034010466600502030f0700740007d4814042c80d4451310250a0351070412000c0303070909a0000d40480c6030410002c2216a0020360710f24840f0079805520025079115040340c0e22003e41d87c00480e11500f500240c00304091801000080c402c0c800156003881d035070040050641c000d8060184006491090b04143c1c40c591a010400808001c2d40300401401030880c06656451986100083c2082c1e100382d06d001c01580800101c4000d665003004032a0488810805540041e81c1c070a0f0290411035158030240080c01100c60003c10300c02c0c2003001e540c0300d0031004010042262181c0400070385002d540558401070f4001d201140006a00c1a941c2c242120200c442c5814107030b440c60f0541c00180000140111a41c95100f48034050419250341c84050074035080460442c03402c40c00080c2490801548401a0018600807603855150341003420981e441000041d540c408411154502162085004001180005441c111180b41c0392095034081a2005400200e4501c0c00f010444481d98000c1c0580d000d01030210301 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 282372994 1250 282371744 282371767
    0x11e1101140403020a020a0515180a03140f070b0a0c11040f022b0204030203150406090b0406090b09070803180a080a050c0a091401050d0302010f0e250e071103 70
    0x4042c0300314440e900800402c80c461050180d0819260310103070080e07d5194408640d0f8080c001034039900350b24505d61906040075800007405090311035001500c180e070f040481c0441d117075020405494548203030f0200d030030301980e41401401c0c80c4100300300c90300019070603045440080d07403090740d80c901454010400728420309040d9404089902ca84120508a44c0e00744201c0d444e40c4056100b0382030a100d9440c11800d252568000c01e80360304188044046080b480000078041040f21f078486461103420403019401407038603150800041900d8007040d1965408100003a00c1144001a010203a645440140d802d10f009007000d03040380d94080c501c1e203500102c0c010303000c01d20010800c00c0d01101d82c0100700910480c0b20300014082e94016940004148a09180426031605d440322901070440b00d0a45a40d017070030500f410100c0c018030290406449650500d010415a13080000d61140440441101d14505600404140c4c488420503c251001c1c07040300c00c00642c2e51806440f140d0043d80e84103096900d0841081e01 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 282374100 1106 282372994 282373031
    0x3020603100e0103050102090f0d0218060f1207090b0a060c0b0402040b0607030804020f0303120f0c070b01060306141516020a050604170c011e1101 65
    0x100c0c07155a4600400801449084101400c65071240703001da000c1c0d802140918890307103d0586003c000d28098074104c0120b43d001300f20110312154100f8010280784010101c59010520b140c68240d5510740d022809070100501f07001d0001142050066000c41e0f51081c18640940306040c01400080c0e0040c00c010344094020101d40e941c0ea03154400a80540002e044050b00907502042c0042015003000e041d81c0101d108a480760311840b1050107050381d07405016445c10401d6802d030040342c80301c5008181c854100c1c21b10b500e454503084246d20381d901400c0c0d0a9029800195840004101411404040306080a030031030f6040b250180700c07200568240100d40919a41542e46040d14003190303540d11020004060142c1415200c1c0d91364540014184000c140181d00d900810039400300e0f9601ca2000000566130b02100700050400c000c5003101c129007141c03004182c03503599071800d840c40003040c81d = true := by decide +kernel

theorem cover : BRFrame.Cov 282194244 282374100 := by
  have h0 := BRFrame.cov_init 282194244
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282194244 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282194244 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282194244 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282194244 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282194244 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282194244 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282194244 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282194244 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282194244 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282194244 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282194244 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282194244 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282194244 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282194244 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282194244 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282194244 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282194244 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282194244 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282194244 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282194244 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282194244 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282194244 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282194244 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282194244 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282194244 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282194244 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282194244 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282194244 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282194244 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282194244 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282194244 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282194244 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282194244 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282194244 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282194244 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282194244 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282194244 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282194244 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282194244 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282194244 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282194244 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282194244 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282194244 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282194244 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282194244 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282194244 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282194244 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282194244 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282194244 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282194244 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282194244 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282194244 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282194244 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282194244 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282194244 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282194244 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282194244 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282194244 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282194244 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282194244 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282194244 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282194244 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282194244 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282194244 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282194244 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282194244 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282194244 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282194244 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282194244 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282194244 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282194244 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282194244 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282194244 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282194244 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282194244 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282194244 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282194244 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282194244 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282194244 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282194244 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282194244 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282194244 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282194244 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282194244 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282194244 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282194244 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282194244 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282194244 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282194244 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282194244 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282194244 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282194244 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282194244 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282194244 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282194244 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282194244 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282194244 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282194244 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282194244 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282194244 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282194244 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282194244 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282194244 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282194244 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282194244 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282194244 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282194244 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282194244 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282194244 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282194244 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282194244 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282194244 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282194244 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282194244 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282194244 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282194244 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282194244 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282194244 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282194244 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282194244 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282194244 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282194244 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282194244 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282194244 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282194244 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282194244 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282194244 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282194244 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282194244 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282194244 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282194244 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282194244 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282194244 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282194244 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282194244 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282194244 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282194244 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282194244 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282194244 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282194244 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282194244 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282194244 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282194244 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282194244 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 282194244 ≤ n) (h2 : n < 282374100) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
