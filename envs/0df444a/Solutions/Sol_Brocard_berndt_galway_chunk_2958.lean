-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2958
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T08:14:55.445016+00:00
-- url     : https://prove2.me/submissions/f6e0e42b-e34a-467b-8ec3-1a6222a4d1f2

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 531834532 ≤ n < 532014388 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 531835782 1250 531834532 531834553
    0x50c0402390606040b06070f03021b061206060304030c05010c030207140613030e12030309010608010c022103040c050d0b040605090d0c06050a18030504030302010b062802010e012906030403080711 86
    0x75240248614149d000da000901e031018801c08884880c1042c1e0741c11143c0030f0908642d0341c0c803040c81000003071105d4001e00c8000085014540100f04c20015154800006d0041107440303400100a23400c404401c8a011650b40c41c160050300020945900c02c10684171160701e0500c0d66201102e25004424500e40c201226000c1c0c0d4102d0401400250701c039040020000c117415117040b5005003160810941c07042150040059600e07030750003258a05402c20b55940b0150f80302c1c0c030b0724200101c0c6545280e1003a1340c0816504451010003682442c160b110b0790189100b00f001e40e0390b003441c168840c6043d01a000004000141107000150245c1c44a504442562400241c0070248000340180412989054011500100c0d0820403d0360900500d00c1102040e03c182d418400010307035095407022411882080030712000807105a9501c00d6000c42d1886001500034800402e02d114411900f900c10360003a00a0000107402110300d0074004100c90045d549566810307403546d950718084540860b9481c40c440b1f42d018062201 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 531837032 1250 531835782 531835793
    0x9110f0f0301240b04030b010e0702010b040c0201140603030301051305042303071401060b1c0e12090406080a02030307020d1e1a0a060f050d050c0402390606040b0607 73
    0x1111a11118640e003280b540f40e00a100c2034a801540b0104807a10100024000944031003407060460301c00c000040a6a154094180d0241110152694000e4949002c9c1005160305401500402c442a82c00082c1c80e20766a0034103840344400d01480350070103401c2018204600107a8802c660190044410980c2c0da00854003100c050b1000307031490001584085046030500151640e1074901c1400140200122860500c00000c0c5010f152038221500210841d00309006005400c00100078801d40184c4d4602e003d5400210980d4100c030f2495806145850760100c1c9800002514880e00754000700250f04150b015401c0000300310303411000712010076001c210041d038a400302c0415070030a44100074607010306c080480342c02107600d0024a20100079050010801844400b030304000c0541c3c806585141c100802401c01c54540a208100c2c0c2d0741161001170811010921a40000b18507155140581140c0f841d01e14080341450f030440107001a9045540490058503065102e4070b03c400b4003402c100d007401100e80701c0 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 531838282 1250 531837032 531837041
    0xc0717070308190b091302060d060b0301090b010302070b18030408070b03070e03150103031101021303080c01051f150c0f060501030506070c0312050c0702030a06140a09110f0f0301 79
    0x210701040d180e00a1060320356078002c6586824080d6182009224001000503000d10806400c000341c8920060352903040d034545400700c91138046d4559052102c5592241107282c0c0d40c1c800d1089480c0745160800009040d0320038021281e0342078009a034500316844000c100314880f44281107940700b61004100c0010030280a100700e0005220000758162030389800070000d088500c038240090300c80c0d0861080701e0020030390048680d044d2500741c80c0000d0b04042da000d10600920881c6210350002c0040744000080090360f80c0281054003540c0c00a005070b0316030110728054410115803030103a40d0a6410184181c0014102020924401e450301002c408e65a0300c030000c2c005035030841680c1c0507403207500600500c50104146600a545407624285d810070a4400414002d803040c4108202c545450111b01e01c1050302040d00c24040d00102681c103681c90b1454050010b1088080c403c48080740500022031540007071003590308040e0002d00945081d64040300700100f04d80c400c003000d030740311a00171181c1045440900c078 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 531839532 1250 531838282 531838297
    0x615010207052d0603130605220b19150306020a180914060f150705071d0118020a1205040c0b03100303030f050403051207051e041707050102060c0717 66
    0x20144040ca034403d00d520072000304111424060350041050007000d01c00d041c0032400241e0880c2000600fa1180010801010b40000340303031304801e1142494005118400c01501c3c0980321422410389e21120128110041d00e4502c860131031507000743c0e00c0800c0807031016001407210343c099103030a090749440a110030b041e4140c80c0e0401148981c0c0c1d42e5014800241c00041507070840e0007180c0c00314046000c6000a91103030509621020010790105410042050800c651000f51103180b07510103000c140c42000721a1000c0910410070a000840c3c80b0342c186608502c04c84032484541d40d5a18001550544844c0240001600827200058144800209400d025000d140114007008589401d545035040040070707a0941103c10820314a080103000c0001c0c0c101d421240c486403040750b4082941e0340c0043c1034a89008104c404850203030600700e00c554102000000300280d401406020380d5540070902ca150342c5401a0140c0b5001d0b9100001050054090078094800d40e803184001d05541099041780b0341468001d41c1 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 531840782 1250 531839532 531839569
    0x803030c03060f01180504021e030702010219030c022a120c0117012405120405030d110316030f020d021605060105180601030c0309080315010906050a02061501020705 73
    0x203001442c0380c510030403140000300b4078040352817a501d40141d48035403402e403003103a115550000c3c12000a201c1c2540313a403810200305031010340701c0c50a040041d0117544583c3c1c08602076a2580d94019449020744a01032000314154000c155240406070214119020a82143c810f01d480d80f1111800f40d40700d80c0141000694072002d40402c6200350009442003580541c070305043c195501c01840100344240583c1c950400440c000c031103991344074030265440e11409043c80340f440c2e020010401800400030050032094441e04040080d4526200e460301c880c0004d84680e80d42c550b0191960080d644039400146080010101c01490300a040101900b00d911010b0001c40d65041c02010b041400760a005060061a0a50b41d5082a0f441d10001990a0400605c090b061503690110408072512a40c006507030309501031011a40e80c00c00c000d01794500459141041c1c0020320a00c0041142d504c510180e40c102d0780690024121078030341041012012034141211030443c801c451000605d56030b0074251100c82c00000 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 531842032 1250 531840782 531840787
    0xd03030605191505090d1e0f0605060f0d0f020f0301060b04060305090d0309030c200a03050120090a06081f0b0a032d0506180106020c011115040b04030203040803030c 73
    0xf03841148920f08084010b041c0141400420400e0304c941034085506a800003034168850080c543e0781e00104190900034010b1140c21240b041048041e03401980507040403070b94113650105c880c04021902044440c0144400c06107500711005040c0000d080c446204014000318445480e510b420056822aa00c4840065103030350900100703003406c0c0100f24048034945824000f456803500d010b00031440e10340d8000c111407520200c402d1000390075060845400001081c4242e12031780ca0811030f010302207035a08819502c1200c42c24041e40310060044035102c8002801d207901c0c491070310300309032610381c001000084400082c0e8015885040b1600360032018004a0300c140342c40b110380c00402400c03140388082c03440f072070385502d07400922401c204001503480a14950012540c0d0b501d41d804540b183c0300c1c0b00c001e10b002c0c40e40f10b8004940d8540119000f440d450003a40e80c458620000030070603545000c2464200b004814030030125001c500844151030b401402401224606645d847d00c840c5580d000b181e4220240501 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 531843282 1250 531842032 531842039
    0x1b30050f0c0f0a1203110c0402030c0a0810180f020c0a051e07260a1719032717032403150105240f1b030313020d0303060519 55
    0xb0542e001000441520300002e03407420008040548100520702400748094500070380c1000c8070800203905040d402030820364403070034440d81554003500f00011990100d8801e40c001480410f440c1d41c4101180d82251280365004c40d1901500c00805c040000102880e408008520040408110701e10303542d1b10410040210380551b0b85076450040010903808500c0c2c2007024100920485c60034060754004001c002d80750078101c584202c41c80e12103e0b60005200c56118100a4000c90220015221003031080c01040c58607000044214112580e0b00c035850f4524448e00c0842c5140f800c24042103d07075622400c5816071421000101c1c0b0965002101d404000748503501c0e0040704040044800d10300800c0030f43c0100302c918014440c007805004e05015003401000d44441030b94000c0101e9490400a543c9059000d0b55032502d0805400198070070503070189010600c2078050348200700041201e02c1452183d9212098142d00d9003040554440e140080d010540ca803000402c00340d4170a403032404c1a40100001d9080c4134039 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 531844532 1250 531843282 531843289
    0x601030813172805060405011401050d080f070c030209160f11061303020705040e1005150d1b030204051501140a0917030c010501060c1b30050f0c 64
    0x2030640000c071845804401c0b0000c002d00018080c800d440741540043e04600c0418802070088020480c090700ea40700311070612041c40b00c19072000104c0d88408076142c50680e207950510440c40722040313000780b05070000c21001a07a41c0c0c3c0c40d4054a0402c0c0f150080c481c145689030002403a228054600a4020383c3e443c1552003d1a040488822601c410b8140308001d505004041e03526140000e10b10f480c04c0c1c41c0400b408040620902c40d00000c3c10303000348200140c15054034070666524075807152031111842c1c04080b5101c1c4503558000c0d400d1400050500e41d905000e1b6440720302090f410310070710000351051040880140d03154040c440c40340c110704c146203c0100c0e48100051081980c0c20750310050541c20007609810580c04000b610542d6107803000c0f641e03084400000d051962240d040b01c000f05520b0305001140943d07000d00c0c1085074034002c0825161440b0150340c81c0c0000b440a02c034400c080d8802210300540b41c0c2c03016207101a139103400b03100410210b00944800b401d00e0556075450896801842d181c0e0407519 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 531845782 1250 531844532 531844567
    0x9020c0f060106270f0512071502010902010311030f2202030106180f0902090c0f07060f0501031218060309240506041107170705030d06120309090b031e070806010308 73
    0x3c940d202e10032000c0c2c9017805000f050171050062a0058058100c400c80e004400c02c044002030404000c2d1000220401c00000d0080008002c200d0000b8103100e008e841512264040da4090b6401e14615016912004451840c48003821221211019aa180c50b405680c0030f11580004000005a14240d0410038101e50116081f00d407601201038031300240000580c0b03600d004940e10500d45040383c0d5482040d1000102c4078064160014101c6040c407030019810021608810304032441000311a20600380704409540700c040f003020f0b2141d818050780040100501c2904640621401448901c0c02e422118aa0641d6076101e904803240ca43d49410601c40141080d105074003180d1030754071002e03042c40c106640764802011059150b9808440225119040c89024421985030302518801003004a5803800862415008508160041580984006800c1c102c5009910b10048002e02502e00d544400c080d01e201c5c000203c102c1c01751481442800b2640740b60801000317000e5800b910310b036038403500503480c03800800 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 531847032 1250 531845782 531845837
    0xb030406060e1b0f070b04050c0123160f05030a030c120e070905040201170910050a02090f190b04060210060902040503060406050a0207022206090c0909020c0f060106 73
    0x2c50403004000792101016032104000701c110502e1a6204200b5540060600034800084c040050b05030a20003081030004140303440300c0c800c0c3c8841042006031f540500e00c0242d20001c250740107400300941006440444803440080d4410101c1078007000390390f1250307840c50700107030115008699110120310500e500099421400ea2460601b0301c52008260f1046441d00360324031991100c07c4d00c3d403001c5021a0b01650714083d070201a4144041c46140c4044266582e542e510b0a6158071480c1c803010803480c007054000c80d030045001500041d2140c0d01041800207002c00c41c201907800f0501040003043c0d066890340180700500e4207a008002c00c03600c058000e400c8132142da010194591040004000c5501c010035102e90144c1c21580025080d51240418400b0f03200c3c070b4000952013002d48021000d843c0c1c400b1a200c4804061210400600d0348610b01c0030100d80d00017034800040380701d6000420075045150000d00d5000d4940c41610424a601c502031844c1c128203030030000115074410b110540c070b44070081700c10b03902 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 531848282 1250 531847032 531847049
    0x12190305010f15030203220803011d100506030411040204121e110904030201112a010504110f040b0a030807140c0f1e0310050a0b0306010302060a0f1106010b03040606 73
    0x4070b2816843c1003070390000300d207050280350b008800070300442c25104035100c0701c2130b0f40f2440780d0213245646070843c02540240980160980c1c110580030b6007100d448200f503c5246948007185071941020b040100c6600000c004075940080c0031018040c0d9207079400034100511003207920203c8030103e46060b41c4034501c0c060000c0400d052100c1c1d11000f00d100c0c0002c47c8441c07001a00c1c41c005a8a40b401c04901500310440034407010b59000900c0a071f40c41d40741009440406040702c0481c2400c3d69540d4850907144150b0703010304055010740c1140450302d0300c007a4051007400c0082001403a50048800b01d10640a076a005840241e4085003c2d01405442040003440c03103103900c003410150841c0300c0040c1d4405000380140f4043c43d6071144101d90400a148980800d000040454217030382c642d0618480642812590400034a0074046200c00900f00010181d043c3c03a8007d16003404d00b640480100c50044030920300d4020006062400c1d00119024441c185c082d0045001855580c942030505100396260f0f40d00c000d03003 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 531849532 1250 531848282 531848309
    0x7121a18090c010c08192d120207050a02040c09270b0a08150408070515090f070302060d0b06040b04080a0b0f09030a0305090c040609021b06010f12051219030501 71
    0x10b101104540c1000891560313141c8007403020104031041d8402d0103034981590101f405da40902000001c42e8000300080c1d83d07901040307107802c003101c05c02da000318407000300303994410f085500061910360000041710300c1d989013401c101070340c40c418151451004580e103c2580099000126208030601030081710035010f407400070f43d26203805d11590b030350100307143d012101c2039604012400b04440e00080340c004230380041c101e544018201084131003030381c1d00f0307070303a0100c81e1050b510a801b032450f022035100101d9170014040c60602d4410503c200180400941d15540083c00f0040807548881c094045c001a1418000615400d04245440c0480d60006043c1d0061006201d04203d4210000011104621a90b280c0402d01da00e0f900034591034124954002c6521500b000030210311010305034040c1042900040740074086500d000c00d03040e1104428028910404a800c505226101d0806c4103d40030794421801c0312008003280d0074080c400e8000420481d40381d0092032440c490745500d40182030140500409000 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 531850782 1250 531849532 531849557
    0x103050d210905150f060a0608190e0a060e06071106010302091f0f170616020606120c030d03061503050108061303090b0c07081507121a18090c01 64
    0x801e50590000400c0d40070341c60300150700801000f800000e4200c01d18184071002801c00007076600866400b198803e00941003040300080303c030312400701d9601503102c0c804126242c20901c40e161020b8440c80070045081d206500101c03000845520420324091001c00c0030300840d00782400024041202c4070f02e0140c1c1c81d4032010052015a584202454101c4900d44003000d00d1850403488150001e9154080c2c440075003070b0840081c00500c40034075500e81c0c1e0040b40070b903102c0b603aa60803118001451800680016885240000c041c1d04212503203048940c2d030002140c121055901c0020f00e0000c240f02070200194940c8420010351661421801e003039015400d06200701d6040c178840d01c1e076070280107041c00031006c2c903d84008281070291405101815805101c165542801c100d03aa5640710f4500c00c1e12141e100c0c4050040c0d00c80c0c0b00200060045070580c0e6882d034010340b401a103101810b10a400c0d00f13481c1c141a00c0c00703130230f694609203105034002201c030395000940307000c0307500f44c0c107003100006c00301d050020074854039 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 531852032 1250 531850782 531850817
    0xd0306080312061f030b0102010c0903050c060a0c0c0b09010e09070206040209060d0c0e31060f020415090801110a0503041506030b0a02031b0901022a040c080103050d 73
    0x100d50242d992440314056640b00d8001880c0c9006200c9600c940f00101e000000819900d40c0014007454002c1e0024000d042e03c0c0d450403a00081e403840043c0081d004443c484066103001e900034101c04402d0310784400601d00f662165410f030481607024010f0070000241c4a40b20b540c004410b410301c0b10b000c40b0003590b1840d040c040a901c038100100028480c1040300d002840aa440003a00740c0099005564128010b44070300b00d03041322004c15155004c10200c8011404101c54188284102d00e1365240002c45a91186036284000382c42da04441902180e02803101181d1150750034812145c4080c2070346c42c48003a80c90300c40c29500b1035800d1a00c4e581d0746041004020b0050b03401604a80c2c0042d446000030300c42d4610000301e00c00600b11500020101491081400301000311500994019201c80c1821840b160842500700505d110341080e4270302580045041e0041c000041141182441c01d40900120303034003501d00004d0440c0c000d4203808011079441c41c010f2080c42010840b4076071541d030300e042c0990a0040022007 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 531853282 1250 531852032 531852037
    0x3080109050f1522090c12050304170102161a09030a0906140d0216290c0306030c0603090d03050907050604050d030e061911010912110304050d050309030d03060803 72
    0x40303d58804104501803041d2500c00024100d04065602c0401e04904815890080c3c101d0903401d840e0795040c0400400d0110070035155905855202c4025490985000441c595008a21304060501d55007405503840b000290001e15154520802e103060642c0b04503100d41040c50805085290075910500000070400c2e04440c0c040262182c60410142d66070700315236802c0a600c45c1700c0a00309010300102c4c00000d01e0388044500107115200360064105404180c842c8240d58070000c0000001a8040012440d0941103500840d000440981590400000f41c40428040d610a4442030784e03d40c8041c0d08a11581d0381446030a801a03800c2000d070403ea450000051190300643c060349220341c4460202208143c011008a02c0002e4040d000d5500c4807202c2c03e051650500d0020b0100200300f008000e210380480605c610400240d11540c030304001c000700001240c41c250700a500d0151032108100218190740c803500d410b01c15500c91002160b0750100d1005060611105440c503005060418a080c840341170003009 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 531854532 1250 531853282 531853291
    0x503070f08010f1e030c0605040f060c050601180b030d0203030907052e02030c010908090f040513060c0903021c050f030304050601350a020906010c0203070e0c120702070303080109050f 81
    0x100e2000d5004c0000300d030340e03908080d0300090030a104401d00094194101019104a940d011940b003400d59030b0310301c19542c0e0a40e0703400c010402e4100c840144184598070320360324111001440006031404403800032901d0002003407600f1002d64004400c0000b041010000354014180a540c85042542000400c1941c20410100002c006410b03484503000305100700103503604901d008000b48002900c40c1440c07449580582140e6001d003200c1c0c800c0031501e08140c021240501c441c00c21400001075503480d070100404200b40c3c120308110705041c0000c00750343c919038071022400d0141d000e8548000b052500914100e18955113864941082c410040440d4010951038115045501c03501e60b0300c0120300c5001c40402c0c2030410048080c03c109030780c0607240c43c0082c020b4046172013a00c1d40005a15007000540707110840d884025032540c00303500188819182d071140a0340200100c0710307050400580c0d14250712910004ca07200c030300680c0505410010300d0783c004805401021788034401c009a04060320b81030043d000080 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 531855782 1250 531854532 531854549
    0xa09031110080f1e0717070504121b0b07030302030603011b0c14011103130516120f020d0204050c0309060106080601200a0213060512010b0a0e1005060304030503070f08010f 76
    0x1440d002102d40c11051113118004007035282c0d14000e0000b91140402461125400e0303d401c00190f0710714081d0049406854075444600c980d1012035994a0b0340c1405641c070001412051000000c5490b001d0f409000120b11948000d6120300d050000d2508440c01c1098144010141b06020325920b03400861070904250030071711524004009800c2e50340545160032501c443c03050b0001c200304408100c2640c402196109005444501001d94176658000c402d1707014645c0340d4034108449000150781c270400b14400030f2000e09515400c1c1d5072600003a0844e1000c803540c2d0f840c15000010000006410b01480b0b0242101c4e00b002d20030b070f00300100000c04000b40076402c0c100001540c41000c08400c02001001039540d0f0062040011484002c2c0910240280d4410701f8014014560136200e0502c042c00b40d4131003241c02401c43e8007008d10340070031100d956501904e111500c5862581c007041c292076400007184181e0081d16825541d042180d4014008081f00c95004108800000140700c0607140c43d80131407c561815 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 531857032 1250 531855782 531855811
    0x121002030c09190f0b03040c1208181503010b18031b0a0602010c05030a02090d05010c111203061e150a0804030e0910060f05090303040e0609100311060313080a0903111008 75
    0x28a400001020650418004c0368036140c09d0400b0080c2300801000c00032041c0424010401641e0240201c911180300802c158400a0006011412813080544000007210100120040031b4a000c241840a0345412402561100f11600c1c064145400c42400918003803008002c0001612001407030703404083c0180d8100b540024044c901991000901e08010340c00c00300130003020007000707406800038007052500c403598050340351200030013948403083c1c0b03111b032101130705031818902480000e02003280381c40102036200c105004030201202d885c038041d02c00e24560361030f0200c80381843c0c03c0c00b400c4900c4000c1028417502100e4204242d51030041c50802c1200e605080003040039000b40b40580b61030081008260309844040342c0090058146842c0303038080c0c0b5050b200780480386c075800c1c030102c4545004d0101800712000d03100c40400c2800c01400640e8000054003203652540001e0351071030075940c801c0501c2000180f401a0910510459021205144800301e99504002080500c080c00400d00200f0003049001a03 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 531858282 1250 531857032 531857041
    0x1b0f0303090213050f0105030a02011407030c0f080309010f23100902120a0b0402070305180a05041119031505040f060e28021206121002030c09190f0b03 67
    0x41c0d081480501c1e0b004060b4541600540c0d0740ca001803104440300192960100300010383d509000c00c07025003283d0103a54003040340d820404580d070181d101c91411800c00091108034800f10741c0344840741d40c0062250021644c0c0f030a014250301d0941d558460242451858070580c4600f00880a20078a450808007880c07560079510803c1b252426007195011a040d2030001aa006540781ca144c880b41c41080c612000300a040c001a0a120480c080e00710018085132007080a03404039690034031200c11030040203201400c09900c03140400c041e43c9200d199254000c40c0411020f01d0b8603911a50000c111030070389000c0040390301d12001500b1119843c406d042c003a540d9074250800601507500104007605100d54000c000d400c000c601f001c102484050b28038030340c400c3d80d48030390703401100741c02104c648120b41c50320300b036117600d403003082000301c9000340c04044035845600d542c0d101040403030002e944142c40300325905880b10002004d01680c03c411500c00100441c81d050b05012180840d0450010390f490043c500c2d84960342c = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 531859532 1250 531858282 531858287
    0x618092415120f07060e1903111504090c03050103020405090a080f0c011506180f0b1803010e01140907080715051e070501050a0b060c0607080c071a01060207061b0f03 73
    0x1100c3c1c514960358043c0c40404100c194000e001c625603800e05442c5040000240d5059688480075070100034a20008142900c099240964107944a05e5a40c8001840c09079a82c100b9000c40b0403130b11039640469283c50041055280902c692030748035000b1406807901e04e8061b66014510b214a0f9608c240d04600415816503242c0d00350b108407092029410848c0300785032aa44e003d000c25110a84421446445050204000b811548480c2c01c81c0c8a0307941c250b040280c6d254446800614004640360076641c0d60b154048803000c240141c00072001c0c00d5529400b40d08014900e207040401d00d4002c080c0c545d0000e0380c00c21011080e10f40b02c4140000e03500d402038459140c81d6001640b2030600c1d030b178042d000310041821001d2100c194000d6000d00784c400410046c2c0180d26007400241c0c05000b119038155005500007415090194031569444000b20b10064580420359031404a0382048440799a05001c0d45401440341c25010009140545801d04040028549183e04410207550761b240007070085490401c810201030 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 531860782 1250 531859532 531859543
    0x501123c061a0303040315050604020706021c060b0901020a060b0d0f060606030c110a030305041e0602030405010e01021e0706020409021207090f1805061809241512 72
    0x509200c0d03a0003400825040c281c0141000c00d01031145030500820360a240e24002080303408483e03000300d2260703c5401c407100060041800034242a0060340801074180000d8040c8014180b000c02042544d034142d42a900440031140c140e00100f800c0e22080110040a0b0307000a944940f10780d100d00701080c0103100c50b0200710034410403503006080c00008901d040070841903400c110309503191759604215108200204a501080326401d01507140c1206480078046813003600301903807240c0910140088050340108070307400c09100da1410381d00701d40d0110034802040028001c511a8820b00e000a5007405881e2000c02280d054211042c0c2e02d1100019002c020454503030140c13030003046126411902c6030302d00c441c2800c82d402d0407a136441c0041d4404d0400328200c5820500030043c2c5010001e103a29510304407200300d00604c4050100390b80840c0c81941070700b03941005c02c0c1c881c0c404d001244c0500105241249250380401e03a0003003019190615404101d2200071598002c000e0223070403101d0050341e0100c100601d040c003 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 531862032 1250 531860782 531860873
    0xb0f09090309210115050d0b09070302060c030c161a0a0311030115200c04021b0604030905090f0402060d092a1716050114040e0118050112 61
    0x801448a0f95414461014a1a951079401c1000780203075050a501280031100c2030107581d40c08414801050003164410340007503801300780041151100303500c0341c00103a07080d0050240801250701c0010700d501c4100082c01405014043d1070200000d0b5810080c4d0909806980301d040040000046880e40c0d15602c41e4002c100f154130b01000865495031942501390442060288800208004104003004002031071410020305240b01c026081c0d0400a108000c060360240703030340d60140d602088250010080501c40c46004074865214a600285000d042c481ca20301c00900c1d88a00002c840104009030700e401c821501c112221800c0080d491f00c0c549424149000c881d09014201d1039210314181d10301085800c42402d69010308040f170104200310345682c0c0d40320342a1846040d44100b15808020a50140c628130034113483d0912250308107a2100c0360f00b951050240c1c04a011071444400300400b410440c03180c0d90161140c10210301161b503443e1201819035608598030440650301315002c5003085c080c8500702d17440 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 531863282 1250 531862032 531862039
    0x90509031312060e0c0d0b060102030c1c09051c110d050a0b0402040f180209091f020304030f0c1101230a050c0c03010e060c0f0f0a1101050a0b0f09090309 68
    0x4a03456072540c0500c0c070b10b00310040303400c540380c0440c051409400141d142d00701c82d00100b05400304d252aa0351201b64417006010341e415844144410b001070301d01406030002d001c011401003540c0001000004107444031b1039200c140200000a0f81c0040c02101c1d012101000d82c1020135408818922400301e030154420400107020b5000d01d642141c20000700c1507503d4040d40c000c64051107001122010402251800d10a926085411501d40c10040c18002d00103a8812041d4041c0c6500c4a0043c1a0b1138001d040d0340181d500066000080004068211212200054080c40c0107258026103994610303d881307101010f641400b00e10400000d281118080c11140c5149004a26484902036840909103412105110503103000f034a00591250405104100c04800341d0402003d20b41c440d000341e0401a40301c80c1c41c901940e40308003c040e4070b5500c40e600400c03c0001031b96421000e958101421030071651301078401c10500781440919010f1f031f5a036002d01c000c00d04007120b15140f640c44c1c40104a180d44100041d0300e81 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 531864532 1250 531863282 531863317
    0x8040b070b06040501080d0c0503070b07020d080901020f04050105030901110f0a0306050f09010605031008072705160f1b0f0215162306010308030a1d0709050903 71
    0x25100040009403803128814080000c990301c0ea00108001d42c0c00074000c81000358005080b081c8014030030190300038502c0c024805e6920304500f0351213600c0c90301821203039003015a005075032562120340c0c040c40d40c580c0034501030001c45c20154291070164440c811849250304008020000c0b03171150300c080d8800f0800040c400b0009036107407008034218045800806019001c20f103441e000145c5400c4c00000e01617441001841e9100c140c1c00c1c0203003903405420103404503801c10403d130804200407100704084c0e000f82c02c0e0983c92403004401000c50400d500182c5015606150400080c81a404600400a890a10305c2e08000d1000702c40284204c03011a81ea80401000300340401c06da81c01d1041e01060545c2c1d10f8000e60f10a010f083c80c9401031401d40c45107c4002c0c0741541c602425030302240c400c100601d000624510540b0030f00b842c07060f00c0e524010003138000341c2d1002d40010a0125003942d130f03c54500001c2c0155604c2508003d03003810ba61300e0f07081d540719102c01c1c5600c8c0d0740000d0441405004480c2c062200d00c00684 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 531865782 1250 531864532 531864539
    0x61a0307080709060902040b030c0f041d190c0906050901030905031206120f0604060906060320011e12050901061502250311040c03060504020d0b0915010f18030804 72
    0x3952081c8522880340348031314009000c2a0100c0500031203043c1d038010b41400b4519200d050661083c1d600400300f0b8991004240000704014868411030340b403140101e60401c20b282045001c590300c10002402d42c03c8a20710705a075a082c450381000448044400d14207042c5e072a482c0310300050b005895807280c01400750000240c0e0782c2d00c030410141e1b500e0060030280c3c0d030303980c5400d06d02e0082d2b0740c0c510f6001c000403410f50100000800140c0701c0e400c0407825034807810010403140e50f20f80d00d000d02d10441a010704401220303071040c03241c01c1d617002400c83d864042da8848010222515500501000c3c0864000c04403e501d403000102c0000003500514002c11a8040e1041c20003122a0020b48865203101c0e80147e008a14214141c815012800790301565000754000700c8580303503a41040300508448107002e05154981e0000555961030344090401d84558800100d07110800408104055034001c010031446844180c01c1211a68042110300b002071483c10440c401500040000701241382692008020031000103010 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 531867032 1250 531865782 531865799
    0x20411090a170d0c0506010e19020c0303060f090c07030e030f0a0302060901060f0f3c050906060309060f04060615030e160305100c12150302030607020a080403061a0307 74
    0x4812000740e070003955103000f80d51000f03c410003920355000e07055500000050000358006c0010310f030070884218403c0c07100703808040c0e039100740d810440d03442e8551780020082000500b0558454222400100d881d9603c603d00240c1090301c40c000c444001d02009056101d1110b41d4500b001441c0d50030111108445500030b1510f03000b5070320350741150b40d03a1309542001000508043c0d44035842c01602d002281c1e2941d030038141070005406070380c1c450030358032524110010192a4844c2200100d84a51001100010381d820101030041040c0090034081c020310301001006882000841c403160000c071000d00c80c404a440c0c82c01c254000d499075400c04c10b0070741c0e03161954800498065100720808041001940c4001d241c507642c00b00e00c10490705c40a411500401000741e400b00041c0d01c041c006071600d0070000c0030580040344074012078000d85101c010301c442054061082d4901044402d40c00346091004040d800500d60760740c0a9401248001498903880700030328001e0000b03544110303020510203002c8500d1181d807000f10 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 531868282 1250 531867032 531867059
    0x7030c12111b010e060106110a140f0c15160804031401020706050603010504020f010302030c131502161a0f0403240b011412070e101e0306050d020411090a 68
    0x701820740c07242000b2081d0342d1040c0501003501d9000c4003e001d083c0c0c030f842400ea403401616a840c11a60052002c40f00000e252800484100500107009212010b5003c030132900d0301d103460101910440c0d03228046a0740b0030780002142c07034060340e006259545d20f000c0c2c903003500117014030b40004003481480000d1802808055019054850140340c040c0241d44038001403500700c41050390041d400800c02d100590155000760019600240b01d030030f506240072407440c101c5500740b50030b400075500c612440208140c01da82c100100000c2c4450b00e20f0244491346031640c0207144c08212042c1d00400080410042986031640090320021600b0140c00c407030b0365081200c03c51091031107011001029180c0610703010654414143c0070f03005501000200d16280201c4105400007400610741002c008120840c1c1c0c4040c1c5030724100d204c0007826500c4046070403101648c1360100214444c1080105807500c0404c01496076004040810703540c05580002e0900080b65541c4054890300510f6600548a10300000c3c110680116 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 531869532 1250 531868282 531868297
    0xb0307080f0f090a03030911040e0309130513060e07090f020c0105090f030f161e0309230904021813110f0f120a02040606090501030506030a03050307030c1211 70
    0x104080d07181e03500c2c0d8803040002010f40340011158040355481001a00aa0081d00014001e0005c2510801013000180a840d40c00780c00114a030170104801b02617080c81008205800ca90440a120a00e03140c0c0281618000c0d8580103050b444e1a410814080442441444068001c101c8188003000c600006c44020b58040601e41a180d841d09000455044003c190054a00000e001551811031002448811500f002c3c00c5031400c0c00302d0580c0319000903032075220714810303404203240e13380d060722070b403c018004014640c040b14200350700301c5100101c6001d000441803005011942c000b40c503201c0780003044c0b20348000d0003400320300700211007800304040400b1640120705210702c17035040d0414070030710500c521495401810b6811610750351000c041850449080c1041103a40022201c64410980000d400d03901e0030750105002c1550550280076559050207902d5008000b80c0040c5038450307103550001d000b440010001410155105442400c880c42840f02050031020140c044c40210241c00d50142e456001c0e00 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 531870782 1250 531869532 531869551
    0x221070e120c01051c020a0206041e170c01020c07080f07120f0f02010c080703080714070c06030c0509150a03180f0f240c0809010207080405100302040b030708 70
    0x10314451640c5401c4400c12100034110000c0c112602d4900c0040d1900d801c180544492607048840149030700500344007400001c03500d0381c020300d40350030141840340d00f01d04c0e030240e00e01881d44000054400b04e010704000e4500c1c40c01c01084280e441c0e00234200e660081c01089510f49240c01504800500c0c82000140c0303965001e10541071f181969514494124540784903000100b4003142006180f001c42c5040c90b40c500d80342c1c010306010341c8a21541c0d8800d40258032048044020034a0b200900000300d500c040d00e8100d01c0035104c405c1c0d15041c42a110201c81408611950341090740f42c1110200051080c800e5400091018082507800c1c00c03407234400034541e0004a01d240000e480c08010180c909101c01000c019580c022031503010442903915111103000f080141594031007403025980d020b00818040004404d5600340c00081c510610070002011040040d0021903603a0040c81540c02103000f120444e1700711401103030401c40c4000d468000b940a80903980c80310b446032401104105a40390068005440ba01001 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 531872032 1250 531870782 531870797
    0x20c060f0708071d060a141c0f06050d060b01020c1518030a2d2307050f03153c090712060207030c020306160e090702120d022107 57
    0xd070046038180200504e840f6800440b10160b101c600300480145070307000342483c04424034132185005410940c8410810a88a50018840c6030000c101d841010300d440d540001c1405440c1c604000585100c04034007003d00740c280d503080b101e01e084e03000b0010542d003048050714560811821100c1c103056034004092081c040742904000134078501d00031440b100c40da540038510200781110121615607100d0844400404440150904804140c1001203800d114001d491003802000c05400c0780350501c81d15a01c0503004180d8030360030710040c0d81c000c1190410030400340c001090566440c10320300d02c0808866072241d208540c1c502d1020300d191590415054008000742074502ca030b107410015560f038180c0e03882000148842c02d5a1240003881c59001000d066001c5d25025240c0b48140d00044c1c00d0810079148107561341c107040c40d401805600318007440181c400807580070f1800d150420f0041d440c0d40b031f1145002c50020001170150706c00c00f4954140d81d01c00100600340da001c1c142c80c003041400d50005440c1c00010a401 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 531873282 1250 531872032 531872041
    0x20a0801090c05031801110d1b09270b120c03070e0103020a0e07020a0c06020d02101b050903103923120a020405180106140706020c060f0708 62
    0x18001c0942c15501d5581e0350f49556a48445840260800390303112907155256900b1404200c155005813481c02c2015000244c91616410300c61341c1e034051490704c10107114030624100710001903180001d040c108508018100c0c440850100d03002440c0c8424815405030003103846402080000420f07410001003a011a005551a00740d5078000724424800254010040901482846d50400f0540e401400c54011240b4552580c1c0d00c81d2401a01d03034000c03e0040e0b000202900c04c841d0b0400100e1850072083c0001c008186103007629001e200c0c07000d03580c0320900400040c0c0d801103440800c41001c50400d00d03001041020783d00c00410340e03c90216803210200711002e801017141c0c07044408500c041c0c01255180c3d69420840c1d0100d00280b1051000b000c00c0341c40091080703110035090051030300d00c65807040d1001070b078680c01d18003004502c08602c1c00c1c02e403240785507200511a20740c224040314510103002031215124901032800d640039104001c0c40c10f906004103410f00800d0b40c0c0312a030982c090340c481e44800c122a500d = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 531874532 1250 531873282 531873299
    0xc0f05060708070204092907020607110a0b0403091d07030b060a1706030f0a0b0f01140a0605090d080705030c06090303070212070c0e01080a061404110118090609020a0801 75
    0x26550060700b1041c00304400e4006182a6211001c3c00d131041e050761030710440388049000d1b0407040d00ca101d42140c5003201000209a410b00801e584201c83d42050f4011500c444a180d03600c0d01a1f020081c140d103101c6002c0340030703d03000d07010840c01484150b1607201c4100720a80c94006420040c2c8182010070f0410b54240c940340fa00d1003c1d01d5130300314540e80d5250b02175031000c801114040064600398050180003544508240f0a100108909005070b040004605001544114007a0160300c9804548002111000c882c1c1d10301604100301d03005843c003503484110341000600103240c00240240407040018100081060100140142c0000030080d24480d90b10300c0076480d107034801201c01d1401600516400c0e420140d03400b020f0211603000701d4090b4503003a150840301c148002d081e002643c0b40d51080c54281c0801007280600e004259551000c0030280c10142e0324400030301c0141414505000d2191a06c041c00c2070781480300401000780321401d0014959428600000307601440f0003a0000707601e13034000f00e103009 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 531875782 1250 531874532 531874537
    0x40801020412110d020f0405070c29090609150903040b1201140111280204020408010509160b120604090f08130e010302030307020405040c030b04030203091002010b011215120c0f0506 80
    0x1600605502d00c1c0403804010040100b000409010501079201659004600300740026002c0c2f50301008817090604040441d03802590340140108855880102045620300b004180301c40710004905155034a9101c0440031401c60056400078500090003203800f9000c0521010840c3c121035200741d01000c0d070281c0800444444400c10500c03482d903448003614640301e21000020a0041c2001c0c60b409200036242d030f002606903405640301c842581c0d110020f11140b840b046c004058040ea02c81041414945450480c50940c09024443c5800251500000b00b464032984c00c030799a1a40d01c2907021402c089a4902600301d60030001c4848a010b48510380130a440e05070885c424141c3e600100110704141d070342d60810016041c01842124602c011b00c00c0000040c6400c050580260322a401440d265030092060010207c034094007202160f040420a8000340d8002d038841c50600409000840e98079145030100b0024566a4885044540490f01003000d1004482c014010b03a0344032407484031155038980400100d070 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 531877032 1250 531875782 531875809
    0x1091403070201021209030a060501080a05060717161205250c0c1806081902090708010302090f04080f0d0203100815010639020108090613061104080102041211 70
    0x50f0300200c170410040805102074a180000102242c80c030054580e101815140281c2c40000c455101c000fa035802c2103824020158082c42c1440d00030381540c02d11044a00c40d62002c0c0510740c0c80c001480311404110721a580c0d201040310710040500c0380d03003004031440d4960703170240c54109940700141c4c2e92138401601c01e40d22103440d15000303a41d0156040c2070040e02451800441d40f6041d0307260303a03024009a824020b00c4000210b044100b82489000761034010f00440c210010440700800240100510041e03652003001a0040e034086e18038410340e81c9170b1500e0241c0e403007204954000c4e086c0105854400d4105600190322405c48007610b4031485907078074042a5104c1241e01c40c103540011010060003000c1c400c0f0003100802c0c92a440c0510360b0018051304202c00444140026055200c0b6a41c3c001956080388410381c01c146840d0082c5400d1a0513044005602c1d04d0140082c0019204d8090040d80140c91040e1000782080c0f00086503241d035160003010103c1407880d001c842e40f00c070b680740c14810740c03170f181c0b00c2076030705 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 531878282 1250 531877032 531877037
    0x1106010b1c0e0a050715031103060a060507020d08030a0b01020c030109080f030919061d060402010207061d0306070e0306150d15091a06030f03070503182101091403070201 75
    0x5512041c503181e005420701561810700b51080c3c0c40c80780b010420030050f94005040c0c40e0200340c0100480d12001341a0b8140400920410308208140310751034881000070400c4490038940304d034654001d131000840948036030310b024000280210a011001c0d2a59102440d40b8400340c003165164018001454213031021008050201242408841d4541603064001d40d409160b810540d50407511007110800468500c24096961540d01c1110600c075042c41c0700c0309024041000001c0c015072070180d0000b9560b80041c024042009014252403042014103d00e6019608000703007550030b02e160210004111100c1505214824890f10b004200742400400c10000401000f0f4010301440380c164440c03406270b81e01e81c00d0b4603000c0c556800703512000c544036400728901d00041c00c2100c00d039070500344101454054100c0340c0f401690003c0040384001740c800030890700c0715042d0501092070480b082c03000440300c400c140c0e071490440703806d401032100242e010760054050030300c0f616400a1a05440c09000d41c1c071b000d90b4000901 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 531879532 1250 531878282 531878317
    0x108031c0e0316020a0905070e121b1c022112040303020c061b100f06140f040b0a080706120609140a1e0f02070605130803130201090905071106010b 65
    0x70038607404031810f11075500242c40b400341c142e50b500c048400c403603040350300304001000c0c08800e010b286042c481048090024900402a1081c2c0d408588034844488035802e104141c00c03a030408a241c01201c40129064008110320b24803c005001240720304950701d03c404590103400a07048003e4415410f0b40c0a489d003541c01001411426410f006855104018082d90010000f080c41100707541001303244006d0a4003107000c901451201103c0023540c0e4950000e201c60f203042c003140b17500e076251150030f50b00302e210445000c6154100980030403a4424941c1000c0f80d10f00030741c940414210b80101c02400218004102000029501c2040c5400c80d0103941d101d449803004030b808200c1c0000d0302d810842031084484005440d2984495401c000c0310b0325440b110308016000305051090003028072405078400c070380c80c1840b0f554412036038820310203210085c136512151140000d800203591141c0b400a000e801c80b0300041007142080240503018001c00349120800e4400d01c400032412030350400c1504d050030880c0d0042c0c0c1c2e = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 531880782 1250 531879532 531879547
    0x11030c040905070203160f052a0f0409060203010b12160f11100c02150a0b010806010f02010e03030408120601030905030a030b010216090e06070e0f010c15050108031c0e03 75
    0x81d00003d045802140310600181c03c401100110381c170240c0703114002c442e070200300615182c0e06014400c7c09240080c5480d452040c00c1240600866108020441d4003041140b4400002030003020b00401c090708841c80440042000000c2c003008086642c0d070481c1650817940e03012181c0301c41e035142c0d445000005800031141c520045c040d8200007000c1400c1c4013519148105105440121055074080d00c005910080006000300b0340c0d40791403500069035190a1007802c80550018007003c41c0501814100304d400c40c08806024030030b61200c2401c810510035243d8a0810342408081c580007420b581c01c0d048120004514298001c1c130800824036072102c041d40c100420840c1c154000c00c0f680041e0b42c198022104803580784030b001864031000d8400804001500004082c58520f01032000700150244040f401c1080c0c42c03130b034407506150744584c000d180060b80c0000c546040d6845001082410401c0d41c105800814401030100c007510981c0010103420054888140008040c2d0b180c000c10070304c00307820030070210 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 531882032 1250 531880782 531880799
    0x9011a09190f1d010203010e040b0606070507060905180907060e0301060506070602030703290409231e070302090a050a0b12010203010509060a0501050a11010f090503090411030c04 79
    0x3154008490200448400c0011a81400340d034045803244010350b0351a0080d4a00b41107141602d0307240c848a0740214115030412805038015803020b000035055031100c40008055595142c01c0760a055800360503517907000c1c1d98040261148140d40182d600c101c03651a0140b0350b440411178400c3c42505050008d000c1e01d0310b40030040e1115460040166015500c511003c2007940340e4500400c040ca00c2010016640c0c034150200804803081d58902c2611900440d898010104062100050380300b8200ca0011380064280340c15460510400031b4080e40e482440d00010041d440884c0034090089209004071602c0100b00d5032680b90f1646000c029409503e682c046060841c09a1140d0b0380100503010000d041c05200740080c003440e00c1d000702038081d40c3d000001400281891405981c1100090702e25116803403c0200282c190300800022404000650300c070007499a000350001c2d0f02000b5510000c001050b100c0c00e08a4a0340d12611005010302e042c0540c070005040740b40100c82c03080c1c203011340343e40c100390405424 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 531883282 1250 531882032 531882049
    0xc032d08180307081b0f030601030201020303010b0d0207060905060a0606020705101d04111306080c0a0503072d08010b0a020304120507030b01230d03050409150803070302070e09011a 80
    0x8142d0507105903200407801c0d400c10031031070000a445109100c030541c07882d0100304d030381c1d9542c48000780640c020302c00400050740c00006981c103555018403036a40b05d601e241002c000900884901030041c504040307031141444404554640998000c80c01440200d443e944140c1c0d840d90701c0c2c403906800801040300310b4000c512030301300c0f2901c105041001070205506507002905860300300403224000d25000a04001f0850402c2007480100302a00f459605440c03e0202c41c001801000b500409000b00040002c0b245480b40d40141200f000c01d00c1070482c101c03001c0b034500d115007414040c62808214080d00119001c041c00b000e544010708541c0c01175141c1401c010101040c00300b00742c0115254401c440010000903544004035009c1c10600c28000c5a40000144034955031070500c14250040c120b0a00540209034080304590035a6040715002c40e0030290000801d903000119444409540400b02d008000c155010030603000710340d501b40500e5015292040780c6403c0fa04c1014050040c221070070318001a40c14120607 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 531884532 1250 531883282 531883327
    0x6070203010204081015061403220203011406180103020609060c190303150506090904060b0112050f040b07020d021c1e1106100e19090c032d08 63
    0xd42010340da0014586080300c0200540c00b01a15070006d92881411072800c40e008111a2038041a4060031020b00303002c0d488003030007020111410000d2040c0d030800b041c15020210380c0c05002003107044c0707900314030a41c60101510040c0c8510102c402415182c8820f030101810380b40c00800261802143d003040064603444002e0402040c0075141500d50542c46030804c03020420300945001c2114908080e11810840180d00a035200d80401e0218100c9600e5000d03c4e02d92180d03105200164480c48240180d0740c03010426941c001c0141040104403642d401040c000d8092489240d045105880c2e0304020b0344c032041c040d4138181c01680001c200104480002c81080b108401c141840b103101d1448581611b0001085504032000ca29040d240104024040140c0342c0d000c4100c0c0d11b0348040e241001355516050fa8040c0a1148690032411040c1b49041c1c5a80440c10240c0d0140c00034440030740ea80350821620711101c100c1c0448030114070011901c41e3303084070440a85640310850720314146071116005002d01c580f84 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 531885782 1250 531884532 531884539
    0x100516030e03060906010302010201270f03020f030406051305040203070f0e01030b1305072a060203090c0603010e1b0910030911040c030e0105160c0b04030e030a0c080606030a0b0105060702 83
    0x21881c034240c1c60901c9168011002e1401401c082c0d03040d40006401e6130b885540c000030515000c0c48241046001001c001c802d41e0703001625a01c80d11882c04c040b4a440d41c840311108560000040004505421a008090914030b011142407031342c3d0344000b040b04900088a01e0b2000c9011407001d1866140301d130b40b0140f8039000506002036901c0704800805e40e00020060201d15543d40c460a00c0107040c0c00c00e02402100010241c3d844580d01010b010300314001d0f50040007003401d42c002c004641c000c0004d000003006c91001505668880da502c071102030801c0020b41c0d00d1281c040c200c4c01070701d02d00d21182003111070288000d0070040c900c56400208400400a03140f0a44002d000c12001c1040c554a038002e400e03001c015950045035005140905c0c03401c4070000340c40100389215004011400c0c5c0e812a1100348000d1300980f640c0e045a03140e04091b82c0290828100e81c2c1d050049400d04006c02c01441c070504180c0c4c00d40002c13990b15940786401d02d955415502d0300a8810760002004001510f800d40c01172500070b00c00b5 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 531887032 1250 531885782 531885797
    0x901140607050304080a0b0a1d2e020f0a09080c0901030807030e0d060b032506050c070b070c06080f060d081b010228050301060e01050a1103030f1510051603 69
    0x117800c454182101751100301c40c1c40b80d40030184101d000f41400f400d80d004550705412801940d80b50146665042d5500344c00200d00e01000f0b084180200000b901e103010f480c0400103540d02d58604482c1100c2c1c6e40144840d401058509602080e0300c0740019000d03400c1c80f40500700d810641d080d5160211190403412080702041091307071a0032110303122000d40c1d401003032251901160002c039010416041c00c07486500c1c0090308442000c0c800700c1f100c81246c000111281e900301181d40b240c1e5401d499040042c140c01a101c0e03a0000280d03c020425030a142100700c0303419035582e0041e0f0b02c0300b2101c1408800c094840990129036107841ca008902d880c001400245480f0349441c4c2d801c20b000c101d032800e980108403551058075030081052318148944220068054042c42d10360300d1981030910150404c4030124526040210120703556034998050442d4034044141c8000f103948a10b851030002100c0da10441b0b480011041d0b600030784501d810a80088205480309490341c5003000800300c0300c0d074161880342c034040e0300b0007049 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 531888282 1250 531887032 531887039
    0xf060402012a030801031502181207050a03080d0b0604080a14030418090b06040b030d0c020f0a03060f1508031804090b0915060d030e0907090806070306140901140607050304 76
    0x400c1c100c882c0c490712903116104c0a41c51402c150303c001c0800d000e0182d10500410940c101c0d10400103002d5102001140d1548000f50302880e040e14021341c03a001a41c10503000e01021003404810005400d0202110805225500b90201031020b00c0c00b581c459500e05a106400c11f20020343c080c0408185120000c04481c24107640d40341e80100180f0384820016a990380301d070749506000600c1e21555006c01c00707417024020f104142011031758a0003201c5200c010082000402c10455a80d0703240780346054002403075403004d2910303818588000e003030140c035941d9124901484554261807000218044802102c091414a1654100144005e0f03160b41c40070f9004c5c6d907d1807000300040600b449540500244d00081c0f41910381d001100d40400c44c044c100e030380b140040001c84070020350301a100b40c01441c0181c41c00700d2036456170f03103041c6d500e4242c42d00901454000c14082200036603160348000c049403124a961421020540c0502c10501d0081c0140030f02d000c1d4100b184e903d81c1c105903000381442c81c820740031203260070f55 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 531889532 1250 531888282 531888347
    0xc020c0a06090f0801020a05041208070203060a020c190b150103020403050714090705340209012c040b01060f0c0b0f0105090a0e0a020103110d2406020f06040201 71
    0x806400c60004608951018841c204035190050050004c08000314038110701400c020b4880c0c091880740c01040c080444110041140940981d1340041e0b002d01202e03d01d06003807172004065084810b08082900c44c0c0700c040d2085200907000c6d481d85070340092014009484d102d14035000d50075003103901b0341410380801000001550400c001c4004103401c0500c08581c400100410200e40030242c841010858240301c01180d00c0c0700c000301d070b45061046000e44411549900041ca00e03c1540000c082c0d4450406c5000089802041e1081102e842c0b104034184001030b1002500c3e0300b008021b44014040c0c1c0340c88401070181c036008076061800d03411a410039a240400c90303501c120400d44120761400c400003005004012605100c8226500a1075843c8140080c90f501402d441e0384808021010341003544403407010844c86003020840e0341c52505c852003800542e0650244584045250b600e11a403015068400114a0320214041300c082e954840506542d845540044400c1c1c0b0088182d40404001500d000c006c581 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 531890782 1250 531889532 531889549
    0x61b0c011d06010f05150a181206050907092306030a05030a0e01030c0306030201050d090813090b130905120a021617010605040203061003050408040f230d0804090c020c 74
    0x419420041002d50304054106842d88507640c4418015407900341c030403070110740d68000d032444440c2c1d0340782c03414030962a0040c52040b118a0b601c645150140b1413051410b00810743c01c098860000902210b46c2c0d141c0c0c5a0b407103c102c1d141407080c1404c1081180d100c0200340300c051241608010000c0031a1442e00d4243c96203800c590040c1da040c00850b035911211201035805014810a2900504042040c1440c0d80c0001c0c2581c4580c282125a4070b68036403c071405c1003034a1054500480028140d82140c3d40c803a00c69500800300030142600c284601010340c0b960042c203002e0840d00d81c1d40540a84500707d04907150252640101c8118070950289150040750702170305400c42c034010601c002001075508107600d017003821140c80e13402103030140e401007003004010b450300c013110030809681d0300d800240347c0d4541c1041201c500039500024088000c4500c005580340010320031403070b9285c9031640d00d08100e00c15405c101d0000c50800f8002c2814100344030412040d000c542c8400420003080c01503588655402c1e0006a004 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 531892032 1250 531890782 531890831
    0x12010510231207110f071a03060301090804120c0e22050a021c1208101a07020a030c0e09160501050306130905060106020d020304050a05120f01091a0603061b0c01 71
    0x31110f82ea48841138030104000d0a00c66580c0c0302500386542410a01340da00c0000c08944c1c0d201030300c0000880c1c003c0d10301754000a01030341c01604003901d80340c542c50000301181c0c54003010340d42c845100b80b000c143e014800000c14064548485c0c9200960844810140343c0020720a069a03980500d246c1d21025071100030900014a8152400300340e040701906c2c103000118220007a02040165950400c40001c144600b014252484610103400000003100182094415400c0c001d42000c06041e000040218140182d415603100c403003690103d0b542c1040343d5648100f25903100621103400f900820041d4082c600840d0006405020508000980c485030419a1710f0480e0442c0c1691088004004245c0c1c14400f0400c85405407002c0c62800e4034010000c0c043d227140780949880b840d141554003c820f8130400c23484090b0003643c4000d1100060b41d01380380f410000000e0010036a00b4404c0c00164891a02084941c403642c00b100c492100e25a03000070740202c54002c0740b642c0c0155035846800508a040c45184403156 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 531893282 1250 531892032 531892037
    0x80c0f33180405010b0a080411060903160807050d030813060b040e0604020405130b061005120112110a18050c0c03180a14090a050a14040812010510231207 68
    0x81441e01c105002c2200d40590003042054814031801940706d42c4100d08541142d0007100ca04448002900003410030710038080026414402c06a01001c84800d188041d82280e12900035102d01503910414000800400a8020009001080001d42d00003003020b0040c9114012000042c2800d01030020900301d41c00c010010a0640c000000c020461802c0d000f040e62100c031440d40c642141d402952501003200001d01403070701c80c2007010303c5103844520500c00c0d07c0c05d504101103825155607484400c0c2c2da103c280910191400300311020165001d040011024089a402c0d03031680e4410442d4a04040007000c0142415080407010003134400003e1041001e0400540b80070309040601c00c60108100c3c08103825404180e2041c1c03084805200d40e078444c0d241c16407200000002040c55503820030841e00a240c00000c050803c400c810a2000380402c0e80086c0c0840d0b00110f1701005e50b41d898100304041e0521840b00760000902e80e1900c62202a4a02d0121941803600e030300d000c1c20300c400901141149202255202c00 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 531894532 1250 531893282 531893317
    0xb0c010f0c030203061e030703030c080d021225050f03091c031d0a020a03081c090f02041a0901091a060403062705100e1510080c0f33 59
    0x1841c03601c51b460501282c50700072880040d09840011a486540740c0c400902400700d001d40110030701c00c1d0b07142101c0540d00e80140440d82c4076900f2081d947c4040e030540b080307007001040000e8450010311303032284451441d805454207401c0c003c00102105076a4801010300301a400f5403c1d29006444004030030018501c6580c4000c6001c5484a084c51800000310002c04029809813194501607129001d990302680d410240c0d20fa641c0c1d5034080300c2d41807550884140505d862805c07020406103c091284910890b1086600b4400c040038040c3e442c400c0c000f81640e02d944941c412004004081c0503a1205000608007494030b0200360701500000c0054200d80d009a42e2280c40d0181c1d541404440307146a5842c01e80100b690090000c01c0c2c0312265114802082c601140c0d40d42c07915078203c0201004284030349000e00001c264146059081402c4903500d9104800140c402e5a180030b0b800c0c03508644800803000040c04c01030340e05107001c0480303400f10810003001c600300f410540340d900b075031349141c004040d0403c40049100 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 531895782 1250 531894532 531894541
    0x9040809032e0902152206050301090c0f0f0e131806110406051812010e0d08100303140f040f080d1b1a10090903031d070503070b0c010f0c030203 64
    0x5002d03541016421500385410f400030700590b14202d4900300018201c0c00c090329103222100c40104a40780c40c4003074030300303601208000032481d41c0500114160365420f0b005000c01400a0b1040d1201e20641601c0000304072034070700752a02d82d44201020880c1040c0240586170741c9840d040c1000403551032210000795040d15010100900081d40a83c680020f402c1c100c00346403c0c42d1074001051070144c141145403034500b4000382400383d43c81c140112442c0d4403010003004042c186080265450b0f143c14001004074040e000010300d124040300030b4008490f055141c4501506c0404031180030384c0d003ca107080c0c0d0000d4041c400810610210a0580050280c0500030105a802d030000580700e14602c80d100034a145914600da800100e180e5007582c075401041c0b0026907a62550103002c144c4807400c2d0002d07c801464264588207242c2d15400041000d0824800d24000f614507043d520744660b218003821340c060b8800300c410040820404020070001d042c0e00c000080c1000ea1810080944035940c0120300026004014030 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 531897032 1250 531895782 531895843
    0x180102210906131205070201091d04020a08030405010e010513090c02031e030c160c050301050a021b06040f020d030315030f0b060a15050a0203040e0a050f07020a05030304020904080903 81
    0x1941c00074407991800b04401e45070394078203c486404c500b02e0f01c1003100c04034a104c11a40a440b480e8064100112039480440c0c804d080e00c1180c2c40221416071040119200c00103904001204407026580d060b950b4901c00c01110300107484691241340b514118400c007485c0018607a41c0740c490a040c0800f01d9000d1a51000308460b85220020301480311080410304005004104481c0300031104800b0142c10311406455480c1840140902150300198042d400c00003000000901c0f60700901d468079001c000f00f410403080601165681a00700e84c02814040600e40010143c03a00000f00b0740103034030074640442c0d82e240d131880c900c1400c16030354400c0340c149800301e08410070010070009890380b107001500c1c0350801c1442c10a402e154030150700051000c0c001d001070600d40480c42841205c1c00303421034004903540b134108610803800603c0101c0700d080441501c0c0b808219090310105007000c2c07c60300040154250348407502003002905001d44212140142040480c0203904e003030220328030b0950080c0d41d000c00b510303404450 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 531898282 1250 531897032 531897043
    0x70e0a120c060210020a09140d05010c02030301050a0807080c01050c030f0711041b1e0e03030403050304060816080c0a1b0b0a1a0303120a060f0b030402040609050903031801022109 79
    0x803000c2c031304e005101d085113507079004410008a984c4076158240d0001e0450105102c1c1c40ca00340090929400c1c000d11640003500080154103c179401d560504500e90b4402c003950f110002c0e800707410150b42020717442041543c45100601812a030400a591920303034100e01100c0791b588544811160601e0f45608841c2d589000d00c03404d00c606504c4440d0902402107001c009003170b1492004080310002d400324414400034490185815800006402c40387d4a50b01e0381840e030350300d4016218441c0040d071b6800028007410600e0303000c895481c0168803110071a80320210341c20696049511120304205100c0c85100c19840c4085075a0b0009009002c0383d01e180c01c05580520a86112186008252024074a070b10311689000080701c0b14000500c110038040d80310422031401030f2940e80c0c000c6030341401088020401c09005402180202d100722400c00070280e813192210305030341d021030f49501e00390000c0c40010790f21141d1408c04030701c46401038001881c11180014110504040703da0700080f02c05031104110101c0002c111 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 531899532 1250 531898282 531898303
    0x4050a15090e040f020d030e030a030e042d2406031b021c031805070b1201080a02010c031b0212070815090d0f0e2e0c0308070e0a120c0602 61
    0x481000f07150540781d00300050700c40c40001340282580c80d02901072510071091034054a5000b400c0c0d98400640f0b0500900849021400030710680c541507201400d070110044d100d00710040c0001c009528101c50085000034800042c0140101da542d14540142540c0076110001600c2203480c001071100d0044400d0411218064045066501008132031124a83d201451242d689241c600402c1004040c2e00e003070654040740c54018040e04c01c0385004164902c508000e000e01c5584806da60a070390b1313030303a605980e69001c50384d40107408248070220443c0441d22903c0906c4103409480201c41071245507901003205241c1c115072041c81d40d04105014000b80000340300248a400480d0b08108880c202a4021a2140f031900d030b41c1400d00003001c17202940a405060102c030031100040803418403060485800b45c801c507011b41400f00c181205001900b126005000700400c1e19010b544804140d50713110b906841440c9210103c660054281400241c1c0504281482c40403900c0303613481c002e03014039002019140c0300140a = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 531900782 1250 531899532 531899549
    0x6060603023a0216020904080a0216180f020c0609010209100302041809050f030a120506094005070509060603090c0906040e01051302090703111206040204050a1509 72
    0x42480c1e000664619207003400a5120010b0743ca0314110a004d0341c0c00342412001350441041400c03c030910000001601c1c03801304035003e95200340c03101d250f02581c1d1001400358016441041140036102c0a20354003100111008480045ca890728007400b480c0790110460b4100104c0e9000034011030f81d81401011031442c90201d0a05500b0182002c1e403642c4640650f00182d1a02c9a4401400c02070000401c072a8040006600c181c0f5900c0b000c0d034400400c0803580b0745011408034184404540381e800e05800072032003072003881d08440d6034029502c000b5a50000000241e03038444412500c00c028916100301120075144a0001024180d14000a12250780e0000340407a1081406001b0090781a20218903603000b004100c5810003030741c2d00d001c00540109019604005150700e04030030000c4d04a034032600e048a550084078000c060750741d00a1300704d00346d9203d10360003042804c081c0040b401f20040d80c040107800000c02400582010340782d83c049442c458040c1d005801d4046d03203c4044668903001a98400a0310100 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 531902032 1250 531900782 531900847
    0x70c14060108251e0b0301030b010e01120b04110a180203091b06072402070b0405070504051501080c09040221010902120106050a03110414040f09111c0606060302 71
    0x3040042901d2815220b800072905024003000300084130541d40001812502c00000e4aa5850303080000f0505001d0089030099541000041400401c2c507880c0c02100c0d901c030840c080035540d107a9919036450001e0318540c1d00305895180110b029402d409512841e846d20000c0140c617880e10f080100c0c5030041c2c1c910000d81c41103c0b4078412610f42c803845d048480d00d90304104440305004500c1c07103011001d20310ac07814003800c910200c0d648003000040c50600b0b000701d010b94110741343c541d00c44080000b00e078020b46160007815410504141c541d40100001c80e4000a00758965050800032400705d4160780c09402140d03811250000f5100a801c2c1c03e0108a0141c1900c007402c608280b8400d842c00240041801044140400800e481c00c404d032203904101d880380f03420b248154442d65180b28905c4400c0702105801d21460a214403690008900e1050341c00c030940112070244c08204d08018822428591014030f00007030710380c141c40c4d00462031034050031000304007940d401039548040408119400309401070340210404103 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 531903282 1250 531902032 531902083
    0xf03030f0d15120305031f06090303020d0e0915030f030d05270307060209040e0115090c110d030504020d0b090601140607031202030a020c0111090109150503010905070c14060108 78
    0x921003c0d40c5040d40740c18010b1b0303603031500c03410114807806440c0c2c2c0205a1014941c0802d9650703028841104681c441c4d001c640c6410741000054580446001115801418080020361420182c481d06801007001405546121550004841c10342d40300e40a0246925102c07000e01107002042001054991186000d00c00010b01c1400c80c181c59101d6244060406500490401015940d03503002e002048920802008182134003080c40d078000c1028402c10300c41a00d802d080c902094050b2000324022f001400191454864484058000708000b4000b60780000011210200140c120301c1520b0088030048028517940d171521443c48808200304a00758040c10b0180610720009410000c01e4900c044210b0001da01d07669101a00c800a005d050040043c40d800c02074001540400080203003a10344083c2c3c1d4409041c0d890f8401445427401100390782d400540c080004101e81607590740503c1d013002040c40c2c0400c08800c20384400010f80000c6050740d210360081c0c001001380c1c440411400c4a4011410030b00d0740691072 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 531904532 1250 531903282 531903299
    0x110a0e04081207112505120a030e030714040e013c0902060702120c0d0c0f050a0803031303051b01020c061522020f0c07031505010e010b07020f03030f0d15 68
    0x1405626981707403500301d21041207502800f01c2e18a018000c040c207900c1110446d002c886944490a46040c1c001c141c2e04010440942800304602013a51060000c0c0501c1c1c100c5881403000914404945c00359079542c510005144000d642e90210304c542d02900c000440350b40002404801413400a0022001d0b03203081e0451005071140000e031000ca40d011101090740d600d181c1001c9040042c450440c60f400441401c407101000810b0318000190b420902043c800c6540b9103084c001091344034015001598820700007d8010104d4501a8003180e01c07a1904500300300c2d9540000014144100b00d441c050b07500854010500d01007005220780c4512161344101d90081110301207000f60084844071240703041c03c98250440341c0c900f5011123101d08100840d0b41c1d92052510b040d19250083d42c003040b945200f00c40d1550071302194a0141905890903010010056440d0030007a8a4582c40003604030f03005940b0848018403036906101510613100c94096090703440e014440c010049640d280610012403561210500c0542c8 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 531905782 1250 531904532 531904543
    0x605071809090c15020a050606030706090315060b04031a1302090105010e0613031b17070501050c010902120601141225090507050a090e070c110a0e0408120711 70
    0x2451828005a0700c0d00604000c0c440183d140c00040883d1100c5804100d12030340010004241406142a900c0c80d0b20340f80100743e181c1d0841e02c108000211100c40610104d8081140320000503e42400018603941c3c90002500503082a8400d4a460100300d122000290240c0710959000030000c0429403041d0140d40014004138060140038104401880c452407240c0f503580894480d0b030340d807005c0d14420039070702e1402005120105080064880040c40005081032454007840002c01a0b1800751100d14240801180c0a0300046c02c4510590348a0011801588900207140c251404050140c10b2940c1040011031a038800c004444d80035142c650540042c2d0000030402c0115044a00458024611012800600030300182c0050034103618000a000f0003d42140c01820320303051030f0302c505406030758403030882c48030074011154007003c10409404d010000300100b0b401110914000c20300c0b0386507500c8214580110f14201c0e01140c40123000039000003461011810950b204001e4601085218503140c122610355 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 531907032 1250 531905782 531905789
    0x240e0307150f020d023c03070309030504172b020307020405060d051b0102010f05010303170702070902120901060e0105210a14150114010c030503040501020903010207080706050718 79
    0x2103a80d0070b9440c44402e91a01111314040300d00c5000d544940d207000480c200c40c0c1008860b1b40da409141800900442841c181403081c44002500d014216500d6a0094014040b05403040301003180802c404690746141070400d01e482100b400007030482082061913090f82800d40c880782c80f00c4911500200001130f0740001190407095041d40c012540c0c4e00c440d000724046800140c0300030800e01500b0000c0c0c0780003d14001c28142d0f10300903802031004a04a052460880720f00703002c080d0014071100544000051421402a00403100d44116081035a4480300c00d01242c015490000703000038010184842c00d0003d02510019120080c1c2c1c00006524060000300406042c2038848443d040c40c00c0221050310341844030f9424603800c0030f20405002e108138401600c4100615420f80c42d04403040000c600348a007007034010611035068542c900b8035001c4d610241c0707013030700004d008603010345d020000d000341624280058030040f40301c1c085113038541d00e02d072600009841000b41400700300403d0140b600c8181c1044030726001103 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 531908282 1250 531907032 531907073
    0x20c0114030c04330203071514010302040c0c020a060c02030708060c190903060c080a1508060a0b0a120803010f1d01060f0e18220807120c240e0307 65
    0x6208001040342a203c1e0840400000115107004e191166402100405020740300300c400180c4500f81c1c90500044804804143c45015140e000600c01400d00340e0210313003400c00c01c2c149082c002945d940003401c9441d0f070303401c280c0020710280c1042c0e0450500308004d101a1080c10003419282c0740010700d0011a00404151101c400700385100c050809005040c040c0c003964010400b0b01c00140c1c9000c000d001d0306010380c1d02c410020700d40307201f03691b80b4408000d408040c0e0364100083c08080d102c280b8140301424000e603001394803954075a0006281820a104500b05c80d1045402d00d44a601d071004880c0f01d00c0340b9900c841c0b81240030540c1c0320b941d01d840c850741031705456039401c15011050014400712894902000420340001384100480c42c2140000300c81842460209017070021629000b80304060451904d80040840b182070107c0e40c0020582903601d520150349280000c1381d0303503954591805500c041340141042c40c80307009105442c1131450041661568480740210f02d81095643d50078981010214504503 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 531909532 1250 531908282 531908309
    0x11e0b131104150f08090316170d090f030201051006020705011209060e07140a030b0a05060d0f060207020315010e07120f0e031909120803060619020c0114030c04 71
    0x40c07804041c0c01c1d10040d156800050305640401c0e0720203070072442200d0541001c1001c500020b000610000200d0f80c10600e0410048004030240d62402c04105289801104255050016104034215031045034107050107414124155a404e090103230850318080d16460001c60841720600000d60001031401c03c0310420320f03144c40b05001040f0302d03100030b00300241c0c01001103041041d101e442c0a0002140c1064a1f40080710382401c040031000c02101900901c0300514090003d80090391050071030b484181d010f40c01070701c0b11140c10491341d9002c1c500b110a1908440103030380400c0b80c200b13505082080c0412961240d01408040d410240b44119500b0018055010803100075034001402020750440b100f40e00040c14140160107540300e44a803070f0f400000194400091203040e44c82034901c00e08041e0f040b116110428030720310303406845a42640d07000400d550382100c0100560540c5841c1c00c5040c001e109102d50180010881031400140709000c0060250100c00c0c041c0300744850070f003086007102c0c12030324a40d03003856 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 531910782 1250 531909532 531909551
    0x1805012a0f02060703020f120301081b030109080724060e04060c020f06090708010e010c050306060a210e06070f020d230a1707020d0c0308060609040e011e0b13 70
    0x70441d500700c1c02074014002094410815400007081c59080700b940081e109600d160016070200c9000910618429600000000c40e034008103a80c0056500300c040e001203040700494072605074076444141c8c216000464081050010410581d413034102e0020000306010880c82c1c00c140708442400980013408075646c644840c1d1030a40208030007100c429210058038070600d4114403560b211050752103140c40c103509040c1005203548c010700c90041c1c90301c02e60300c0301c50840e15100240082c94015415074001d00855400d00d0010030382580d84012003440840380401c107107a568201c2404c2c1100030340701e00c00344003440582d6402c40780c012810f0003142103030b49005440c041990014030342c0c0c8980c0c4030a040031f60000042e5495007a0f4062542c407103401402840c0c0380c0d00e494260003282c0d11040b080783d170340000d4005005540041d105001d030f59017010008118a00b010b50410000b0200c460750311650341540e41d07451038030088a0a5000e0380c203c0d0100140204895a100c0340820400d42d190b40014030310b10350b10401030703 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 531912032 1250 531910782 531910793
    0x702010302160b04110111070302180402030f0609031b0a0203100203061503010b091f022d2d011109100201091b030218060627060a1805012a 62
    0x21107207141c2110f00200641028100480400960703910340c2d0020341072142c119100800042e0f031000312903004e042c20222540c00c2c840188401c0015000301c0e410300404250740c06407441000744500420100c4040e6681e428900c400b02c62083d48002680710b160003400e02d10001d643d010030a0020081e070340700c015942c0e41d11800002d8130504140da5615400708040f00108003003a008001c1c00001e202928802034000c9856a80074503c1c5d034012201c0c0050f44120b640c50401180b07401441c04640140545140300d8214181c0941802c1d400ba00788441880750f407013081815441c6d40110350038004240e008002851003035401d034400d403040000c000e00610001038003010140c401d40c0031003940c1d504403601c04115400e0403640c2c0289a4a80700c240c0c441c5100342c0b00a84040284003106020350401410985000d851201284d401500703080321121414004025001d9526200c0040c290044565111034401010803501809900d440e0480c50411518054000002040e18070306154039484000040010b0301500d4030 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 531913282 1250 531912032 531912067
    0x302090d050a1406190905010b04110304020103050a1109010e1207063c08060315090a03080115021e1009120e010206040c051c0803011410050903030702010302 70
    0x400d800c4000820050140072001c20703003018003449114600030840c001c50040c0c0d56904141c51201c10036000044564070104694000000b89102d0400420b010881c1c00c0054103c4801c60f401d00c40c0300f000042040110345c0d0501c1000e41c4140c0c01031040042482d028542e21150041852403818004a400c3c548007a40d181c10040c00c00d00303035100849030b4158841100501541740050700b01e5210002c014005d808494010420038501515044422007a02c012012120581302502c1c03160180079040b11f4106004e03c900ca5244100080f90040103951218640100400c0050b4000801c900e040b0400c1d4a40c140c1c0885d040c250700c1c1000c1085c0c0030002c881d94000e0b0600030807041034800f05150510000c2003200596110410014944545c0040d08200005a0720780c101264014540440030384180040d1921141c82d0041488892802074540e44031342c0d4002c0b80394000e8102d0203051a40d95404180c501d4428030410117003080703152a909203000d107008241e6078014800c0090606030045400180070044101 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 531914532 1250 531913282 531913297
    0x510030e01020a0201060f060507030c020904020d0b04030e0a050103050609130804090911040e0303071e0203040b12100506120c0a0c02130b0307050a030807020f0315180613031b030302 81
    0x21583d44207000c0c4040e00820040c405c1081c911170085c40020f110b030042059503100c1ea0161204150ba81a990800803480001803080381e10000465a00020800f240812480b403440394907922000078003d0208540c1d8144c43d4031003810542400c0c2006483d40380c0c22000d6400031012240300007841d10500c3d14203900d010b5500802211803034058160203001c8510b040f0248460242c40030084503224914841d1280301c1290041e0100714900c100d0000090200622a005407080c0306803410075403907001b40716196006000e28030203001144180510a019514400002c203812606039103004074020310710003450001021000c0c2840082050009070313014541c0c069040c4d078020045e1a000d44800c81d544c00400b440d0b800b0600920031854082140d0400e004014192604110020706048440d0b0030801204488549160140140007520040050001c0a240105400c2c1d04080c260406404280c0c03800c0c0d40200b02c00c006c1a002e80380c510109401000e41c0149140326001043e04140504099001c1c0c40380c5003 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 531915782 1250 531914532 531914561
    0x150a02010605223905130620010e06041515060302070b0106020601060509061c150602010b090c2706030c0409110f12070e130f24051003 60
    0x28810111014801c03640c0c0142d0194843c100840d0010045025414100340002c3c032207683e8081c014060480c0821640d07540c0012071030b200d0726003e2418908007141d40b42c0da0241001c031f00080c2100e42d80e4551640c0d00a241c0c00070a000b00001044107620b140c0e00c80020740058180c002c08260400200b2080d00444406041d41a180882956a03180207000b50300c43c85080da403802a5000118640b0320100d0040d0482e4000e83d40d03d03003004d07419000c00209a000e2070101404102040c0021152042030080c01e06c03d441003480c010041d868008003900f543d281810092003414040100601d0030700100a507140c01420000800180c0040d030000e16075042c600600a5104201100300624456034000810640d0500381e03040c404114031000c000081d026049103034054203400c3c803040001512001100740d00140c2460280c6480d011100030a60040c0c0b0007003c8c104540d02ca20715803c0e142028002c10301060078419040186c4180314001c0c4003c0401409414441d40440c210341c1146c901c2a080801e002e010314 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 531917032 1250 531915782 531915799
    0x201050c0309041d1902031221150102190c0b0a0320030106020d051207030b1906020c0f060705060a050c07140a020a06020312010612090b04060c1805150a02010605 72
    0x2d816a54045184d04525403c92040c0304080c2e00f031000300e0b204c0308086907014000b0090a2000d100323002e4a070700402d40d08041c07880c2d164a946c0c01055109007260080b44c0c4001400c8880080030002814105004c000c07181e12100ca10300c101c0003445114000c0100c6010704005500c80403c1c02c4c1c120058255141c80d07100c5074000c2c11503a480c40c0148002181280c26039022126054040f4500352040c1c0586114801002240c000082c0142d000741c2002e0b50421008180003004078000d020443c18055039085140103a1201603102010309200c0490060440100c1c1c41031b08203c2c00742d4403213136903481c010812264142c5400205d42d50b444080183c450140e8001200f071041d20034a8a20340d6580620384c401d03441159001d0001039018004400c1f514040250850001c4603820b01d2010340d0150908806610643c0e503403140100231610141030306000d28422000402c00c9c4c1c450713203001000b040270003260045440d04050200155902c02c4407288140c25000346540e1500030400c000c1e4010281a8080ca400c414807 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 531918282 1250 531917032 531917051
    0xf190f06031a0a0501060f020a0f060e03190e0a080a02040f06050d0602090a0608090615030a1218090608070612020f04030b070807020c1e1201020f04031401020a09030201050c030904 80
    0x35812480e00c2030307480380d100700645d03a41e0b04402c031451900c244c580c4016801204405020178490a0b20103100c500480011507032800c04080e952941d440610368409400385169645a40c55000f4105005100200e4440c14814100703503480d5228290703004000e10542c2d07a4040c82803181110b030030043c000c01008001210b9241c250500f88083d61041c0d449c0c9200e01044500410b21038050000c0c1c2e405045140c008080d03694914180122009a001e03d0550500c200345c038090014506030301a8240400960740c0b0410444440c901c9012007290382c020780381c000d040020a2200a80000b6018129144e6107040305968024504080091084498000340e00c03800240100600c41203001542c014422a524002e40d43c1c0d950800701e8940401042140c1d00c40c1c070041c541e00307203186600d0180740c0341c0800034410801c01006246040c01c9074020000c0703101d030b03841c04101002808170450810114041c040300a51500c100000001c01e6000b045c04024144080816107000d0241c003001558000100a002085280c50 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 531919532 1250 531918282 531918323
    0x1c030902030c090106171003080f07060c30020d090326060306040209073605030a0c1e170105153f0a0c030203060f190f0603 55
    0x101010507030003481035414400441c00d000750704904071111075940344c601001c8030f50100150040a80070340313900300320301e0b002201190302c20303004209c0a1100005560340304054a411400e51380300409171070900c104841c9021883c1d211442c460384001802e014074410801030b80c0240028083c0b030002d40c20f8a40740001410400d038011480c0009210145d0484481405211403104400300468141c0d402d90003503400b107401814020320180d006030150800010038070008507805071500c540240ca070b0700d00c2101c90441c080050303c1c00207080540003d5014144250154507034900c401280c0c440c4c41c03c0104146c01c200c031310103040400400503001e07010480000f81d01c01c038030041c041c0105407040c0340f07088c901c450381c0c490030f00d00041e5004096907000004071343c3d0042c50003030821700000b443e2581404940518048020b40d010b200580da05842000a00300d401d00318014545021001462078140c104141c003403150f5140d0300342c540c80c0e46414010000c14000a4050400060030056000a104801e9078003145500f40 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 531920782 1250 531919532 531919541
    0x806010b0d060e07090605091513141c0b15090901020405130605010c02220f02120907030b04142e0b030c0d0206030406140903030a061a12091c03 64
    0x180640c1c020b00042e0b444031842d1610070401e480f4580800d02c5210f0030040b0f140100c014060b1044000c240c0c2070743c0a9a200722401c181c0c0004041c00401c01a5071080c0004013848003141403060007525021104004600d00105020400700050401c41d05803001580c0301c44045615085148042c11a40d03041c1080191325004c0c2d0418004c251280454000c10b86481341944074150483d401650391034851a059002d005400c1c40c1c051400780d40700c50006040141c420103000d00220100030400040e541c0e840c0c2e0700034115030700703011f029041aa04088020401300f0710f80200660840d030080622401105d411a019203010001c0c1c4807400c0303914036554190100d2046c80b441b0481a41c02c402c0501c690800d5404068aa8420301000c4e540000410000405401d1000c091680035100e113400003110480482c3e0540d00b5601103400c2c1c031042c0c0c07000040103001442402648020301d483c2e001851110f5030444101308600944140060b40e401e0700000034141c40301000500c0581035403009900000ca0b030298000c0162 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 531922032 1250 531920782 531920797
    0xc091318080301060e240a02070b180114040e04030f111606020c0a0f17010f0e031308120d02031306110c2e020a020a0b0f04020a08010903020c0108100806010b 70
    0x691160481c1c1500e08000c6c544c001c400d400221064094080800c0c00d40303207900302c200144110300c035169010031100424402841031071400320002081d02d4550000401c0c6640d9802801c1040c00140310400241e050003440c5a002a0305003000448403130a28811115001c14241d402614460908072502c1d26492180d810140c503465401e560710281d8090070300501131064407505110b04140307841040707800164260701e58004100400440d0030020800380c2c006031002c84200e103160350000140102d10b06d000504000c01412801c024082d8203400b0f5582204a000312034030419500e80002c0000e4503c030076035030305554803544040b04010100171680c0c1040140c101e0713082c0151a224103044110011100342034005501100381191a46100b640440c102031340050010030300b50300c0340b20100b10024582200180c800c0c0d62814402d0785070303c1c05004000300490a40e1021166904d04131010005c40c1d408191000701030820300340380c3e8594542d0001390322800e089034000502c0e40500800412101d00b07010040908 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 531923282 1250 531922032 531922037
    0x203010e010e06030c0d030f050c0f0d022512020a080105070c051e0c06070f051e1005240f040906020d0501050405130b040305040b0307050c010c05030c09131808030106 74
    0x582c0d651040c1945d03a0b0b603060409034421501c213012000a4030075008902400c046c1c0c40c003681814450041a447e081c5000002603031500300d082031400705036042004a000050705c220346164440409810b0170030025074081c0c0d40a860303101d800b950a545908540c0700c02010000c00070001d610f48a03100500d5103021000032211805230140e4840000c03d4081000030b410030001c0035212145050007049007a52200e0401c4600f60080c42c1c0728008284288a0080c049201080c501c490b00142c280c03035403c000d140501c0b450043d00d8a41404820306032000c209401c1c404074440503241003640c10005000241c82004258000d040c8007100080003c5600500200c1218074414041030b62540e0800094520440d4101a004045510035012030b1305062001c5d0410301030b0525a00d072680f2207807404051740c400c484580100b10000f0702210307040024403501141c0c040b40d180c014111f00707241c024809c0504c00c00b030b107103407143c0e01d044104125205961300c08440805420019a00c5072980d14210040780c000b4800c0c5800b = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 531924532 1250 531923282 531923309
    0x209191205120c2e02030412090602070f0e090f01020c0102040504050f040201020c090703090203060f240f040b04060b0a2001090803220f051e0a120809100203010e01 73
    0x4000d00380c0070340d443d8241501c0074000c00d02c281598801c80018010503600c0340c514000c00c41e4550421480118055400b90007403020b02505413001800c0203040d47e01600c1150b100b8201040650380000d49030701552200d040703103005900c50302e0006107000120b00c2440c425510010f00078122942c158000c004580c802e8406204690703403511030303008080c41164082d001d80c10015144c035440c500341a4681c1d1080042c04c0000e4010b460b40c010074034201003201c481142c440140c0c18020f5100d500004001c108943d03407602504060128041418000e52000c0c19010715114034140505903203e41000002d0805044000c0d01e5102d000d00041020510004540d086030705042c030711803985811700644100d47e410060a5140d51298086401e00c0700c100201400d1441c2c2c04070100000030030100c01c642d082c40c0140c0041c409050310448560002d81007010070202c0d40d010307181000004041c20074019107e000390070000d076030341d480300c41d0641021107071850782100510010010070407a035107078800b905032101502d4008 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 531925782 1250 531924532 531924553
    0x1060201061d010b0a120903090306050a0911060a09091509180503092e0309120905090f042d0314040509060904080c01180204050601020319030209191205 68
    0x2420700c050202e85000440c1c2401405544140002440c0e590080e241001d680100300078060704856281c141240001c0c6801000c0080c400309028994110000e604100101006a500c00c5408040303080603c0c0a0000400e4115205004400c0b040080107018024411164010384076048810a400f54803902031510b1580030000102c110003604c1c1c00d038030000079890b004841d000c1003001c4100ba40e60f0318040e0242d0740010000000328100080302c4140d0384003c6a580810700d4a100000e000810b80001c20003808003c000f40d90714500704a030000c60701d000e040340c16240c0d0b003012611040c2d03602d041082c44043c4100c900d0b080859000c09003906001c3c2d91441407501c510a000040c42c46144200c07035002e1509004100305191003d800c581141c89621001c2c90400403854060940f809025624003d80102051806504250141d81e90111091001d14540111008a05056840e0300e10b00c0003007542c0840c2e000c0942d103488182d1080401000d08207280075a84007a0030050f0310400104a4060060321002d0 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 531927032 1250 531925782 531925799
    0x8091c1803051e030c120f090a0905040b010b0a0203040302090a090c030807030f0305010b0d1a1309021302121f080601031514040c170c060d0b1509030c09040f0210080106020106 78
    0x44005e84030660140801e40348125074009150412401c04c44030910800c40051103903150480440288042240801c2910709420312600e6040164031504416604100c3e0200407076001c0202c0301505d5045a141240e511080380311002000c1c0030760014a450351551010090160130006000400d01c82d580351009440c25250440c1030310020b00c94030f590650284108000340d00c0d240c12280780c01070200300744081d0001e00300015800e0760304031800191032581e4400c48006c0d401d040c0c0c803280c41c0070750141041d4500040580b1401c0d0401008000c1071600280404800705c000020345064001c2402e802100d010b96100e04041c0441d0341134685000c0c003240750405034140031a40d604245e121315008054218014541505001aa021591002d042d401a10340391307507050380c9080c041d216403014820f000034011441420301c00448680e0a183e203004600b4040d2001603540060324404c10780301a10201030a80f501c3c0b0705502c1070810030b0703802980000084080032403d07500c442c00e81e04807402c035402844450354074402c0 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 531928282 1250 531927032 531927037
    0x60907050307030b25080106090501030b09070c0f08030c09010305091605040c120f061e030b0c07020f1f0e0a030812060a030203100603020a0608091c1803051e03 71
    0x80c550550455442000410f2071050743d1170b48040301c0c0701000c00850300160302c421030b020018100404281240018010140d000c40c01c00042e000a00f17041000354465400101480c60061440e010058200340340b00c10012103640c01400981c0c82a00a61a0b092840741100d40b608440000350020b46400d0005105020000f8a441c504044030212100c06081401348005441c203404002c0c1805281401ca0710764050a104090b5501c640b84e400040444c2003032186180c10440d50751480000c17010100a1010405030340c01690046050041c1c2a65945a440840c650f5000e5201c03ca510030f0040880301c586a244074991003502c4070664902c1c01c0e4200c184104441d840c003a010241030070350103008007500a8500c508640c0c00100060241503802d0752580040e20f00308410159099880c0c8502d400c20460412075182005000b0034141146546841d0701c0079562800600e0041a640d940013a19446090183c002c00700605c90290034003c060340c5a0402580c0e8031110380c007405400f600f86140c001c007124007105 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 531929532 1250 531928282 531928289
    0x301060201020d1a01081f15050301090f0e0d0507030309020a180e010204060f050304110904080d0c051e0d0b04180b1e16020c0315010806100533071103060907 70
    0x5500d203c51f1034540c850f80090402140c2e600a803c2c0301c0802003101c1500030b140d1546241180d07030b010380e01d41c100884c4500392030909000c050480c3c10500e80842c0c0400226011030b4100741c52402a07150281420304601405802902035080b1920650110b0110350b506400594102c401c102800b400c5040c1003564200d11451042c0781c0058080c0a15243c4584642c005540240c06407180c0d0300506c00c00c3c0b00082d00c444c410346089403081400151001e0380c0f880c90007081f80c8030090f410042e0a01c060840a550350102404220382c07200c0001949850122940e440722070820405070081204801d440c280000000c14000b050310b680c02014001120858020000440181001111700c11600c8035202e01d2400303e1180b003d44254010107540713502a4a042000c0c010840010a0350b0425516020f113440c00c4c0500074116032040c80350760341d0502c19030701c42e0344101900100600c0d480302041c5500c0d48071a90010348003042d8139404170008200d001c2c802001d0040000000c1242940c45903280c0786002d6079129910b22 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 531930782 1250 531929532 531929537
    0x302010c020703081803030405032b090605070206070501140a060513150e130501181e050a1b05040e0609070f0311060a0507020621090327150301060201020d1a01 71
    0x301101801d408a17103046001001c3d0469091a86941c00203003080f91010509000701d113014220303030700800302d440400b00889103401c01007034203804e04500904501c942c00300070380680d8001170141c1c10000c003507004400000b59200c000445003485202e80004d84020321605109100c1c01200d1041001944078060450062500204d4003d117050340002440c100103010f841000c10658844010840a0140b4040b0541c0c5002c000c0d28800e0302d01c5c200a007040c0e1140000820026610080002540080c107401f0340c0c1d400540b154407404400c1d58101c10441030f50040e503049410481d01c40c8124800160460150110700d042d514103e854020101c0510b01c584800341142103504880d154508000c2c00420001c07050b840c00c00d140c080c1a402250243e4802d90709141c074041c0404407984080b40030601142c00c041c880000d1032611080129200240380001c941308074007001c00f520511140d952050401000e4403104c8651b440b5a135800c03019000350820950640003605160402c90320f40d80000d41c0149056058 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 531932032 1250 531930782 531930787
    0x17030c0a020d05070e131209121103011d0601150c08160f0605040b0403020c040515091801051807050d12030b150c1b0a241e0306030302010c02070308 66
    0xc1d020042c20000310001918103000d90304001c81e41c6890b400d480380c41000e0003c0c41c44240034607841e006100344000f07915a410000d42c00000e00440c441c0c9004170103140e03000030b0020b459005680029006051400404103445400680c24441c0840824074904807a0419007803400f0000e803071410348101c0e103100c9004200c42c030200808604140c01400c03071828180141c5200c80c14140c036654602c00c648090301d0560340740c0705ea80c04000401d1740c100203043d078581003514244500d00302680c00798448082c83c14054416442c002c0005c01ca8014149010b12940600d40203020342d0030400804c04c0c81403036017948450107000d00b1a0118a1b810406440c1c41c440c0d078400700a8000d0180c20751308400810150110030b5200e64035102c900700308807070000a0701040030780001610ac1085040d144e40064018034041901034681c6c0c3d0410400256888000700328644402c9402c2c0308100d40100c102d45810703010711100101000c50178019401c1e079040c0d024100b035074480d40082001e2000200d00b130b6070f608002d200041285508 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 531933282 1250 531932032 531932053
    0x2041401081518070e1803030a02190201060609090b060904050c0a0f0c0b0a05070e030703050319080f060f060c060405060403091e050112060e0c1e0f2502030a0c17030c 74
    0x5c9000c030b941c072002031007081e40d0a0700e040c001c40b815070b401681e100c00481c0e004900b02c00300d2002803940c0f4141c245203000070451289080f1015000c610b05100b81d24190b903450200000d944c507100111407200d880284200414078040202c86102d030021000000061640d441e009031803402508422000c43d040103040c8601e40e5410018405800024660001c0011521001035030340c81c1001342501561048000d103440d010f142e0f4001425451aa020300204080e40090140e2409000c10460700050281c0c2d041000c1c600c3c88010807264890b9980801c00340c4036000400090000206000c1d0250307201e5a84c290711960f4071004011000c40c19043c000380340002c14001c001c50340c010045504506070410011502c199501100f10403403c0481d072405d05046d000a480e0050b490f94100701740040d50306000c4170300b01041081c00700319a000d5036504440c01825010650055096040c021517003039401030444101244a01c0c000f101c55a0311701c80e44400b580060030704d1907402004405d17248a91008801018078005 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 531934532 1250 531933282 531933299
    0x14010b030a090f1b030b07050a09050d0201170114010f0e01080f0603070f0801020310060c030c12090f090b0f0108070f05030c04080706021b0d020603130204140108151807 75
    0x30840001c0b40c040c1c0c03990404000248882148a048104c0011070100c69450341c14003514014000f010f0030200a400c00000d00300903003210456080c0e40d0f0a90300346070442458801628107000380180040b201c0502c10000902451400c06188211003e03a10350006d02a207840541e80303980706c090258003164000001880c031040360307040c1c6a44080d0040403159203c0d55000ca2803010013254001d610284d4000041121040d025071040d0020420392808403c2d404242d2402407120b85001130007000c03039030282240510f6901c103070591342c0036018440840e1030f10b555840f00e61004107001702c00c2500036429080703204121360190041354070802043c1c4402c50594030b800703001c4959900061114807055024403010400030001c2011401404294000744180c9074420042c00d180c0402407602d07442545101100c0e001a11124180c03a0130000a20039400340640c02e100160160405240701881070340d2080001514000000d9184c04220b00c00e40c07007580355160050590784811100c8040511540001020000e640 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 531935782 1250 531934532 531934541
    0x20d0204090209130201090503060f1603060504021605060601230915070b010f0b03070e060a03020910080615090a140109090612170c0c01030c05130e040614010b030a 73
    0x1840100000741410301a070000381c800c50151014000401c86403142d10855030441600c07006400104e00400b200d207460312406015482c018200200501010000b44000e4042d800640107000010301c255117844101381c540304801280c042c16140e41c4680004500c00354002c1051520321480e892250442c140d07590b2000c20950710140c011038010711000b0940c0070f0224090b0280c03421910407156911a54581026024582219006920742500410500035003130340000e001c20310b042c02552490740b54030010b5820350090064010550b00018884840c400c09175000f6941072050900702d522a00c5e1250070300c50324000f0b0254800185d00604c00d50700a1040030404541520b401c18145071004c1140e84178088001035071b0807603010201c0c0300c00711080f0000700040301000000860105400d141000941782c40d15544101e400d03002410b1690f1121031040741c510500464a44190324008070b082c0c580d4542c24000c242c0f00495081e130701d80d4035103402a20300496019540d4101c4400c0d880c82810b40d05c501c6001070090 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 531937032 1250 531935782 531935809
    0x507090e03070c030c0602061e01050120100f0c0309080405040f0213030305030702150906060d06110c071404020f1803241602071a0c0c030616030e0c0d02 68
    0x184401c1c0225800107082d90540b0f000303144500e0700c616141d450150040d14040f401b92030308040c02c140f051182080410100990304483c4240b03041c20303049000c80c0c0441c1d0360b13104410710384003140125602c007801d40303155401550100b00649010480e06100e102d0440c200c03030316104001d09545003000204081d01e80b9400c07031a14840030b088014a003044110280041c0742040c1c1c01200418004020440030740d40510080f024000120b098003000e01d4101e0000f46c44110090070031b44218061300d1414140000c6078088110325084411582d036920061281d80c0d62241c1b1403040c42c0d4441800da01e4102c075403c0c00c0c025220b0a82c1408419030038824040121079241904221480d0144102101100407080c3d603030071240401c00b00040190141000e040140204000080e01400d5601c600c4042010310b585010340700341071031110b181c1902c81c03150f03800c9542426090508258940302d40800d0229040c3c520720b06d98008a90360700d08100042c000007886450b601d0380800782c3da01002002c2e4407805401e240c410441007 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 531938282 1250 531937032 531937061
    0xb0301020d090b10120f060c030e0d0e0f0d0b060d031101230f0c0a0c081608030f090f060a0c02031201061e1b020607020a0b03040b22050709 62
    0x14401c29032005030407540c5244041d616100203905200900c40320078074590280075401168000302c0761a440d115003031103040000811082c2d80c0d50032100341a100c0e52010780d200d5030342c005031004019107040092180c0308802445100d84800714081102c0e2410700c0010240030780c080b224048940d07444040107540c540103202641400129000d06041200a10940043c500d45952604200098181c1e034541c00c58000c01005404400d00140070b211100102500d41d01602031070144038500852030140094090380060151282010918504001e820005180b0030104015460615611801140d6840910022620b0a078204001292803180d0680020505411b140116450070040e050400c4100c4026400040007540000005034181c40c01c0d84041d400c0c80840c40e010141c0000b0b0712800519414242d4000c0c8500c00002d5a131701113488440400c0b00030011500010380740d01d07140c00d16151840084a000f80d13000000e610a000c00e01004088507126078209000b0034845080000c4540103103c00390b1455003 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 531939532 1250 531938282 531938287
    0x11b030c050a120518030a030801050f0411181002070f06050f0712090302040c092105191b150206070f0306050a09021321122114010512100b030102 65
    0x200f44101070741e488649181c0d884030b03581d0400d16044a440c0c1d90300c00c692886900502013110110741d000b85618155202150301c2c5840c034800300e00040040130030400c0c40c4007400010a4045441d034002ca1108400300007541c0364031180da00c03110100d854084038060030300c2020b041003091003c1c81c0b00d800038010302d490540300c1e0f034501000e981320520b101000424580005039102e01c28811810300e4024042e43c00d03400d040c00ca00450905100e00c1c08840e12050646102c10405004014080c0400c1402048203140140071072001c05410015140c40c1c01c074110084120070784400141e900011012280449821b07409440c4a480b2200d084401c440c00e41b400000305900c070130000c10701b556881960001460b80010059481100c80004070302d950b01e5910056a83c000c640b5003e100042c1c498442c0c01a0350303c4414540000c100250656800040b0350741504051141010340d861313090542d02520b603007184207615180d26a071380c90401903510440d007179204998001c0a014400520550000207000200400250 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 531940782 1250 531939532 531939553
    0x415020a02120610050405270304030602220803030103080a1b020301060b120c090123070606030807020414070f2f070f0b09060a0c0f0c0902090f011b030c05 69
    0x80142040c5000041203070001000c1c00300034032001e44c00400600e01a07a0900952a00c002d01005030342c0401020070060085440c41d1780d05070024421075000e50350180e4119251088110840341034a0003156243d100c0c03840fa000851041b80000590703040b05e0380541494541900380108640080c00015883c16070980c4c01e00c03600040c0e4083c095000130303040c44113005841d050f034540c40d0708040f40e024050b00d0020780100941c203500d9034031520400c5041d51040d0040b500311010b200c60b5070b0740c0c23040d0740c0c000d4010b52030902c0110401109000a018407802240c0c03e10500d25110003070700d030a00701a02c815011901d0200442e120700c0c003440350380400c5100341e0502040c0141c0b103800040c2040750800030722030325041030b10103115001200c5030720340181144004950030400100081040c07841800307154420301c200d1303c0a04040205d43e290640840381d1104921483c603517603040c41400703500031a403402d100d00420208030700694803c000040b90241d10074140d0150a01c02d07141075414802000f410f032650f000d4900e40d007 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 531942032 1250 531940782 531940789
    0x3091e08070b250308071808150408071502030103020a15200f0111091f0c020103020711030d020c0f040b0109050f151603020d0f0c030f03061a071b05060415020a02 72
    0x40f4406000761200d841501d00100d00038280700e0a90415419800059801c0c0b1109100203100d843c558050f42c0a440760b5225402e0015050291100c01081c1d10400050700e41d002800d50040c6040320b10a581e040f4009803607082c0c0c0c83c0b1301c800510000c1d00207020020340003025403e2402001403407801009403a0000d01403483c2c03a095810640381d850350480c00240742c08540c10000b04c4031a50f91031900602400b584000b8004081030403001d006810150041807003018404504e24030648070304010100c9491710041c960103529046100302d02480341d42125583d141508280c081e6084410050b51044d07165070403e010048240441c1e20b01541080103940b1444101009100616900707218049100b000380e024a0000c1c9001d44090a202c00c11a402601e00703091508038201d071040340d074141002d0305d80d4a11103004030010704142c2e2209001c0e03444a4000c0724043c107100c00800000b0b00808001d0b07075002c840c12003800864900d11895070400d004000404c002e1040001d9111503113410310580b0300d0020b464000 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 531943282 1250 531942032 531942097
    0x903010908091c080a0f0909050f0a0c0201050c04031403040503010203130b060d0f08092b060b0303030601020d0810050d0c08010513050309041805010903091e08070b 73
    0x4644007640050303040c100b842c10840000562009218400c01c0821076604c00341c20f801881031050500081c0300a50620078090f042d000302410380780f807040005282001c1c40f00c2c0824011344507407020a1919403541c0d03070300703106000300e40c0300e0184501030358505851a506e80b503649041d0403075a80940030520010030a55001e00085010b9602d202001e0488180c0b070400410710900a00014446e0042e158000b001079080c04a480c036541d00448240e0f10341d011304002c50090403a03120043c1c0d41d000000441d00204001e242140e45c1640104030800c04116803505056a0348030a90786180964401110043c0d41031183c0001c0742c0c0110284c1d03602e4000c40d6510081401c15074506011180d014030780400b40b10740c080c01d119031541f100340c10400307030200b0b06561501501d9100300c1e8102805541c842442190304040e0720002c000c2142c0c0100200280b107924100208009801d001e40156401e800340c03840346e48265030f070702542503504000c0508200e6181490b418140e50100ca00800704020b862845000d00d010b50781c0 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 531944532 1250 531943282 531943301
    0x50a0b1308070803090109151b06090501050405160f120b041a0406020d0c05090109150309020306040b04030807081b13031b030303060603090b0604020c0c0603010311030709020708091005090301 85
    0x130350301c0b80034a4001401c881f08681100c100300c029250100b8003c4e610510b8150b40700b1808483d1510902c0720f003821405411540000b908075030070300040c80104080011038500350f00c103410708285c0faa6141c0b50104c0780c0d9030142c480d1204001843e5038280201c0c3d1007095103034100b1b1051080a0000c102c000010a2000d01202d00752002c59011a42d40d02078401c600410b43c2d034102c07034501207103899a45800070f0080c80490051001d4000b800350324500d0280294006664150014221121490245003004250008503000c034006a10310002c40c1c8a1800765031001d00500c020350035102c00044204a2038855041a546c6540c0420b00c504000013041c140310700220440c101c440d46004143c20340c20041e080c4c50080e80807000305858041c0d060081407824a8060b040b4204940250b56201c54042003841d0032610404241e00c60030000000007003001740100e070708180409505071031603217503035130b61f80030881c0034070000030b461000e040040e50310a16150a1080d0145031030b05001c3c3c01c22240c000840c2c2141c000d0354 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 531945782 1250 531944532 531944549
    0x9090102040824010b0322050c06040e0a0b060304020102330403020f060105190b090a090e070f081203162106060201050606040b12041a240109050a0b130807 69
    0x2c01c00c560b202100c0e0340c42d5016121490141d1b196041c83c0c407502da01d0b01203001400c05801081ca080d0810442c040c0004800c119000703014030b4840f92504ca03026007001043c0d948543c0c1c0352a0529101581c100b5805a902c42d41c2c050300a44400345643c504e4286003040d0560346200820190413807280301c9404464103010b01d00a50080a01150320400313140707001e9043e00010322940c3c52022030040041040404820f0b9406400c00c41c1d1144c845402058401c3c00c0d5400c60301d1100d05010612041080000d96001140c00084041741860385d90560584c407101c0c0c0707030070f202d901d060b041000800c00300032100498440c003020300d804e840e0104030310201c040300c240491790400801c2c0c40e01c00030441e10740d090052a07007141007140c0e178034503080c607101100303545120707048100758100389107400601403200c00d80c506602e001206000270301520b44050050100240450450511510321545400360352085400c0302c00c0c1d61000e0802c0c1340413030500d6410b821a41101c02034140483c0e0b840710100b2141c80501520b00104070a5 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 531947032 1250 531945782 531945823
    0x1218102a02100f0e040905032205092d06060702040207081b010507031406030a240c08010509070c0209060609120313033c141b0a14010e090901020408 66
    0x80c50020030314014030141d540324a0900e0f007881d0207e0808401c5855494103c03059000b13072503906016012586140e80b203039500040c01020041c1d0320302c0c1d800c0702c8070002090403031100f01c2c0d03a503406080c02d002c402518040e070064018010300340107081c150300038840c0b04d01424803142400c2402d4800c94030300002e01c040c42e0b0076035154814007562a0b0940601c0320031468000c0303150381600c4c0c040c000c42d59600c61082c0103401c0000c0c0f143d60a0031014100503078441c840103080240314902d0040340c0a89010b5003841400c1c01149400700140190f48120404c850700341d402030200c03d0729154a000c100c0242c0125894a60150100f00981e45015080000300b189054200281d9141440c504021b2448000265800b86c14445584448207022600480f1500303481a5259807007115418140041729480c802c0700c03c801481400602c0c01c40c5010260f5070310f01c10600321044000d15485281084850125808150100d449029400784510307100080584c0140840c1c001800e181e611500540340c50b15580440600c186132 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 531948282 1250 531947032 531947057
    0xa05090a0f061208070204181506140906180c21060a060804020a0611031201080102030f073b150309010c081b07020109081218102a0210 60
    0x903000344801490005101c1d4003c0c40740c0e071121000c82c031806800a105590790500314054408072070456500700e800140c01d4400d512511140001003030307039026881c01a144810006901e107003e030107251061001400c20300c20800c9611810904003005054204154010310101001c3d0403899140d5102ca10500410041c1c1e050071400d00070b504015402c02002c02000004020250b02c4200701642141c4c641e203444402e04c03500030f44407030071401505608100348020100010780300105401450040d480070f66801c041e62102c42d002c0d100002961400e80721072069580807205c001ca00c0d01d07181000c1490024508c043c142020010350106420001c1e02d220060101c14040c445100348a4060802105d0425030460f08020310907a180c001d48000d446001403000603884116440b4800e140010f0070400c0480c1c107040c040c110340b4440c030340022650509400721a500d0f05c400e440c00c1001001a000340781c84800202908813558152444c48561a17811200d98a40380c1d001031b11550000303011103880e5655000d000c0c02 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 531949532 1250 531948282 531948311
    0x7032303100603050906041115040b07061a240f0903030f2505070b07020627012303011a1308100e011505010f0c0204050405070608180c010e0a05090a 66
    0x1005055640c15a12800804c0700142009540070308c0780404892401e418070020515404074403494112601e680c1002c0341140400c02e0315080070740d07900882e10880508004110900c1088152644200c41c214003c1818034194030301c00f001454690341c4100b055140c03440000111340786500503060207401080003e0301e03284941071101401c059280d5440114005c02e840c0d05c441d0786d1688540162194808006890421940d036401190054071400480c3c500c07228003209651650a044044a804103000c6112000030080c3c03140300c1300380e43d24032800c03d03800c69003032007010f1012004448081e0804002040440407002a202c2028020601240181802d000308120310050303c04011040d00a47c0c10240000070904a502110059400a1800daa50805181000c07039420340b28000181d0002e00d0b1034107001c02e0010100b440000c0e5170f1952503456a940310403213440c0041114036106c4034660850080c04850358816040500360503001001e00000ca51541c0004000c020242e0b06584810f66603024110581f0 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 531950782 1250 531949532 531949541
    0x60f2107031b0506040b040e0c090418020a0b0906070b1519090c03060302030a020d081b060a0e0316170d020d0507030b0102031305010c0813031a0a1107032303100603 73
    0x1080d0340131420649820040c100c10300683c01501060642c40300003401042132542598038051008000b03104e01e41003007000c482c1e20b82990400ba8054a00e080c1e000c00d001c1186021501c0d00740000e0001440c050403a11211444500a001d00305881d80c030400780784103652032094a000c40c1d04c140c000c40c0c444c146000700050031103c001ca90f0109050032b2010400c0903a80c041a9400017a80540d280c03000c05507d45003505852180c1007407411514104200014031210026a5503c0384000101c03c200c02842c09008503943e000380445800340509000c4003000044410b020701041e001508041c9062503081498541a130b00042c241d48800342d5500c003002002c550500641096402c2030000e989461904c0360301a0120b0110f0080f103051140c0184000200b2034408110b50400344090207003c0455100d150100c6041c181d114514650169080420040d1095104d402c400d00308031042c141c980517960340e05892122010000e5030514036406441c65001c070100c2d000310310440080c48155000c2e42032071300180c00c44 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 531952032 1250 531950782 531950789
    0x51608060a060c0b0916080102040501021002090a0302010f0c05030412020102150702030307030b0102030d09060506150408030301150210110c01060603020c0706212f03060f2107031b 80
    0x1549080020012942c202e000074643c10340104a0403040c0d5110240030346840c5c5107807013451041c2521207000a503664198051b106031102642034800b90f80c0c030005c0000980c0914050380d0340c40b201d102c808000660107042d0100283e002428641c2004c030b4241c0381c0300c0c1107820640c01516040300c004800c508569040c015140580444001e4045500701071a00a50b02c0c040102400d0a0554505188105070700030001c1e82c1c003944c0194400e02541c0d204c4d00d000ca000e0300d030075285180103941e1148008545880e08007500d040e1001b002c019821607190207400100307028005041c4095000c0d0003c1550b1140090003803500420b01d824030f50359030f0100c2010b280c0c04c44005501440801d48107000c1a108401c011884c101150801d1502da08070000e4250585e94040142c00d01012592500ca50b60443d0301c10300d0b100803500c8011840380c010580011410701c2e420312003100c0c0c4552024103900d0001c81403030f00d58140144804200410028a035050b651030785490103036081614186040d5000c1105e012843e03035510042c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 531953282 1250 531952032 531952039
    0x30c0906050103050f0a0c050405060301080f010509031c020d09152007051507020106240201150501080a0f020d02070807020913030f2111090406060f0507110f0405160806 75
    0x298940f50405098084c0080c204c00d1201f0380700c116182560f4031a80903039000d400d004045039603035651640740343da07508624404904030f075007040c4c006120f500001c415140004140c1e140000003084000c01c000c000d50140034280c10b0030f503403214094042110b40f90180000c1e0000100000c2c0c0404c060202c040301c610030030200101c08010010702c0c0000da03000c00d1802d2082c0d0642c0303070200140c0b540f80c020707800341c03003140c001c44c070030100980d0b40c4000ea8082c0590740d00b07500310030340080281c487c8207000c0c19a20038041c054580403038644e0002c141401003036032000309402c8c9662001800c258450110030283e134803002c000d58600e1400304210044d4503086503581d4000a00000c3d032544010aa50050b103003c14000180061082e45600000390021001c00f8400740c4010074420001080d1380004504650010103d00e4083c928100b40460f46074002c40200c00c2e80e03516620385500f011031a55940e000c01e82c86100341c680000d5000540b0410351168000c880c00b5140300c0130090348158810030001c048410040000d8031 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 531954532 1250 531953282 531953291
    0x6140f060408030f0d2315091509070c0b0709170706021906090533190209030c09070302070510090f030f0e0904051609020910030902031204030c0906050103 69
    0x1030040004211190525185501c503117880344051054020091402110026803440b603c0e90304130414001d01a10a402688003010980740c2201441841001212a840407401002c408150362801170392240d88224070b46404100c014095550041d400e01c00c1e500c200100300d8503501807109420010082c110091038600902d821740ca041c6000b5075540610780030324031002e00d44a00809000094100c3c1c00c9094111045503401009103181078a0003800f209281e0341306003100004280c8042c610411070054140100151010418000d901c000794400c9a10380d0f454401c5004248254441c003403118804d0481d620016103c40c1281411418041c0340780d0403065407440c6c0066600010390900740b220740c40340c240c40d1141d18084950b0084c0e590701d0555121540c42008172040008101000420444081040742c50141030741d6210580e000b07034040e041c0d000c1d50280d10240254409403180d80400d41080c001403c684800c0780c210350040180d40300e604151084d1041500c28410a440d138090b103c001c0200b1703e010007 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 531955782 1250 531954532 531954539
    0x1314010b040f18230607080105040e0a02010f0809280501060602070312180305060f06030d0c03020c1014070c031109060d11040f0c1e050c1f06030606140f0604 70
    0x111500500c5500038900304c0000d2403020640400e510710500400100201e4401d8100f100f0701422111003441014401c900f0400350042c910300c0454505541076042c2c655a0168109640560314400c00502e4483c2a2190304140c0901c903118000f040004a0b131024100301c80d185506141d03083d204160080001c2d940510410030001e000743c458401040314920304852800780d111062801154190b20292880c85401c0c00d01030b51103043c0b54501d0203aa401c60449842a021903425110641c20700006409a0802829a00907007400740c14040505440c0c07902204542c18494024030507009111f00780c440000c110014400c01c480030341c00082c4c0c00c41c00c448040c4d0900d0244006100908412402044000b10a958100584840e00044448000e02c0c200340700b2001150382c0180344424200714030b004990104000d08070f8500070b0044852801e494005450142c558001d00200002a00401d140659840c00008040384141c8945405021080c21076a0b07a03803c2e61040101e138900b56941144205000c05c000c0 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 531957032 1250 531955782 531955811
    0x31202030f19031515031d0718060e0f040614060904330b09010f081510180221010807050d020f0603041a0a0b010c02091314010b040f 59
    0x1282100302500c8440440c0c103115000710044e140901e280500c2442010f40850b5181c0c3c3d1110184204100c0c0da0100260900100e82d01914100c940000050341c21400c400c2c400d0032100c0e28103a0841000c0c220200c0c01c0d96492003d90740409080740d0b00d0329041c0a510501042142c10702941881400a1541d90101c0c241071000a001c800050401044040701d07030242a03e198104450b09440369092001041d142c0311050010054400d45507524820510000040f40410780e2440c544241c6841e02c00811244015101b01141e40300098070070040a50b40c4c1000240c42c19620103251500300714074101584600f104503400c4070b90704440d18950b043e1907600c2c00510441400050010032a40c00b110380440149060000c2048201420520342d0086400410041400748204140b070840c6070036200b40d070f41030380c0c3c50308864121074000075280e0005012054200247c613001021076000540d84150f02e50b400c41550f03c0d4090080d0881415070103944580320a1620329191254980e01e2242200600c40d131200401ca4 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 531958282 1250 531957032 531957037
    0x1005010e0f25020c01120905210403080406030b040e0105190c1106010b070c0e0403050d0b010905220b060a0203030a0e010209031f05060402090f0103050a0f090c031202030f 76
    0x140340310304589000100c000318401d0034444481d8114682c119003180d200b0009450382441c480560103e03d584800420001c25442403506082e0000080c00a1030061a2130b075209600d103601c10f02c413603001440080042801007009000900c000d44001520b020040c0502040c0d60803c2000038003a4900403c0100c3d405005680d107200f0414010001200d00412505440c04a07034280606800d10403e400400c014034a14010f010b20f502482040350b0f5941e0b42c11032240c511100301c0d00180007480034802401c20001a0f000008103d0050401c65000c079111804941500490605035001e04a406032000c081c0f2454031615600f1f0700140e1b803280c9040c1c82c010020b5542d20000d0324003102d056884c500418500d42c01c1d4140c45804000401756141c40c5c0c1510f41e0241a035500007407142043d490203021880c00d107081d10856a20a901600c0018451205c000540040400404518440780c03204a289800d4242d489114034891040d07881c90203003410f50038080e80c210b441e0715442055500402070080b03000d041405 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 531959532 1250 531958282 531958291
    0x3041a042003190f02190b07030c020a090906050f07020d02030703050c070b130303020d210c022d0f060f0f190609050613110421080c010e1005010e 65
    0x80d61144009402183c507201c0d11024402a540c0035007594820050781502c05011640219140584c1801c80365840000c2800b6114050a04c00d041107594000b0340103110102c0910700080140c209255a041c10b9007d03a041c4100c01c94140d030fa10380812030088000000e890308210144005c0c1500040c40d00b003c0e503a0b2103564406001c1c01404070315904060b10400882020f4184040c07416214206070380783c00005c40590008038003600804115003161403043d0344180146804e0842c0d88c00307a0b0305210f03c2100621451042e40214018005030520308500d480040302030702001184030900c0c0920b1140744ac24803483c8000d40595400c03a200344285894040c40884d00818408000c0c45291a8a8035568100101e01c418000e441c1c100040040e212404d41d0045101c0d070b20580e00452010215804407048a00800c0840c88220003803000b480b0505603c43c1c165a845100f9100003402d04070780d01c82c0002900448042d008903034444e0082c555126050ac001a0b00c43c00c103502c1445954185a410210540005c1 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 531960782 1250 531959532 531959573
    0x6061205010c0e24042301020f0c0607080307031409030903071406030a0b06070f050c040606110a0605280b010905010503010b0d1a0d030306260714011806020303041a04 74
    0x5180240030580d011500100b207120040b508050300701940c100f0401c11000c91b1030150141d4012003150705000304040c01c640d00001c05403442d1070340c50b5075030501c1500090600020159550700c40100e845240c2e4803d4000c0c1025030085860b481c080302010714105031504044d8a094049503003020303680b42c083c141c98016812100104480d0700541c00310b8810701826038042c06951201482c4400e005004c6000c403d0404142c9042c000ca03522070200750354841060740c0304800b6074420202140890304950003280c200e215083c80b15109003260141d8510f41410010454106030346840743c04641d82c0000c81c40b0020039081c2403581c2158507046c2000c10798010211400d0b400c0d51650303143e030100c81340c01c00e55030b0620100a03d00070a0100e50f0078000c0060103140140c4e804c0040041c901044400c140c0000c106500d1620000c2440c070341400c00c0c580c154480003030300c68140032000d1429150749960050407005002d140d401942c8174a041c0c101086000308540c81d001c90b25141e04e0900c804500d03109042110068000d = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 531962032 1250 531960782 531960829
    0x90106090609180b1513120506040b0405070b07060e01050601020a03050d1a040204030b190e0316050f07061d0f06071112100903080a3606061205010c0e 67
    0x480b11a030142031030001869100040c00e52170411100c5000c06804803800c50702000015540310b00417246c40c01c540400103001640700800290001e111140c40d554000c0c032a0040e56500307983c641814030a038000b804c0c201c030f0560303e0701c601380781004092249542c01a801d01c0201611000350f14060400d101740b01418440f50345492849401009400c5140350890300907104546d0b559032803c040f8007890040e55183c01c250910b600c00306003a40540119084040e00c0800b461805403210000842c45820030000c980d83c2c00b4860b118070001c1410700c2600000c109503182d46000941004480c400350034003150341441089400314440c125100c190964201d0399000000c2180326414400140ca6004071f035031180d6241c41000303281320b2080403641140704468071a0700d5045668840d903501da000e507032890700101601d50b03540c9801004100c1100ba400d8100036558a0f180c800f0f01e042d1112425641d180c0c03c14407500c034160111f0010810241700e8520b0b1103a03030b4a4100307581710180300020329404c086003c4c040c10314800c = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 531963282 1250 531962032 531962069
    0x403090e07030b090c09130603150f06031e02090702030310030303020a120c02030c0114060303160f080304030e13020a0909150b0705161d060105070f1a0402090106090609 75
    0x207a0281e521440000c10031031442c0340980c405c405641c44407640c1c03400b1b4821101d46070b9030381d00c071801b0f04400c0c0d0741c1c0f04064146c00400f40a071400207100e411005410551650400004141b00c0208802542541e401104003041d1034014811072000c007400c48002c65004200304007000315849078401c01e4982c1841c015944140da60400ca5044924074060140749141c2480100c103503400100401403c44064020b0004101810003044070102c1101c1598164104100407040d0044d44c10014a03814490000301c01c1071102c40c2c9402041c2d800440e001c801143d0029200e003018500a80c210005d22003500d425443e201014034004c05c80000c601c540c04143d03413500303200003040d04c4903010b4001403e1007105a645031025410040e40c0c4d030106404c0c0c81c4003286114004a0350320749201e0380369104a00d04514901c0750301d940c3c0044615900c400300c01d9504082c0c2d002041c0000c0c0340c4801e0001c030f06403507240e8903035181030a004220803280113034021820f010520104110040c1c05c41662411251921843c04000e905c = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 531964532 1250 531963282 531963287
    0x21b0a08071203060b031e0903090604050d0602041809050106050405090c040515030f160501020f06040f030903080304030c062403150e1f0b04060b1215150d140403090e07 75
    0x2441c0c20803041114040100700410b45074281c1f0000c407901d064600c40c1141c03107000342181c0b80e100d4160719640000c002c01c818002070804050203c540d42c03061a0043c68241ea6130340f5000301034002c01410000342d80310444102840401d02030440504000c480801c82428082126503980e01c400b103c5038040c645a40c0002c900341900b03107800d1400c0c1406815134050342c10840401d5202c0ca03054940f101400d8400e02d000c40d00d544001501c00e900101d410062000c0d8495860f00b5410450000c0d08808010031000040006060840650700542c8130761188a0b000d2414580303682580e0241c000c280203c5400300a50890302250480d902c100ca80242c40007030201c49400c0c009024048052203041c00d032140703ca8666a904c0401000809040030030707410052203514004020030b640d028450422002c1e414002c4001c0341c4148180150000882001c1d042d02c0c8032100c0108500c040502d50002d02a03401048502c0655058000c00b447d07000030380685030310391404d56009401c0464a00503090480c0019001544490 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 531965782 1250 531964532 531964541
    0x18050d02030a15020d05011e0308130801090b0702011a0306160e03011803090902030709051c0203060901020301180203010503330907060306090c08070f030b04050a021b0a08071203 79
    0x9401a6203d0300089201003602c0296114a0302050813520740300c00042c58007c2152500b11900686060215091131600c0b0200c0300d400003000550242c3c03507206c3c005100e4200b4414840380900c07410f14207078603180446010782125900b18040e03000250184484466035000b180c25030740900001f90300d120383c0304510002c5580084444c0803c4d090340c40c051102c0840040b01001080e514483d0b540c803502143c4400e26003081e80404c1d962500402d0742d140c418801443e0440310540701c041e03401c407020544811034000070700d006001e0710048042e95002006001c4410144254058050008070035480c5500d040c1c0030940d5450b4915a01480f0f1080803035000801c6a5680280041d40a00040781c019091070b260301b6485440d43e104510200749007a40c0018482c91074066400303480d0417030b01c600682d965490030548420080020200c201641c8900b601c3d469500da00c039041c0201c5600070010b84882c0204000a82c0e810081c0c00801241d00022018000a8190003111841c270340c030100e8046e0180002c2d2041d809403 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 531967032 1250 531965782 531965803
    0xb0f1f021504150b0303121302010512180606030a021c0606170601060215070206041b1505041a0c1f020d0203070512060a0602030f1c0204080312060118050d0203 71
    0x221103405110510280d0307507008000e00d000c8481006035801c10320405540c0c2c4036068100e58802c0442000030110000c500c10230001700d0041c18454603088a108103400c034650100c139441c0da11112017001404c120802c0050302e52100042e001080546d8084d00000c141d0310b040100c02ca20001202034020800c60f040e0801c0f402081da83c1d0003187c45050b5480c8140e116002405403000521405820a50b070181d4480b45074000ca0360ae8000d403040e51295200c184403281e80c90440c40e2140302c8100000b50707207000c08007803809503a182e903282902c4034202945014480b410010401d45650309226468012401240288510600480d4002e07040300801038003010340241021004150f102004105a240d0050000d11801c0050351110149030b42c0c510411001680d907009140040c5c1c400d1088030b1701075458000421404131303004014021515020302c2202664006c0d0060742803900302082c440c0e010b140300c0c00c0c030a4025500b400c0c185980c0e580800e400c0e147c140d207441040e03c114005a080000d54809010b27682c1030 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 531968282 1250 531967032 531967063
    0x50906071b030c120b06010c08040501110c060a021e120a0c0c05060723070b090409020a03020a1202030601150206040f0303140109050907050402030f0c130e0709090b0f1f02 76
    0x1055441c040701c411305070a4101601d8004006001440c551300c155000822103a01128803410142090011101d0290111303c0600c00d01c200781e800106555a90b0140c0341d041503550003807844900032201845c0710700302d40281c40c000c4c2d400200c0b46d6080814950070740b8101203503854001d10891050404034000300c1c06906c041d4005400140510500680c001c221083c56200256680c0b0200710245007584c40d40103101d08907400c00c0c140304040b102c2c5420f0b08049945800108801e02442c0c40c0d0300094003800303072076202131242080c0d8010039003142410702c005801001d00310544070051100010180d15100700078001480c4050821180b810103000394444805c1c058204407025496860b00b0040b80101402d45201050b4801d1010000b00d034540b0303002f1284034000c58401a504c0f0b4a8480c9000556000300c040710a00c0c40c0481000300300402c40110041c8900351669030f074204646802c1004040b9078a80b2880c3c0d004e082c021055407000d88030500d080240c400031002c41c10455000090407400c0907002c07001c1840 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 531969532 1250 531968282 531968303
    0x18060b01120f060501110a0c0b0d020c01060f08060c070c03030f0c060c180801020724060506070f0b0a061d0709050d05010f060501020619020a0509040921050906071b03 74
    0x52140c100d40c09107081d51400e0b01c846d40d8855800910319074812030482c005181111180c1d06007c0f444840010380b4900ea60f800700581000610700005094951a404c000b4100801e000108070301c01082240355041080701420750f1900c52203444015031180c0b103004c09014800130030484000c03244514a40004141c02003401c0007041441b000c001d08030040b204840450313801c80240400d507900d06108031841030758030160f02640120103c11802001c0308000f070200460303907076070000205a01c1d03400090040b00d2281d050306a1030805460001d1901002078660001d036460070505116914600b1011080781c0015140112180c7e03410030201d0341d1011030341140350007007600c0d00c0f80404c008054015010500b1041c009201da69240d030012661880700712030b80c2c030002030350441c031030308249850f4024003410581d4a4024604072840c030200c0c042d01c50340d0320115000368030380d031800601c901c1041781822005014603220346004610380006145019021740a003102006a04007811840c12001d600c0007154000d040c1d96 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 531970782 1250 531969532 531969551
    0x33010c0606091a0a140d06060e04080d061d0411040b1512010b1603140d110318120f0a021e03031605070c03110f0904060b120118060b0112 61
    0x2d018280700c940000b014003003d284503c640c68645000401c4d2080346103c5541c0036001070400101949021040d94001d98658022441d52100517526200c2c5006140301680c401c0403500fa0780803a4107540c001c3c4502d0403603828200e41642c60b812080d81190300b14074071148070007032a000200281100c428581c2c2c022910107038030ba1054011006000d0322442c140d0001c0300c0b0b0b07aa8014103200c9215240740003500041340080d01d0300081c05191204002d011800500e0f0400003010340039012600c69038802420004007008220640310110351002500305140082e08030301801d1055049c2c01d000303007142d1413848500420844030040c820002e20702c101130359003100d0400c2000c2034441601ca6000b5243c50041c4440c41d101c0740d82090181040fa841d00e9444141c12500a00c2c540f1881112040d80d05100da107e6902c090000180d980c10715194003072802540e000a14845600c01c001c07503d44812207401d0241d061481c03a40303801c441140e500c800301c0d070400004660300c02e01c030004a500403000107461005a18054800 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 531972032 1250 531970782 531970799
    0xf0d0c030e0429041a01140f04081c0302120106050c12040e040b072a030302090907171f050603070504080a080d0c0806100e06040f090f0533010c0606 66
    0x3c849168030012031000c002c81c080300740001c3c0e4640c00300100d4000b80f01450107485500c030391a0a50100307014908682031880310282201194040d40c0107446a0303002080c2081d1070000c0c0800a0400b800608003145050701d40c210200c0507070014460302c42488804980c51021080038482010b500b40440e15207581d594564551228660040c0c8055480303103040800a40000d012f000a0304000027088804040341c030a0188a102c440700400741202019000e00a10609171036070315020b070050300d043d201c091001d40441140c16012a0050a0301a001c0403c15030340710100400d50326001703644094079000e41da5903031321006480510583d403000701188142d204050a20003094023a103424410440d091210b42c104460032140040e056810b517620044008030f440c5428040e00460710b4001004d481c082c181a80c038911241c608005a000c1000c403511000c8000840c0c90030302c910b507400220030403e4581411a10000000d020740d40b02815941d540c0c81000c1003039680984150285540d001c0400d01086444c0d0110 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 531973282 1250 531972032 531972071
    0x60d11070b06040b0105030103060b0d141e070b0d09020d0503040f08100c05091908120d05090a030509010c050a0818010e030f0c210a11030f0f0d0c030e04 68
    0x207440c0781200201107002407a142c050065006816910242035900396101c610051601034605548915400c43c050000380714900c01001031402c180107031002c00321641d0b03010f904108105040c09260001e01c018020b0b80081001d540302402d800c0030000d00c03201d0300c0c03000c141a0407803520090400e1001160000708500e20ac00602c0603034100c032060b91f952442d010310300c0d0162940503041d0b0b00410300c18084c202150800940241e20991a40d00031032040b40e440c80024200340c460340905074103003c002804210034101b401401d420084450080440703180f1520014410300446c60b0701810840c0c654200010700c8010841044002c2e00000072541d255085070f600c101403207101c1082d602040c02c400030425240317008170b0800ea5011300403002e00102c148041c1000250110740c2041076032040303105143c2c100d094081060b9030519220b108480d04181d801c404151821940400d122010b600910102880101c0496406541406424034100401183c94151150200c03908840d0f080380c6400517903212803013170458 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 531974532 1250 531973282 531973297
    0xf0c0303090f15100b0304050109021e01032007020111070e090705010e0d15050c070f06020306010801082407030b06180405060a120f1b060207030314180f060d11 71
    0x1290b5080c07850715403c58080c9000c0716005030301d1103140c0c410020780c01c41200543c0e2043c421400040c0c074941c10340c0010410760400c07900a48031304a405100d001560184210b1500b12a416442030ba0703802034680181d12440703028802410058221044d0211a0080010754042c110450140e03800f840d0150b20745544403124400c4500041038141d038800f0a0806814030101c1c0d075084a43c203030703807055100c40b40c1c0080c00b03000d2b0110400700b400b0081840810f0050210003030544c811720025a0708d0070210001411290103030400e00c42604807038100d800311004030300c0900d4900c1009201000b00d540e02d001c00d40080c0007104003160012400030340c8550030a02d1010b441c01200089800304200d41b00c81d018807200c0c0403d4042c162585180c806105c2c0840d03100c0301d280010510441101c1603a0700038488903d40302000c1d50000d00582c0c0621014002c16820000d101000c191307030700aa43c1007030825144800d503480292192809a0300d0a01c481000740c440c1012660f101c1e070440e40074440200c401d204050261700290 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 531975782 1250 531974532 531974563
    0xf12031b0c0203010c031103061504090606110705010207150f0212030a14070201020c070302120c0a231009060305070c05030a0f02010f060312080a0b03060a0f1a10050f0c030309 78
    0x106101458082c1c8112181d180040011f0780c2150344440c02d02841c854600000251080f0a000004100c00c05005120107000c02d43d56003111202051205403070503855421103030540d0462101480003601044800480c1d40151401c02c01d40c120a000503800d1411220403401c0342c0c50000100700d6015010307003250311030041600580c0c0c0d1a42e0760650407803c0707001d208484159070300440c1041001d403411140500642c5ea00a06a507031aa0b00f00c00010300400d450740c00000035000704601c0d0385040400100e911003803502615802c25641d01c42d500245049158084c090a1580d548086110a0b02c2400d42c5668203038000c0403030340e888079030381c0340603102e2071104500d41c005600304a900f600c000858007824040b2944030100c0200f80c00b280a00350365851004140c050300c1039403000b00d414559070401c81e80780641160840001c1c40300e09107804100b0380c0c02c115031b00d061404160030001c2880d1034900690200c1d60240c07a04c5906c0d007004580c260014071400381c8500f034034840882800034008021404c1c0c0085024030 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 531977032 1250 531975782 531975791
    0x80403020609012d2405120109080f250803101a040e180106030f02150903120d020f0705010b010908070f0e04020111010906090605060d0f12031b0c020301 68
    0x214016084c3c400c650400d05003d1050700d4000301c0c0c841100d0482e8501d240d009408074004290500000c008a0074400c1d404803401c40103000c0107a41403000c20745c08201e20301002481a04081e03143c401041c0f00701d4442c0581040d00184110071b01240d04c0040d01e0310890401650409403542c20314440e40d03001907514180ca100c103024000351000b103030f0982c1d8481040d94a060303030070540b5009464801000c01401c0000800b02e6081c104000c2a081c4034000240d4440d1031031050200103801805030960f0740e0034000c020223400300030103145a50000760080c840e90b000b00b881a542d2105c13881e103201034003d9a859024113800803468070100300c019044210b45e00c100ba82d4040e882036555080a82c3c51080e03101f4400f01c03100010341071208601414050782c1c00790040c1401880844210005400c48800c40400e41d00e4643d40c480c1c800400c0464050f10381c1107401107504200d030345911340791420700a1036004000c140010048140507264044d800c0001241c8107880011002c00c40894082c042040008040f40310b540380 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 531978282 1250 531977032 531977041
    0x6010302130f1817041a0918130302060106030b06090f06040b1305030c0108060120070b040326190302030612070305030301090f05010f032301020c0a0203010b120a030c0816030804030206 82
    0x43c094400721070603c03400361402c040394242101b144d800f1454503904144614482c1c2d9100c4152100c081c010031800051482c4a126410300904118068002608150801c0314480303090f640c0c0d10540b50b0900d0704540f054034418480e80001c009100702c2c0d020382555580829001003030541440c0c0070302211003d6007a203108000c0320b40111259841207034aa4003064081d1a804c1040070003007050900c000b0782c482207404154413246045e4058006500844518680b491491410402410381512525080c04843e041c180c9444103540034000b00d0700004d017055804000202c055440c0c604040d041c00740082640c84403070300d900344552264001d01529aa00382000202c411040340751107241d0484180c00e0701c1c0c00c000c908503918402e44810700765070040c03044211202e0f154006400c0c8010288151140c00400c0003400a20501d4251010703160824030481a04259940c100b0010a41c00c0d0620740c5882c01440d44940ca02c1c3c0707848a0f00845060300c072040100c02d04842050342196050b406180248c0844909948 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 531979532 1250 531978282 531978323
    0x1060510120f060303080f0717040b0106021507091514070b04020a14060a0503130b0124140d0c02100f0c0e030f1c0203041e17030c06010302130f18 65
    0xd40d4400100011445000945071814007d0100c1c0c100c0a10315107094100045090042e0381d00c1e080c0e03416660907044a00421100e40c041091000d49243d4070009200ca06d0094006032111a491003003142c00400c00c0303510079895200b040340320401c9d441040c0183c0c03606000d09000341440700c2200c0803402207074800d4011865400c1c2440640c0e4600c00145404d1500c840700004407440e81010300000000700c2c0945c0c035400011403c250450290020140e80742028085d00d482ea01c800342c1e04561602032240e040c2100c1c00c05041441102d231341d101c460101051001034440f080b071601074002030b8284507c0c81d03c0c4102c840c03003c55420420701070144d50380d460902c24035002050b1300c0300c0d035034086417030305a00c6041c034514020008528441c2c0395180e030050340e060983d101c50481d2402c08180d0000120040f480051146542041c01648440b40c00703002542401101c0d207003541d0314401800f000e4400d03002c0c500000401c0f032080c4c1210200e07240c3c1e50002d1200041208002440c009027443c2241e40c00b644820b5400c0540 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 531980782 1250 531979532 531979541
    0x8040f090c0203040f090902131803030b040b0904200603010815070302090603070e0a0f06051b010504020a030b0405010f0608010f060b0a090902030c090303040618090b06120901060510120f 83
    0x80c1000c1d6170604092074280800010406d00c001242c1024001c00d1140c10420244680c4c034400135040300301c04481495103802001c40300301006d0584941d1400c1030392101c90f00d4080d0415809640503480c124401c030103c40d6030074540301d0740c0d80071039000314000000b01e01075401141c00701071711240d0501400d41d42c943c10410784c143d0003141161030f0044014800522902e20400c40703200200300207000c01444d00c4c5c03921011600c2c410b42e81c2240c004910000340d81c080b403222982e8500007240c62200204980e042581c0011b4801603184000350902d070084010034244042075205604004000d201045501e0792508a41e01034407048240c20805840c0c110001030040d00c010850320599065924245918101440200250030261a190010710207020108098034100014000b070400c540781d840d003010715142d1062002999802040d4000d0800075001c281c0d482e504291103954501c016070202e00d5550324030090060000d030384082d0340040fa000c2c1c208041d50b041410a082900310900c00d12074440b144d078480d0280c4 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 531982032 1250 531980782 531980789
    0x10050d06060801051e0903071718040f06050a0f0e1b0f0310152307152309010e0703020d052a120615210303010f171504030305100308040f090c020304 66
    0x4084c1e000d81a0107004001d0003880036110ad250b425030422a62008582294405071014a000350740c1c6400f40401d140c0002e0b194001d2968105120041d42005044900c0d0380d070241096142c41070000c120b00385290409c1c103859036507003e5142d09403a4500000e810003410858454408020540c0341e0982803035202e10071509070b00958495500b0422000b200989460340b090301c0652720f070801180849002d0040e0300584105d1011101e0a9015910450040e14205005003031520681e00d0104102000b00d00810501c08403078040392100c02492031400c0044c14600200b001889010f01150100108240c0800c0003d40e60415a1a5209051a1aa8940c0c1c85074195040302c600d0454201c101128030780000d20300b01141185030050711002003111464510780080e00082580d1080341028012011510000d00300307495880000c20152800c0d0070002911000900003408158586001824084010030104001c41d400794045a42da5035441050388009814010210b80c1c0e410110701c11516880001642c094 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 531983282 1250 531982032 531982043
    0x80708090c01110a0503070b10050604030c090f0f050a091707241103090a060c09030809130605031906060515221a0703030c030510050d06060801051e090307 69
    0x481102500564810802c101400303140d03c1a11001310020340c007800600f0026110350301d02089420110000189510107070400350042c4000d1004001044060743c5140880d030a16000140307981d007605c1c030310019041966806814500305414408a043c2c6588451501802103041d224028008503070040d03603100b2080c0150601a2404034150a201407080b00c075501d2818880001d001c2c0c1030700640306243c1d0400c82d2402c1c4c45400a13501ca90510040d0f01800100303407802d00d45540b80c0381c21552070716914001d8040041c081c820001503000303080515403210010703110050031140281d83c1415880d0b4542081181240e0a40c01c059000440381018454003a034116205c2c451820260003d28600c0817004a404008240403404400240d01200d040d02800102220204507900c000070b0070b002e810f980c0d101080b101014900010004a410301480c681e06550048031160366441060038260060903407604444225403800d41480006282e400300481c1803500100d0321001c40d039401140c135499004001c0060113 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 531984532 1250 531983282 531983293
    0x290906060f0a200a030815150d0504050c03010e0c150903190503070215190906080117030f1602210606010c0f0c080709060f0506070b1009020d0501050108070809 71
    0x1d850b00496103100015500d0303605546051107011124908a041281071700829042024003c0b04103109014015800341a602100d0020070f9080d010058403030203a0450b07000703076154040740030004180080c80d006140200280000d5917591209500d07100f080e60a148104105402d000544000c8800c0d034131003080044c003924240000d2184a4029901002d044915020400c20440103943c0c000d8141440700c14440a15126442e8441c4080b0702c0982c040c1b50024800c1481c400c105082c1d01003000c0c3e05442c0304140c01441c0c1132042c2041403440c0070308404840402404101ea480c1004120300e1800c445000310b030840c410315140c4000a143d0b18102c102d0604076004900003480c154080c0035034404c9284030724201c80c0f070009562202c920700e10454005c000c4e2a0020b120070004903402d4000d84d0050718003c040d22240a01e08000102c60f845940c0c00149619414030008142d5850140c00b07800a0905410030b41d0303207a448040141c0100b01c01d002d80340c0030410400c0864030091103201c0c4180f0802c2c0c1c8600404 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 531985782 1250 531984532 531984547
    0x31501031101090b030a0f0e0f0721080d0b15390d020105060a090b010c0f2109030203120301030201120b0a2102032b050c01290906060f 60
    0x151403101c040103814401412000144202000025440355282c3c100000d00c5002d101707141c0041d83c911100044183d84204920151100d0200c2e207403040710303801801007009480300320124081c080040d01c042c00200012407000f00c0200306403c40020924219407440ea07007000030301c0c0e8003500c0c080d14150740d082014141d001c074001a4040e0a40000c9608034a64100d0070000a0000d450141100e41360001030351500144203042c05d0000040e0054021044240300440c51480000c0012501c0381018101540380c003440010300c1184503031541d000d0141c1d03d103a00ca050001c50040d04500840c0700803400b0b03101d8555014182d200c40700503a4140c2c0c3c0c0c1691a035440001007558030024002c41080030358480d07040c6e0341c00562407020f440b42c0d080c1d00300c0c48140c00c0044801d0740100343c10030503603024508600c00800e01e221510150f00359200c09a040b1802c02c147c9508462403202e00500041c8a10f04586d0440b0300c941c000980382240d8901c0c440c0c03040b50b5481c080d591301c10034441070340240e6a640c1c01d40c1d4400e102c190f = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 531987032 1250 531985782 531985793
    0x80c040903140913020304030210050a0204060e010c020a051507030f14030115090803041e0f05010e010c0507050910082e0903030f09080a0f080702030306040908090a15020c03150103 80
    0x40010f82c10061039103070002c0c880c8440c0c400326802500c003200564400f20300c1d0702c00e0000501850364011000c40c0210700b0305c0d18008000d002c88801949540c10003100c07441060456a801034000b001e040d01410449901c0247c00817442d10381c0c00001c082c5d0124802d101c142a20754031800e02604d421451f1103415086918211410003600004500c41003407004548000c610600208042d000800c00788809414520392030190307032003144107904064600c85801600f44866604002d1071030810070f007032914113550221070400c9810002a600000d03400718646080c01403000102910400f99003004041d240184480070369200005030982c2200040d42c0d8500b5103103443e08890b406000c00a02030304021429010600708041114900d0404a030b0f0b4010204003072040f550f120a2050350002a82820000d5040c144c0000e90b907030000614192040d5100c4581008006800c1c1c00e071400740c00d000d85100c5c12651035104152900100602440052144412082241c0741c0000e640e8004055000b0f010030603429910340c1c = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 531988282 1250 531987032 531987037
    0x6010f120221031e040e07081909060912030e0601091109090a091205120604050c0f130603050907050d06021615090c0f031a070e19080c04090314 64
    0x2682e00c02d4409810360040100031219420900035180515592040c0b40c01d100d20462203044400f002190501003804810041c400e50f641010a0703003400c0706c09542c3d0fa102031211040070340c020690142011004400c212040c1c120b0b00c4424400c5034942146092100c08904030740e91a48407608030703442440100201c0c2c8a95101c1044014100382d120328100d10718011403c120020754070849019a60070382601804611200d511001c000ca20349180b1300448032810f5514002c003d0511441640c0d140080b03100340403400111a904000bc0200030340303030072683d044a41c0000e868810070340403905180010380d842401040417015070360000c001401180e00b40e1540402074100702445410700310380d02d92b0b00f0b01064858501c2000f00001d0313038002c5004550b031b151500c6500c0041d0301214500c4020a030900000b4902981603401021010304503c441c0e403820811a411a0361801090b0030a500040313100300340c10b0552000e0240c56a45080390541c0c0d0300c00c03041c44111144400302400094094010100301c00d1034500 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 531989532 1250 531988282 531988319
    0x20d11030309030d11120a0507060b01050d05070c060b030f030d0f09023705011d0409020a3002030723040c1205060a05100f120603060c1106010f 64
    0x80381c1c2810103940c007080ca00005511120040388800905c5555014100b02d080040700c001661707070b400e00c3c803690005041c1d8000e079000108041d440d540710b405540d1040c401d48084400541c01070000d41000300c000341c00403c0c00e603030503241941001565101c50500292016240259000451514144a114030020110704490a03540c507259a079a401587d954a5a440d0b00384018840c8155030600b40d06090780d103500307081c200e02c170101e80340020002a13801c0080d006420000d0341aa80b9401c042c41c001400405400c1c1c0000e500030380c1404042800052842940b020f644101c010703440c901709110152601a102400007503169000103028448030f008003200c150f600c181e0707811080d40004100c00080c03da40162403100e001071018524015058100c0c0a440d4000700140d641180d03013402e1801040614490740b404030144078080680c000142c2c814500f454055215000c200902d030344038030700b486c003170700788181100006601c0e855418009070012940e6412038425204600b901464106030380c400380800075 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 531990782 1250 531989532 531989539
    0xf1106070c11060d1b0e0f09041a07050d0c09050a12050f0102070605480f0c060a060506031e04030c0203010903020718020705100f11040308180d020d11 67
    0x48004483c2c90740009000b20814004021808410711601c002c408541a041e5404006085121040903240c1800601c0f1250098441c091641d4945c00c0000e03100085c00003440a920205c0704000030150f03c8000340111800d02c00090100c0002900c0c00c540d4444207002d046e50200140e441000075212050301b03100e03820301c0381e03090300c0c4221196070700e41e401c80c1c00100094036559200d2080024420580c8440311402480c00200c1c3c2d44410308200e0841c00d03a10300c03070051404118000e189120f54200100343c3e090000e09054003651500d0148000e070300d071001541c030710900e03074148200814185050300c20780f0312410550146140d00324800c2c282e14080d1002070400d40602c0b40c800702101c00b689084c019003c910b40240c000307245451510420144160038441c1516100d4414420036002510100344080032100750180803840d04082d000c90401403102d000c0740300810500250010130080700314084c2c4044025180030004400c255410f110b9a00d0842100a6016105025030f40c0001c10034810200c607442c018 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 531992032 1250 531990782 531990803
    0x7111017010f05030c0d1106070303090c1211090a0b12030c0f03070f170f12060901090e03070f0203030d0603030801060305090102340b0a0207050c0406080c061e031302010f1106070c 80
    0xb8003c0b880d81da1010307104ad00002c1d00c50f4494818032034084802001014484a00b681d88421629000b500003007500c60b15220b00340d00e00c0131407083c203480d400941219100401100704043d1940e49240c2e2684010991030007801803162904140101100303a4a240f0b82040d032002500c3c200359214a0740e08420501095205010b11813240c21080398000340c8125402d80c1d404425500b481d20400c08090016404103100a007050b0340880d19a4001c8103460210740c0c000740a110030075813840044d0035030040c070702107040c1a072030200000181544840706504a80150b1000c00c1580c40b0316418034242e100f120000c85075182c1140c602c1a40d020b5240b0100e0f000045010f0003140ca04080d500c0e441042c80c01d440e4040001d0b0081140c9091000610602891901c11581040f0192400b02c146881e0301c0000f180354400c006c042010482c0301002c403075070035506045049080d40ca2414060081070085554401c1e80050414403100e01860301074407800c0d00d803070f00710401041613903100305044420305003c113000c03a205002c2 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 531993282 1250 531992032 531992063
    0x7080706020c060a0b1c02010504150e03101d0303010f152105070929221526160c080c011a0303130302010507111017010f05030c0d 58
    0x1d1040c00c1c05042c8061010841406072000c11040070810b941c1c500301150b1b11140540142e80280c1114102d0710340b0084120860842c40080c0c52007018600714035050b0241c4103959107407000725440039080e40c41840580c1911420780d8411a600d0209002d8001110b443c510240502004051880540480751030308000d09010404840e034a21400007198007842d46420070300a865400100410182c03001740d203800c0002c00e036071184150201741006c00281c10b020010f041941011042446012030f107001100018042c1d813102403588242400e000100018440c0d404541c02300e16904a0f00c164014214204501d502c3c1c1080c003c00a4500b5a480000d0100540d18000022821000361081c0400400005071000701003541d00019060075152a200b60030802c5814100d42d0300840380340540741c0a1030f00649035000c0789042c000a002c1a0245c1e0ba00c581040d50005456511400c0c11040020140303902e43d03140d07603c1c9098200c0740e2560107140d0f85500560a003507100c0c100011520002ca0080d86c4850b0252075 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 531994532 1250 531993282 531993307
    0x130f0810021b0f07080709180f061409160611060a0b130608070e2d0a0b04290303030709030206070614130501060b040303050d020c070f14240708070602 67
    0x580e20f000006a800c115400c20080e6000c1c40042d001344840c0304c0c280300c140195261a4004440e4a10003010081064448001e001c1940d005a001c01c80415055401e4104090060741c0e8907a0680d29074440f0300962800325030a84240d0000816003c15001082d81c0e4803462407040180804400560b048a61300e1085401e0003400d008040040c448030b4080c05043d41050354080507000700038012440094015030509208060040d004206900c5400c650350325216418038101800c03d0213921588541045032005000308140700510b000503401c00034200c0c0101801c285501c80c08102c40309030104102c0030b03003000541004c20007000f20741e01c0340d02c0020300b40c002c5041200050500780c581c00018450001c012007000400d104203000344c21040200d42c00c0516540d4002d00c58401d010703281e8202600400e2412180c1801c21004024242c1042c0640540391a0010380440c1c802d4060010700c0707104100d40300205222a0440149080c1d81d86218529200030b58a071b80505510802c001c0b100194204000d452410 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 531995782 1250 531994532 531994543
    0x170405010e060c0703030b0d020a0b030a020c0d080105030610050906060c03070c090522120f030e070902181905100207080a0b06100e0d0312020f0708130f0810021b 72
    0x2d1080b00300300d44403c09410300a0469447c20701e0300703028a103500b09420150362002950b004992212080d159299075282d1404040c0c051081910601d215401d90048065003100e040c038166131040d0101c44440d41c0b02e804c58404541c55100b41500003107100b01064250400340010418001007c049034a80843c07a500c82c02c203004958040018595100305011a80b1600c0584400001c0c440140301000001c80d00c03003d1381201880644011f00900c1c80e10241c25500a401c51203095154001303560165030389014a4002c5d50000e0035040f114100740303071001c07400d1a100a917070404108503510840814104002d00080380014000001984250400060407140410a101e0054031450b1588003c1c1840001c1c42822540201c1100034850840c00511071501c07000310208416403d0700d844902c021315203207160020b10544048010b200d42c0000c0d42000d004001f0014404621401080c2e205265101c0c225202041280031b040d149802000341080014884d8000c0c00120085a81e014070b4080120343c07940c6040c = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 531997032 1250 531995782 531995791
    0x40b0c06040506071103180109031a010e010801060608060609040204030506090f010c0e09060112110a030e0706140a12020d020c0c01021005010f06080c090a080703170703170405010e06 81
    0x258000e40c208400c101e814000f090f00054181058080001ca04000980320f0049581c450040300d0725001c500d48680c42076400030011504440780f2a8111186600c120031801c09000d08406580c19200000d0000350520410040368400d54607040701d52100420882141d11446450358419020700000c0045034040c0700841c0182c840400801c2c5541404129038251403180c408007040c000615600083c0707880c0d401807a0b922103000d103002480b1041280070040249810b4000c61140100850910002c41d0154070103000c4010036411111515a100000c54444545610000c03149805125040b035107401000c5139031129000362009410540e11585190898020540240c840e6110b003031501007550b01800301054210840c0d000380140e606180082c080d0741480c2c07180e4400c121185d40084d01c0f80075110251442084001c1030b40350b4642e6078950156480046000550708241c80c81d540031401c4220004454007140c1c56254240049000c28114070010b0004006480554854140c030140342024005940705 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 531998282 1250 531997032 531997057
    0x30706200c0307060612080301091d1b01020613170f1606060e060a0f120f021e01021e06150d060f0e010b0a08060a090309170d0f1e0f05040b 62
    0x150b01c3d40f8100701c402d80b080d0380c0c48881041d84c0f03c030107540443e030200212030540704669800704200004000e40c40c44454403e0480b88140280202c11911400e403149003082d005090b8200e8405488a600c51120365140d00d20081030300f100c1440310040d00c06110081d10405004207a40703424424803030144130902d404030310103c0340c40b580d50b4414080510f41340b100e1a000401920080c0304142070002d6884142080c0c018005c1340c405440c0c80a081000d00049520300d16405001866056501440340310083c00641c1c1c264050b000b0b081100e0090f40b0307040071a803844510b941c0104130300e4481011485101403c070302c04a40020001c0059000f1484900800340b07100c0c02c0080004611031071000d1142103d1f0358485081c4030300c0798070904010700000012620f42101d01d1290019080030503103000d85440e0703840e030304c01081c40b8084418081c00c02008900703004050318644030400c42c80248682115010b9180884802f2440303540c0c00079200e10720508400f840200203082c410301c1c29407182030010140d003211300034512 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 531999532 1250 531998282 531998287
    0x6170115051c14090c010f05090a0909060501031a1b09061207080603010b030f0c12010209090403020c0102011401060c0605090f030c10140708011203090905090303070e06030603030706200c03 84
    0x520f8a0103803201c0d507210980c0300150103030070310680000f00b107140c840101000b0498003080b00403482c0c0d2412044d030014845080708001d11142031800710040c1509202c15143c0514035110a841c1c0901c0c0310b030340c0307200d0043c0303180b02c0e035001c00c004201304c007107400422a035604200e061080000290090b440c49000e50301c60340b00c0c0500e0b03150880c205800d503070740e21340c3c41c83c0a07400c50f4070b4102000c40002119502c60808682c060307550402500000e00a0156400f40c3d81e002c10000107203c04c0c1900401d030301c14400400e034000d0054405250320100c002100b841090006503141d100080455025806160040251010360703e030030214640d62840d54201c0481440743d500141b401e580f11408500c500b07600d42603400c6201c1841d03d040d4002030310b0785405215909401c80c0201d00b0b0300401d48501e0210b00a020740920030402400c1084140d81d8a0700122908000700f12118003400b050f20b4514203917407103004000c0007507203441a40d6441802421401404c040e150041900750746031458004c014000e110502401543c = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 532000782 1250 531999532 531999551
    0x506090c010201060612271208060f1305090a0b012c0906011703070b070c1239021008040b071407020d240e0706170115051c 55
    0xe003003641038002607040d60324100302000703c60780000311143c94031041c040019144d005500e82451034048075a080300600d040080b064100201491403030360348169076941480950302d103005d2001809081c000954020b285001e00440000543c005550011307a40080d00c1f20358020b9981e178003650314282c018842e1040123550000d5481c4890588501c4624802003600003801c000c804980c032031038180a00c61281410509500710f02c84100211400581e0002d440c450a140442005049102c080800c8425821307210383c8044407803080216003d02c8198941509802c040c00e00d45004004030b00d0a408416034001c0e00f100c0c00741e9680606400b040b00345441741c00c1145003516200c444074100034030910500c10b00300d140c1544264213800b91a600b69050390b0205584c115402c0c082228100b006420300c0740c045108035500c12108075000102c80c1000c1904940c010f83e2030f9042a5101d84a04090203040701031400104a04c00703001c401c0380c261843d941022032510011a9000c0c0d0003400b8002440c1c0e58503210440700303 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 532002032 1250 532000782 532000801
    0x30c051504030b040b06062115030d090b03100e0c090315070c0b150d110411090616110d061506080403171b0d20090306012c040506 58
    0x5004844000001807030203055980300003d4203000380002d005107040038001717581500e800c01219051082d02c60211a044010040100d10400132240da03d0440e80e40030f4111180d0600180c0c210319a034182d11181d10142c1440b503001000d402c01440c5550341901042c0015192011000d294060b030316400003a590740303603004140751500715100845050070b2952010007094903071103608548403e604c41050420f07502ca01c440b2030702d400030305200d0560010000030009e040004070141001045020f480c20f1154041418088010f4007401c10071a1300030b041003005401241c1829048001a8403552900395000d2000c008a2940c060300f040807110300d982ca400d0000603800d40300c141001854285002c107010b1400e50b4005000c0c00084410a0001c18003601280d4500c00c544449402240085001e6480ea04400b2240c005018200300b2500b1700b0081c841c20441c003462a1088403200d0601034004c00c030591814440d564518600910000d03922001c803000e603803103d004580c03d40501c0c00769004150398204180e20 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 532003282 1250 532002032 532002049
    0x4240f0302090906071710031a04050d0e030304090f02040b1606050a0b0d0b0612060703060603050603061e0702010f020d02070311012c07030807081306180b0a05070b01030c05 77
    0xb031040e03584c05001080540b5034403034040c03070114000800d1011540c44e038101c0744520003030035000100b20191080780c11100d2030700d8801c00c0f4800ca0045d000c40b10a0540070206589041880c0400ca400d5081044140704a031200c2e0400c1144100301000140380070b41c5d42100454a070004444500300c0c400c3c61010700e0900080e409016008418000204041410b03280002c1078000341060090030840214001142c0d13690380160f24100c0403071201601c2041c0380c2104001e0003040c0d1344c0600c00219240201142080c20300283d13440c82203030300d080c0d800c507285010601d400703040340010603840840d9240c00320110399160341d0000e0140340044040c0585c681d81286405010025040c1400751143c0c50300c20038103007208610b0003441c144800e00050b244840f1921021504020060300040d002150001d07401e000c00c1030b404001d044d01210b6003003000c240e40d294401108c182501082610490881c12070074003080f084040140b6a60f10507092003480c0c80c10f0307035958103c101e000341e0040c2c4510810800c100203d0038844203 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 532004532 1250 532003282 532003291
    0x90302070b031e0a020c06010602010518060108060f10120302160929030c090c040302010f020312040816021003090c1a1603030212090705030705090c030604240f030209 74
    0x514a042d032422038188028901e4052800c1d0a8818032004a0040e2034198119116068188240d51880da1140d8001c0d002e00419100303040802c0035a030381c0410007403003c075501c0e069448100203084207407605425003203540710140080d200a1b0080f1700002d2409601c103907c81925109401034030341e2555a86001800503020703032145100c2c42c1810150f42040800c036441c407890446415003000903040c480046072130b000450b03020b10b40000300030003840004002000a00105da01c01d994010810040c414204c0e2240501951601c6141c189408600050145800350101c007140e0740c04402c0a01468001500c01e0701e0701d07214400401e580d50b8000e02845160b00f184000380641ca000158448148145400d05120380d55844003c0c0400c41010410503200340c04680e00d81c45803807a0382466091004000e80c40f0f900070320a0300d20a101d1071800088900b8420a598492017031103000500f0b55a4101c203000140c114000e085807076601080103c0382031580e42060202074407070511a400f02c07a0441c810b0201540c0040d1 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 532005782 1250 532004532 532004549
    0xb0616030210140906040f03020304080a080408010c030e0330010303050a03060902040b0d02090a0902070c0806010e04030509041a04050c0c2802010c03170103120201050703150501050705100c0309030207 89
    0xc0280c11382000500725040395004894005008840c02c1c120304501460b0851020b85c015615014188180c81c1c01820541d05410005c110300802c1840580403525804d0103a4400e030401e21079040e03442c0e0740b42d030a1720079440c0c0201c6841c1c00d6800042901803000c0240c100328003098010410540e5242c0c1445140302401e41900c045281904010f00d0302071071300035a5a131110003500014001c0b100e459a4500e040100600328040d92034100c2450050310808540c0206420761140070000510810100081c3c0d0082d60561201c038541032030303c002d2002070328141c1c0103c1030500d6480006406074596206003480350340c20300c121985545102001904009604900096811044207080402e501c0c0c0c040c0103401c41d609080020030074407545001e4416811448003160b030f14000d040000240b00e0b40000010710041c181d402013100e030307036074800036002c5032a00c0640034440440c5040030301075540640c0c010100075000d01e088500d01c503404000c400a486490a0580000e80c0300c070044c40401d46c0400a0402602842 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 532007032 1250 532005782 532005821
    0x14011406061b0f0102030103060c080c040506031504180c080106121505060d050703030c02040c110c01030203151306050a060f0f120e0607081f060c060b0616030210 72
    0xe40008110303015030010106030707044071052001c03030420811600303402c40404030081d5125a500d050200c000d0032100b50780004103200000003071a2030032030400c0360b080e03030001021030b41035854001c0c0b008100030307000000d036804c90b40d01c0320762640b4000c104c2400c061003403040b03e0074110305003010346c11420742e1008e44c06107031107588007440c0b08005075034100703988008110302000042aa41d80740004003070407240340000c1c2c1540a88034011090540c84001e054010340261800c0c030580403412002c80700307516127545441098100601080d030304d40c030035001560031090340b41442c0126021100003640c15000d20b100d030b405040d80c07004204400e0600e010382034010841420b01041880800c0006410400403004010170440c4841c01d190000780b00394080174000d03196404485e490300c0d083c14042c00d07507107007076400760b01c0d0504202e07800d000100c0310b141c102c05581c8541c0e541c91120906503036007409491030800032a4806000e000406095801c0800410300b070b80640d0060090342c989003001012036500750040c0141e00c060 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 532008282 1250 532007032 532007041
    0x13051c020319021915081b09090c0904110d06091b03050705040308030c0307083312061e0601030c320408010903020708010614012a140114 61
    0x10403084000103003441564a03085080c80010a10b40100f1345000c21000d004a000c1900c26031441d075180803113000d888051443e1281250241000480c1c00c0e0903680a80403c5402d01504140403000d80011030300c445507040120b440d000406586062030441d2403080040380c150105111401a80000c0014032410062400c8000c4824500c40a031308805080c1a10350300401d034003604c600e086030001c41e0810451502c03805c2c0b00040c3c100c10790056a1001c0085c0ba610042403076110004404100a2051603c1d10142555007040385240d03c0003030342c00d561142c1d480d180c00e01c4903182440981e22440082207035648801d03100214000003040501203030304252078202c0c0031040d980c1000780d4074400c40b0b4070550301e44048142600182c0703050040980c4a4101300104001502400c1500510310884c401c0d02070300c0c442502c1d02019400c0301e9040c49900d5084629070034280441d40aa40c540403504aa0000031f141082d00c003400b1811041030310001c440e0b40c42154a1201e0454080c800d08035084138100310040d80342003 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 532009532 1250 532008282 532008289
    0x9090203012d080102070c080606031c14091003090b0711070504020906090a0644090a081303020a090b010906030e01060302040e1c0513120c0b13051c02 67
    0x1a103900548000300c0c402d41d55a0b44014200d1000001d084483c000e550740c01280c0f8107500a114035108145640c499032004c00d009103804070b56048d012a00701100405411043da04407001250318401a0101c8404c000c600c07500e4640459001c54480c154a010030303042524904113595903401814202002a421030007803d214010440004031030003110b02584400c40140090028440c8030545075114100f800005030799908a1084500c0e5120008042d141100244000c100350504c0c1c0c0c08015a030381c114010302403410704020f00a8100d101002280c00301d61256035404129800304005c011146a101820011450005410405490361490502003149100c00180401c3c0b90740c0a14800e141d00d681143d60300641c00d43c050b00055400601c03c1c00000c0c0c3c1e04400750346800d450501203200b641c05e40042c0300f216020380200e0b9006041c000c1c0c0042c10380c0c070380030700b0001600712a034003156542c2c0c00c903d000a2006244015000039107a080001810600d40010441054021102d40070204901c0e0f1300d9001598 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 532010782 1250 532009532 532009559
    0x14030f070303141204050d03110f030f090a05030c011a010906051914160605060f0a0314011103010b0a020f0f030706090819053016030e01050c0a0909020301 69
    0x280d040c203200790303624107845002c0b0321802130040c3e034014004402c081109106001548150002040d1420403c01110350f07140c0c4028440c42c040c44803c4c2c5800c00201d00003c90300b0401c641c1c0001c1400586441c1d0480b5500c503421a80207991407200d9a450b0481494000046150204e1108090070080046445c020014140b4040c2e90f1080c420060008640e0306a640100c0b241c46109070a2058250f6441280c9014080311010800c155a6130f4034020000383c0900b0181c2c2c41c4d030369890001b400e00108914580d98110702039001105d0380c00740d5485503103518003602c040000d940600b40c02034005880e1242040000d2802200f83c0b005182035010314000c0c50304400c04812510b80542124010a0070365407130401c0030b21407043d4108036030440f039100c00d084400c0b580b0601410980c0707414401082c60400003c1c1070b181c1e410003a01f440e441a4154400300310341504201d4041200c0e034140c10003042d4500905160740c2111380844210f03880c0c6000151040d4525070100a4a0241408500031411941400c1a005101 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 532012032 1250 532010782 532010789
    0xc0503040b0f06040f0c021011040e0c071a0106030911090f0a0207030507150b130e030d020c0c0a0806070906050c1c021f0204180e0d0518061314030f07 67
    0x25a000c00700f4000d80382d541161030b00c816604414024044060380003076a400040a03102002e92400868055401410003114119002201600c420383c82d07103c004a1164030841007124040a01e12040c10640002e0f00524000c001a403400130fa40c201c81d08080c62940343c4040c00522600a00c0100099010706840154111516800068940000e460b040c0c48911031008041e150680c900c942083c0d0b120260400750994000f6200b180b002d0a000740d52100f910540842c20450343c005002da040c0300304542e030203000c041140b10210b50300c10410340c0c0485c929030015004400c09800c00820005641c0e00101000000c00e154906945045000c0d10025100c00e801014149040349111000186d28030801044100005840180e00107100900790b50000b50302901c55003000401e580400c146011017846008411020395028101e52451028222040d600000c540f545983e0742c0d040c0a100343d1615409810805066035400b01507504050030740e4200794001020502c00e50102150000e540f00104404046 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 532013282 1250 532012032 532012051
    0x6041a12250f022103060307080d120207061b11011503030c020f0109171f020403030512060307090903020a260a0503071407110a050306130b06060403061e0c0503040b 73
    0x207003030320080803810604c80042c40034242c180544960921500c0d42d0086018410071011145919030300c40d811611803416018400c00b241c40c1c0041190f910000b50020940244a660005a1440c0a00418020b103440403441c2000840564015207992000d12504d00c40c80c07080681c01940b14910390300184414180d107002402004014026001039000b0aa0100503002c2c041201030080c04250740795540b00d12048981004170342c904421005e200e40c500c00c54081da501a52860320300300341c920f01c041030100d02400958051040040000e4110740520604900300e22a902070900c5924500f0844403040e40c00c0c0c1c44050420031000c684a2551b03000084610044050815035141e6840050965043c03110b000c81001501001540e5810000d440c0140b81010b0021208000d0b02d039246c00500d0b81c4c0320000c03140c071041d040002032224007160005191035407003c00201441d280039125901c80c0141e5043c8100c2c19900d100403086100c0c0784039940a6691502c16900d012400e40c0780540385c0e85609036024001c0f005 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 532014388 1106 532013282 532013297
    0x30c01021b0d08070e0103090f080a0f030b09090c090408120c0c1b150904090210090f06020c0f040b010e030d050c010b030313060e06041a1225 63
    0x160000c5e80d609004420000015402000059000d035072058140e035141d03000524800c01080c002030301d581c038482034820380708010f401d4820b10100d01e03102c0e016030070400480510000360100c602d08200c41200c83e680b95070500c0c5255100710b5a090800300051020044202405801400c0300040f4034100c80300b500002801890341215070300e046510803084001a22012031101c09080f01c000003c00021b015550361340042c158100034020480481c80c980e104010125a00c070341c08000f01080c1c0098071403041c8003000a2070030b02d011010644150b40c0c2d1030441d002a4482d03420003065407005411031313103404003500c4050700d07a400c100c02004c0075608080003008682000310695668405823110826400c0c02d1031410381d8120400c83d04642c006030b00740000a00d52100d180124181e8500451542e81c8010500740b1300000c00300103114a0f50143d41c060b8840300c2508409503501121407504d001d03030 = true := by decide +kernel

theorem cover : BRFrame.Cov 531834532 532014388 := by
  have h0 := BRFrame.cov_init 531834532
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531834532 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531834532 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531834532 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531834532 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531834532 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531834532 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531834532 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531834532 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531834532 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531834532 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531834532 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531834532 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531834532 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531834532 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531834532 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531834532 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531834532 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531834532 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531834532 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531834532 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531834532 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531834532 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531834532 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531834532 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531834532 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531834532 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531834532 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531834532 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531834532 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531834532 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531834532 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531834532 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531834532 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531834532 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531834532 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531834532 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531834532 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531834532 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531834532 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531834532 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531834532 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531834532 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531834532 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531834532 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531834532 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531834532 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531834532 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531834532 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531834532 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531834532 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531834532 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531834532 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531834532 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531834532 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531834532 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531834532 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531834532 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531834532 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531834532 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531834532 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531834532 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531834532 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531834532 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531834532 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531834532 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531834532 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531834532 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531834532 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531834532 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531834532 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531834532 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531834532 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531834532 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531834532 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531834532 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531834532 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531834532 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531834532 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531834532 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531834532 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531834532 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531834532 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531834532 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531834532 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531834532 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531834532 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531834532 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531834532 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531834532 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531834532 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531834532 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531834532 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531834532 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531834532 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531834532 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531834532 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531834532 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531834532 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531834532 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531834532 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531834532 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531834532 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531834532 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531834532 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531834532 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531834532 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531834532 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531834532 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531834532 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531834532 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531834532 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531834532 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531834532 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531834532 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531834532 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531834532 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531834532 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531834532 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531834532 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531834532 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531834532 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531834532 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531834532 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531834532 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531834532 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531834532 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531834532 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531834532 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531834532 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531834532 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531834532 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531834532 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531834532 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531834532 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531834532 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531834532 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531834532 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531834532 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531834532 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531834532 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531834532 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531834532 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531834532 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531834532 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 531834532 ≤ n) (h2 : n < 532014388) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
