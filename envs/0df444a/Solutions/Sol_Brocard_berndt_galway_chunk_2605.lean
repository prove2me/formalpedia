-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2605
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T07:12:04.869577+00:00
-- url     : https://prove2.me/submissions/cdffa8c5-9a90-4480-869f-24b8feb22377

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 468345323 ≤ n < 468525179 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 468346573 1250 468345323 468345329
    0x180209060306060d03050a03110408010b010f0f0e060705030904020f031012020a050409171b1203150d05120d020a020c18190603050a12171003140309040c031b0306 72
    0xb00c84004071103545c20740d03c03500020f110105060701c4038440c95010728000c0240008100c500c00210303800f480f09001410f85071000503040c2c2003006440014801940141055041c180103540803940d4a080b410030a00794010b9442855000b800090202c5c00241c400c00030310300500c1031100000b0200d40e00d6560101040d01020001c1d041808001704001c00c2c80c0643c0810740d88c50244418001030b28208107840c036903a00401c11008041d070b0201c000c80184100300180384000400000203491070821503001e803070b040c43c910030040c82950380150340b000700502030000f800402c030710141c2d0715160003624044e03034060f40002d0329620041c4180700e4a104103152440c2407114840144c0b07423140c244d40b600064580c400455140130700c00541c80e030307100100240c0c042140140460062442d0031082c40645001813006500c81c2400d100c00800c2c005003c04040c06154860032a5402144020780d80000b040860950044500d119800392501051030715140d0550800c40d4001c5040e44444140403142c2c4080d005c03030300180 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 468347823 1250 468346573 468346579
    0x1b0304090b120102070201121a100906020f030408030301051002150411180411060d11040807060f021204060c020f040213181107020f030c0d05030a0206060d0f15020d18020906030606 80
    0x245041041155544074009c21115624a82d50426a03580447d84808250718104001480684108021513050151351407185441020714906854082c4850b964001801858440c12074004030100183c002c1000c0a03c042c011824046246000d04004040440d480800e03401204041c04215404d110106014403481d03000b1000803510260405000441e00104a028149507850071018040381d401c030040c10040c07860030700800c0c0301801c100c4024044a0000640030070340d403003801b01e0301d00f170381c685410b035010b0b10000c2c5000c0b10703401d1140c0001004c2c1000c140d40385e038010344006503607204c28180301c1486081e40c901c3c0b585121800310300c5045008841600c00e0300e25285130148241001072038100b006480c041ca00400710740302c02113000c001803801360900070700300c40300d6000250301403030715805100325940320038119400d00306158141c45002084900d0003004005002c044c40f07842d49005294152051580503880800c04a100d0324106182a141408183d10815007240042c82c1451300060142c0b1982005d = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 468349073 1250 468347823 468347837
    0x7020a121211360406090e0c030c060d1a04020409090b01050f0d020415080d0507140c061206041104080a06060b0903071205011b260c09061b0304090b120102070201 72
    0xc1e8001e5030124125065094407054103e62942c00340d41c941c080d500c06400c004400050207503c1c204054581005006524060780001a100850790b42b5002602c401c601042408290000804090303c0000700da00d40155000c1d1012074080345680f015480314070b903588504044545a41c8079010072150a4003041c181d0307032040c00b6105c50030050030030f0340040015460054080e1080c1c0d8840340780c2407c00c0a094041c00000314041003d01c18064100e2240c10b0b2400c03200c0240070315503002008150540301c0e200c10114808200d0010800d141c9840d4000d4000843c0c407801c064441d5240c210f41c07078072003800e00b405a80701070400384c01240640d41041202c0d190305c0000d00030035809190900349000710f034682000f61040d56a40d60b4012101c0c0e42941c6000640003241c3d43c5c1441d841d01c0500c0d501c0c140c09207a038140b092405050400040724104000c41320242d4041780c00c107490b00030070350f0000c64400140751501098000400c0005001805803c001501001102d200e82e01c00030750280c080c01c074010000041c1c006000 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 468350323 1250 468349073 468349117
    0x50f1c03090c030c0605070c14030d08060d0b011806080f070603150b19030c030c0906030b061608030f0c0717030a0b0d032304050a0e07020a121211 65
    0x980c41100706a11a02444441942d02e888030b0724990310580c072120109000188240c100004030394038102500003801c014060fa100304021941d50118100703100280f14515020450598031880741c020503175880321046469603155040d05030320380c1c1541c840741d00c81400c210000ca84400c000c1207851105900d4002800b00a203400c908802501d280710140c00d50012442012030007c0540004224480365400c7c40002c40301c898400504442c6000c03803e90415140c074180305070f1ba44d4801c45078411205145400b041900d4044000340c05403140c9501640e06c0d18001118000300460240a1442440580d88498459503505525107480c45042d04c0244082c03011101c00300e030600590040c0d50005402c003030000e003181903580821054204c9000a401141c040b40b0101504c040c0c600ca0b414500c8200d0f28140c4c1001d15041c080341c200b002c00e0041388612000301e000191000e108001d81e01e00d240d0040c001492043c4003040251008a070324858280041c1460440c1c0b00020b1110200e804554011a400c0c1e41090 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 468351573 1250 468350323 468350327
    0x303061e030708010c090902070b0a050403030b0607060b040e070509010b030c041d092e321005040c0f1b0501020c0714120703150b04050f0103050f1c 66
    0x2030100d60345002080600030000c0e850070031039207014100c10000002c0350301c0c1200c0060003042c03041d80204c00950040013480001000d0310381d82500a04400804039103a211171034107901030504000040e41201d0041100420b10810f50401c120064040d18100502c0d03820182c4c03683ca941340760203004c1c0c001841c10010000300002d40c00459100080c403038143e060681355225141e50314259440b16a40c1c0e0714607020300101d00f5051104452100940c258400c010411156034035144080340784038185d071581c90040e2596000c1080f64200950104008060884078910a02900203010303200300444401c0c02c0008900c50405114041845c500340d01c4001001341c15043c103d800086803164100701e501074514000c0043d03c240003801d492000040236240281c1402002c0f04043c5000c6006446254500140c0384190300102d100416660004071025005480d00c1c0b00f54068100200340c19002443e050401c1070202242007180d0507030b0322030000c0c1c3d042d401c0390003078243d500d13003080c482542070550b00c60101389203034 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 468352823 1250 468351573 468351589
    0xe1e040b0d0230030a030504051e19020d1401020309060703090c090e0a1407080d020c0f010810180504031106070f08071709011b080405060a0218060d0b01030617030306 74
    0x3d01c1040f00d82620100e00000c0d54210b030044110203021a4440d004d00c01000420300c00c4083c2128000340303601c66003c001c0314017642e03050100c0380c404258030240500c20564170ba640c0b50400c09034000b410344400040c0b00110301d0003540304845069240c004c20300811001407080c05900003482e00710071581941c07410b0000030402031003401340300441441400c091030001210308091840c504d14220240c201e60349445410750400b0741c40d02e2008110b400c07807a01a0742503510040c10314010f40007860a643c0a40d41c0c0307540c0da2402c84282e00415002440c01041d03491501e00c03a00f01921543c03080da070340d050989180158940d561702c10f8810744c01181c81241c1c0c11000394800c241e02e0380d1001040c5440307241d000c20a00f50107102c0000351107540140e515603050200340440707848501c1d4450302070710300074240c2d180c180c90b01500c1d05005001e8054042d00000c0c111a0303000c484000d50003011005003020740d40c0c070030708044400804030304110350b01190402000292030496000e40c0c0003900d60031000395180d941c48104003d142 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 468354073 1250 468352823 468352879
    0x30c040603051f031b08010f09030905030c150d060b0c0106080106050604080d0f0203161a1803030c030403020109150506010822140f06040f05070b0a0903030f0e1e040b0d02 76
    0x4401e0143d070011b0008001d0203a143d240e4070004001901d4009424014901403043e0405406a485081004559100c1d1030081100b8051020300e50340350b801585001000c0d11076031f84a01028100860b00201550042d400641140c010400070072100e03544a080c07049600540c45035003419000000d5584480340250701410a5541c01d00c103803441d0035040c054048070f11120181c1501c07900c002c9001404500210945290000a503165140710240b14020595581c84004c1905448072008008242014000d402400005601c00e40307400c0d00f0200110010b00820084810f140080c0c0e001c00440c0e4440381c42c080c0f03c8a00e240301c402c0c044200c0c001b6142e0360046440445101c000340719044090807120030a00491340280e100702c90783c901206460070034914144694103c210380344001c001c5a000141c0041d81c0c002241e92608010102400c070f440306840328104e46d2085031b08040c3c8444c040c045424102043c814181c03040b1420810000140140a44010074803c000d4108403019181c60140301800d0747c0b0030f00 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 468355323 1250 468354073 468354113
    0x1c15060813080d1e09020d02240a0809161809081608031f08060f040807140304050a0f030215091201020d3903020d0b06030c040603051f03 61
    0xa004210b94810030580c1c00101d00709041941e440320750015410402d00c2080342c83c0ea8200601035036480b500090503042805100a00c13412011404a071103c24400c114581d160100c1c4010341c40f088504006403200904680b40112b5000304840f041040a0601104050f560200d20030080405d500b1505e00062054082c00e513070f01042885020342c1078108400100d0440d1240c45002c0d12801c020540c0c0c5000c90030882510281d103403021003800b07810300c00034049602c112181c9003580b094856042840c1c451107910b6019144d80400c404000103808008000d000300d4109503800b460850303031042104281d807518003000b0342c012145410244031003506006052003010003001c0c0d58031040455180c13400ca0303000004013226070307840d0881c2c1c080541d03c0c051398480c814800c1c4078500b020f0860882440250030390410342000d00d940403441099861482e808481c501c0d0024001907a01d090203144945190418070500c13000030305040010b040140c02d079641c0003040c801d03889945241825a41c550120400301c1002010f = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 468356573 1250 468355323 468355351
    0x120606031e151e150306050f01030b07141606050601080915180c090403020d0e0901030b0f1005040e0f06150904032109032d020c010e120d051c150608 66
    0x7003c1e24031407041441000d0303559400b03130b00240380d03180c40320070351390000c0998031003690350001000031820702048250b00c00d9282c0b038a11290f03021403035403018500620b14259442c0800e158031400b0081c665000c0d0b40a0b0000340c882c0e0400c0e596204500c1d0b030b5a03150342c071014020500e080c0801c0c0303411742080f81401c0201600043da002e0044807000304151000c2102e041e4016400a45884090340e049040c0f03403114001a0b981c00303000c2d81592036005110034050413803c04c04031088000b446602e20916148050a00100240103a030144a102c0ea504d90010155070322074003800d4082907042c0b60210084031031100141c0880d0140c2c0e210b0310241e0b01e14104808200f2291041ea4540001841600c115000c0a21a484880c3d0154070204420030400c10940c0d00344900c903500c1d640c0000c00780c0028040c3c0840e2001d01c2c25040301645030b0007003110240781e08100302881c42044007094100c0d42000c0a0a42c111421549950051b6809c683e0801d580b1100704800fa00f42180c601030045500c2400302a0740405070b00c03c43d070 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 468357823 1250 468356573 468356621
    0x30102090d1e02090702070e0105040b090103110d080a05090103150f050d260a030c0207050102061b091e12150406020c0313060908010f060f0b0a09120606031e15 71
    0x381c84c0e0000f00d41d0840182c00c4200e00380304160010a40501409003600c080258204980c040391002c241804041c1c500c0640b4641900c01d130b40c03000c00a010b030350f5000188a45482c60404c024005030450100180440d0404030144109071500d10540111000c00000b82c0d51186007009201040d00000c00c143d0380040c009504400762405042c42c0100341c8164004250380d162a650002e00f103d0200c458082190404079042020383e1340018443d0f0480789103010080c5540340c0e00403480c2e045c410044800d420030707204002e2721034040c0f0009807001d014205503001c0070001c43c011601522003040000c8200880d08800c04600030403056405000720380c000104880c07401c034210000190f10800c69000c0f00c00600c0e04803040c001d40c03000780a145c0041e1040c490512017507080100207100183c260180c2c401401c0089401e8507458814500700c0024281000c40200c0400103040c13881c060410f07400180c03015180a4450510a8200c144602032140c1000c40307a91b0f800a40c5100401520105030104a00c01c071080d0b1503 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 468359073 1250 468357823 468357829
    0xc0405130605010e15040504051b0109030f0501050f09070b030718050405041b060f0e04020a0512040c08010b09060f04090302010615230c030a0503090a140303040c05030102090d1e02 80
    0x1c6001e0700c18416501654500240385610070307607101070800c1c01941058144230006a0020345280d242d03400080d10b05124614400490b039103091540054205150307000054140441940b025000f82c03541e802c1c00200d95141084160b03954907601c503600071400c080000407888d81c81204e074204003180e003600c8108469540c100103001d44200340c400ba945110040d1801101e460b0030011180109600d0608502074101200c01408800d4114907042c0100c3e00002e00da0380413407081080358100701005c81081700310706040c2440b40e1902100c3c02600859882e140c20345003070f86030180499101c0c480060038940d02e08103000c1404007074000200118250364a5410210f482044a96000c020940030b0f81d80c0320283c0710100140310b0507c199002d5404511040202c00d10b02900801191156156402c0180c0c1e0387d1204800c01d841c2c0b030716400d00544a1110f0b002c41c0128118003000450040c0d01130714001030f2054803402090300300e2040d8800d80340e024104814041c00500460b86121183d0042410401440925008 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 468360323 1250 468359073 468359081
    0x605031909050c0405060f0f010809010e0d02100b040203060f0409140304081b0901080304050105030907080105010b071a0f1302040b060a030203060118030507090e030705100e100b030c04051306 85
    0x100300d82c950003240c0d55640070b0070244280c80c4e200a08072000d805140c1d00c1c02c081142c01006044181c10040f00d00001024100c0941002e840d1041c80021548400e004880081d1030f03d460100031a052030509014201301e1a1074000e1b03d0094000400415a10214800300801040580800c442c0900010400e402c07645043c4007810041c03144001520b4110172440c03001d202000c1d606101072040d89010014080c9c000c000081d101501c04c01c3c2030050384c91302c40da0301c12843c180715507100340b0403076082c44008036206c031040c2d02070704a05120300e95a40c0072106000161000c150704441d0521540201400518129041e5000780100350001d04005081200030780411b07150b90120314040e01090700001404407559001a025403035054404041640504551f981c1e40c8884440c810548a01e41b685414280700310f09104444482d644001103074400c2520b40f000c030000d41200510800d09010300c117940c60a540440c05400b85404d03004000d0400900b45008100003880c0140516124078000c1e24503100080041c85 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 468361573 1250 468360323 468360341
    0x7080c1c11030a1d06011203122f0a020a02011b0602030a0e07060c0f110117040c03050c0301020406020a150b0909010623060d1d010f0501170106050a06050319 70
    0x10180b40d40c2e180403600300c0107641042c204c80c1000107078906802d26a00c80400c101c0d0640d2031452a0708038079901401c2c100c401c14801c6203a18035403894610000021421900c54100e40c484601c40196413801d00601114036020b240c16460250708483c400c10015845580184074103040215204142c0c01d040c0c881c642260005c032040c0c03280c0b666503400072400396020442c060052440d850110b031415000e0303070b90303a000b0350009100800480804400c040aa800744001a4069400000c0780009107042c0c10040182071003444190380c180030394503d4038098201070007240c09131110b43d0001d15820340c03680e82d41c0da49946280a410140c075500c0310303003e0b175550300d10054502403c503240002c82d946081c1944117403002d40901c80190b100c040d400214601e51035082c15035185084824000803960059007510f150480702140c481c929500e403a41070f020500c5070741c0c4080e060310003003501501859140000c103402c8440c42c1c01042c1c1c2c000c946030400c0109071700c20402964003601300c1550003940322800c4249002d80307800fa1 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 468362823 1250 468361573 468361601
    0xe011d250b1611030106030302070308071e0501050402090a060f050105031506040305070e070801061b0c090c0c05070b0a0503010b03070c0c060f030b04110f0d1805070e010b0307080c1c 81
    0x71a901c00f4002d40480d8442054030407002040814a1b50360080d41d942070a110040560602041541c00d10594600c084440400d03545001c4076540b0070f14246000302011103040344645001408102d000743c83d846914107807090f040c8164030f041c1c10000155003540000346007400b05503080040c42410344403580a800110710480c01002d541d1705125030113284082c0140781c40c040201c200010444258091101c42003d45c144100454008050410760341c141001d800400c1d64506190b440382880340d001000504060040098488039a01c4400703681c2c4074410f4080083c0005c1d000d00041c4030714442c2900071074100f042428440d80b01c0010b56221342040c4130070340c04000400c0024079240e12485d054000c180942004035000c00264007103038907401e0035016450180c0301102009c43d0030705680800c1e902c940049417208981704880903017840c02c655581218002d000c0e880e05070400000c1e02c2110841528002c1c070300c1e6212a1039503030b503024601c3c4060b0040800d5034000c030900d071030b5003074608600e105402d00107941c4 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 468364073 1250 468362823 468362857
    0x8040306110903061b1c0b0307030305090f06120708090a0c030614010506131502190807060b12030406030513150b0102060705090603010506160b0a0e011d250b 70
    0xb010400d801c1c820020691441c210340f411031000009000d03005c90300064a440c00b100301180c0900c0400c0d005007814510141c00d449000404418103802002410543c0300481e407420001d9142401c1c40303943d008840c42c1c0708003c840900030a030414041d101035584030f0040070440303a03000d5454450b41c3c10042d85078425201c1550310415203c5d59564a4946405880c003602c01c03602e08040030001220707100d00e903c58940b07805c010341c200c004414428800c0240d2600300074a0600031001e541806c010540c400801265058a045031002c403605020b1080d02d20010030310051030900c4d18107001030300640801020074031080841000400015070f54038050001c0010b030000000c0800740200068500140a018034050000922a40b000b603540c0104590558006941003a183c9251030380c209000d4800c04001492044810100400004540d001404003a4418000c0c8410384c00c0d492034014080a010000842d608030320001340b14802c440d0070720340c0800303100150301503416944d000c0b40c6001d41000c8101c12102d480c0c = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 468365323 1250 468364073 468364087
    0xe0c0a0303050a0807030b1003050709090f0b040b030a03050d0c091505070b061906030e10090302150106080c03040b0402010c021003060810060e071b0c09060e160f0c0804030611 78
    0x1014000980c000b0a5040c07c00a540004000942c01c010b08481d107810141c880d00000c00b403501c02e001d09401040b54040500100d11644401c001401802031b040d8004d5103400301d440c100c1e181c00102c60b90740d02d8154440514103803240a030314019000100c5281e09005c8042e4001421407000d00140c119003126544403070b00d0740032900e03040d048070310f024040501c28481455481251100124810200c1d102d03030500081a040c4610030b241401442d0003e800c02500d003c0d207040a06401145540b1403d200c07a45060701070b80c0f03850064415600a40e11208824014800500002c0c1c02c02c05e0140c02c14014103000303405001e41e03800940103140400019000941719041041b200e5020000003180d0340c1c00f40d02c01d1142c41e00b1700d88a0041004014154020130001540111401031a10035000d5019000a00d4102d42c0752142e08910142845124103130040c25003200060902c264104500140c001a40c1c0f88105031907450f408a4076800709110903608140308010002c00180300748039940c10400341002003611018 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 468366573 1250 468365323 468365327
    0xf0b0c0d0905130b12070305150a05040c03200d05071a0c0c010e1504081c020c0109061d040203040f110a06020a12030908030f0901060603020406120e0c0a0303050a 72
    0x445521020306001c00a0002d000320b0303841c2052044810190000051130041c0c000001d084074240b008403070b0341da00407520f0200505c080070480002242154000d44a41e40301c030a0890f08442c2c0885000d008412540414400504030403400859111b0b83c85103100201d41c004001480004801070450380c42d40303c80d104000d01c0038011502601070303901000e030720b083c00c18207a1600d484e103003459050703410000c04001d02010740d42c43e00440842c070500e03809511b864588803c603050b55256108003050102c114042048032003032000900340c0d402103040e9610642c15107001010b0301c4559440c0c110a1500303c0c980c0c17200714680c40d640301542c4654050102000c50f9503960800110075140518802d00800c9400f5091005a8001846511030b540c414120059154a010304400414a0010003840503000000740a220700883c44000e0083c034403070300200b04076030759400280d04a1186100e414081000303805104601106940a5001d801c1e1a17026104102135960008511401940045000c60b03004200000c550ba = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 468367823 1250 468366573 468366583
    0x10050f04020a0801030f020d0803040c0f0b090d061d0a0303020403110105030402031203250e031614041107021005030a05091203040209070c020415050909010507050912070f0b0c 78
    0x2640946003103151400603403000301683d40501001e0700c540040e0306004115102c025082072855000b04005881e13003850310300390001080b01d1085481502059801007000c941c1c1c1e508907194008000e284030400c43c10356480304050b144903519048180c0d02280034021a040c05c0c80002980c0780b199030010382e62421460601860342421412904010080c41000700680300003590050008031a084640c881d03071403400c2565a2000d590744003c10f10825104502410f41010101c01e07490f50072803e44415084d1044081600d04880c400e5118003456421814182e040603840080703641018038030145016980d801180d46241540310040010720004100a03d80d00c4610821b82c0040c7c51901512000d0165070892580d0701026001a20900d49000415001801490f404002a601a109018507400307a06404841034051013920f001d82845800246990418428030384a140142c5800342800c0401d03003400040c19000c000005640300b058000300c1c4183c051220b0600400c5401d80c6103a0314109409424205 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 468369073 1250 468367823 468367849
    0x1807140a0c0c29250c05031009020f0f0604080105040c061209080706020901031d100c0201020c070608090a060f05060a0902180906030106090f0905060702120a050d060803031005 78
    0x603030380f001210041c484034002500b10007000a980c980300c841c4121281c0340c2c40100c1807083c100c280300200c28410456074400e04001c8450071400e40758200c1145404c5015100d25400003903010000340c2d2020164509600600d84584004d0996403c26071a5440039007103400c00e0710103844c80001c404042003c507511918007402901140424001e140301780d524100e0601070941d005102c26004110340c0c1041c2d2080c0c8c40105440c2d040484180080d0001d401d440e12555880081030703042d4100982c50380c18034014000c40705401c011000405143d86006000c03a0400c0c4003901800d900d000354400c2130701141d06405051080003040c60001114103100d010043c2c801699884030955900502150070318000205140d10741200a44628445680f50000039005000e942c01c0000002e24000c1d42c15180c0c4516488020580d11a000300c034815216428140c0c0d171520807051004804004000342d0100f90b10840140c8503042452401040003a103494406081d42c00880318000e40d010603880c100b02e5490310070800281 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 468370323 1250 468369073 468369089
    0x4030f150e12031b0f0a0c06150509040209090f0303010e070909050c03060108040203070b0a030b091003050601170a0f08030a060603020405060403020d0c030221010b0f1807140a0c0c 80
    0xc2c04030610000c4050000801c100f18408030312103280ca0f0b11369180c00301d4445044c0b54401c0c564414203840d014011640c514420b40321146004070b40740503840600804416540014000d0302c15070345660800140280082c4894401c0c01440140b070100402040a14081d200980d10a0010320304000002c0c8010110380c001701400341800140030005054400b1a5040b04083c42c0480d0140d0311800420302d40802c541c0203010500e000a0312140d020351641c010901000c0880d03d04c1d4041c0c032980c50740c040e02d10442c00b0180a6030440001001024034010540b500086402c0c00d60702021855180c5650000012500303607a007070000801c002010707050380309950107440705003401c509041c14103002c941c180c016800028059040f881d90a418041100c41e001c0065030700900d005208070f8282c12940c80006503140607126582004101610340c5000e035400c02566001920380c902c2c4100c0e004158240100c00f500d801c081c008104892103e0100d0031000704944402a190340d691101e03a440c01041c203400e5a409114 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 468371573 1250 468370323 468370333
    0x6030c0a0b0c12090603040b07020a020a0807090506030a0314070309030215070b0f010f05011818150e06180c0d0507030c0228080307200a110102011e0e0304030f150e 73
    0x81a034521051b02c5e00715130050145074290759003c0b42070b40b40050061002e50f00030500000040d40000008103d0300381c03002c401c8144615200ca505041c1ea41c5580e40340200419160080140c1c40780d080006071002c40c2c080e103000c406155aa40100d0813ba8132411030f04188080010154148001d1541158000708140c0c0080c01079803500d4051241c59a41340035403410041401450790216080c2421540a00204060144610700727017030500004101c14502c0c1440e8080d003031400940300106200592141350003402c1440c800060101460300c0c0744d8001c201c0c0198401c14000700391800610300c41c0c6031149400f41c038009072460090740040e00d8009000440390750a041c42e50722005021440c1064174034540c0c0161625100d4075008070640e01d5400c400c1990f203026140c020011901140020700c10050380c0100d1203030284507401c00049007640d201800305042c2d0250919002d001846560003540841c407200140c90070306403a0391750b00c10f803900d4001e001d4899840e141c400c079004280038403441000340300c4100100 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 468372823 1250 468371573 468371587
    0x6111b16272922020f0d0e061006050304031b0812070804030315061205040206090d0b01050108010b090906010e03100612050d020303010312110a0206030c13061d060306030c0a0b0c12 80
    0x60a140800c0f0b202c45000b44e000709038201340007900740503218400e11000307052100d0712424014030742d152003c03100036243e10708010000801034021400c40e07020f20740691b175220454003907040094990100c2d010458800f01d04000021140100a84007070040351aa03035420901e0505003030050a440e5156421000c0702c1d0707010b00c100a0107400c0700d030643c0c0107044c00c400404c25503070706d00000d042809440d0040d600040000017190401c441e008105041c1c903001d884244c050303601c42c4103000f100d0003000c400c95002600032001c940250f016100030510340c0002030071240f061404081c0c80302034030b50700d61048103981402d69244003000b8050144030414045403006600310341c916220400e4692100c8010818401c10600e510403094080c4003502c903c58010309103c0c0d49081c0702140f48920ba00c02a00030103084a07a20001c101103229000c08100c4c1c1030311005400308040340b24108803240e480074100c103038148206100c100e0582c89800000d4010002c60a0503034443c200f40c1203440c24003840700003034207000e07030100002 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 468374073 1250 468372823 468372859
    0x33061c03170903270f04060602072d0506030a09080f0403022b17040803040e07120605010e040e010219030b0a0b0702090f0403050706111b162729 64
    0x1182160070038804d24200c44001d9010590440403074000d213820908140000c0f030096000580c410480d05060380f0305070f1038240900158002070800c0000b6004003c030800800440c0b4004014641120000d1000502a030321a40d9602190340000c003c100780700000718007007081d4580f51148000b28103230b1994403106015100305118074520a01001031041302001c2c0a2216400c047c0160303000380c0030301d0742103a50700c0e03031180c10304c2e10520700498000c1c0c005a07040c19803201040c5207005002c115401a120050030304165401c01028003070200e46566250350a1001030500c003c03001441d40148083c2e1000940040b00b1014002d062910360040780810304204030100050301d894040f160700c50f140c1d0720a0b60203510380d0300d011552407041080c0a0312030f5007040f85001c090099040242504404201c1100c2c0300c0035064507558445034481340700c080107456000304200056042a454598140d003484100a0035103030b440308421205d000c409000d000d210400c0c01d0001800301c1d41a0800da034422100e00040c41d030800c100d = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 468375323 1250 468374073 468374107
    0x250503090c12030412151109030a0305090d050712031e0509040b0a090221010609031707020103150b03100e042f0a0e040533061c03170903 61
    0x441e038000c00c1c00c05a201d86140c0c0c1841a10080c281418007209003034100c1c01d00300d550742179041000c0318841c64144803240e100a01030441c1e2203c0341c090301811100e2225181a19550021400650003007820f9401c000013803030910040c030103070003070015416000d0352604005145c2c44404894070045420100b40d41010394004040d601001c030103c03004a110710101000c0350340e50030641d114401c454004034210842c1c1e20844010420301100c14900c1c5400ea03a81e0100f2203421910b4400544003008030161500011000801402c0d404c1c018103000c40e0b40c0707400b00c204155007200c9601450724075a0103c148804125080100402003201203002c454504264503442da40b44040800b480f0600d06107079034800da480e011080080c083e5002400342e5441661020b00101c8040e044604550358080e0074011070410f1300c08100c17909414002884007a816005080440a102002d406e45034810820702810307404000e02440b100505200307a48074400c000c40342805031168040588114402e40060103079007030403038040b00 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 468376573 1250 468375323 468375343
    0x9090b090d0f1713080301060c1a0105220204170607180518100f080309130203131b12060c1805012f0d020a330b1825050309 55
    0x101c03c035160355111504910300f0000c01001608040000201c1a400030301c60b0070034078052900070b201810b44882200b5540002d00803543e1080c00c075604842d0061500f1000703000300001d050010318050b26103804858404011000080d983d000728104401640d1210402035482c41c01c0400c041c0d010b042200040c240c5984218950600313039050009059403504070440c10003440021840c0105c1910b070b104003074907503100b21409801012055a408070285061007141d100340d910b8181101d035440389a6480301c3c102003004103181e000f105050f000c103208031400031003003a40b44120703030018070000c0011000e001c4c3c0d03501c40304449030b290844a041020380d81040030f824519100384184880801e8040310f080c00749491b00c045050070b1007010b88a150b055000142680c46c14001c00c1c01100001943ca19042550100301221540001940140e0f14144a60300b00700c0201000601d620303a610600c000003c4c59138000c542c5203401c1d820400c0344081511014000c00078504080c50610310b14500790035a2a95001452 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 468377823 1250 468376573 468376607
    0x2d0e0105011d18070215010b071106070b0c040512030c0604082a0708060c0403030c02101b230c0306040f0f02060414041d06160909090b090d0f 63
    0x164071245401c0e808580c064a0340c0028424180742562190141610f042110a54090302c544150039841c150905a418121120700c500c00b481e001c1c1ea507031903a021800150480340c0001e418055200000c5509210310310810718ad8021540310b40c40d04041101c0042444170101d10b43d0403c12031820f0300f00c8017084580c0d100c0d400452003666404140c0006501d40410006d07504080426881d495070000003060103411900d580c1d08450954035412640d8000b44241d11000f00851106145000142010702c4103900c11015800c3c400406810071800300c1d41d52800b5581192405840700d0205c0400c0c02c501001c40481800000401581d40c84c540070a070303104c1d0041c1003c0c00c100418ac3c1e00400300400c65801e808281e81c0540402d0f2925510880d0007414504000410301c100c1c148281d0000a08915054420004281000700a2501c0310405107411032410340310141000601400401d44800e103014000310b8a01c1000646100c4c640300d9003440c10f08844007040340030082105144003105a0042144140090203 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 468379073 1250 468377823 468377837
    0x60f090603030417010203041401060e13080409020d0e0106060513030f110d050f0c0d020612100b1902100b060f030a0b03070f08060603071818020405012d0e010501 72
    0x10500180c0b0354022a07100301c01c200e21003100f2144000301074021310b01440c41050844420180d90032900d0a80d1a10f0140801002076107001501c0e100d00c100003161004c0c001c0c104c640c5083e4076480d1700810303a840507070509500e9850340139000c1c00c40e10034400c42004240c9450040d041096000078007250403410701c000340001ea2115540d40c00e208803850300d1001ca06000707041d81c1890f0032a261840c1c5984600500e034610b8054400c081f1140e0400c502100c4a40354000c0c903141c030b4030b40044051400400d000e004c0f01007400c1c80040200b802c0401c100100a4044084115a180c2030380c4a4001e01d00141d4603002c0c4030f13107814201c4660803030f110101600c81c50035131801c40ca47c81ba0b4480512030020164a20741607410701c94003400090040711015030000f900d650401360b0302540d80390010306aa0741e94510030502d21a01c2024a8040d1002a034498001c0c0c60ba07a64948010034081d4000809450082c0c11061a00e00c03916800391494208000c03420400001d0440f0032500c502d042a081d8000405104403418881c5c9 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 468380323 1250 468379073 468379081
    0x10050112060b0d050907090b060f0d0e060108031b010605130b0105160f0309050d02181801021c1b0507170d0f0c080603010917070507030510020a0f0305060f09 70
    0x401d40061000d002c10141958071610041c209402a220a86401c2254000c4c4040403610718031a00522010074800b42c84d440c9003c8500c0a550110b5010007900145c46a40d110104189042809400d0080c070b0800d0046d41c858000700340c40314004900425448441e0300d0f000003081351752502d034451400345c0d03c40742c000100341d109440141c6480c8100e420401c80c4d0454031190b1002c01000000d00800d0a00a41d1040045521034040c403100c03010118000c1e42c0240c0c0a417442c0d407180750800c441e56000c00c105280828100684041c3da0076600414140641215110120609080c503403042400400402e0003072400743c45019000b030400c3c4140c1201500d0360107030b042d44008001c0c03440304440c00440c01e080c040080005445280c0010a02e00410400107014140030428900d814040e510f07140e0b82000450b504004281d440305101e910a401c121502c2c01828000008140d09110484102100030400340c1c0d209484d2400610101251040c8010716151000b072100a071900e444000f0b166500381c0704400d094036 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 468381573 1250 468380323 468380357
    0x60a0f1502030c0304062604030815040e0d0e0f1c060c020307170306031203091207110d0f0b0a09030905040b121b01080a051e190c0c0515100501 64
    0x30601141d00428800050700150701b40d88080c00c0007844030440741c1000396680c0400030000241c0242c031b0280c00100004c021440d581300303c0c211010704c41c10040000500d440c4610049040996000c6c40f90085900f801400205040c40c03194403003106412903050f0b08030340c8410b940140b0160054001b8008650b1501106c000c40c3c001c208031a0543d40240180d0041c86202d100c40b551030344101c80180c01f900035000d521144ea01c1c02402c1d6400b40d90100c7c0038203001031500c0207104094016400c26104c10071000c504504070340b254140c01e0300d014040e07441c0144280e078030304016480c4800907041c182c08a00d084140004260310070300308000e486007114082080e03008000090500058130b01d80840c640918401c1c100c4641214400c01503010080c0c03a14402c41d510001000b04a079811550024007800601031030102c0c50041455941c016001c1001010310011400500102e80001280c9800b0464407200d42c01400410070060414941490720b05001e4079240114015840d0b1921409050010500b0714114285e = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 468382823 1250 468381573 468381577
    0x20405120d051914280305070203160f0206030f160e0a0302011b060f0c450b07030804170a140903030d0f0b04060614040e04020f030f0604020306060a0f150203 70
    0x2000d4802e4041d190418000702c150440e00450011114200c0c040405c14200e010b802514403e0b00c1540145081c104951124140110705200c11107605446100f11030060f40e601c07020714001d211005d0320600920300683e04488407183c3c005440207101d01a02c400c5001d40e40c0244500503240e0a207440c80c00440000f01c4640042201140101820f00303000c291105000340354491001c0d0a203d41d42d150110a0020284161900180c0c039400710074003802c078801940d01e64440203200c00a1101c44400c40d00e42e1100808095008684101c0000301c1c0c0505000501c0a00d5407440c21494101e21a98908200c40b9400707440c00c2c010704044c10110724042854036981d0f03414000c0c0c0304140340d580303400e00078483c040f5521002018403040700b43c461890701d400868000d01c07544000003020020a0314600d0181084208030309071000a1049912902c4004080030036181170118804c6a107450000f44400d0510344101130814600910341750081c0c000f0001000045900b881c40c80840d002c1318144840c0ba40e001a0883c218 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 468384073 1250 468382823 468382847
    0xa09030302070b150418170306010c051b0114180904150c2604150506040b0406090b0109080309150d06080a080408010e1207080c0f0709020405120d0519 67
    0x105a210341008039800819a03134044001040b582040031400080745481c00c0e06100401402503a580c0c8051245030015500540e0010f20505003080501c040340d80e410b04d0000e50a619070003006501002c2c46040d43c00c00d00b010b03003042007a5100ca003001500d401c0002c03039680342d8541d144544030144c04681800014100d081c1000344014041c0500c1c08010301c0900200c8103102e1803142e0601001005d60203c80e07205403c0d000384d034041088811445100700100140c20043c08c4a944280d81d40c08002c8240d0322441400010301d80c820020410300c00180004d0504c2c01241c0c40031281c0e400411494041e5552145041c1b031000c50195110745604846140400600c4a03401036041d51044624080c1030000000140c0308851209000f84482d80200c06a10707114951181d41181c0c804c1e0074061071000800100240c40da5881d200110707030b80b407180c070042d80e403070010254440f000280e40000d00384400e08007e4241140100c900009001844040c80010a10704c108040c00b00194220021617032841d100d002641c01e1 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 468385323 1250 468384073 468384083
    0x1050d080d0623010207121a0403050c010c08010e250c03090503010e03041a0403051924020901020c0105070203030d05220809010906020d0f121107051b0102150a0903030207 76
    0xa205841c000d50024603298608050261141d00f4000801211f09805480c0070b80d400105414071348907103030000301000b00c00340c01142407080c103121070310b02c2800c00d201d9100c03250115540c805095151070761103c1c040e0806854023a8503000416402e2014400b840d0b1445808c0c1240342007090300d2039a04080f1003c58058204603455401c1000356209400d001001e04103842403a100c0400d01e90002101e02d00d18895072100034025040081081e28070f013044040070140701d005103124800c00d5103c0c428034007030460081501d00e4080e400324140000d5607041006c0c039880c40080c00d105252074840c2e000241c1c6c9014a10780840f15036160000213142401c0a05802c4c95500109280d980c090180e00e4603204c0c540011200c03900041a40c500090700c14400030700c10300e0f501d55a80b01c030b4910b00481d110031219042d2843c0000005521580032110080110300241003150044024002c0034147c600305a6400034884542c1d4110b6204101c244610b1004a00c055040403c03c50001154080c5140603400b034020002c0c0504 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 468386573 1250 468385323 468385349
    0x212030c0f0c070e070c0c05130e060f04030806041406040c03020702060d02040303030b0d0b070c05070f0f090609020301150f171f2309060a0b1303060501090501050d080d06 76
    0x100e40c1000141c1c1509846006081d540c40c0e640b0005c0c01c6802c000414005040844564020032042c10701394050508106902c1c0041581c2c0c242c1c200291401c07c0036610030a1200c010b10070041803503807107001e10b170300000304136014486c9079240200c81540201c080c0c03840d48140e0740e0360285007016000e5812118240e0b07001d003c040d100c034800c07000c41000f900144410b130046400c110a80d202c03882d148400702806940038402401e29290000c0844104100e460304a540380f04110005c50148059042c03100208140400484000d06218005042d560300d030744595581030042c03006001039048a0018200d110180c07414802702d50704803e0440d11250680945c280c038000c00380600138207107482072007080304c0d6104d41040541a40c0d5413494080e01d44900d02e004242021003008901240741c14422035800c000c0060000348000c0e00e807020103115601444040341403221040b0200b041103220701034503004241a0b0800c004940c075000200309402031f103140c000c2840c0c0b0000b9103041d01800350751050f40a8106c1d249030403 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 468387823 1250 468386573 468386587
    0x2212030914030a03050301090b0d050106141f020a020907030f050f240303041211030319120504020d02060a051b03040f0f18050c160503040918030212030c0f 69
    0x584640c0890081006500024034940014140000d0650300c5541c990b0751989943e191643c0710f0001c254500c0a6071b030203552003070740070045407090280c0009481921001d540e00e4840c17a0403c0001d86800b4000c848841d41c181c1511400c94002c910138000750b40695848075107a4400b0022002002080c8001c1442d510b080300740000b0448040e64580f20301e0441c884441c4194016a0314844004864580d50303065000300410b0044903420074a004009114000b0003180c2408200000e046030031145044014455030b080a004183c1d010a521480050381c2c1c1d0100464141500840d442d07403840300c2c019008020000304c1c240c100380b2074811500345445910201128000720b2030103130b03107903031092088004084990001240103203a030324a820458080208403010880100d0606000d448000d00038200f407041480444081e20f85005c050742070f01d01c214003956880d400e01000600b194969484806181e075070030124400a50000fa6070100d410210307200340c0c3c881d41c0e04c06100c4003034480c0b8113010b454540d020401e0 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 468389073 1250 468387823 468387827
    0x7060e0111030a08100504051618050301050906040c0b1312140607020c090a1116020a1211040c08040f0f0507120501020309010c02030705030f0304021306170c0301020f221203 77
    0x1180c000c03800d9404172000140c2e21030412007a148281c445100310801900f800c0b11703040c096140d4020803c0149022201316640e0800642101d8007180c0c21038036900404c04100130040da001503100601011820f00d0b08010b901403104209500c2070050045040c469a1540b0501c41040c4403903080f00101400c48080340f0b00900000d40381c0300310064081c014100000400c200c2c0c40180103404800c081c0c14480380c2444440600403094182c0303040d00740d0300504490401b080f00142c0c805600d09644c00340d0b0102501c9212202400101d07003607004850200315600051100080c546c0c2c904080303103508411400004204c50901d00c4c03c00843c2d5000c0b081e000c10f440c104000b048810b4014500c90480b20b0020440d6041102099031a8032079844004e1042c0c00c104031030200000c000c805150894000380c0801c2c2c029022000340c008881c0c05401801411282c001ca4001c0341c10204401c01c7c95107070550080d41461410f882c074084a0040080110b505258a1303000800c00702e010000344c008100690036810690140e00340 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 468390323 1250 468389073 468389087
    0x9020d050a02030d020d0e061b0303010b220605040611011517010609050609070f020c04021602131514060705061003050f06070c1502070c0e0105011d0307060e0111030a 74
    0x890190241132403a446803400860408440d0301c0644a140000017203c0421045501010326050b90510070700c000a281c400c1080658082c00300d921a06695005e40b907056807070601203107480320b0030b2042d461047c0710700c82d440802d80b0121001410610400341b400000640901000c1c03962189034a8850310000d4100103208a4540c0f404050000f00185d07034940b407a4800b507503c100c0303069411042c1203000c030344018414a0440b01e5508584155012800c0072800a010b0743d000031042e0503409a001c54000640c94548040e859581007210100558420510444000740692044004403c1c030340000a1154071486e00320f822855104044d03c0c481e150207007940010758518002910180b054400d4040320381000036180f4080c0c2c500d070729030041220040d81d810040c03128404241201940911100c0c00003603007070643c00054100704501504560410780010f05031072255605070408040c00c20241b105840202e070040c00d6440914101007034200070401640e000d40b56500c0d14116100c001002c40c401940203071 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 468391573 1250 468390323 468390343
    0x615060306090603052d06040b01030c1409010315090c091a060f0d02071406091e07052805091303090b03071b020a0b0f040807050d0c09020d09020d05 66
    0x101003007141d444910071011241e26000040c070680c004140480700028182c0703d010342c1201c2065000341c04e6450440d80d070614800703641c11202c0c241030b01d005104000c11244aa0080c0245040c00320300b00090700b0005030000018813000e051038042e01c420029440e015000240d04076044800800ea1302c0d03440003500000c0101050000e40302031007403c05c006500c2c00301c040300c0450080158044c100319002c900000290300450b02194048801e55807443c01040c10b01c10a40b03d00b00010140124000081a41d01da00100c05510003540c1c010502c2801140e03035445111141d000d6442840c1020b60300c1020602565045070400e03640124800100502c0c0e01240c07040d81d001e40c1c841d55880180c0307a501d05244c0c00f14041920b41d400440d25501e00d0202410010f801d10403014001018000c50641c0c5480511a80c2c5c13151310282d0800200003001c0c40300403c104201001414150307088818101c4a0300c414a07542d06a000c0d00c04120340009240007207801e035801ca802030940051082c280503900c0c0c40c0c0b296888400390 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 468392823 1250 468391573 468391577
    0x21020a090504030203031801060f12110108070f050f09040e0f01140f0412030906050a06091b170709031e02010e0a030b07030c02190c2402030406080c07061506 70
    0x200200c0c0c803206500a071070042d503068000754155103038010082c810083d407400c2c031302c1c5565070381000081040c0e46500d00002000012030000341d52800707040006081d024008000d051004450501c0700d000d0f405850700f44240414540f1a45813203801c8200c0b81c1e1403041c0250b15500130b08200010340344a601049414035009414000c0214410170b640340c0140560440b492803010f00810001404540603041c02d802e001c9075864009250902d65540c1e4003120800d480090909584100612a1704d4482c840c100c260002044001510003001e42c0003024589c2e440c0c1070a91182410021031040390141040700041c543c07042400801419110380c1c4004045107a4080e40002c200c1c1c1001280b50400340500815a6081415801030f42e6602c481600a45580c0d05940218800e51110304500204030002c803c41520450443c05200d180c2030800300000c00001d44172001c240e007103001419641d0000100c0302124005e08140d6056a03e808a8250601500801904050500c00c500800e411a0403107041500c40613 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 468394073 1250 468392823 468392839
    0x103021e1909050306070f0302071a15011b14190b04060b060a1202160c0e0f1e0f061c030e030d02070f05040203060406030c06030b090604141f2102 65
    0x70501216081c805210303c0ba0540c024030081042548218120b030300c10040360401503e0007555aa850403030802c21645001c400001d20280550018088140c41e4498400d18000c091203005031400c208000d000c9200400da2007034060000c5040e0024041d51040107560b440f50380b80400786007021104004122402c03200146405803412451400e4026551703500355564694000c103042c0d038800d1b402075201c65012160700c81f45d1900b050018500c0782881010380100d0b2505c550341c1c1003103d4542e5131104003070168001001064840e83c821542e94000d641d0040135095020740c2522501d0126410b1401c04807600000240d000448090541050241044000a60880e0040c80526500300d0300d440290080d80c013000f942400402c05440c15402035504881c0040c00010303240da60381d681c41c03049400d50b80000086600c503448450700346800c81d01d00754042401e607800e00604240d071110f0400001c0050a444444841c00d05a20080e82943c02840180024080b28109103080340072a4a800e0201d0004078410064 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 468395323 1250 468394073 468394117
    0x16260d02030304021c0503070609050106050a031401050106170a020d02040b0a0203090a141e04060b0406080f0105010c0b0106050705120a02070e0912040501120f0207060c1e09050d020103021e 84
    0x1c41e01e20011207541106c061810300c1c440e552407070b0183c000c44070191030640d213406002c160b40e6100400d01d0000d502c00d602e104172001c5018203081c25500140e21601c2031100103244111501c0b01e8110040d80541e1000c1c0c0180d0700ca4030b5034181c00003401a608501e0341818049030703420b0705a40000c002c1000140488214a1956580004502c7e21903c070718526084030101c02035501c910305081c11003404141c010804101d1503150000044250015440180000c2d81d00c8180041010525602070151800780707803055100d81d03161101c0340c4640062040b001041000100c0c1810b002d01070058404101034910b48640e14005420025958517090103260036071040003001c02d520300f4000070300743c02d1a281800e081d03040034600001034035912050300600c0700300c0d074031811191403540d1584010304000788101d400003000d0403000401004280402e2851081c1800103070350303550690704203c6a03801c80d030046500d05288070a0b03100480113402061b1501c1c0c1d02c07402e0448a00807a0390104054440c01901030b12101c0c19006d = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 468396573 1250 468395323 468395359
    0xf2a03060b040c02030d09020a15200a050a0314130e060f03011e05060102070807091401120b0a111b030903060c0301030b0705070c031b0302010905010216260d0203030402 75
    0x10741400d00f40940d01c10011103c60355400e40106910700d00041184220320790b100f400c0034002c1102d2440b9000584108102000b81e01900f8404015501200040c81c44004a540b02c0d5511040650060144840c258007482c0c0170001c0021500c0580820280c00007180d0741d40320250b00300724281d0310103204080d07a618030a8241030504c40c0c040008041268a0b1000d2201207030503000f8030020b4000c904501a068010a0412041001c40700804c501400002d104114998031080340e541a00703d081d24204440317034030000c2080a0744198200406d0400000c03804191251409640304d898062038030503911100d1520303102d0b0044040c4c00104415810f507038050361001505030061000340001081400d1840c08122403600c03543c064000107100b10f00b500c20180e01ea840d2001000c035403440c001c2480d402c0301000d1045507408944107000700400e0000309283c14210001c08182c1640380079601c03001c4104816201c00d00f0901114040316030861055034000781c1840c4000b51030754802c4900703900506400041c030401d41 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 468397823 1250 468396573 468396581
    0x31a01031a040c0912080d0b060405180c0d0903020615010c1e02030a02130510060f09060e060909130309080604030c0b0403020c1f020106080105060d0f2a03060b04 72
    0x4031200641c081d40d14031141c00c100041819801e41020050b0350320380400c1880d803c040328032170359000d4030040391500c04400c0b561080d5030790750801e0781c021502804100031b00d451708268004616080124409513958042e000f9102d4010110361403c01d42c1844021014590081a4a40035460074800c06100b1010714006440750545000010011083e04401d40700034040340f0b0200201d5407009082c1d441028517500000c4007050030840038420315a5980610241c024000d0725607000700b002c2e05000350404034424001e40000d103140b00d810705001c103d80b00003130565110003c032803c00b50014a070090909118048035048520101c0031004901000c402044446000880f40d01c55541583c40f42c01c030720565076445c5501c24025104905600c06c429600320540e6620980c4a000b09400044140480300480024203583c50f1381e1024501e64500400d0140300d460b0844580c00054000300a00d04500d2540b07802d03c0c0014115000700e542c0c441c610031005040c18410030304800c03a03000305014442040e404041000b11 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 468399073 1250 468397823 468397841
    0x140c1c0b06040501030c0e040305070b010f090e0d300219121104052106010824151018060804060f0209010905150c030301030506071e020705061b0d031a0103 69
    0x1101c2c103a2030402c01c7d0344910b403a1582c081e100e07241c03c1d0304010480c3c1c1d500f58041c000ba000190880c01114003400707680c1103407044010b4010140c0083c0b5042c40b4454000d03200700d038240c1800d405000c400c81c1c184024240b0040c1030640000303035801195655440002c00040e5031216003400d000030ba42042c8606c0345011800b1b81c0c201e03000303080d006030705d00352504e01000545034400c600021203078640640c24000c01001c1c0702c034a0003080c11001a0101c800c04c034444410b400030b84035085900c0352080c01070120350790b902002c080d8450403e440c0005051488031003500c2100440b158001e001c080600301003045544408014000e5100d44402e02503e010265080c050b03001d916a071500240a4020810192400641c905441c03075082c4100c900d09115040c1c0e40e4103540c0241c105a9441c0d10000078462110b0b48464000342c05030000c59075495035906504001c1d1140c20324030580c1d1080d800030840040e81845081c0b030701c1203025660112280d0303c100c01c1c00540038101c109a109401209104404c0040d4000e00400c840 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 468400323 1250 468399073 468399083
    0x120203070b011e0302130b040c140d0c0e03060a0e06070f17060a051503011a07030909050406060e04030c060e0c01021908090613030605160c140c1c0b0604050103 71
    0x540d0703090401c040c020034103c0c4810091041c15000c000301603100d2007050220002030400110b4540240800e0000350341e035140c0750300c0420034845114031080308010251150010070900105075003110391030031290314841020080d45070003460144211805140d2003c84580410801e80d0119030b19144181c604855041c400400700300e40d108022640312100c1700a40d803103c8018160000c1c0e070785440100b03030b2170240e88116400280300000140050103885402203080c00388401014900161a42d0044c45160140310f44040a9121400300e0108840350f040113024100c2c0444811080c81d05080c000c0c0b020040c0403042d28090300c5d112001e4448840410002ca5a102c1031b002012504060800809142d083d45403e664010b82480305036020340d250f41c01032a41d030b40040740c1100c5007800c60030030108a0314050040a4034181e280b024000541d000303c404002503407c407000050607211464514104072100c2c6006e40e21042a0003140404c0b02810794900356107001d1100e41c550380c0e654109000465000b0f000243c0 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 468401573 1250 468400323 468400343
    0x2b090605070c030b10080303070f0210060b12070903020411090111070e061002101a0a0602010902100c050c09040b27062a030c071104090b1b07081612020307 69
    0x1182032034521300c0d00110824044c0071029036614556096030401d0f07405000103070350000300b54401c3e030707040181c00d00074203c641e002c04c1120300c0c0c0710180c0388500c50400380d500c010030200006066a030144102c0401185c02030828000046180421101540f128000340c2c04101840540e825083c400500c4000352202c00d0b140e0381c00ca46844013005920241000d0920461154080082d1100428040e120940d5000b46c004c204014000d0100046200e071034028100310383c0f51007112005641c40e912160303e8040e80342481105114075003059824145000f0301039070080e0b28503050000304118810070b503200f002040305030808031601002c4e9845217160048407001e258007007400f050390a40e1700e485082940000110003c805007200c110500190400c03104000203000103c0c5607424822080d41d0f40b205000100c504004083c540e41e9600302914000d00364130320a481c0b2050340545065200c044419040e0800c0c8074584a02241c02034100040c007001007114100400b8201403c142d0000094480913540454420 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 468402823 1250 468401573 468401579
    0xd06140406090b18270c0f01020f070e15040504030c0b15030a0b061f02061603020a02030d0b040f151d0f040807021c320304050108092b090605070c 65
    0x212802d10081c01900703441220114202a12175886841340107408440050001045013108110340510f02c0141c0c03074155003004054031158140895200c00f640d12024a00540351106849070351046440300800da00a450b040502044c07541298030203c40300d10580c0240240c3d5180b900030b007602081074540e43c1d0550b00c028000d80014000b0610190312840c0a0850b9440c80b010f0042014940c1000b81c50030056009141804403003000c0464070520000242001c3d450b1515220300259a40b040c0764050101d11b6840403900307401c0d900c98000301c0c40c400c510301d0240450b100e13400703001c0c170650014890b24080c404060010303c1c20300c0b045190301c3c2c86040180505459640d03952109403c9a01042003240d011910140031013a01240050703c403440c6010b0182c540d511542588081900100394414110f4212080c00c52480f4010001c01c40d819194280303400810780d191a091645804069080c52046010110109407102040d052b40e04c80c00c08196a0a20307401c2d51020192911311641001030150f440e520824 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 468404073 1250 468402823 468402859
    0x3030d0506060712080a05060103150302060d06030b070e120601081504080f0a1205060d0b19021204030e0a0b1e071112060106022b030c050d06140406090b 68
    0x9150711039070240100b8601140fa41d13902e0811041980d202010400a0040c449908060b108490b032110003801c0c00c000c0304110503c0000e5405551100031312540c00002d00c05d02c2c001c00c0b80c108000440d0701c172403145c00301e04010902034003440d00000014050042d12015070308007500014000c0c100e0300d03483c01600c82c1010301402c644402c0c00050044d2191071007001070400c419910002455211416514442040014231070103003640c4000c1c0280c0c0c440c03034042d1003a0300071802241421340c01c490070894070640c950700345921402901811001d5442d83c0082c10400051581024035032001c0714044840c050340c5a150a240800c0f801844c113400040b1079480241620915000c0040c54180d00400c1003000c81040200091070491407036580b613020b604488010441e0740c2d0100702040d014220502204840080003000004004540c00c00c24100b41e02c4550750a0703000d01810440c0c0c034400f112401403043d0b0b0388604031583c00d00c1102c601140568a08040000e440d08540305096480d0b80081500b01b040e1280404 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 468405323 1250 468404073 468404081
    0x9090302160305160e0708060906040b0a0329130809061603090503070b040303050d020a11070b040f0b09031902010e1206010e01060203030f0a09030207090203010b13050a0503030d 79
    0x22025032085103242840078a03020070700c80056114030020070b21030140010345000700c0700c0b03940600044200601030041c00c940140e0081d50000003501c10003026660100050090102103907005c3d0816100c1c64080b080c00f4940500c16a1800d21082c4606410400341e0140c0d6640320494414016400c4500743c0d40c0000e0070b0000402070098002c24203400c04110009910f40c0320f0a81304101d02041c0d5000041050b800d0511004000b4000c040c03d50381098507649002c2c0062194088082000d640052000d80d01c1d8068080d000c44a9230303050403546443e0b00c40514074540d03446400703000384440411100090918004d02160001003000d03015080b01105c443e00001111900356089062060448407c03900c1e032205c2070381d00c62400e8030400500b42c951514455614049040e04510210b4204200300010700700410a016000720007035400281080780c0703082c102d05141140e00300c11220f80c000000068403030034050250141d01900d501c407184e180d0352403040190b84402d0348640c64042e0014001c0142c6102c403584 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 468406573 1250 468405323 468405341
    0xc05100801380d0906050108030c010605092701090501180605160c080703020708010509070618030b0f09070b1206041b12020c070801020a03061508090c040507120509061905040c09 79
    0x1c00414007000305e0380d41500b921070076004010258008900034181c0c8400340500700c0100800e8440c840c15041802c003607503200c2d642c0340c0e10015031502200100e0180c1c009521418035540c009000b0043c545800e440040360107100801555920b08100115607a414600c003c5281180035440ba648a50300b02e540d07000e034607001203505070150b0198003000561800d0a000380b51246031a007000c1d21303e85041410140060719800c44004820358043d000b48001941200480c2d001000b00110b9079940e902c01d205a483c2c00500e42003447d1151000c0342c0900008118040e10b0b0088004407014403400c103c494061300f02148104801000840b00c00e001205405198014491b03110160151580503071140b12250a80c0d201c4204980000d81c0d0b0f0000300410030000090381034109a0b482c0540d1141001c04480303550f0030010301c40e14469561034012454440c05441e1800da00b510321017051065280c8402059102c090449810000c0d040d20141907183c506248222031060b54401c0780d400845007000007480042407140c0c = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 468407823 1250 468406573 468406597
    0xf01050d05150c0a020d030b030604110a0312030902120316060b01020a1b09110310031704030f05060621031602121e01290d0c0510080138 61
    0x4581200402982005a840f03461410810b0769a904000e01c020318003008469264105850040c9605440d43d01045181d0465080094105418110380c0001c09621113036000a0a450903055420012900b503040f0454850088401c2d07040c002d49094500e0700ea10138003c0020390790a031946903100203a004c3c1d004056011046c412070302003601c01d079070356113403112120038008414600e0b40c020401d0b1405800b4000c030191480e49420304505190050410300e0315140001003000c14080e02004443c080d1809660007580c11032a0042c00701014140036885210587e00a03000750901d000d000e42040d000c0f41c102008613145802940740c03150a20f148038420103900e6040742d100d984c201d0141e01800c000c000d54540a91030b0b0312070030122181c040f029402c4440081c12201c2200e6034100e4012146620f802400128006550650305a000d91500c91080b16064101c698040b003090502001d950340201c1683c16030720218010400003405135103c2e01100e16049842003081d45001032580c00211100c050302c03101c9021 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 468409073 1250 468407823 468407833
    0x6030612031b1c08132414010f0e0a0e100f0e070807050604140a0b07050f010c14030c0a0306090e031c20071502031501020610061211091203070b0f0f01050d05 70
    0x240d1240c0c6c80c1004402074540780d858550103101d602070080304513a801081b96100c810400341c43e1812080c40c3c0100142070303200d250303502d10058003004000d10400c0c0003480d240c00704214083c0c0354001c80006004640003c04241301d000800708841c0f01c0010144191100217181d1810149021140d040d0120303250751440c0c020100c40d00018416401101900703c05100360007404264640490a5084031120038410301009000041c8199085c0e10804807a00700b2028540b51b5501c1c0315250381038001c4c3c022136200000051800c2c2a644c6080d2021014001440c07440402045c400982c0c1241c805403070381d00c0790034000b4880d00c0d0001c400f200307a030600500e4818420000c40d10080300304541c0e40c049070401c4070700c0c440700703606042013500c150380c14030000382e11140d243c5e0401940b6003451002000d4406a03254161841d0381c6400600303120f00a5825514840300007045592841581070560362a5084401c0032140a00c041c40401e80707100c44942130078440c1e40c609240c07100c00c0c3e00c2d00c003c00500c8c640c4120107072503601032 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 468410323 1250 468409073 468409103
    0xe0a1a1210020a3b010302070615060504060e0a18021c0603080304030314070822021f030b0a0602060f1909030c140d0e06030612031b1c0813 62
    0x100c0c0007509481d0300c01d80315000c44d1640010614100300d0a0011061900c01c02980c0400342c04405580c0c00d6106000c0c40c0c0117841e03100c103151400041200001c1c40800b00200300c0300051881d440f200a10a5500750b40c2d07503542d001c2c201ea0601482d804c0754082c02c4a21118281d0600071504543d000d0110000e1000e40b100420010101d80d00440303409410540728201d002080005264042c092485c1c2000580806003885c83c001030300170f10310103003d8034075161030314468141c0841d9a0041510b800d007540080c9100d01c800f143d1845c1403a075603c07001c500c1000c44d040c046140315519100c0040c1048070116005020340340d445164200d00004010a100307001c0300000644080c111203403080c0541d0360300c00c0c0c0701ca008414450901c103031100840c3c07074400820351001100e09005544003c07440c3c2da000003602c0701501c3e07842e00d03800505041816180105144004520040c0c20210041e01b0015070301c1d80b20985540302c120200292248180340c2e00a404250001e0210b0f0340105c6403400c8154003805040b10a5043c01 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 468411573 1250 468410323 468410353
    0x90d050309060301080102071106042301031d030d0516091505250317060a06050306130203133c0204090c060c0303110705060c070602040f0b040e0a1a12 67
    0x717800c000c44a0303501082d0320040021105400d41c00000842e155814185400c01300300640d08100143c082401610b8106030059010390000c0e89a90080c00440440b9142244c4040d40ca80207a0160740c11035003800d01080800d0001040104c05a00d1039403446d4106060541c0f2980852000010404025007040420703000d051703141501600003801ca0451140c40c5803400c000300101c01d104080c4110008101c10f0040d0780d600d40009004654450512070340385e81c0c595001a00c1a681c4412002085000204100c040054405524030316445100c1c042d49401140c19000883c10340e2900031080010030340c0b98440380c10b0608805541c00d81c401840413404000665946042100a81c0410702080030b03160540201509809111100708892507031909000c115102c060356400041d29840c008a0000785071000c2c01a2741c4c040702c020f030520301c0b94050080c2c1d40d00710b211011361042c420300a0503924500415034203000ca00031750710001280c03481130307102d00d10f01d100704075002d54000410229481481d640d48c00f051 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 468412823 1250 468411573 468411577
    0x10030f120212040b040602060a06050f101403010b030103020a0608040305030f1305010903080702190c03030f0c081204021f090b030c12010e22150f02160b040302160b090d05030906 79
    0x105000120f9600e486c608000a0328103a0054807405c141800c0c03a00c02d201c1c0c1d4031070440141003070608580708043c251080c07400307441d05a01c8a02544440d10004004900e59801c0401141200d2080c1e0b2000940756803404104c0b4503079815034000780002c4003000400c01d041d14074111640c2115620640c40c0a40e10203039a014211510072004130007058210081000c0b03250107102a481c0059404082d5490001c00d948901818038180070040c00c0c482e007c915500500d01c00c520343c5800c00e502c140c803542d82c2e01c0101a5158502c9080318128800c04006408010765002c1c01c00c413102c4001c40380c54040d025410120603040340d800c0280b040340020b01c01d21681c00d40b044945660740c001d1130100b5481d081402c000c11005040700080c09040061800c1912030b0340083e86501034406041802c001c00a400c0d070011007007002a00c00d410718070f00103410740c03144142030202c0601c040f4011031103502201c500000d04159209500000d1040c240040c41c140070981e00343c00e143c11448403403440307007003a07916040d07158000800360307 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 468414073 1250 468412823 468412829
    0x1516080904050403031a0d03020a200307080703020f1c06050403140d050405060a1b08040611070305031023040b0604050415090c020102030631061d10030f12021204 72
    0x7a2604100b8139244606c800414402d40291070b8820f09050544000e035480c4001d1400604921002c00780c0041205d0b4103e107609414001000d5a500c547d9602e94903940300401d000c02d91249400d0100c0074150724114100810520404260181801d0b0b0b41d10344500800006000f0740a01c02401d11050200001c4001410b43c0d410342d0b040002d640c103250401c103240c003600800b031841c001d1500082041c1400d11004a410300021032909600542c0c0c2c03807410b403019103840070054040c41004104c100030140c010024510510894011614569581002d640c0c01c41200c003184c9109180d018064a0741d040a4004412011004c0c09076854940c3c0d4001240c00c84020a14103141c0c4241000244482e10303082c019202000d110f403000f542141001c00004440d8400c030070356401e0403002980c06204000104042e0044811800c0042040d181e0b0f40b2034480e2003c44101c002410011901d000800421406c6202c2060700d4100d840307a0a21404e43e60359030358058011400105510a29080f059031104a00c020400707 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 468415323 1250 468414073 468414077
    0x2010e04180803090d0908010b2805090a02030114040911040f02041a2104050c0d051507050c0106170303010308070203121804050a05070c170c0616020c1516080904050403 75
    0x40151704400041c410741454200a9072a4101150500240d40701d5464211140c0e5150340988401c8011070000c000510036800590022040c804224408401c0d9029504136040303040b061820164880c1004101d540c0808020003c0785178051107201c6040980c403510084d086410010f1a2940301c02103606c41d0145103480c80c000c1c3d88001078020360741c14102060518401a0241c801c440d00380780e40d810b601c404071442d040c0c0c040c0c0f82e24078001c0d003404802c00c42540246510307000c401c1c0c14100300d50018455402603000182035802c1c41c50001d40c0301c0b441c0c0c501a03065043c900107582180d0030340d9108502a80481d17801c2c1ea2520401c140302031f00525080081010302060000540f9002031038060005407000100f80000d100e2170002009585038008414803001c0707520441e0003988081059041076640248004c4220a100c0c050401c07004071300d90351a0750441c1d0619001c40e114038644100b0058041024001090030130018000c010400c003902c00901d455510900d507580c00d02103000c0118080395411030701500 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 468416573 1250 468415323 468415333
    0x241404061d010906050121020307140c06091c0509060a020a0b0a1410151103130b1c0b0625020d03051e0c0c0f0a05120f07090902010e0418080309 64
    0x43c031602c218401040e0a080010b100902100c030032403084540240c030f421042d00000000d04a51082d080200e44064240616032540141500b90f65144800c5501c283c030ba2242c2038107078454005900444400210700da8502b80340c00109014001c4e00c0d0072501e903032810742c420070b0309100014014440452003034003441000160103800c081001076081018215406a21190701d0500070340901d03510300c210740a090308149815041346120035241d449050f02c425403d000a860210310100c030320307006002c40f803045543d401e00302c010011084120350034210619030021041090385d84600907503101000302114250b440c03190071015000300b09000b505107011000900c00141c0100a03252200d0035114000b0013000560410f0450003640780ea0340703201d1072000d1060b02000010b03030640d0340f140c14250107882c1c00380a0b11002e02491034526038480f100c00040300f25000c0e026000c0386216143c840d00d04280e80503520741d06611049030500c001041d0403c0d01d19000116442c0f400003140c02940114000d14029005003 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 468417823 1250 468416573 468416579
    0x50a0f051c0f05030106031d10020c010b190608090102040f0b041e050f0d0203030903070608060a14010801030f06021608190804170306030a0b0901050703241404061d01 74
    0x2481801410706030304103110a6040114896903c0402d49054030344909000513010840c018078101c02202d0907a946a034450030700d4001c201a01c0c3d401070f00364141640024071250188004000e80c0c180c00382a2410203151003001000326611980750140c0100c940e0300010b141c107403a2074001ca428483d40c4c00c007461918000a0810414003584901110240d5a02c8001505820503000591101c1142c0206100701203c41883c410340d42e0500848840500040449007070b142e4401c000340000b08219a1684280e2140c0000203c07184201040003422005039a8502c40340c0c296074890307082c0c01d1b001d00c099540039405c0c045e50703058031841d9000c8815940941959038440c201d8882401104d0352050840c010030050740c0602c0000380503008000e16042c03800030b0f80c039140d90ba200c0110745890708603000644441003030360034055000c1044d80854010190307940c0a1003174050842c481100e40d04c030b142c000390604448074410005540d400000c109160401000418025a250358140c2d4110084880300000c1c01040010 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 468419073 1250 468417823 468417853
    0x1d03032e03110a0b070506010509100905091e060112060c0504090905060402040e0f030702060703030e15150402190f0219050f06070305010302030a140c130905010c0203160f050a0f05 80
    0x100802135582e4140c5817261a95604d5200c1c0307418411213004803000e01c00310303200c1c00819096402501480b00104407614003440c105545644054140d10040d0101200901036a40402d00038142c42084c52070141c94042540c1d0f541c01045580c4410301000802d00002c1145c0c40d4600814810328002d10080809040500401049074013007604011603034440302e902900303403c011068800858044541d544c80350114141540030741014510144d181c0034000007a15a00e15128015000b20081411031420145010501003240f0a17401480175170041804540c100c00d21852104404070340c688140c54440807040303442c8004000d400700445040d00000360070701c2184000c02007183c1c4200f051034280800d501d1500130945603d08404041e00c090b5400340b0704072480f03a00700050b002c0ca40014242210301056403070340780700030011480211459424076481d5580c0502c00810f564911480c10040e542c441c81c280d03600c0c0711a01001c442241c45001e0b2119140200d60a80500d0100c68041c201624095500b0a04 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 468420323 1250 468419073 468419089
    0xe0f040203060a0c090303050304020315011707080111030a1d1207030206090c06091e0d030507110d0305040b070204110a050a080702060907061b0f0302010f1d03032e0311 75
    0x148241141c903111004070113961060305242140d0705814990317541d032103e0020030b0518100041c18040102100b00000c0c8041161910710303002e9048000351140961a1030000e4243c40c0b002078800d01c0c40e0303000c4c0301140c3c441c0c01d035500c1110054180940725411000c404051801d052040880305012800450f6860074103406000665016140c5e8014122200c180c200040740d50103100c07515801920300c648680c2c60031820390812505000c000345006004c0000b03180007003040d8030061040b2071103402c06804015074108441c1446450703078103031211030400381004402c0c24150050074082ea40310380c5400d04205034504040060210381c030250745003581e5a0301c0140c003901c034070008cc1000c403c56019108000340c0d41004640305040e10454a420494031424a08006e6549585e040251103950341030a10410180c05509c0340075400c040c5030b818811304100319035000000d0240b80903901207030020070000b25404170b61120b0301e241980e08074800d80710a8a400315624251041e03001110704c0420000418031628001c03034 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 468421573 1250 468420323 468420331
    0xc051302120a0903020a0516050112181101030b2106060306090d200d180f080703080c0a0c03060c09051c0201030b1507030905040e0a031e090e0f04020306 68
    0x10040d403920340030300c9900e45009001400440742d50f56420f0705404062003405205e8526030000c08650117820701807910303030107104a441641d02080746034110301c401901da401030f451518882c100512140217aa210300301d000400d0890305040644e900440010b6a0300c1c0e15070040300ea41740140302c100840185111a203481000742480b40b2070b501550030008143c078001009404200360b071421405039400030752051020304c03082d261220703240a004440240d040c1d203d490300090580950f40600026170743d1034285000403084c050a03d81e03800c00034040c40410344000051a882d440c080c101c0d032881e610b64450442a0340030341c0044a00b035440b8120090740b580c1c0200340c140a00400c03142c03000c2c8041e1400d0403056800d00303c04000d042c0341d202c071401240703643e800c028003201350311400c1010350b41d034000c1c900100042d0850240350b01c034910707004521040082c005241680e040d4036446009030482c103902e2000800448a007000100424000041807400c400424940946990744c2d2500c90350519104050816000074 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 468422823 1250 468421573 468421609
    0x3071502010f0b042013091a01030f05070207050607110904080414060301140f010903051f050f010803030403050f1c09200f0f0103230117030c0d0f1106040c05 70
    0x10040d0120b01e29000b201c5e000c00c50100140c240e071451680c111554402a580c800b402503131608243da685140d850152a140340426642001082090410101162820b5480c0c83c010707445a2410301c1503090041c024050b030f50103415071020060350a4000f50600c0411902181c8410ac042000c00c14109010324001d8541403c441d180e0540d81020f10782d80d00d0300c0c0c070f0400040c17245541004204199001e028048050741e040029a20400b03003a5034001051001580402c24151900c400507110301d880c0c2ca60306050b0780181000d1480c42e111920101e40c5034009c3c19010186010401c069020182e250302d6000110210050101e0382108078208015801c0744580c00d00c060b1b81c5070071829450b81d0748649210b000000215800d0b15480c0c40b040c01200105914000c0100e500700e11800c0e9202c1d55406150103040300c42c50104a0f0301d0b42450100d0546038040c80ca0fa0364a164003403070340ea6aa5038010540406181001d19000000030b545101d8140f4181044c1e40079520402d504609001c581080030900f08465220 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 468424073 1250 468422823 468422831
    0x8010606080a021b012a03060509060123031003120c1214070c090e19030503160e100e0f0109030807060504060204180c080a0e060708040203071502010f0b04 69
    0x10000181c02200014241c2180560014403956102a80301980031512036640007004010b444c04240c007440510300c0d05140031119110a01c08000741b20f4020001921000b40040b1804e89072038006541000d04a95000700e2010f104011130041055000034600c6007141b041c802000d646141414090f0303075420807020b010003030500c01500c08180400300112581c41ca524108488902c0402c014801303016040d8000c1c40c5503040c840000705040160800f2244019020684101c1540d000340340065003030320000100455400d0002420515400280000026950034800455045000011550500051040045407048880036803034140b45000805c004d4003802d18600d154116156105c40340950b07031f0000d0245803214005801c1001e80d806030b030014001a00f80001c1c4a100b00313071183c0a05400c003011400603450b00001045030700399001d10850020348001a244e0303920760010445075200024010398052294010000f240c001c0c4450321000400a0740c0005601c221100c0810103540700001c07618819410 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 468425323 1250 468424073 468424079
    0x60503030306120102090a09061a0918090312040b071d130513020402070f06112502120d0201090c05061305130b030703030c03180b0f1605071e080106 66
    0x10480340c000030304075040e0f504050560b0a050192140c080c02c01d8000b240c151740007030303d801c4581101d403c2e1009403500e03080d00281c041030f52405000304001349034000d480107840344940002c0c00d00a40c002d02d45505403843c060078031110812202c000d41d030466610f04810100042c40342d1000b0100d44003d5100d40884c6500c0f5403400240602d1840783c170f0709027a02d07a01c8001c46c01c0c5c4140c4483d40030216501410554860850342400007032081c0c084401c2d550f01d0b0800100c000720300481021100b5001d258070f1a114024194645069402c136841012a0048100502100344040400607800b04010755800854030002c0c0349041c40030468158072a50046c141071064201c0c041d818203070b607001c2c1e550648540c03c503408003003c5400500700800000f83c16000d000c1000c0b0038103600c051428000340c0280c0312560340d4203840f03030710000d001e03118031415407507640c2072144c2e04d00150311000611800480504003d184140b50711418100016038ac401d607041c05080d401d00c1c03d41c020203030100e001030141000070090b00385 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 468426573 1250 468425323 468425329
    0x7030e031801030608071d15030312060112060f060e0409111215040507150c02030c01120b03030d050403030e06070c0f03112a040902011706120d0c02040f0605 70
    0x59803885054a04050000c0100381d2082c2d004800a1490a007224085503a07000d0801f1204032001124512460340b80000e0381906091400c10171024002e0000c5242c0341055090f07402200c409400c60b4104841c02c01850304002041c002c01014041c20340600304120716101c030181030700f2001d0101501aa08100b091070105040250b071403102d032415101508940c10b886036050804c1602c5010b00405110b000910082c03000c0000d1030421b90f9522115032071116508441945c0d44186c0820007903260b4403000020817554030038401d8640500401d100481c2240c42e030030000c0d0440d007080240404080d03903101000300381545405014845103072180900480d00b400711000700b99003820b81024180c050180c100008262240661182d5450320000b510070001410b6503040d500780c1d9030340414508013810040b0151515092042c0089540d0503181c41640945110f484940703072500404044d841012591518080442402030444c0781456548400c0c0d108524070400c01110128140c54111501d07090003400140c07 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 468427823 1250 468426573 468426577
    0xb0a0b0315060918060102070605072006090a08030c060c070b04200406060f2304051207170a1505040c03020d06060f17150f0705071a041a07030e03 65
    0x840c05107124080d081c00201281c800d21481e00720070340000490710160280310120044c03901840c000d0f400d8603100d5a4505080f502400360380d0029110b003075400020440107030b00404005405001400280c100040710340020140350b03080d8048400380d00001017a41a00406024041d4444010b54049081202613251007242042c0280000c1030044031400318a0405101003091555901c000c03c1840140d0b1108801452a03075040d007042d012401500d490b5208030344403d070030004543d490364224240392802003001051804050115500d0094500200d0120b0503145210762464503d0b00030400101c01d4503103450040341040640700344919000c203210025202d507a0410850350100d4040200b4003d0303041200003002c00360711000b95485080000a0000c2d02c6a500b0040e808500d800e94291000002c6400f401050884050700002e82c51000214001d0042003c0d14015000d0040001002035480040b865000203031000d03180701c0d40d0307012070405580c4441c01c81a8021035901d0244080342020350b8143d039034 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 468429073 1250 468427823 468427831
    0xe010e15010804030e060d06170a02091b0f03070306180b2d0307030c090b0904020a03080a050d020a200102090a091e050a0c02060709030b0705071121010b0a0b03 71
    0x70864003c90f0500d03101d9901003890003402481c0e01c1d0766007510200d4000030714140c4114951038035000c00607828610007040140a03035801a040440c5691407840c40e4900300800403440302003050900440001c02000005541301e420382c0d0701c0010b012801c12040395101186091400c07586d600300fa81000035620b607a030004660014150300d480540f8418011800504140304495400d481000d40c0041440503c450590031643d00003c01c0108840c0c80091241400b400c035070280d04003c03162420000204200d00070300105002d85882c4e0b0400710011045020b1380d02031000ba50004a00196074a09075800112039115105950005c49ca031401e1000440d0800c082c4d44a0358a10742da48500a00c4026000c103041402485103d001300218501700f88864014020352104900510a0b40c001030003560040514400b035035002103070414159903103c07080b1005c3c0c0c01075404585082c0d03250003008064482c803941c103820601108410109403c2c9604060840d074034240c5841c4104031000007004600d424008403500 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 468430323 1250 468429073 468429077
    0x6040b04090209010c05030706051b090603040b04050f072306040819080405100302031f060512270a06142e03050303010b030103140c130213030c06090e010e1501 71
    0x907816a400141c8a808091740b0280140c080010030340c040254503400644220070300c00214003525141e070b21100d6640500b40d107a98101c0803c01c0441d001c11501c925041d8403510070422100300010f54540c0c9410320101d03521031070420008041c5840502201c440002c9a0351b8107503409c50034203181001707403a81c1d00b16000084004a20001040091000310402c81c0e0107800d014250960303188035914010000d520403119001d45a110228103c1c40302c00780050b036000c85920b540c07542d0411600700b1150715041c0c80030b000030303d84c9510340c000741044240510940407401c4200026010080d1281003402c1540d0340c0b0003100403840c5811040160103070031965079040c5030144070030818081802604010f0a0021600060718610011000041c02c00340b0340025410380748201c881c031181e44401424a07031741e410100c58050780002c03034026043c18002c0940c060031001035403110b0032240607626110491800c0007500000b000620056051025502d03907010540101100700c034001540c0382014103040078231140112281 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 468431573 1250 468430323 468430327
    0x14030609040f02180c09040f060302010c021e0a14130e191a091f091523161803050c010f17090a02010e010f0e090901110d150506040b040902 62
    0xc259100e84e00014aa400c13a21403013082c60908a110001980100e40f0031842607051240c081c20114903405140300b100d50603190b020a180c066404c2185900c011030b410b4110340984600030484bd645d10342d02c80020f01c008030203180d209041c04280140c000011070284000f906040f0b0b40d881898001910111040401a0700355003502e50b460182c0100c8000c20200014600c0c502c1031013415100821450881c00d113080b9035481602e000c03401d82d0180d9000f0f00c0f02400b014001c2c40d00000c510300d680c02204c100011a00c02100e60030901d0303501c00c0d03801000d4030740c0d0400a01e40d03060003184607008081700941841d030255008034945540e0b07402d03a580039025400d504000f2001d050488642c0913901d42812146d81d4164200c151520129465541070249002e90002d0b0085554408550064001e00e0500d0340c156510b0350100315000500400d201c000d4112a429981c078110600c03e040700c40086e1201c0e40c0610300c00310317030f8188601c502c0d81440759540199100388410001000195040800c84c0c00700e840c0b106002d030b = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 468432823 1250 468431573 468431603
    0x1107030320030c250602330f01030303060503030c10021b19061112240a0f0e0105010f0206220f06050708010f1a0904020d14071403060904 61
    0x103111036165001c108018440400d0f401c01d21103000c6070300401140c540e030083c04026052888041c460300284201801360b00600d452034800000e400d40c1c0d01c80c01011007140041c040611008980400c41140c1c001d40303402d00500140100341c0e150090f10001c003c00c900075818400c0c074440260b2101120b030b0107035800e56400a448143c0041c03070303010a080d494180080d0750800810030042051041d1000040710014038141200290000707640075140c881c000780311a6038056032441c104c85a0710f256861000740ca800410030040030743c0d83d5189504080c0c94540300494240345007c21401000d2010b8010a0600c034150a00306141ea500041c030341d5121001101850f000005207249035007041951402a260701c0305180c3c0c21080c070030703ea00050b008028954074148543e0340da0704030a80900150140100490444410003814a02c2802901011800420061500d0703d048903a000b103c4140d020904900040d800304030420780c101030798205c20002406802e02e10f00c0c14100140001a000b0b0005100c030501c1d801031 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 468434073 1250 468432823 468432857
    0x1f120902040b090403050c0c0603071d011e02031e030609060603041e06090b1308041a040f03050a02011403040201050405150d0e03030a060602030408060c2d0403030305010611070303 80
    0x24250b440c005003140c07416040a04004080e40d000400c0c4203018440d050498420742082001c0f644103c015550b02c2d0345044001c00b0104040e501a1300d214100b14000503d21030140072411106110382c9150001c595440c041000032078610300c3c0180709000501c003403081180035140d200000d0391202007211916501c0d6a28500f015203403e0113110344180700c224061f0501001038a5001d070178807901a4242e41500d80d600d15043c5043c116140e402040903e050004014042c0000300101d80b201807075086e142841d440b07129040030201140e005440c6644201000415941c0280900011a41c1d02111741d02c0c40c585600040c05900c03461090900403c25122440c10010b038040c141e80e181e600d500c4003400201301c040c41c070541e00d40056407400d1080c0d2a007100020340c0745c000800c507802c035200c90024044540d140c0c201e110303490300010103442c5104141d4040c040c0c000100780c5203100b00351589501c00d80b294110b0600408480e01600241c060040c0288601d403c10130008460301125813619207601d18030000111 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 468435323 1250 468434073 468434081
    0x21306140a0312140d0204030f06050c03070e102c090f10140607020429120c060c2d010f0513110a05120708190c0626070206061f12090204 61
    0x174000d5228030110b000300c2003048600304409400c1c015001800300d030b103513611400d0f40c512054482001051f414440856181001048104211028101221b81d01d107032491814403d81c01e880c034440c0203100c800701c00603189800107034580c024600c100c01940900e40001340c180507007039500445a1000366589101c2842d0349100880d481c25034060b10610800c00d0451042d17031303484000c410240306d2170008403400125041044503009651034083c01001c3d0f550b02401408941d603c0300054656034000d41d5000218108c14084540b00303441200480d1101c45c10042040e421100504042d80c02241008107015564400060700341c00d03290040c1401406c00f21030f80c00900710003120350103c0e030000750140e40700120b0706022070001c0c12507210304255212004070b0034002c2071200840400a00e01c1480801c10f00070248501445001c20514070310303050304c8404070080720502d2171007182d40070300682c00f00040090724141034110003000c03603070b0803c885182500b866005c0c10300c400d0a806002016918817040080d542c403908 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 468436573 1250 468435323 468435337
    0x1104060f0801020a03060509070507020402090d02030105010605031e0124120f0c0201110f1605010b0409230601050a09020a020c060c060103120810170109021306140a031214 76
    0x310403000156207200c1c80d8042d4000e0120100400e10380100003c50b17061440c1028800e04d5583c1d2407074504012682040020b4020300c120341c1d0411242c022150041c0c8092013194007030140e98a6140c0c90340743c843c10078120503004015000e82501d5071801084840180001d00f07240841d112401e00c00d5019492048030b0134090b106002003e40d040001c0d0f1069503c465020030300394007055000b40602150340c45c20030814030800002e901080c43c01c00848621282c02c4211a00b400d100d00004120725066000242c103849000c10f081c3c844031844900b40e80800c081281e4100c6500e0040082c100d01d40c07402c0300040f21803002c1c0c81202185c640004540460b030380b00b80521100400010445510b44503840d480d5a07035044240002c0701d040810300030645e1303c140901c014521680300d040080c04035a0038800322941e1b182a4a0025500d59202c846c0940143d0b6000c21000d180c800004000031003501e48040d0000000640c0e40c00d03401010050030500100d900d0000340c60341d80c1c5440c200b5001925082040031154402d400b = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 468437823 1250 468436573 468436589
    0xa05070609110a0906050907110a080a080a0b10080a020306011b150c0203070f081602122d0c10140a03020309100209090a0c051303030e03011503050604110406 70
    0x781c2540c04000302800e600700d4001c070948050001e02e444820940880d00fa500619900c214241c0010b41d107244280740003030002c44c0c2d440c1510030403040c035070340c448040e0050b14841000ca007114082046602084c8502ea00d420001c88400700402041c1101524805000d048165a9900040041d400340d0080a00942440c1829030300d41c2005510f080c94aa1030450011040c140ea05049541680910001c103440c0b0b0181c21000c4101c4003500b82d62070203255440009507100300c0c0c051101e2035026075030350b12216594a41c04800780800034507134005038205810030f1212302d85c14440c060142e0214080010f0700500c6075020780b800190913689000c2640c900f01001000401100b001502c0c000700c1d0791680145000d0049403089485150308809501e0590003406d00c3c031500704011000107412441c01d84c100c04034900583c02d2844c0382683c0440a002a648990810750106118489540c1242824407804d0b40000c20f1041e4030303121a0466507629100c0d40090409070648481541d039200b0307139030395030f05c00c0e40140890 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 468439073 1250 468437823 468437831
    0x1c05160b130e04020619020c12010f060e15090c1909030b060d20010e0415050f09010f03080f0d0903080402030606100503010501140d060801060f120c09020a050706 72
    0x5140800001c1e4010782415580d008030840c002092050b62602c2030203994000c01c040c1c02c1c2001854000c1045020403080030452141344929040341e250b4450151804085000220345c4030604002c280a4841070780c480c0c0c0078090608200041c80c946d444c29100c0b038007011900c2900c942c41c2d000042c20f0601031180703010701220200c030071200c010b500b0030b58100845c0c1c07003412a9640d6990b4903040100d18811000007401183e2038405030031b20208511480e03400250705041000c150529100844c044035403840d0001000608048d05100519000040250440301141d44421660401c01c408000710002d2200400f996804103c07030755500c45220a0354941540d0000808c031898044c140200052800d0b20141d01a003c1d18000ca550360400c5601660540295100c0a10b540d00e4080116201601c65803a88080d0700103014100c05040070380124001818803500100c0c149090000600a9810562028440450a0311242c0000d02001074120440e18550030060300c0e244408801c3d5903030320850800030205454 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 468440323 1250 468439073 468439079
    0x3080a09030209010801050103050a0b04050a0f0606230a060f0909050c03070806010507020d1704030506040b100f0f0605130504020c150a02091e01020115080604110105091c0516 78
    0x1205000300220303402102c06114a0740c2e5081c81078226203003808040c107190803c0c024980820040038240b0b40017071042c4101c64103900582c4451420901100b81101e0300c68491000704110b030000040e141008004801076032400c03411100180800c84548030b444c1c10f00c500100451015801100e5403001401100014080da04c1c12188030710107a4411980c2401044011005c501254490700c26910040d80c090302045449801d515506841c5542410094a9140401010000403003d000c8903000d10b00c0f40c44201814108002071920384170068100f810714103480441001a4401d4580d05000c1318918180755903105210127294142d5140760308420780050002070206140b0500089a01036413000658003845500d8041c1200181d2113081946a44945c0002d0000501c2c0f12140003015464414000043c800e00030741013100907035080764803248154220a003000f0a00c078008020320740a40091805500d000c200200003415901007075055442894012404810007004010b6441400303a482011112140c1d = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 468441573 1250 468440323 468440327
    0xf0d060b0d0c050901140f090a02040b0a180503150c16121110050630150f09010204031205030402030c03010501141801030c120c0e010b030106020d0e030303060112020403080a 77
    0x803070ba03c1550b004041920002540e48418920076122920090404400348031500804c81c0c0c3c6d41d0050000c011f03080d0700300000181868004014400c40c4440d03240c046101859101601184000358040d0b0700a4000c2c034000c40c03903d41407814859000c103419516644800e8580b00d80b264168020320300a1100c5901c0561004090708507202c2414206400115480c0b0500c3c100580e06941d01580d0712504001c40c010441440d4130340c040050408102c45041c420110750202c200b610741208044070800d2103500500303001c0403055840c12550300c24441002945001e1456452540079802200e12004205011022504554041c4092044a03c004009000c00d58403642c0400344900302074413280c407416456014401e841414000d0504803900000c1c1e03245500e00d881c1048481103500d000c12207004a0221011500790100c0c14140d0180403e596035a44039130400380040d01d401c45030030a80040c0056030606550f641d4000003101e174004000c0c60100e004d901c1c0c000d10700010f8020ac0d000200000004696001215 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 468442823 1250 468441573 468441593
    0x3061409032703070617090a021e010201021c0b09090109051e0f0d0504050a0501230f07050607020138131e0e01150605090402070f1e0302011a0f0d060b0d 68
    0x446115846d07846031a0100f83c25030361140303030700000d410450030381028801c91000c46001c1c04845060002600d031501c01c001100e16090f43d072500704105695000154200d0a1041500c5d070300c2611035000300300608203521569070380d6080c0680008000c00468814090420034040d000d0314011420840d44c2c2c003000d16001030070380d401074051180074001c070040018256218000003841c6800c4640e41080ea000c0c0c003601103003147c2c8a01440d1050600400840e030018508004052091200b94000116024421480160112000880054207284104413052021541454030003c0c2e000c94041da148200c08070000f01818030b40c103800200d0603055001408080154000030000c0034600c0080005441b603100164018101d030040900158091181c512181400d034003c04260b030052500010101c095500d80300b03c1480c81100d40a00881048920b007015024022903c2e620307801812000300030500c101040e480c203202d150f8907101c0d00c0403080c0070090090981c0105500a405041d003210609503003045000300c = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 468444073 1250 468442823 468442847
    0x10303020c0307030201080a022214040f09020f01110c03010e0615030607020d03020705010213060c2d0201120b101e0503161107050910030614090327030706 69
    0x160207014644801c1d49404903031941501e6050b1160304041e1141c40d80080290005c0c0602c18594100800441c1d9054080184e04010b100340c00e09906035061150911003503d00c03240540c2602802c212050300141e030381e80812064985c0c2843d22a0740c40005040480c42d1034001807a10d82c05503e0071071284492680841c4051003100e1040f00203010f07200d00703400e16907174480480b543c50042c0c10031140380b4080f40c82a0003c0c441e40d40281c1c0054100703424050030501400c03e548c40342011400000c08041000500c07032000d503044202c201c1060a0340b0101c5042441a03440b0b140090400c104007006a000440c10384c07091130b850001501d00d8000b902c0508002e05181c50500100d0100700c503640d54040c1261040d01124802c81d55036186100c07280044009449100c1c6042c6541850f014070a004655500e4180c140352040b4504071303514000d1495400e04000300c6440074180801000240c0c100000c031400042190510f01030320410755100c00080580748000e2002c000030300d5150245040003e40035130320412074802 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 468445323 1250 468444073 468444077
    0x41b051c0e072d03021e1005030610090501120b0406080a0605042109150c060c031e02030103051b030f03071208011706061e0a080d09060f05030a02070c0b030f010303 73
    0x3400000e5110410500858103904040c41c1440c074040c001400c14001003503604210851b164043d4440b407000074000c10740000e15100081002c01003240030310304050b101c03541d401c0740e0030000e03041810400000d00d2401d1040c2c00da8520707070710b81c40c0c0d80c2c4917600ca03580558000c008000c10380d000c6011500d40080900301c1a2802c0da00c084021178500c4868060000800d02c54005031698219146080c07001e84c50b04041c2c140c01c106100302e0041e40e0010170306d9070103607809910040e42e00091250400c5158040c86600c601c085039840c0c8180018030020703100180401010703040501540c0f200303084600013440c014031703030308000c006001c0401c20b01e0802c405484152627a04a039294118280e0700d980039014401241204000d003035128102181143c14003900c0450400368180003805c203d03040e42c0211300240da081e800b0240e1648903a408002165001c100003000d00b845103442c90b03440480280c020400c2c00080c0c8800622680042c1502c204071700d10020301d00400b01c4101003a03c916240c0300c2024101001d2100b1b0380 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 468446573 1250 468445323 468445349
    0x30c070605030c03010e0c09090703061701090510020d150303170604020306010c02010e061306050c2e0b0402070609111f0c060905010e15090705041b051c0e07 70
    0x51041c000d20a5901c50000c02c401e46003540c0c40c3c070503002134248000d0200012220700300400c48041c3c40b1550754a20404550718003196044c034056540300c40f014500162915030340341c00001c0000490100c0d1605207001e5010740961981ca00c40030700300040012000585000105020000c00c0603040070b5440c2d510a008602010344d90b03504d030103001c280d110848496000503c0303070b41494019805030000c0c43c05000041d10150400d0380d804003090b400f5407076800c100c0200b840801e091800880801441c450030420700c3c2c0468030402c41d682440030050000070b02540703542c3c50390720381000750301c0d03c6e4151600d1139008002481255503a0820b00064240c4250b071070b008901d500092044501100460515042c0c00e83e40c400516000b078681000914280004440f555290041d000b003000b020803a4180500200c2041440340c1007031500706180c19000c1c4d00050040d0b040c00c41c4c82c0e4048600320b00c02c81000202d030800a0352220b51154244076540d0034174409103040d00d0110044e115500024240d42603840d4100109 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 468447823 1250 468446573 468446579
    0xe0c091905010e0f070306030b01030209070e03030301090b19032d240c03060501020c0d0203010e03190818030706020d140a0608160e0103020d080c010c02030306040b0111060403110703060e030c07 86
    0x40c00e40d1060300010327007505400001000103040003442194490f030f162810b01c100322041c80c0040e0842d80700f03a00900ea040d40390110b8072404d1a15140342180302d0200718820850501d1a1b50ba501c0101804042002032990550311000e420141c210f00d0b00856488a18404d0307001035642d01020300c2646c00031028440e0301c1e1000e0b0703400300344c001e200b0b040070303918141c000340f18a80081042240740009a0320498055480b8000c14480c000100041c050551960010403000e140021004190001c01801c00440a900c0004007428003c040110b40d10700350490005a80c0c1c551441230300c0c000c1c05004800d03003010208030007040030b00d11856100d40240c1d0441c0d02581c40c10030903105c84052100b4240203403590420b07036000400043c580483e00710301052240c2042405d24200e079141d1421103000341c8540d07000d42c200008000407803a041c80351000104007400c00651a00c240c21900b592070100400083c18055403035100c40d15a4000c11080d00110b5020b40103100e02106014143e03142c0d045200050382c2d510a00f2008 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 468449073 1250 468447823 468447827
    0xd030507060c02161e2d0e0a05090307030f0e0a1203020610080c063a0203060a05010305090c09070908030d060315020406020d0503041a0c09090a0e0c091905010e0f07 73
    0x1094070315007250a200001414034104400700200b15641003401c4000400b07200060310301e50011b000038180008102460715100c1e0400c0103807400100f03000306c0e98008000a0f80040d8002614940c104864600301d4094480700700810f44c0038105410403850030303240074400740404d40c0c00a00315125680340340c11a12015560140346965000d1000c00c15030102041c04001c00c03491080d02e03090491001807454213103240d900780f038054a011142d020104456000010031030b00342824440c620042000b840e0410581c50400001e6444105d0120704510a01c80d8a0120362040c0c03180d1080005000c1c100e043e20303a10380004224000801903840215021104407200004005242c426101111455005002400740d101c200b1039083e44010310072601002a0340b015100e4540609000388590a02200c0c1070380e4503240750811403003000081c960300180f402c2001c5091000c0300462407190052003a5071040322a29010b1040311104000d58803888900d19200001a82c5a03100030305d180070724010742c0104059204d071401 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 468450323 1250 468449073 468449099
    0x90e0406020c0c04021801122a0314060a0e1e011d060d0f150608011107060b0f130b04061e0e01060e1008060103090c0b1e070209060d030507060c0216 66
    0x598281032104000b88201f540aa440d0300c6004524982c0010300078070b91605041455450f1036420062250403221201b5150103115140c03451860144078901450007500161104181d07000799a91130f0000d50100780d185a408115103512071081003800c42035078450b0a900b40100c81c0340f004150546030390021400a080c4400d2640e440da4001c901c00e2000110f58445041c00000815849002c5035141e500040c803803402e00c03600182640c4510b0460760344104e41408000d507813107500410f220742001d504d5002c3e190303a00d0100342a9149406808101501c507180014024202680081c084220100a584405815030000b50640700815008906640c884a049801008001000d0740041b43c0c010500c070700c80e019803c140e500400525000c10045001d0341c520640502692211000c068041440c000e241041003400940e042d5904110f810581c1940000e0103000c0007901075405001d406110a090602c101c00b100d48a86d0005424440714001c054000e40d00c070706c4100a01d024040c248008070710740440d511 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 468451573 1250 468450323 468450337
    0x303052703070305031003050a050c041109010815010309170904110304500c01050c0307020d030c080f250f060c0e10050d050108030c07060e01090e0406020c0c0402 72
    0x1c60034410315680a035800c0c1d002908100581c518450300100241040000c0e10606105001400303c2040d45014481034618580c80304030b1011040c001001681d0303201d44101d0340068807008d900c00d07c500aa00680c0280502032014015142305501c0c80481010321004185181e000d6504002014062000c2031090106880083c100c050b051480300c80c1c080708240189c0c40f041e21400140309286501031125440c0c540c1e5440d4144140761a03440d1800d10700511410664103020300344a0714000144001c1c940328412400024814103080400c0001e040c40b444220204962003035202d6913542c03010407510b41c1a001070aa40340c000c40020782c9201a01c00e0002e83c5034400d58440384503400001a540c458000c0e264484030b0b01c04102e81c1401080355961031400c0e54000720055111280e850a0031070141c01520130503080030185520070000880002800552142210010301d00720101a8903200100d0721840903610500f41e000022051100f80041680180110b141c03110890307002007040c90620040c0d0141c20 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 468452823 1250 468451573 468451651
    0x40803040f081303060504060e010507020304030204020f090a080f1b0108041509080307030902030105090706020d0818010f0204050913110621010909021305040c15050c0a030305 78
    0x8408140001e0341d02140400c00e42c03060441e9802d182c00000100302c0c2410a6009685503a110800d000922070740384034154052824200078401c03440c0805001e0340d00e1040b48402401960b0002d6450b42d01c0300306070156000300000400b04660680d5a411b40c913511040e0703160100e0503002d140804e103400c40165005100051042c0c64081b166665130b200e140404001c00351002410341c4501d445000a00f00400451051225031000205140300d401490300712880208007002c0d5500840061000e907030001280f81070700c8144d2a12101d503a58a480c0d0303650441905840c506150b082c1040307d010000150007900c00d50b039007603034004025914603500c2c0d084100400800f400f07640c0c002c0c00d41e8005050401c000d00340c01400e01318504134803510419058031104245e000d540100e5841880c0d030110b1404040f01c2c90300c007100071030030b11035400d15413a814800c0072144a41842010002420003070740d03005800f0340304c54190070010b444501c0301c2d900b0301801805046807105004038400201d034220301000810803000242d09 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 468454073 1250 468452823 468452827
    0x40b070801050d062a09150813020d0c0b0408030a030f051b090315040f02100c050c09060a120c05090105031209060a05040b070c0501020d0f020606010c060e01020f041d0408 76
    0x2615110020610700c814201d0360442100078a036100303a4071081d0318520702c4580d06c02c2c100b80e142460300c080c5815001c4090040007941c20070310200c003802c1690100c019030126042940c03c1541c0c40c021098034565841840c0114012800241711100403000d840c03120580e48042c804103041058000071034808481c5804001c005c03415400c042d4060101900300301401070125020541c03180c919426194084400f03d40b2031b4551100142141803440d100d414041050501c50b0f100da81550747c10351941c080391a40c81c040c03007008000402c5a900d0b6000c150092600c0070072246000359505181c0301c003440c2401150300035000c10340009001e080c00123800f2020045000f5140c10074070064104450780d88004013074020448188000b240b442e2006004021007403007101d92940b050316140000e42040c40003d543c0092000c105803002820780c0108810390b12010901e400261803546d0719001d001030541d070034184650340c404a501c180c1c0d4070410703005005841e0f0741d0713100c81d16800382c8664403240b010007100c0040801d041 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 468455323 1250 468454073 468454099
    0x15060d0507020c1207050a0617040b04030e09090a030f0e0303070602090409020303040e010609141023270301050c0f0d2003061806010207140a0302040c08040b07080105 74
    0x6a402590040c01c00d00c19621094640d0700007654000d20004400302580003107904000a11305482d10f40001c01c0a820410b4407000c043c0d0094000400081000d403626495034001420540306401c0d1061001004220844030b00b00f0b0240581d44207a041d80071000b054100344a9107025001d04004030003080020011494041190749042c040c0d007080000c26003103038681e400d200040e6810f0010300007801c00300026a0f403540c508000189200707010390264800c4028078440760000e84855451000d5417041e420301103410608100f0484260300c4080c2c24039400c03c8080ba10300314000d0445019160200103902000c00c0c042031104043c01c031001615003082d8000100003040170611903001402d01e507825040b002442810400d01d41d00c006c0c5c09030a10741c0681400100f0094030b441c0030201d060f07580c051015414860324100c80040e43d2641e5a001d0b100007801d59100e40815683c0b000100c00145a018206011981841c4d801600078013040d2002c41c0c40071110000100b24034400c100c01812039000408003100000 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 468456573 1250 468455323 468455347
    0x1e041202041d1c032a0801092702061e040801060e0c04030f020d05010501090618020901230d1a03010b18070e060d05090f0706030603030215090705100c020301051506 73
    0x3c400c05205050b203c031807a1410604440100c0708091500c03003040801212020b000701011016003240341124074000300040070401008154064149580c2c0210150303240f400000d00600030703a40284186154102c400b001503688202801c200c2d1440c500278481c0580354003480396102c0341103c9464a41c13400340401c2001c00c0880100500890014160100c210840c0d240c0500b076a1003600103010b5681c0b00c0300c00308a401124000c0c13001c2203060000450a025294000814031440c0481d202000c500d0740303140c001494140011640d13000c0d00544100b050083c191a081013861079003802da4880e52070a580d0000c80c2c1010380300452040c01000715038000d55281107051310301c118181c2c0703401d4202c0b50500c110b003a030b032070b052158a010340500c800501030346640e110322600d8020325811010400d401c1140070070020303400003254040d80b0a4101401d016070b130760360f02c0b1a00d0b01004d54000d07584850b0144842c0c0a05400404075014071340254000d100c0d940c0d4200d504024076280c00c3c0a290000d07010400350020304 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 468457823 1250 468456573 468456613
    0x1202060f0c1006080d0509010804032a2006030610030e0a20030d1412040204090206041e09150504020901020106030b0c13090b030706051e041202041d 66
    0x546540e000506220380e4559007460034070380d032058140e001e64440041c803a0f9102000210710b039000c01d2415521344100c6400081241d400500010207005019000c1c0381c12155551440d01b04110000d075002070181a820070008001c143c003000b100b40070210039000d031141000781c12244103d2020f0f050408242e920780c4200c0c010102c3d10a0010203000d114803110000b80e1416075184443c3e00c58042601c1d09003040f003054101380000304180103100804a00121602071031058944030101d10340c407c1d40d00c1c3e8441c00454042c5c080441c0017075000c60b0009000c982180c0003888200408401c1c5154102e65441c0c07a40b110403561660400c642c001c030894020230040c64a5001404c128806200115102d69240c0c1c90f100c0004081d2913403105c2c52400f2034110f800149140c0280c00030280c00100340604280c840110b921009123004150801000081c81c03446500d296681601d2042410815541d4656884040d8014102c40710101d100c2d0381003072510b94802c041c0d407075070020a00035100a020301000304481c141c01c0b0 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 468459073 1250 468457823 468457837
    0x212070c03020a180b01080f07140708030106030203160e0d021e04050103080a030b0612040b100806010e040204060909150e07050307030f0b0912070b07050c010905070f0609120206 79
    0x510491404001a103400121400609007240c032200d99220f1550000c0c05c4d40c0c504510503040000140c10401000401151681c2210240c20700d609100d4181035050010300c038404c0f019000281c000000200c065055006510030340c00c5211508a1100b83c9000715903140d200c003004d903030000c0303c03207148405032428000404129442004501101520700c02103020b60b44c0c240e109580c041c0000c1002d124550305801010204ea0003100c23000e1614180841c04038604001400240c250110320001a02c914a201058801380c190302d812200d1a680d1180c1c000d031110b108441c200c0c042c40c20401d000130150301e0b90045d6002c1d10340c80540707031200500c912030b03400003000c0c1d0000da08021f120380800015940c4061103820065802280200e80c40c0034182008642420060f010f03072200d1b0311030782c840404039010710f054418440d40f204038001941c5409000700e5590240388400c8000e9440c003241c2c101007010004040c002c44200c4024010f40b90744d5004280c07800442481000d8006100034409001850000010401 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 468460323 1250 468459073 468459083
    0x1b060f150306090a0b0a06080f06041e051e0114040f021306060e3003120c0703050403030c110405150102060c1c021c05130b06060f1902011b0203070b0603070501021207 74
    0xf607236071008500c4c0350642c501400756840d00400709220600020a110f030740e04210001d1100184d410303507950381d1340e1a0509414214503074040e001c00c0124402c2900034800c84c0b14000d425955506050030b15143d0303078403816012441240106124003107003c03a401004100c400f1501c80c8a005102c44003400718015917182035010103844041454840603103400540c2111a20303000135a1140c650f03442030007079034801504613000000e00b8854040042e9101085a041d80d9151800c1d11200d10030f4904404607440c4041d46561184c240820494109400c09910384400001da0031104a80c440401d59015031082ca04002c0014102e40d1008686845a400401c20035868016240d41710448840d03080485000b80e450610a00382c104200091164029100d43c106001300c42c90b505c0c01c4091b181000c030b94441c034039142c0007422145c0c00c6c508030b1034000e42c8021017400712205614060a0000002901e951010074100c460072803032008100c581c10000b40100581e001030b00101041c4000000d0049a03030403800c02111 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 468461573 1250 468460323 468460331
    0x30507081528050118080a03230406050309010b09071b0309090e01050603071e0e04110406090b12010b0306070c21030906050f0f0604021b060f150306090a0b0a 70
    0x105050a5a429081c0c00180b204001003074104400140098540e43e1440c426000c0702c081070084440210741c0c0b16095906040030310313200402980100702000303443d01c02000326002050008a1f641c00c20002e41c4030320840740007003025034400d1040080380101551241c0c001444c0c50109000300500300d030550344d801e0003400d0400c20b480d9905200c609440540c1c115906a075111002d00516060401519019061811070740006000385260381d203443c0028800c4841080446001c901400035484101501d140050002e101d081e0b218410380010f041e401d009980182040b00359850b03c010107100f14028084020b000d803800ba11040d50850b41035520040c00da51800c94440103120000e0300307900050581ca11500c002c10444194140001281e40c0101944240282a01002060b0b0060307030049074000003c0301d0058807075485424544200c0901d2171100740b14401c40081c0030080707984c1a1183d1159034201820b403104285d40061648034501070f0344002da2940506108800501f1030b80030340d0303445192484002 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 468462823 1250 468461573 468461599
    0x305030c0c100e06010503070305060c09040915090c050a06081306141f351f0f0c02010c05030a051e071e02070501051209030d14160305070815 63
    0xa0070040b49100d800101552600f291031624000d0140d80d00405040780513203205451364490f1912004000d041803030641001500c0b898035a1035a1041c2c03001500500120a1074a5220803000180080c10701aa03a1b0307120800300142c140b0381061b800090b0780c280d036641d003050b8450303c0c110f1041d002c54031012a0103a460707411840300c0100380c0e24024410000031202c8020303105105080038040440da0071268040c11402204540c0c003444414900320b5003150b014203844a44001041c60070003c12241030446040311890f80048810180c00c4000030400a800c1040b44411144040c4d00701c800d508030400114405000044a1045a901165000107005650003100d5442601980e6400e011140100450503d881e10801603000240d5040c0f034003034900090058600301000070780103004590a00b0800100240010705184050050350750114130001c003032101424208224040800484d4881030310220f80c2c09425003d40302c0c0c0500b501501c0c942c0c4440080ea00c0716944a0804c0104c07500481d00428481101 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 468464073 1250 468462823 468462847
    0xf01140708070b0106031b090501050304030201060e0a09111c17090a0902030405151005060714010207030915090e15060c0f01020910090f0603020c160b03070305060d0f0305030c 78
    0x625525101e4003880040c1d40c1801009401c68001c0c00000811f00c01c00300001010641081e50b6400303882c0e0900f000c07500c4c4c0d074079490200d0140496400224281c0403000a00c9282595600041e84003403090800c64a500c4c41001071251141c814001d900d00d10440b07400403004141901d081780745503410b1040c1146855406004100100015031040180d190300004100520406010741002e062902403004400c0c1440c0c1140d55022200380a02d0b8810600000c816040103101401848510700380742c0250340354076442c140584640001d11035402113441d140e070b140300322a1040c0c41020985402031030711146d0740c41d10b41107801651469180f06810601c00c0244011141c0c0400546841552001c00076a907600d448043c441110303100d000c0741c814098444424403214802013400e1058903464030340103842d0340703203507101520f042c00802104407071103000f01010500e14400d03001175114a4071a1418002c5854080a0011110001e0780150001d880b1868502c0024401d01c0255000340f00498001d007400254942 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 468465323 1250 468464073 468464077
    0x30a14120c100c2d0e12210d060311010f0513230303031305010612022d100201020a090f180b01051b01090b01050f0105030708060d0f030201140c090f01140708 70
    0x50281c000f13100000d14500b0541c81000d0841c42d000a481003804006598105541d982400007400a81204003812001e000d070b5100c241d805030180381c00305002040d0390382843c01000d100440c8c2d41e070000364009107084e0b40c18002d0044030f40ca0056841c2c4107843c103241811901d807401c0499010303001001c141d000300507999010030265008021010038860f40a205103400b50841c2d155a001c003080a03000005d000c05640c5a07070500403200c103100345080242101032030603688034541e8006070740d120010300484540207038154082c15410340350391543d5540d543c4079030040301028810b204010881700e1403034501e8508030700ca400c00700004006040450810110b841d0700c05000001818500c1940e6440103c4014000c80e10f541d1801050141d403030802300c800300e500007042403000420b89018810f114022411039114042041049600000340f160309804610f4000d011b0407020010400a02c0301c0c0c40031994081100080360362105008003901c05c003000c01401959802c002440818889105000da000070526540c0 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 468466573 1250 468465323 468465377
    0x3041502060727031104060b040b120a0603170a090807090906050f04020a17030c060a230105030d0e040e010911031b030304091a030a14120c100c 64
    0x241210b85400d46004014810703240c1210807070380d01d507480004882c0101d810070082e6500130090030100c211650100c0c1c060001903205900300d980001e0001040c1d24504007510084075842c0b031a4485440c0ca0180030300340c4d40d41e0b01004e05601110310402c01e5440e91507005004000b51803d080a60980d11a020342c1031079565446510710681720400f0030308000451003601c1e44040c1d0b2580810700c2d4201074011548610107801500e8640d21020340243d0203040800642d03241c2d40315a0100d4507245090b411200142140307140c1418100e0320040c000785154004000c0c80d0599070080d000f03264044289800300c8500d40d540c484280c0141d925444084003203400c0c06000c0354140200c1100000156030030034945000000716628135640240c900c180081d07a804021102100c8142c040481d001d89100304802490880c1100e15606100b040504010003d111416500c000d0307095090b113030031540c5a18102c10744e101715214070103203412005800c0580c500641c0300780c01ea0000c40c0f03000030004520407200c0f00c00c060819 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 468467823 1250 468466573 468466577
    0x4031b05011b050109120f020d080c030402060c12070614060301020c0c0603100f030c0614031302010804030e0d06050f0a0c0c020d0309031a0a05010504090f06090809130b04150e0414030415 83
    0x31440101031f503010000b644090f1068600008a883c1c440e4445c2c4241c000604000e01c6840d000138a004480c40401407665080342210750b031941e03405076142c220002d101c1001c1d00710f100a10500003c00c41e15061095030b60302d0705031034003500d01002980c0030030140d944002e11255500405840c0495603601c1d01e00c6e594080d40c410b007119091503061090240c15002c00c0840700001d00d00400c2080003101d1451240e48007a0348c207007070031085900c641c43c080d11340402790703c501c941190002d4006021301c40184c00460186a000301310002507155850081e09459413003410102103000c803264417005003800152484194000d02e0920b01d015104d5507405000070441c400e0703259041240040c80400b80213445920f0040004031401c001a1132950340d1b402750742c6c001c03040c050140f5950b1000c2c0024032000c0340854000c0000140000c0c0a1040c03000b101c001403900c0358506010780c2c60a60030088010303c031448030301501d252842885440d5030b156600da01c00b82031400000014002807200045c46140a03040d04440001360b = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 468469073 1250 468467823 468467837
    0x20c130e250504050118020705030f0a0e01140a1704020a030209160801081c030b1306080102071e0209131e0623250e0d060204031b05011b05010912 65
    0x301c0c81d11020007440c2c001901ca01c0c41c0c8001080007000082c1101c141c941c81d0030016840c0c4403141001d81c214080d0303901070103003058001010036001e64052030408000350240c03150b01c904d801d4500b203400316000e0307000300002185000843c144102e001f03030400341e413183c4014510304c0503907140c2c0d011408002040d210b00c03101c0e00c0c65510310041940c0042111340502045c03c0140115600846092240004018103105050340c841305c88089444e00d920303050b01400032441c24410031b5070320000f9900039030000c0f0007921080340b880c8800c1d0004908404e81038110b41c0041001c2410b48401d41c1e0303525400c00080044441007907000b007020b100d2925000d4a6005030080400050140402c41c02d50f041251703c00c10310700740c949080200500c40c010181e4000b54135094202e410300c4846501016036900441a421640c401100301800e010000b09030014020303240f241d00b443e1742410307800258611030703480b0b8090540402c00800c7c11441d400904070030130396154017035000410309454544415104600d8501c01324005140 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 468470323 1250 468469073 468469123
    0x203090607050306150c01140f070f02030c07270501030516170d0f091208041a0f0a08071e08070305100f0b070212030f0c010b0a0303020c130e 63
    0x2051080e40e601c110a410300c1d514514141c4002545a80c00d80c542e82c100640100d00303921409825070009000c400e24040f524294240600c0e0f406450300300300c91310b80c0010780012040805900c04419600d0041c0d484000381065414035150106003646001403030045a140310342d51001c034816005483c0214010005004c1600e8010060306040410b40c1203076480c6078114020601ca48030011300a101da06030380c40c14503140803051500321484011a40401855120020302d07070b0900032504003c0040340c142c2c1010344220211100c6011090085070501510403009200354a4100d0259505a90110b500e00d0320600b0742c034020703400301e000d4001d11001c0c10010745a1400c10080940bd481000d82103003070300b00540400c42c074010740e580e41110b141c000c000c80e40102050581c11500d031254400d919500c0041982e84404e800c200c40b0800da08601a5080150308107015001c031401c160b10b100c01541d030164081c1c032480031804203021040c0e0105920f4503d444d0390f91410030010313906020207040d8140031428600e0910f0 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 468471573 1250 468470323 468470341
    0x7030e19080d0e0108041709030a0302070e16091a210a0b04020306131a0306010e040b060d0b070f022802040510060806100509150a0f090e0106110a0606090203 70
    0xa0050800340520a501600798040e0b80c01611246d409a402a808600c6d41e401500c940c0c1c01e401751003142c54042c41140c0d94134003050b401181302000e69010901c050303196510b000d0085c2612078840781070030102e01c4513107081c0455501841c0c1c1204860890994610340042114000c0790303c07a20041030f40d50070700500e00340305590142d4040e0300d0300e0040850302541503051480005007000d03c2d4000444249603100050160603c07500e0070048045401000e640241da034810720000c1c0802d00b2101240c0041603100091441d2900030791158075290000034140307181e40c501000703892510383c03507900c84150f1049408040e00c1c1c14880760215400350301e5414240e04203031148140b1064501c003801d01518000412400d101495000c1241d59101c40c2c202c030f0240c440c070f14075401601c9520418103032603000f00c4030301c0e8589160341844006100c80321450360b50070108010050b00f207640104500500a80c8060300c0010089a03114040c0201d203071100206403000210f580c0d80701d00444540783e1020782000c1c2c0110030094180 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 468472823 1250 468471573 468471583
    0x507050d02010c0207090c09030c170f150105041a04050c0c100b0607020108040c0e090a120c0201021b0105040f080601030309050a0b09151603120f09080f07030e1908 73
    0x80c940003d0140090154010707449010754016040c40c0341e620749607646507501c20303140c0300002e54000c45182c240d10748901a0100e05620071303082404034810b20540b1441e0000004d01d401d15206c078014024190f07400c1004000150100110a002d510480b0390511340307d99030ba12540e80108442c0328015900c0445402365818501c24010f007225491400304440742c90740750300085034161030b030920b05055555554074006240b18000d402850111442108000c4000ea000807101d603000d0140310503404113940742404540240c400702c030090050b041070b0102c40c21038441800c1d44a900c01c050410a082c66161001d000315581c0c144c0c01030b1480d0f480760004000381508000200084c08040e2244a801414070074011120b101c1e02e00414010308913000149500a0034a0a0b0340048200c420305c2031018071982801840240e03410807a8260030318006151011000502c520b443c4140d00c540000e051084591840086402c00a01070301400000c00c00e8240380c3e40c0e41041000e0395990404d140d0034450411200c2490701c = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 468474073 1250 468472823 468472843
    0x302010e0303070f06020a05070c030f11060304080702010e1302070b040c0603110a050c0a0f0605070905040b0112050402120604032106060801120c080d0512220201050c0703050d050705 81
    0x10b03810400c00c4001061103001c0c000941c2e9040300d000350355400c0c90300003101c0398401c08402914141d009000441007020307170680d01c0b094500407407001108101c10010454644002d80340109001d000304440001540607800361100464024111443c40310510880c50a90788040e00849900c05000100420032818588034009041d042c541000001c0c0300c401d64441c14890b40740c204003407000100726074032410410090303e0f41055201078045007a80b5149014030240506807005004a040da01380492242040c1c440c0711396054050303440c44c001d00350480d4040700416001d003050741c00200ca100040a0400b04208090140d8841d5542001c0001d007200300c1d00a01d0b0765400d41c449580d0900c00208081036000d02c82505513084000404420041c1d480c00860095165000260300d001340320003900403030342190203130a01c40f007903940c456501da4991008420250250018424500e150340e13445000d948200090b00c4030032481c0b4100e640484d100d40b1500d1030103004504100005000050700410030030144500804 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 468475323 1250 468474073 468474079
    0x307080307080301051e0303130e09010b010912060225021008041205032a03060130090c09020708031005100804030f02030d06171c0e10031b02070302010e 68
    0x202007481d910000030344010b129140c4030300c52050a010078150107035841082140001d007101c0ea1010700d4260203004044612810045400090000d0349070321040c060f40c0040c01d01651030316200e031f007480c030000b4640100319400e840c03456013804408400504e140789030001407050f8000e8940110a0310400c850300c1c00f03c144034000c00031482c0034040020039440f504000721180f41409601d9aa91564040f820340701c0d42a2250450f4640107008002c04031180118094007082c0c1e40e548281440580c1d41000c101000f12000c5a2820344030031109a441941c842d42010344616054240140d460000400360780086100b078440510000c1413200c2c08803d01e1000c0c0003000152010302c043c0060210241010034018809418011640d400303200c00340c42801128640024408104102074480f200040749046517019420301d4441c0c403d0480050313401d0652180c0c00000d9035514201c0035030394418441e064600c492083c09058a4002080550b00864440e05c0c00c20340941c003c0420601e27500006100744800755850f80 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 468476573 1250 468475323 468475327
    0x1b0c0708061f030f0611070b04120216050607020f060309061e010506030703090c090608060415140c07110a090212010e060f01110a050d0f020705090c04061805060f0903070803 77
    0x808189802c00c9002200e8000e00d5840981015042c8003016203685040110200d60005014040210b80101e40e40903078000e0500e0f210045a6a00c01d80c1d44100ca88018605100740340010800ca2501c00000c0812038800340c00c10110324580008074140e81c105942021003074014804008203100400f0490342000c0014103511544c4d454540450268400a0a460f04050720740703a03040c06100d0308a0211008182810003088010742d501c0700c03a91146402d0390115050280d01e03203140b041c20200e000c1c079903607610703a09504c2060340c0342c100ca54119035000300c9046415414801c100030321951568844401082c01c2400035a85085c1440d8841400130160040c00c5c5800d205c0c02485401c0d01c402d904103940b103c00b82858034041040c40102450300703002d010300809500c40c02c0b900100060740300c002c01c04c00405640840341910f440b42c1c10091117001c1110207000c2c0410500007046150704ca80500784c06000c010705c03050925a20b07040400c020f0f41c0103640c60030b000840019101c6e401c0c20208200c000400304900614 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 468477823 1250 468476573 468476611
    0x2d0a050f0f1b06030a1d0705040e0d020d0c05070e2e081015031709011b03050706110d0606051b07030b04061d01052401170f1b0c070806 60
    0x1110682e030355107849001e01c90100024180350081d074010070140c2c4c0080d4280c05000c00361441607617541d14900899000d1030400c21010b041c43c0d130000341f60305844010b4004d400f20080718070f022501081181c01c16141c511400c980021400580600075001c1c00364180415030704c0142c40c0c0320b08100c0507d03088011b101c00d485203003000118000700b0081c44540d1207010215214002c0307600f6452495460300090701d00c80b482012403030f011140b54020420300000380c903000b0354150204017801d00341c0345840c0040c0124804120340000202c50317911001c90044000e001138240303400c18030864104e0b515a007102d004600f0000303101c42281810a80640c6014002c0001e14038541159260a031300c3c2c0700030f080189100c0d1a90620b012056040d0540c0c580d22040c0c0700208441d00d81200e0141c3d48240784461258148201080b0031140d51080200701842c107020040318141340c48851050707640302001040541303101c1490030300c0d1440c48110401000c20710072500041c0840e50804801c0307070415038041e01400076220141158 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 468479073 1250 468477823 468477853
    0x3010f0303080f090c10170a060f0b0304051507090816050307091e0216080307093002010e010207080d03020403060e061003200909010f0509030a022d0a050f0f 70
    0x500341060302641c00c2d121b01e2160040a480c001c4581c500280762010b018104a0070018a50000302101d0a0299105040782d0b58250b9801512058030090820703049644482c2e2a0a00b400d40d030b40d00000c0a203820a1100c7e0740d0010f09060101e6602e100d103401e90044000c201901d41001410040c00301c2c50010059518210001c070024200340c000303000856004200c0e0720651b00c2c2c0084051000b0b4220208a0392031500200c0104000e02a024070071340c4140840003541c1c259407060140c100e1540c076042e16004074403150015100c1c03048804442e0f046120b1144040f0700c81009110b450040d42c0b01d91005a143c034110f1070b00006880440b02c45118a07401407003080411004400c605080341e820241800403031440601c01000f0010f0500000c1c0c000300c2c84800d210f2a200151310000c0c01c0c6480c09410812501c440c802d0075202d11642c41144010b81c071060180c00d80c000c490000180c0d50301c0b070f180f0070740e020000d032041d2504200341c4131015030310b54002c00045115040117100486112800c0005041d01665000f12 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 468480323 1250 468479073 468479083
    0x106021c110d0e0d0b0c04080f0601120f05010b031e21030c030a0605220b0a0e01051309061506180501050708030c07020a0902090406060311041406070803010f0303080f09 75
    0x4802c1008903090220030162510385500100d1900050b145542d40f40101c1900c54a5019109600c1070344a0b41c2d010140101c00411034906980d8a5442654054825151080c14400c11032058803076540c0c031401001265810044d00740348080e021060951100c0d041403040c03d104c0c0300d210250f10700e0030300d07030003c00d0103d4260f04a03503000102d91b8100742c9a0715030b40e142500902d056081a03800102940346d409458642c1a8020051000d4040034091000c043d81440b610611502c69a0355402c0c0b548014007862034044641054660030000000d44401151150803c0d80c1035415000c10340e29643c0760034066168030200003072001c013005280501d0207142c10002003e2307101d01c80025152071404400b01e442d4646140c21070303405640040c03a0084079525690024025800120010720885c504800003400b107009024801000a580c501e0350306040c80d1802808062107494030301684564200b04d40800640c6800245010b0940c0c9050300d40081d09518004d0b180c3c460143c100040200b0802c100070701002c0001d0 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 468481573 1250 468480323 468480343
    0xe0103080c10180204060915090b012609010e060103080f181009140d2a03020d08030a0c140d11040b07140601120803070c0c0e0106021c11 61
    0x5455695001411000c6003000c451082e10401c4509114508070501450301020583c41d00840b82000707000d40d2503c2c07031030440d0a20717840c2c0c8543d203d004000f0003001c42182d1102c4410310040c1010050641c000c480003100324900e43d0008134004281c0c06100e080d4100340f09140c141d54100c0001c01d0b1a506580b208881800b44085160314a80c0000d00c40c101c2c0d908066601c0c1e2143c40c050200c0c80c800010001c0135250a0090142c0c84104c0d0b42601040201e01e0407031180c1040d10380260000c0c2c103000c2d038052607444200300c01c2010400084401800001611180c8002c04820b0007034420329124240050440c0540b030801c001c44040103046003403000f034040d00c1030071214003409600002801c0c0ea90034403102e010b40a241d0181c401c0d1007020401c1c0c014400001c2d5803000303205143c2c0540d035040ea22100300000141340780b180548880c030b0610010380300c60701139420007039094003c1855290700755890440705201c1c2d000360030850050304102181c150141c03003c00210040190350a0440300c10000040c0c4c695500c0b0408 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 468482823 1250 468481573 468481583
    0x150109210203030706020a0c1b05180a020417030a02070b040e0f040204060308031e0906090304060f0908100e0105070e10050d0902030a14070b0406021009110a140a0b040e0103 77
    0x82540e011981d0803c102c440499000d2819904c503c228000505207400408055900046480301c07150f402d21403020304000c2c0d4000030580c0040f00e803100a1955028401000e0006450b8200301c04070311602078050f48603010302d05100841d911036507035000034203100441d8810022082d040c030041c03101740300e40159507502042d18080f10b0101d948500000380a0b0400d6400034201c4d03d00002400141c2d84100c201c810800c1007002075000ca62282c010191b034400045404048035003051109100482c442c40104110380818a842103040d40c03103410040c00d00d10701c44c007019003150752101402110348080c090250700c020541042d203c044000004907000ba90240302c00002c01c4000509031700380d0005a80620342860f009422155410110f00c0e090303401118a469200e0a44220300c80080d8241c881811901600d9280d800340503045000310544020344004802201c511320850f030110019126404c0e04001410441804404410040e05000c16400c040e00312102c40d2000b0442440b10030741041403181102d6101b = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 468484073 1250 468482823 468482879
    0x6060804020d051501090b15070209070f180603021c2c190b1008030705071a160c0f050109050102030415031d0a12030c0c021002030c1203150109 64
    0xd032070500e090640b810380c0c41c04e2500c0194004100c5149642c01040c5141c02610200601841140b1024527401185d000030340c040492000150494450008002540303950305100c11012910302d00c0b0101e2080039002080001d6005c43c80b0685d14150b007801400c82d0348199410041c100000086034503031003004611240b40e4400e159081402c1c41c0810201d18030040045410310110280d161002c02c80070f040c5c414681085001c440490001e00120486000a900034000e1140e41d1608044000d14a01410a14500c040612400000c5c809244404020620a1018490340c0d0f050160700c1c80013810a82203d4104a0000c00c2800980d8000045078283d42180040400088a030341c6d040340500710444480100085010030048010310004030100380c1d030704c148070f80c52100d45001d20840443d808007602c00b0006042c800c69601605007010124040300312071040d00d01d05004402d030289805036000320740c00400000400c004400d0602e018024000c1c40c2480c00045032460a21040203112140451039068010 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 468485323 1250 468484073 468484099
    0xa080c010c140109050a050c0105030106090905190c0809120918100f0e040605010e10032009094e1612080a0b1f09030f0f150606080402 60
    0xc0c46582c0248030840000038441070400c0d281c29902d03400e02c020304454510400041180365809041941d05884565a6403034106d860040c614024010140913101d88400c0f035a50071120340c24902404242c0161500d85800e141008100d06d4607040b0106012107450030709100d02c1d80c09a44041924101004a08940020341c5414903034081c5460598006091604c000600041440c0c2401d40588202c2c044c0c21704200701c0c0c0e61603600c608040b200312480d40c2ca041442d1024400112801ca00e11070f00441900300c0080c0003245004604190000c0c0d640c40156032040180000784010742c0c424410300c888510050558110020a16440f024458102040c06180e1400303203aa01441c1801e41e130801d040c10b2210084802c90b81031111295002504c498006203980c40050080907860240c41000d41c00a4072401b07a0282202c0c0300010000c102204038208480c100300003020a0403035a1030884640a04015003040201d46413240785000c43c1f13101c21013481d0070280104051500410405c2d8000d030151080084000 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 468486573 1250 468485323 468485333
    0x1031e0507050d061407050406050735030a0b011404050405092406100c05060403050a0306030212010c0e0102070e01060c14061302010e01020f0709090203210d05060a080c010c 77
    0x1a40703420160300300800e503d049040c400719030810982d119582c00c51012036245c0c1601250300c4c0c8154010140403035402c001d15000501d503c00c02803821030f0990030b011141114090031210386810116052441c42d0003006102100c003aa114600d60801c09090400142c0141e0a05001e207025078440c861203a50f03035400090703030420203001071050700000144074194001e01d50101250307a80c06035441c0b402900b110081c408a0760140b424a044c242e081401824075a9036660304a8040d40a82e403603008158440c800040181c03100842542c601c080c0030004180100c00b00f100624100c0001d4110341103611520040110600100e8064155401d5142c0701c40c0142160801040708011617009100d903104001c20402c4140d5002c40c034920f5280300341c1e52041c90103045401207a880f0903250100481c0c1d041034002304107200c226840b0320203091019050300d4031800911010f40020006001c200004100094881c80100b00c91140503030062003210007078066030414010715a125807950303000c0e050060500210050107 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 468487823 1250 468486573 468486583
    0xc07110f01110f0a030215060121060807030503180616031b200306010605030106020d0804140303010b07150903080406020d090c120212370b07080603100501031e05 72
    0x81c600b4210740c0100c0600080c02d541e90203004041c0d00600400e0240f03c03003082070394002030080d4016551510040f1600400108060585081c5020540d03034000c000340001c0b084c45802e00441c05807000d0350312810800d000e42e080100d08241a4401c8000308400c5540048098012840c02d42620381a18241c030150365003070440b10224000b5000344920220f80050382000c5040d08c50b5002c0680a55035166622102911640028003c050142c0c100290742480f0034400c00d00d9a40c8140600b03000070300c0e1868021103a041d80d20070380040c031000c8030001b040401c1c031040680302c031310702d03c154642040003154a4800410591003d00009c080d10380003d00c0350785224041c0c001c6203641750807906005010303a503068aa110078004038001c900130b2000d01c440c00030381c80c80454451107242c43d403107d41600c0804081030f015400103040742804c42503a00403880d0040303600310041510449041d151070411f81000b00805203010304403500e00300c030b950800c40140300055088040b4465600032807115161003d261130040e00302 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 468489073 1250 468487823 468487847
    0x70b03070207290d0615020c10030e070906090518030403021e2106011a030f0414030c1518030309070302041a3604080720120a0b0c07110f01 62
    0x520f0100710400401102e070721000480301c0c009060b0303120496aa100381e880c0c08034180805e6009030500c017084030304c90294212600c03040d0310000b83e8002030f441ba4403000840b00507800c0100c0310340da504100181844111142101d100c0108004c609052955000500300c01ca94400c82100a000e040041c00c00d441d1090389403800c4c141c403005251349040c3d00102030740d1004244a611071000f90b41030b084483c51951000c40c3c0c01100000e00044030380c0d07250b03110090700007002c0c40304c40e03041c0c0700410814030200c40500805680710103403007440300030342030113981c4801c082040d1402403da43c101300140001d030140018000c04403507058401141620303107161030404101d0715800d038a40150074024032820328110315aa99a1800d890007010707190070b0002443c12062902100d008004503010003940011440c507000d030ba050030501a10f6520000041c80200f10801001d180c251481d50112140c0300130040c40f5641640c2c420b1240484a08008994480508180d03000030054040c1d00844140701007a4852080203800c = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 468490323 1250 468489073 468489149
    0x3020c0108090d1407080a0815040908070605090312040c05090c04060203030a0f150905010306060b0307020d030e280314090d030e0f04021c0c050406051213051608070b03070207 78
    0x7207807c03010014003002d4080720051180b00c1000d40070300d4940340ca4820300a9954020350064240542c59490300000d044c0642094805d01c800d02a40c0019265038000368400d91143d00040450b9181005200350703890042d0054206400c140320500c0929400019207501c1005040c0c046051346560860034014404900c0e4100008650754000c070b107045a6800180c101c0744608820055660384910070201408151041c1c40140c10031109103441d0b51080c1c019203100301d4103a003928140b60368208002c500e2402e800d4548130300500d030714400c400e140c2c00c220380301c603e8110184405d28003403914000034603111007540001c003403080341190f180582e164004a82075140c0007038401c658038102550031501c0900100c0c4211501400c0a80440d04c151017082034908440711a202c031405c1241812404202e010020041100a13820091000c08103200300040404586203182d12010325042204082c02c0010320b070000d0041000400030702038016800107241c01256030101c410380860140c0c4011121060300c003001058 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 468491573 1250 468490323 468490327
    0x2011805061b070f1d10090f0e19120c050a06020a0e0a090606090b0d020c0604030e0a0e0c030f180d0e1c020f04021813060303020c0108090d140708 65
    0x4850010072504025a0303040003c40348865590181c61010900380c5c0103007041d440b07030020303625884c18091086070f40022004080444168542039200200c03148080c00703010245d101c03aa508503140041c0b001c04d9240c41c0301c64450b000340d4016160808070b41015103180c820071104405100502105100d80d80549521060039591002e40780802041905441030a92244501600014040146115100890b90b5584505641510780207400141350412601c541145400301b088005501c0d0a00040c0e2095120b526404003250f171207014000508599003000c2604051b000c14000f06072081002d9030b41c405204080032505a450f81521a1b51450380240c0106d03a01c80c090a5145440d00000c0c118944441652689600c040c0a03401c0c41c80c16100b00c0300a900021201c00a500f1400c081e0000c001480400101c05451001d40c00030440c00040341c0304889850340e80345414800c165040c80700d80c41e090001d180c4983d1509010600da501c480118400320140a0701800000c41c2ea40d00405a41e44030f50401030403a = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 468492823 1250 468491573 468491587
    0x90118030c05010206090d120b062b0b1c11011b05030405041b0806100e0a060e03070b0a0815030703020a08011e11040e040f0b040f060b0d030c0201180506 68
    0x594001d200e000340b50242c015040040c8040c01c000807000500b1001e6540c681d1481c80e4000c20b100284000880aa084482000303c3c03150000d00d0144000e5010200720b100a01d84126540e4502300d0302c0005440e44540782c1c0c4d041102081410b6210440c215810206070f80901c40c1042c0180c41e0720b40c2c40c022000349955296071040a104012014004a800c16030382441003c62013540803410038940c0004401140a2601103003082c2490354000010120318103009081d101c100001501c068043e40c030100000d400103280c00d465003420320402000b070000b0402c0e00d00704046c00c0009003035031324000c2c1407001d5503450191600c103542c0d04000000040d50045c1c010f81c04076844005072030203402c0d0b180c0c100485000104600c081351085203c1c0041207034042a505081078205120700200540261054603441c034250990408a17200c3c1c01c00c54080c610030ba021000071340d407900d010b000707440642029a104071402448000401d421410036101a50b0904e0800003921100845030503c00c00d030b0b0005078004101007051 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 468494073 1250 468492823 468492833
    0x909060a1421190302010b0102072706030b0c0c010e0c0319060f0603060f0b100504231c0c0f0308070204090203010e0f1b060903071a190203121806010b09011803 71
    0x40300040e8002c1d4001d002c681d040d10700680e600c0360144560410482f1038400c1000200c1d80320040e295102c80d02201040c89580c1e0785558a10603c107480055002500081d0002c00032424881c0c1c041e00d034101005030140c40d8403440020b850f40a0302c4840d10305004c280401000300f2500f540001c0381d540040c03401700102038680c14058018242c264040568a2a01113196968034080c2000d40c1c04c1e100d0303580c515140509254800520076101c1403c1c40054100040c1c40620b80c0d03400046c0c1d0903046c1115004902403481c1d06100090800030f501210506001d50303c14001300f11f503d4100c441883c0c0680c0c0104900e096440800c1c0149180e070111a16402111282d10852901040455924204401c0c4c0d6604480034002c00042d48101411958182d015040400070461007100488610b4426a0f91905212016210411000751545224016040001c010070001311450390203401070540705040451817100c1148076603882042c019885c08101c089501e001c5a0310030101251401c004513404018560303207140c0 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 468495323 1250 468494073 468494113
    0xb0601052d04061b0209060111101406040510060c0303020f04030b1e01170303041b05030d02070e01210b19090c05031018030e0a0504050c0909060a1421 67
    0x40c40c400a40320b80e951540c8281c804c01c0c407140c1640c005144001c9030302c849006440d69030005810321440d000d0480c100081d010140300b03100b40520140504d000a02d03001d0100710894000401d5061402120501800070760743c04810440d11591505005a07202900d0405603105d002e87d03880103060f50070b203108128803404080c01e4501c0b05038402c0700b00031180e62a001c0c88002d60301080713100391090b8001c1c00001c0c00300c0c41c42c0d00280007100c18412075070000c0382c483c404241041c03140c0826002607030000c0f03400c2080021140b002401880f8594a609250110b01600100610000d00c041c047c04030080100e8600441001d0341c13100007568138000c1180d60194607154040d0b100034403a07103120380501d0b0010801c54841d03000e400d003081c28907016220510b0fa15078064600328040040b10f60800b03850701c8040344a8a0f0344c443c140c018161200b0142e100c44581c002c008400400600c082d000f0a540c07a420015075041c43e0040000e00c1c401c44041150358034a80059071109408110061507115031a40041060301080d0 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 468496573 1250 468495323 468495329
    0x6050a02070503010e12130b16030908150a090c05060406030606110303061f02071a0c190510020904020706090f0c0b040f050103090204020702120d0215040b0601052d04 74
    0x2941c052542d254101400c03600c2442450740150001588181d88000e034038000c02e40079201c041480001c9481e070255404c95000b40d10072070780ea903501018090915412480f5013005004040c01807032440f444580039451480f005e44102c08039500c8880101c1001a08e1109901804c00030b411561526031300c00c0020060601c51181c1d03c086211502c1d00ca2441e04003100b12071003802e000c0c04041a40c009031404800c10303040c0c0c2e1110002c6005121001c15500000d8a841c40911061b800d0b80b5166015411018281144802c4040c02c240d070120792000002c1d4041840030240020340701c0143c03505000b4001c20060b20a480c1c00070869840d2000320000c0204900e04e41e1315240c02103090164054941c449510944540e000740c0111661940d810070556100c5d1300301c229a20301c09003015050070155408a042e080c2940b0754010f4580254110351041355041000d0450360007000604440c030b04140c1c54007070381f004000e024503040020015104814171000c03002038620008450880150704c00002039002036801c140 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 468497823 1250 468496573 468496577
    0x5150906070f0203090604050d0825060608010b21010b0d0f0c060518060a1412040b0705160f03200114162f0109060207020f0301020c0a03050c03120106050a 69
    0x10250200b06071001050b10701500c805400203190609110802c00380d0094640c088810100402c96212a0380b00c2803851140c0b444041c602808864851500d2030030340789903401802241c1e25042c1c52080303680e90207814100e5040045e80190802007402c6500d405482415509a01724044101030010098880050260b403800741c0c114149850b280d0008071424460361490b404a5408510503546d10324111008003807054a41c10b0414040754088458240c40c1c00000f1918400910b410400c014803401154095100d44680f03001450b250310031107900c104104400c8007801c500d42500f20201014000c103a012207180343c004111002d0980044664040c0c004200f00240d00d04415000c18001c1400d198800101e1030350307031945207503440109800411144007140d9440c2d010310340c0e0449150f1200c20311824007420f011301c6001d40e40d41d038603006020312082600b007142d001760f01c10002441025404920440803980c54607040c0c0c0d88041c250340c201c0c1b41d03024507046043d070b102c40c0c4070001503402e8202e4000c1c807500c1c00b01c0e = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 468499073 1250 468497823 468497837
    0x60e0f1f150e0103030f1707030c120b150306060d051807080a0209070807090915030302160312050a031113140103051b0901050d020301081f05010506070f0515090607 73
    0x801042071501c006071148000c460030440c010300c0084c2c041e134000c2c00b81000d1885c1a11505e4680c00807800d2500d010380d407500220340d88142a103641c5900140c440ba501d54040800e01c1075807440b01c0031030040701c55100c1e241c14400000c004201c4a5a03000202c039a850244003041c000c83c2000031014060750032161800a0a101c1c01d0306c001002a004a40e156403a40c00600c12107065481403410744038080c000f80f42c18104841c0305008101005c140c410700c2d100e0104940d104c0c26850462a000e0b00c1c08160380064000011480c00810000c0e9801d80c1c0716041d80403915015441d5060074100368050700400c803261501c084089090780001c202c002e003e404a400d81500c9100c0c3d035440c84015003c0380e2081da00c4410003030302d1840d2402c03200e41c1c0c0300007050414011301d041840c00500503680d10883c0c00a03044400142c01030341d08110500c0100030350700140d003000c910822a951500002924620550340000c001401203203600051250500610b41c403002400344c540780350700c3c1000400c0c0e2985802c650361000725030f034 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 468500323 1250 468499073 468499091
    0x3060503013206060304020906010c020a09060906092c0a08180f0612180c0a030803060a05031c03090204021b0c10050703170c250c05040207030804060e0f1f 69
    0x1c4101c1450003007102404003032440c0c6480d000d12a005d8001809c180c14803031415038450060b2114003010340108911080020020b040c00d0756081070301c441e58449244581400d260381c9419000400c01103031903c1600c0b040000941c0002c80c47e0400c00c403c02e01070403400c00403c41c484a03420103c03203456600c030120340ca800c0e140180b104002c0c4a005070000200c200da1200000753b0a66031030102c031100c6014087c200d03410200030600142d02101c0320380044070b142c80f0100a10885003030086600000e820b08401400422004141030021881300e5403100c0101920b42050350295112030b0b0440d06244c1c2121040e19092104c214903d41e034516000c81540586000b004400d0b1086c0700c1c0054414407503141d9584240d250f040b1060301030f03604029003045858001005268100700b15442e48801b615034014a0f02c40c0c80240d0704255107444903d0740140d00440c0108070307410019a000c13210552141d48403500085913440120003501e0480da54002d0a0640300305084140c602d0740028050b010550040e00611502103 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 468501573 1250 468500323 468500411
    0xa03060905010e180f0a060e060105010f1e200c01020705040209130504060b060703110601150e011b0501110912120304030f0c0b1006170601050313030306050301 71
    0x50034482c90764103c10741c00202d03d10038502d9000c00c8440310318404498411900b42038050130045041c3e4229031143d07880040180d103100c10300070140180424281043d4030030100e00701805480800480074401d031400d1015105660141d4990340007078400d0f440c00352150850324101a40d41440b03543c198054419450300084526041c000c07038003040c002404c0e0050200701d007106140604bc0280c41110400e1305d42000030040c2c1c450034080c0034081d000743e45280303082c0b01584c111414581c068022011094a00a0484029801900d1094081003e180c003c1d440c12000e003002801301c00c00c1500030700b2075007898050308000e65840c002d0412070808482032448000650700c1107a9558098200120800060000601003030040e54400c9200e10b050806040c2c1541d00c2d554a074034920122100c046188026000b031144981c406a10707070b02c40022030484c5e80141401c0d80041e01a000c02040718480c000300e42c026a042620a4001c40018103006c0d009108200340700420310b00c82c5000400c08040c8001480e01410403038 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 468502823 1250 468501573 468501581
    0x3110613110d080405040c0504051332040201080405160e1819020607080f0703020109060b061e090a08101a010c1e29041b05010905101106040302030a030609 69
    0x3950040743d091501c0c0c501414070002d440322070004001d0101c14000001d1b541c4520b071041800d04819140003480c4004030f40c0c0c4a0081d8800c0d40c11002c03640400340700e0003400080007200c503085a02401c0070b103529070756460f006140034045200c009840c0d074a00d40003d9540b028074070940c000d14940610040714807080c2031199540160644e0f6140c41c20450441102509200300145401401150490b2520680442c2c1d02c1d0594031030881100107039510141c41003404091700c50f089031390f803040360014a011680b40e0180b984003400c5400a2400800140240490341c5545414004010110130b580070701d007040d40f07090002c11301592000c00ba90140d1000042c42e61103443c0700100e255221004c1c0031310350081070004444040c00d0404881d45170a15189201d0120070201448102001d601c0185251900d89400800701c0b00c040204007461443c000305100c1e683c2c110740c41c0303829500261041d10741c0ba2260a0125600d8040510101c0103008103000d00081c5030703001c00105800042610140720362076407260180308407 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 468504073 1250 468502823 468502849
    0xd080d1407020334081809151305150d0f0b070203040e01090203040c030206120403090504150308071e0c0e070906350703060e060a1d040311061311 65
    0x3400040c4d05203039800341d500c00c5020700800040800d0070030249940d038207a81070344407840f20210200c01c0351800846290180d00c0306d44c80100505410005002280401d5106042d40e1410182541300c00000703100ca029102c1c010070081d4003c0c031420000780d140c1449a80140c403400181d41900550300020351090000084400f101d80340441c00b02d86070b1822007204000d400c060f00031140f16070035640000c090390350304000e0039a40c14440305034003443c2824036003e0038100180c0d010a0080742000c0d80c03034030060740300c61440048a4128048558034151450000040f6a00d00700ba9114012250503c1061003822880002901c00240b10758605865420045e12400301c00e204000001c1c0803d04403840d0b0030b4101600041c012000800c501c246c80d104000110034043c100d0325600000d548420420084414411f01d07600a20195180c10509003011040702820001407024106003624001040405104107d903032a403440c428255200c074141102c0004620383d14103401c2e6065110f00c42c583c110303450010909070315 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 468505323 1250 468504073 468504097
    0x90309090702031303140d020c01050306060d060302040c020c090a0905060c16060c05180603010b03010608040f0f0b07032a110c0a03060605040507020a03090308090d080d14070203 79
    0x181820182004003049004052034218003007030003c050038858410b4000d01541c4182c40345030285550540d03451400b0900100c0c041154480861030160340d03040380c00c0301c0e0069000e98040b6947d603803440441000d040701d0350000b500140303020b049042c0c440d400700d100504000c013247e502520ba00c030030314150265440c40001610b545c1141d0085045100304400401d48000d50f01402c0c0c07016149905d803481250721803d12440412000114048040380303100d5000b4000070121681c9041d5410202d00e07078802d000500a000c144100f00000c903040c44070081403d84072550040084000c040e880c940341100303001c191007403004282030105e03500003120744684265542104002e044070480d800c00c0c0441d20205168012140d41c080c240e6400038548840c0f0b80d110186000b091f0100d8907514140901c402c03108005c042d0000c6410513141c40000950010502046036000311145480d42c0c90080041c2d004031560500526161002500d1500c0d08071541146c2c10790400c3c00b00c82006681d07041c106030b0b142d11605181041d = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 468506573 1250 468505323 468505327
    0x3072312180d0f0e04090302012004211b0605090a090507121d01141b090102070603240306050f0105100f03020c012315010f0905220f0e0709050903 65
    0xa261150020b4490603200c4e1600e10f40aa0302000401c00301c0310061000da00517515000b00030a1684004056044503182e00c0f40301e03281515214480c050440180a90600181001e00d50401d000c00c44541e5141942851003c0c04110390362000034043d68041900e1500a458000002805503500d00c510340c41404c1648803101041290710984d002030515aa031110900c62008030032a0b0000c09211761060031280c1c5040710174600700b242e80c209081e80c580360106980b0204215540007641d003c16104111030403805c010840d0900844501d140f41c00c80c05400100c900d00c00000402c1c0607054001c58062141116804400d90300c4009002c03618041e00e518401054003d203850910038840d42c02845000056400051003585404103554803451500140c0301d540c14100c18002c0030001c01e540c004040c0c1e402d080007044146503100140501c1c100d40710f414403450340e4040c4140701c1c02e100c50030242500c5680004004d040000c072001c100800e14130110315024031900001181c403a2691065030300603424000158 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 468507823 1250 468506573 468506593
    0x24010602011a0f1306150e04022a0f030f1801020703080901110a06020403110a0806161119060606030b010e06030a090302070803030703050402100203031009020307231218 75
    0x2002c00701091075030046602440c00a03840105d01c114405041c01c100b01000314905840000d24030311644000c1c0e0311070740c4100608070405030100d2000f420420441030791483c0c02c411a03642030070202c0042c64500180400586100c80c000c1e880300804420300700103d40700a200000d001207030350780b440e808002c080410070002c1168960080302d0740c0e046e02a0107801c543c2d04824954808080e600b169004942d0058000c49540b41403521034082c0004d0003d81c4000c0040d49821055800f400c83c80c2e03c414424002d140442d240c1c800018004109481640340c45e80c02e81554030b2804030000c084610400380020b14241c880040c561003120350182601c0010221421a10340d048000010070f11a84201c00750b116413880090144001c0c400340d4030980031030f1000185480d050040c050050540000f010854000300f040101040c0d00015107425508070140041c1c499690b86405e407503085035540c8a588a2070f5590304d03030007903100c0480204500050011002c010383c6510071501c0d40c44404007000c440c04e4000e61403407 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 468509073 1250 468507823 468507829
    0x4110c03131d0f01090e120f04142706010329030609010b01090b0903070806040303051509040203100b0f220e0303060a060302030703061a030f0906070c02040b0303040824010602011a 80
    0x621b00d050004050328003403140004414107035802039101c6040389001160400c0034851032002814118415203501c00502141c8030b4030012810000d0340c160301401c01c1801700756540d20036400840114200c02214140f5604a4001000044c50018140c0301f8811240085d04000040c0039a024443c03040e19900c0005003041940727111a00007003180d5403d44142d420000354407201308116806030740070b41c90010305030a00044c6202c0c10f80d00301d80381c1c60003044018284001078a00159254100c001c03a0400278610b1441c0f0006070013002032004d017550081303090000d40007425803150f8203400030280e42000c11100041c502d51030344a01040396a2584102442010440e003030080d0003d5501c01d04500d000510151107a03840880000041c1d0500d260710300100801860298180c4080d4002a815005000500c3e28100040444400e118000e004d140c0314001000c0c20703101003060340c02401c14401075a42c02101c885901070948041442a01c0c030307600000000803c9401803080e0116418080302014032004a6814 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 468510323 1250 468509073 468509081
    0x2070b030405010f0612060e0303040c050616020a0612050f010303090302130e030a03090506330102070503061503120c030a111015060f03140604110c03131d0f0109 72
    0x1040d034295407610040404d29459200350780180c031000300d01080c8620750f820018112820b01d890b6036001c0d03100f0024030002c50304114001d41114401c459a035520000b4825548403e403120ba802900601c030b411020402c0b68110880004040d40c9001c10807250b5100808200300c1c0c4000c0c44041d0205105440500150501845c118107040603840c1c0070610506403440b0710303d59440f45180100096844010714100720302440b20316040324290703a80e204a100a550400640890741c00c40984e1030034030100010169009004240040600406440e92850b044600e28100700f11003076030f64482c0c020b21030342203015211402600c0c5074450010055040c0303084410152400710580c8001d0101e40701c0c4040c02745540c2e610b1301800b0310342000c601300301c203401e45441340203052a091182c81034240342c00c002d51048800b8441d0440c40e40114203e401040300329a8840c408043e1181070507090607030100040b0071080e040d110700c0603821280e07452998510f01441070101d01d048d007429100d20b4030785464000100300410303071900 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 468511573 1250 468510323 468510331
    0x907050702060c0703050c1002011406041d1204143f032b02090303121302090405010c020705120a0320030c06090717060c030c070f1a0a0c02070b03 65
    0x2c81d41e4a4008000c041d2440c05909a000f2942d551203244800c0c9281050350070303402e075081c1c41e0000384050070841d0130050b40003200801c43d500855441c2076078030480b90f2104502040c44c03048020b440451401c600011556405801b03000c1c8000124488180d003030a201d107450014080240401500004000781800002c00342404e440d02c4510981c0c202214241c180000c103044038000d54600703024031081000e401034a100c0e480a405092061000c8078607a01c0c0402201e60200781498035410f6940c035040c140755166519138000e90006024010030040000c15489078008096640880d964650b8940420408511556250103250032030741d13802001a00402000440c00760101d0550b10011031350074198515040312003040d135158032010901c84030740000c2c8010000360191203903170070290510440702c55039280c0140916681c404c001001a962403840030903500441d910507070960a2444a00f0003030f0007600310130610481c2124501c0402c400340c0b0144220a1075003020703000b5080b2985410800310035078000074 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 468512823 1250 468511573 468511579
    0xd0c0213020d0618140919061d0a08120a0501050a170708030a020309010809060f01030305030a09020406030b06040c08040519021203070b0103211202030405150c1b010207020907050702 81
    0x40f0105080c80072490801000c00d2410000800300c2d40e201d100880c00700d0107060700c80b00d07400007500840c4882c00e003050310400ca5080440070a100522100d01c4071012102900d020a03405051211400c200c5c10000403c00c041020f590300040d031f180d83d21110112007080c4a0a988003103250810007440902110080c080380d6401e040d81d184a50b40c035038075411176000003d0600141c2001440121542e0060210f0350800d40020007010280740c18520b00302200340600015090180210002c0c10f0050a078001001c065030192080c810555a460500080b02058620310f00c0340d81442c00324150305120381c5d100761080350081c0c002c040040e000c2160040100c0366840690b0403841d500c04034681000104002c0c4200c07840341d11080c07030035851802c1100450381d40300c0c3e000550044040e44c0d4031080340c1c8003030380042d01041c0d4800107036a40c071a8035102c1d01c0c00d036450310410220081c070030030040030544071800f5050301080349080e920001c4103020034070f08074414034600035804801c04000c03c0c0650712520103050740501c09 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 468514073 1250 468512823 468512831
    0x50403120e100806120106030f02042c060a0605091302040b011b081b1c030b0a0302030a20041e09031701080304050f040203073c0806030d0c0213020d 66
    0xa400310b40c0d58000c94034641e0201d0b00c60b00c1400300c81c0c10440b0b005030b0240701d0900208500d50850340d070000c0070003990030068816078696210344008007070300070000401d161502c8082e603200700026209842d008115442001140b50100000781402c1c06540580f28581003030080241e03000c181c1c20840200a540b01c40341c10070210509440071100302800449106018014458071880c20322103081c0c484030468508000342d004080c2d40100c6040340f08110310a4095030402040c1c099810002c107a03540900d500c040d40c540b003420212030074424074954141c0c008007800161200c10f1565406c0c4019120140603604110b05220039505101900c0e9000740707800d41c40781c5011000e4240541052000810a0708000f0300e45c1c00c0001c0810043c41d020351081e00c0102c066030150309500e40440c020385000701e03651503020070915940b581211108989148001d00207a0304c007181081c00c0f4030000900805040310168000c0c89442c001c815068020300c08607407480d074014004030044211031681d5012350004001d4211403511 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 468515323 1250 468514073 468514097
    0x5030d0e07080601060509090a0b13230c030112060f0b03033c0702040c031413020a080a050606010507050307020a0b07020906101d010905030f150c0a05040312 70
    0x2450181510241100d0010700105007000d654600b0048103038000802d00400304040307411034031901001680020406000204100100041660703440a01400c204903441c001c003002043d6541815441140d9402c3c0c1901520303940c4000740045c6210a008103200880d4820034038002031000e41002c810241d0703051010409000441c042072841c1c01031111103008008c0006100911501d40140a801c8015240c0040c2c0c860824400e802d0b55201d03001000e8080c41e00c4c0d02d4002000c80c0071b03400484078031101030107a9400749800d42002400d500c040c20101d10581c0c80d1480011029000200d06200c1c0d07400c44003030001e6443d0580103650552248908450500044c08a1005680c0e851601801040068a400d42d100c00c00d104001803841c00429040c4103c558060000360790784e002d07544940540ca10400901c04030000740040e2104946940210703458854100c00103d0720700080303008100101d0032003000c0e41a0b05d50f804212664004ca07403040c000104180001c001003440e0002c0c4050500070342c1040780302284 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 468516573 1250 468515323 468515347
    0x1b0a08070308070212070305091216090c020f010b031c090b0c060f180606010f031d100e0f060c07020103060312030b1507020d081321110f060d090503 66
    0xc0010150081400c040c20442541d40610850742111440301e0040d00d008590f46c1d020b405030140740038140c00760a000341043c2064504120b28485140c068500740d0344250782d060840003400c0210400700042c017404c040d0907032074601400380381040c00c4000e0181000c1002c031501c0c00d00382c07a0181500310811285100028112465400903c00c01101d4006010706150007071841d610110041c03e908018460b1810b0352420a6000c202650401e000746020f00314203c1d8030804901038807400040c09090164100742451000000030640c4050700804410300844400c4e042c02901e50712240300700749081d008600000d0212040d04001c08125205042c000b41c05030300c035252112406c2034a02403002280c0d969114400318a025000c503001c40401c0b10301c55103440500d9011411413030040340c0003440108081601840b2034030656061b0040d120203c60741507225090300364074103685103514040d10140344482c0c051155041801c1c0d44085000e01a013190316003840e241188000700001c01040d641c90000748928125a0 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 468517823 1250 468516573 468516577
    0x120c02031b07030c060f0f0818160f060305010503070e0402031c030c140406020d050904020d09030f0e06040b070809030703052d0303220c0317040312020d051b0a08 72
    0x101c500e100a000c07aa065180a800000013504030006100c40030700e944481a0f404282003005032a140ba0005054a42e840000c1c501d00c0694021440c40c003c00f030f4000040011043c1c14000c640014211400240c0e03154000c0e4215882800b4944d09030b00072900a0201c800c450404c90b42062014003190162400c100860001061291100c030010b0b80702e030f91440081d5404100e54a2a08900002502d4a482c100380a950399049402041c24404041601400b41d91744d581916407a000811050000c1002c070710f002814100c59041800101d02100c0202e001804c2c61030a48041d00e0009079414540b10ba640c0364442160000081e690b45881000c42c040f002420502651120a01082454941070401d400018a0a0503510100e401e0f80c81401002041a04140e044c0701d01c490000301c0c01e503240450305001c5c1030031041c0c0c1c002178402d01d540d03070881440c80e80b60780051040740e0181050b49c21900e0200c2c400ca80306c0c44000c3c107240024009000c0091003214540400349100141f10450354601c0643e510b41c051a = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 468519073 1250 468517823 468517867
    0x30c15020315010f0503070c050c1206060a08030418020315031006050112090b15151303030905010804050606010e030a0f110a05030f0a031d0603090708010b010f120c0203 75
    0x580c0e0080140724071240d403011901d00d500760900700054800e10422004200b40401081f44041001004246081c00028031041090050203480f00448064030001307981c1e9003100f65100f5005480900000483c600044251019140b840042a140c46c0074140e00502a400242c02c902100d29603403030341c0f4a2590100550301800c5222200446c0d07143c5800d001600300011848404603541c20039600742c0000d61411449544190300d6004880b9005035400030440e0038008980a0017590000140e25541815221500c030899120f41c0e10142425114801103405240a580c0100a5409000031070842c1d0b00079070b040040080060100c645065441d00c03002110350303c0f02020396a00c6058070079002a4200180c90801414081d80200780380d10700a1022582c038460708102800f0002e00ca140480b01501c03030340d15500d00d140d0041040e0703281d003014116161030748a54411740d441c41d881e00c0c03032080c0311b9400340c804005081c0c2b42c2d4469001500403001480040d00000956400710300081100d8011580071150721a00 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 468520323 1250 468519073 468519113
    0x3050d020f1606090605060103110717070b010f05030d0c050c040e010e16031104060b16080706060303170f070c060e011404140607050f030c07110a06020102070b010909080412030c 79
    0x31302a0704044007150b001a1500d41010b050260f81c552500d0840200c1e8401c80c1d01801140d80207061014141c41801040c0380240170615590000408000f491030402c1642c104500b5100d20b4845408107481203042c14400070000d4101d40c0c2035000340e00e0302d075000d0500c0c0b000800c0040ba151204205250500d00d44030320490241d2080841407050040c03c0120386400401517801300b1540d402c043c15500140260401b1580c01c95601040e0300c01c100810055400c180c2c0d001070140416500ca190150120300c2c400e4800c0c1e00040c3e11400955a5041c000c0319a001d1052a160846070030819200c4070b018000b240345c1e5080790340d00c03642c03800c0702015404071181c4a2802449000400c8060303145107810140058604000c0010038450307050581104000c0f650231500c41d604c401e40e65415032030016240594a100c141d800100045c0c0041c4c46501900100000b511038004090560307203c550300b608403059604d006e001400c081c4814804035400c00314070364003280a8203118a21080700d60b56840360f04995010000 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 468521573 1250 468520323 468520331
    0x10e06010c0c26010b030a0803180a1109060f0a06050a1e0507050d0903020319110a0608101719170f0405010306050f01081b041206020702090f0403050d020f1606 71
    0x90310f0708a40745990000ca40f50790003800040040c5000aa41d8030600303c0280c007095001001c54890241315000d501040740580940300e01c800142807100e8900070325500940182c2850001031003a00c2c2c80c5444191218000b0410803401c1d0402e2012900c07070b00007000000601c140c95289505001c0c0c014100d5a40c181c990380d40590304c83d8a8907040d41088020f403280c4042c0203811405000583c0c01041c044550042c0d44181c141c60f0f1040c0c1060b000f01403038511060b410002541c000f00308640d205d50350070300c0740080d0641030605503980d047c1107503010031400060019800c20460040780d02d00c01544800841e0003001c11112440564900601c1c45d4021040e000c0c080c1c00005081101e0b582502980f0700500e011148440501028400039000440c0213086880080461101051b1541101e054030090500c5440c160880c08061070050020740c0584010b9110b0b600031400100e804515030000c41c403903945a40c1e650300744211060304101940083ca02c00480540a00039036035007042c4600c41c001840d00421001c1 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 468522823 1250 468521573 468521609
    0x1407050606011b0510020306040f0203070e012019030509091008100608030703140c0304140f030a120e1f030911040b01091a04050612010608130b010e06010c0c 70
    0x24142900f00d05200307a03c4800c20390000007046000c03031145e074055100c020150b0b0329990303040080c00034000d08071031100492012080c0401c0c540e0101d10003c00000c02c0e00c4d001002540781c290035203000e84412008090b176000445e100040e0700740c010303459059842030501c1428188148005058007004450701054510030301402c00c0007040802c03008403410400c080070000c2e1070400c00c6581e1a0710807800060184240d0010062640c40300c0300840d0500101002920380350f945810102104148644250703100c0c0400314442c4485240100b8109115907010341030305020f4545460659018589000465200c080807860000c4106d440c001e1110201d01560300140100040c607181d030050410004203402649021500c0d20340ba6003195542d001d841030002c00c418081750000a45105100e01e4024a8004101240e080d0076a11072001003070503100f0170348660846507184120519240202c0c003019144d07181c0400100100c0f0b03141241c0341d8000b1018900740005c90b0050700c45010036203080c0e000140c640340b54a002 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 468524073 1250 468522823 468522827
    0x1e0c0307050f12040f06180905090a050c0619080a18060903110a08031b1c0204080d0c0c0506031801090c090b120307061806090605010f24050a140705060601 69
    0x807043d0034043c407125041604041c403d201880b198000e170703820700c24000011254440c041c0048170090441c0380b000e00c802e14188181a0b1201d03810b210031141403080540c0518079203404c3c019a092038030b10307041441c45c0d8804030030200d54114001d0400c8030070503601c0c115000c1900d0040d00244810307010301408100c40105d443c0c0148401e00c40398450350342c4e800802c07002c0005a006000c03250024045c03a4000741e05403040000007040c0c032856049100c4480e01a200d501040320356000350003290303a8002500c012105403102900c10482c0001d0041400c42902d0061041340341800185401000405521100b07103402001c10b400c40702c100f282918819582d1a0410031a02c03280141d03080004c0503a0b092500c207075003607040b903901e0040010041007a40c0b0742584000c0e40e4012141080a540c000c07805102c942d100341048801440280036080701240ca0f444040341803080c0403884603100c030f003800e01c14003403e194000c11202a00014142000c1155415400c9130003007040c1e015256407800382000c3e01c44e0303041074000 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 468525179 1106 468524073 468524083
    0x140d0b040308180717060f0112150902030a06050108060a0209090c1e0d0213060c050d0f0203040f09050f01150c030309051603030314010503030f1e0c0307050f 70
    0x80c003c0c85c00d1140d510540d0040e0a980c1181c840c4409078208031400d0242e00e0030616034507015400074031102c061010421100f100064140016400242031440141c01a07620035210b900501044c0010b0040c41e800161800085181160305404103400394401000c482003000301140300e52041d200040307460302ca03a080e280d0003030303540f46942c551034004d4005450354004699001c2000c5200740c00750680e0a10250000000c017481043d1000440d004207844940c5030460209000c00207031080d01c0c0503e840580390340b00021450f481c000b4003456420320164071400c459924014800c10442d089001000c0e902d425207008036004101e41400717031070b01c1c114240400240c940b00c03c2c00428160715901500d452031600d1001130240e40d0350010190349004401984030462401c20040361044017015240c01d50a4104408034184050420314500399008200162880d800c25a5518464141440 = true := by decide +kernel

theorem cover : BRFrame.Cov 468345323 468525179 := by
  have h0 := BRFrame.cov_init 468345323
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468345323 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468345323 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468345323 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468345323 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468345323 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468345323 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468345323 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468345323 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468345323 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468345323 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468345323 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468345323 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468345323 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468345323 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468345323 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468345323 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468345323 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468345323 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468345323 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468345323 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468345323 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468345323 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468345323 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468345323 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468345323 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468345323 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468345323 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468345323 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468345323 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468345323 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468345323 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468345323 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468345323 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468345323 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468345323 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468345323 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468345323 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468345323 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468345323 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468345323 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468345323 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468345323 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468345323 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468345323 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468345323 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468345323 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468345323 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468345323 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468345323 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468345323 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468345323 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468345323 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468345323 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468345323 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468345323 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468345323 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468345323 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468345323 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468345323 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468345323 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468345323 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468345323 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468345323 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468345323 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468345323 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468345323 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468345323 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468345323 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468345323 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468345323 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468345323 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468345323 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468345323 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468345323 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468345323 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468345323 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468345323 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468345323 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468345323 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468345323 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468345323 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468345323 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468345323 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468345323 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468345323 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468345323 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468345323 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468345323 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468345323 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468345323 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468345323 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468345323 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468345323 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468345323 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468345323 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468345323 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468345323 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468345323 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468345323 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468345323 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468345323 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468345323 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468345323 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468345323 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468345323 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468345323 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468345323 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468345323 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468345323 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468345323 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468345323 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468345323 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468345323 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468345323 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468345323 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468345323 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468345323 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468345323 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468345323 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468345323 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468345323 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468345323 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468345323 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468345323 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468345323 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468345323 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468345323 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468345323 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468345323 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468345323 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468345323 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468345323 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468345323 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468345323 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468345323 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468345323 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468345323 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468345323 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468345323 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468345323 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468345323 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468345323 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468345323 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468345323 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 468345323 ≤ n) (h2 : n < 468525179) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
