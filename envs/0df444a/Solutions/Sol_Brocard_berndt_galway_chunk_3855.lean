-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3855
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T10:52:51.008345+00:00
-- url     : https://prove2.me/submissions/94c61964-e796-485a-b1e5-40dfe782c65e

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 693165467 ≤ n < 693345323 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 693166717 1250 693165467 693165469
    0x7150b040e2d070614160305070515010e0c090103090510050106090605030c0f1b1b0f0a030b340e0405010803130603020f0403060204140306070804051522060e010506 73
    0x1051207110b01102010b01080c0c0d05002041c0c840d40203010309034040810900010315515449009035202d5800380e299903444030042e02e811803408a17010f4074044070440c030f40e0040102c4c3e0071080b16140c202e0043d1100c5a1520030741401200140105440500309201faa80700d007401107011351005050b00c64035500e8000380f9448820031369080c4000d0340e10410910003000310300704241e0000068038250080c01600c040100409540b140341010207030130f013600d40c02413000280e020700c0c2c00b2070041c40c0d2180035220a004589103490744021ba1701e00900144c001d401d40c0390403c01c0c02d9a100550400b1b2802e0354402210358007041c0c00240340100e00c001c618095407801d8000b041e00c0b00000240c0d2800d051290305c104201c0d0910b041140030b0b40052100502019090101000041d80760010f80040c01026030038011240351201050302d0603101400d540244401c000c14480410000f00d0001140ca010076a4000d4907110520500b80f03994400d5901d20305610b140504000300300c0c81d5000f107458a01c1d403030000c0c859034031010 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 693167967 1250 693166717 693166783
    0x181c0c0b070c080d0c0201032003100906050d081903020c030c0a0605060405042001050d06180f11070b090c06040905150f21010612030906110106050607150b040e 71
    0x11341d100415080e5512400643c407c1d0050140013115440c00ca25012660107543c99582094a4550007480c55a00a10220b41f9a10440009000031131ba596109800c0303031603151551150741e900c8081144e0341e048854016000303804a0b412140040212652200044142070f103c4018000440d4213a09060209074189428040e86000d2074020007011041c80342a240c012207010014040d5040c040f091000c415000058803901c8002c102000714804050b1711490080100e6448007440c421440c5008648808005010107a0b104194006507a028507243d402086140c80c10040c1d01035840400020046207414040c1c0010380070b0b034141c82480c4803600160041080c8042030b00d181c160001c04d1400c0381d0114403542c02100d45407542410000075000d8940084180e401403403e0300380d01244900d24108280c9600c04e010a000120a1000308034550610000900600c00c240014001070b41d460722590040344254007a80c12280001c100300107072105983d442c0d840e002d83e4524a90b524100d0111012450401 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 693169217 1250 693167967 693167983
    0x20c07080703151a06030703090501060602210f091003020c01090602040603152d030507060f0801140a0323070905060a0e010302030c010305090a050d020a06050c181c0c0b070c08 78
    0x18421035030541300e40402d100881e08010711719030030507449800006c00300b1001c1c4a02e8026190b198003900e0f41601522184d41d04a6620241e4030a07100c0401c0341440007056001a920210b04c105d0348a226601614003c4001c0c0c002e40740201021752034218048100480c550081081b9609a01c040c005c2864071900603a1194546c0305503540304462082108008561003d20213040c0084656a02803c1e01c80c0c13200c44c40e001281c0c0280c008a5112103000414035040350485d401011904d4103100b0040c4040e02042c01203a9501c0000c0041044003c15403c0f4a50b5038034a0b4a2a04030b0012220020ba40d80c040802404080d174442d40902544400410b9100c11300c0e440a060b03d801034000c0000c050800011002410018000085070180501c000300060f01032208000d868160b50062003c88000d04200c012550003401c5280c880c40b08000c1d101500100c0b88030244441c900b03d030b0701542000307040320402c44080f20580c02400c10600d004080703051000b2001500d5404c0c001e0800700145506c0d5040207540390f1b06 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 693170467 1250 693169217 693169241
    0x24050903070311012106050906060301080703080304170c0709292107090203061912030c05033a060501090e0903040308072a060c15020c0708070315 65
    0x100e0010710129440452201c49003030181760050f00300c0142e500082c001510f17415041c2445450704010412071800035181e41d00303c07004441e1240f5651400b203406a0340d02076071100400f41c0b000840003900340210001c0415210031240d010599a214040000361154298000c6a500504d00b10940c4201102c45201211075103075002c006041024100422101a11400441c0c01d1907450b41c10034220b02c02c0c1400303164010300e4020341c0940c981c1002410000c1d52542d5500c401d1030050204000c000e02c0b401c0c07611200000b5094241900008503134100ba0b0700f90321030121f0381c00000d000901c9401781d00035001310b00c42c80300940d96540b140603842c0c240b00c00700703035800e81c8900d0340007a1545505001e41c200301c000c01c941140c603610031240350035a0b03540d5850315a0002142039603140118900c81c9160b8400480311741212946a441d04400390610740007422000312010050030b40120420f01701981841d035030444911500210803a010395940380c81c0c0035600c1aa03804201c03810006203550402089070341c0521900020 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 693171717 1250 693170467 693170473
    0x1312050324060904060f0e0105030c090a09030c0b01270203010807060f0302040e070905190302101b02061911190308270105180a0b01140a0306050124050903 69
    0x40000020100050030340502c0d44003004000ea00c1407607489105440080500010b1440280d1415a14194000b07050348528020f0304100b00085091341c1d26001683c0c0000002c01c001882c40a9041c215400800c9010040c0300144420000c1400c0c0c910f500070b0103441800d410740410a01c240903480f0700380e01080c031a4510701d5105a00512000340520310380d0120f0042450018100b907030b03807064210825000d0312041c0129889000500090524404040e41072103000f4422154529590100d06102544a40413080010311184850700c80c0d902101c08501a400424207034079143d05076010042030780206100740200c0c0780c2d60442c0300182404030740c165104072400f054160302c141c16203003900c0355000188604406d0311001c08450f007003280008000148516900000713540d241c00000c4415444004c850710169a00c03208000c000111041c081d03074156401000c0300540e03049924081a040c0f581500018402c904080c0049000480000b1200d00b141008104203101e002d0450207440700d21403070b014680c05030 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 693172967 1250 693171717 693171751
    0xe010e0d05070c0324050109050106120b030c0f0307051203090405070903030f0f091502070f12080426101a060708071106090303040806012c011503020702060313120503 74
    0x1170b400e203440e10b584224032048002581c5070200c41c1c10407070310260042100c1c0383d524001800b285600010048418070b5a060801440d100c010000303984080084c000b9101c0d8000c801c02905030b44040c002003005040140184000c00307441c40d0b409491350030002102d03011354034040008076240c0c4030701c2044040341e4140e15607070031110300c0101c12649155414003200500000800000c0c00010b0b1512000120440d9409030054034140040300070410b07011b60083c3d8001c0752407808100860703004ac04980403142200d581e80e00040d0701e410b450406408004001442d801001c0c00c202512410350010301d90114074007090b4100c040c1580401c03050740608400580008018401e240000d24410b5030140080d0b0020300240c242516800000c0c81d680c82900300c05016003001004201150031404d00a040392003040c402080100032030003000d1000814840c0c02c1c0006242c0200c165064000d42c12110900e40141900c0e0341d034506030210210305107035a00e088548540d040900300d016407040c000c0c1d9001e400070380c0c0c02040312 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 693174217 1250 693172967 693172973
    0x131a0a261e1f021c0b030106030c030305130609060e04020705160b13061d04020c010b03120a030e0a02010c031d0a0f080c1509040e19050106060809030910080a020d0e010e0d05070c03 80
    0x101784245500d0f0f00340d0350f03442011000c15640c26144000314401c0c1d4990b5070310104100702c40c100b5031a69000000f44218001c041c807040750068400c3c0281d41041d100146c48801a081561418440c2e40c1d91141e54495400040b2303064440d800101104001c2400804282d40d60300c07000c031400c07403003a1842150a00314031032036015481e06030010070f040c0c14603800100d154003040700002e04110120b542c1140003980040c0350303a0f805815004098a4881c802c000d44010038440c0c001034030003008400d000782080840c03555552000c480d10400c0c48003050160521014a0320f94100c440d99100b980120b25461051100d01c0340a480d00b25004601c4a1140034401c0c02c1000380c800740300190007050b01c5c206a902070b510161014052221510341e103a40148008200b06240c40d502801c6200d01808213040c80d00200046246074403081c0c50b0801442143c41d00c005140d6441c5580f4000340150640d11140340c0c1041e6008098a038150800038071421800c05807051010612000d0f5181c2c820303008010021100400c0030408 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 693175467 1250 693174217 693174221
    0xa140117010f0f0824040602070c0e0a0c020105010b030f090f071d091f0c030b130911032b030e3702030c0f04020702131a0a261e1f021c 60
    0x403030b206450160278800995640403c1c01c4903030704040d40e2041810200007542c200c1d400350000102407400200641d50400c550307084079100041681d90f00748001408206410801c004030445040e02d0340a070740e9403a44a594005e9010052005e241660100e170021421584002c248a0003d0300d82c00d14902e140c3d68049400300183c42e2100c080c006155680010070305584800254181c2000180d42c00140a40f043c070b40311a408d00314800090182c1d00c141103003410507940c6103643d54200c0b101148a0301e2003841c480224090145101042c15500498001c44c282c0d421181d034880c0d0380e10348007070781200341c030355403440e40c00d403c15480c60180d4903601051090040b41000d5000c20040403000d4405403400c0c4440d00131841402d00300f616114102da499646c03021501e280c8401c0482c950301201c103050381d10f1425000c1300128866980b4004015642c0024154002c010000b48141d868100030580712520100380080d240c0c0c048100100d02a4200601d600b43d41e0318520841e4001a808080b28071174122040207400 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 693176717 1250 693175467 693175471
    0x501020606010c2f030d020102040e04141f0207032a030507050a02090117010b190504051e15040501080309030a0b150315060f09060a140117010f0f0824 67
    0x61014604c1c03040c2c0c46016900a20340c0c070215404800d0030082c141e0405041c6400d0b807010000e411a40705210074007141c07a10602054000b60455088030120411303000460030300800c480800b0714080010070f6004d001c3c00e0b41d0003070f04207240a6200e404184601440c0000c0205421000c04012601c1c5205480041d004e000600009401001140d10201d0b195012421814003a0052144074902010000c21600b00740240158050b0590782c06c0c010588061654009030054041e403486140c440f030000301050ba400c0c415683c8040d08149000250516550016011141c1c8050b5800ba60a1400108102000000702c502c02800640100550b035240c0d100e40710703600c4024040c003281c00321a02105000e81d07001c1085030302c8c1e20000c0c0024221800e140003041001e1142c60340345030186102c1d40c20400c0300d669441c036020480d24421021402d90b141e503c01201c0080500b030304005000641e50012501c10b40546140d020741c0c00f00d981311440c1c0d41d04c0c2c0d05d00c41d0b9900c2c0e9210b2a606130700b02c241020407403001c850312459 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 693177967 1250 693176717 693176723
    0x240305190e0330090d0c02060a230a030b0901080703062403050d200705100e0301020d051b0f0301141c0b250e0402090d170306040f060501020606010c 66
    0xa030400c203c80030302141020761a8505041c0600c2e000e080404102045601a00103007400014102c251700c10f10b010b0105440b0640103449880080307083c010703107405500c00d54003100750180c0001c0300038010a20300100c0c4d00301100c5032000078036000032a6401d0826005180c181d49030040100181451a950a0084c0400303040058000314500c050760100703180150f540001c0c501c15800b401018402c008010003031041d0328524200d8208052000e61402404907001c410343c0e1055030803040015000c041030743c6034240c080343d06070558800504241c4004c02c6901c080e000707a207209180005540c02c1c240c804094040c0c0c409102c84100b00f08010001d0200e099031403408030b0409003180d0341d1000c018000c55074030503092500341c5500e4100c6040040d04406c500c0034001c42d85007404800b0b421042c10400408410020f0200380c062540000e041040c2d40e201c00310907000552040c01c42c1c009081c2096202440c2d0000c1c0c8025004504050754040708094a0180c0d0341903c0c01a8010000c95850070300464102d10b1480040d = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 693179217 1250 693177967 693177973
    0x20c0d0c0803030c0c1902100807050f1c0513080307180f0e0f010510020a0f081b07031401020306010f0804020103110a050a0e090402030304121704240305190e 70
    0x21a103074144040d6202d503109041094881040807a1036040c00c0c1c2d00244030585080964501703005036102e0034070f010307145110b01d0034004a65514000351403503c12140001000c54022171240300e8200301c25500c0d20b444c0000103040c05203403164030039001c80c02e40445000700481000d00009140130300c906510000101d00302d04072000c250759007520840410054221642880e00d0108014482c01d442a201e401440c081d03940d450700810b8020300944407007402b00014121100c1215050a0040c01c10550f0031206800107100c1007140f012200e01c0d80c551991001700c07849405940c580441c40c9061003606d10030041030311740c07a441c5036220400b1211400002c1049051517075030815481c0340142d05002d031140c03803001e460342c41d61404281c42c064002c981c000d40780c40c0710b4cc606104100c0180c0380030080d103003104c1403481980c180030a0391a011008100c1c00f5460424030501040c0010b00c5a450006c8241681490004c0e800000b103020b411015514100c070880c0407000034102900c0c031090158822450101e4034016 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 693180467 1250 693179217 693179219
    0xf0b03120315063603210423040608010204060207091a0405060d050f071e1401080c0c060a050f1e010b03070513150801060219110f060d0e0d050406020c0d0c 69
    0x1601e20a034040c0d5007038400c241c07402c18048405080c1041b5480544015030100004a40c81c605444042c4c03113240944031001d01400301da1028013405908090b203103000144140a044e448210381070003500076100340700051141000010b80d5801798420001004000d500202c8511003080500c8013415024100f2908081d01c45105000b052051222012042048010b80101c0b032400c140f1800304190b15580c408040e0f00014104002ca0101c107225642400a08020b55030755030342510b050882c000e1041d203074024001c0764104031b0380ac071030f591040e40716075903208500845440e01c0500700b800005800c41000c0889080d0014040d21050300042c5600c024103181c0585030110305046012090101e0780180c600c8695910402405608150200c0c0540158401040b2410224006698246030014054803402d201022890b080e10348001d01402030030050941c0c0d0b41e03000315610080003005001c0014900e40194850050200d208104442c102c1c0d090354000c14128495200300004102c94043c01c80348038102d500 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 693181717 1250 693180467 693180517
    0x150e060609010815102c0601020c0604120807050a0c0e150303071502041206140903030601021f0f0513030f08060a030b1503060108060a18080a0309060608010f0b0312031506 76
    0x3c6d940c606c1a800c4012a1091589207040d200728880a02400d0554200100c00c942985403c416102103030102190141030007070718101280184101040500b1b20300038103032000140040065004100d0707041403210320706542d070209011403891104105642c940c1080100502181c01403c003602d010307510040061034584d031030b4100d0041c0418004110391081c1c440340c007900a203c8080c0390681c0213000308065441c510b41480000d403941c2108004002c0d1102140c106c40d00c140c3c1c075512030f00f900000541d04204a0814808600c0d910f102071500701c3c00901424940400d280c800c0d400d590098a0181c5608262411030740c03100030441005141030b80321504034018450313a03601008558000c044060141c0300781d0401c41504c1e010780c1c030b50828007180440c1014a54000903074860481d11030000d2490001600c0e4518500040604080d902810701036080c0b00e0588490b14003a44000c400c40c070118101c8102180c4200100b61a0004458200d0381307000ba03101c9080f45080620007090340c000003140010301001e04203 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 693182967 1250 693181717 693181739
    0x8090f010c021b0603010f03260d0617120f0d02070204110714070b0706020703030b1206060a06090e07050c0312071e0509030a11010309150e06060901081510 69
    0x560140016441004228402c0a0f009034144032501c0549031035256604000072048200241c2c0b0004003400b40503a000c0000c11050031040c200130100c0b1404664804102c0c000e10003800e00c40c058181d0242903240464100c0b24005a03420030307070b1020b612107070a1803480e42000c00c0a4100e03044850099400300074200c0180d85a00c500010902030000c410b40762403003402d20b2105821221010005980140014040c800300103064400050b4000340150fa40d01983c50110041c040d1640f1041d000b11944254100f09040071a044e4400c3c081920710741001c130745e611000c40b03000c02d0314818011588256408107440e54881c500400307002c41c82c0d0781100d1400640c62007145084008880000c005001491048510991880c15090740b9090380340c01342c1840f401000180c0c071003025807002007a00200498178a5a82d00130340004001e6504115040030340310100410002510394030146000c6401a40d00141542c6802407029042e034180c90300400c440840e0310103480c0319a00180c012010058100c0c030000381d40c640c903 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 693184217 1250 693182967 693182981
    0xd110a050d1401180b1605070209090105070806010306050a031e0b0a09050c0a180b19090902030f0d0804081e0a020114010f1a0706020d0e0f190206040608090f01 71
    0x2030708000c0c00003a011240c0034211040419140a06150300300142c0c04110164150394004c4100040724139820206c40050b9018441c12800a4001c48240108050b241040d4804e500c20001521003480d0b80e40c1c3c0d2001107048030001d015040e80140303400f006102141c1d02081185207860001041440e48016480e00c403070141040b203400500076103404c8000c080040c00e207c0c003030f00306409a6102407850b00f8500190183d003c2d14a00330900c41e507a2124102641e43c5501e0b14211848205401d115180c07102e071b800d0040c1182035806d82c00303403081d0480c803500d010380000d5038591402103948105041d111540d446c140e40c0d0201c8010981109800181d141d0840c050b401800d8000c030715000001e555501b680c59070100b010507404544200c409100801400300310b61241d002940001a02540d104090b18105000f80140000011501d207054900c48880c680052030381e540c22092411a140001540e443e0b1021002e1110029007126040c8400c000107805040d06c00d412000c8001a951035000440c0d1060840b500 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 693185467 1250 693184217 693184223
    0x509031e03090402121b12060d1502161a0f1303050408061303110606060405060c0708010203042409020f09061c0308070f0824030a0c030b1b03060d110a050d 69
    0x410341488030000140c103011b00d1403030809240d10300700440040c40d0240800014002805400c01c0d9089404001410494201388040d413981103440c0c0c450790581340ca19004018080b00c1403070b03d5804101100742c000607003030b10554041d2200c2406a0341d4070352651000c1c008072000c8060020078400800e502c0b10074400b0718417810441c8810124584e59040040c900480c0c45140080d81d08290284013040e15200d0484040e100107441107075642c003400300d41e03070b207005166805010103520102c280000c0040c0c8050754007003004911000454410801c85e01000c454041c4e01c025401100d0a595007281d0415903a441e0780640014000c0320b08260000f040c410310700b0142c01c104e0005802d003040099464104503040e00d0341020345401000c40c503203001d44c0021801c4038107280441106038030610206275000c000e01881c031503015162440042e582d1070800d80d041c03005d43d0704020070f00040300000c00311111501074070b22550002b4007419104074592101c415032000c0d00c0200388c2003c00c2e5080401d00e51100030b1203600c1c1500c = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 693186717 1250 693185467 693185497
    0x8060a021e030402011d0102070315020a030615020a0f0f0602070b06040f06030515091908040509010509061c140a1b0501020a0c0320040c0507050105070509031e03090402 75
    0x3070346071400144031950700480280010140140000351360300c14143c1c10180d00c0075a03584454100e03840141c0c80c0c00c446520040241c5c002ca0b4906422a00603001f509007080c0d903440034014541c940c098803000c104200b00180041c0e12a01c030301404548069001d2803014040c1014000500680d2150701c180d0340f1289080c2d840c030706448244602418944180034080c490040100300302801c550700d080e150070442001c882c80c41d6811000c251056002c0c4290352404405031007074107004040d0f01e01208250000e1003500e1064400781c00016007410209003443c820a002440d901024403400c0d4100e0301441c3c0c46000780c0743d510390000c1c1e9045031202040010640c502076001410701c030400f0950050b01c050950021411034000c000d907800021304003003000040d01c1e4400c0b100a00e6810300b03494405601003107640f199100b420b0107101c0e010190040b0040400b10300642c000e0200b0390b5000780c1520244604035415400d50b10000c80541840700f00d260f489150070401c02035a24103400311000400f640c01002981c280c1070 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 693187967 1250 693186717 693186727
    0x4080901080f060a05121603030c0302070f0b090402130305011107021215060d05011e020a0806010924140c03130e040f020f01260a0c0311070204110408060a02 70
    0x2680215401d9848a20300001d407a01e8a072102c08990444820311840303001d00006064004070764410b101c1d5101c081006c0c10a100710550324180100a46010202500540600800801c580c0c0401e410f1400340c41d1090b010070710380107604041c44000c0d8416002c1050b00c081e00b11021000540c01e0151003205002d0b9846030341c4031440c6004000e1803040b110103001e11503018000d01002c03808880c840c00c0c0d02150465500750324022508005025103880c006e4180c5003049600d4003d83c1d0100c1d0344c09454080c450b0f5031140282e95905006581104040c007841010046001400110201d20705071400090303424070f000041d02e0082038240385580c210710090f420b00c1d08080b0740e5000d0385944421500040010f00c80061007410075450303102d420614000060300580000700003441c2c0ba4010b0080710f9500c108034030710b034400c2c1c0060031808141c1d0401340e844061140c24006101d460314404e004041110f81032844842c40c08045034204002001d8040b85040401000c3c400014803610601807030344203005800d400343e910 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 693189217 1250 693187967 693187969
    0x21e030a1203021219060e090c0d260307090801091502030a110409061715010b03070c02120607021902150c01060b0406030c08070815040e0c1c050f03280c0b040809 72
    0x40c814941256907250f0042c0104184180001034038151001e041e20b98ac2104080c17400e011051200102c01020070705001c000c3c5801c01c0303450b070000b140f0030b5080742e070755001c0b00f9141c0703000a081c1e070503283c07020b002d4a06115000740e0b18405076004542040203864006141415140c2664040d081a8004091141d581c2d204010a00c0100f944014080f080b9019018a2001c004914081d01c03040c002d40504003808000203110300c3c011100e0300b0340c6d15001050041580800040e60b540d03500201d64240050240c0342c0b619080e201030145114906034003d24020b807070003514800704848e400c01c405a40c1990b4a032600041e00ca1180f00c0140081d183d60f540118031285200f80c05001e01001a0044040185520402c11307042a40e90148064040895010600120041d0203501d401602c40310325030b000d40710010f0f030031150001c0d0002c0d1284070700c6482514030040048081c503131607000d188001101c081d21038407026078203180350460814244807800c0c0714100e44a80d403076081e90b803141104d0031078290310002780c14041 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 693190467 1250 693189217 693189221
    0x9060b0903011406061615090819050a05120a060f060c0b1023010e060c01021c020a1e091e0e060a060f050a0507020d050a021e030a1203021219 63
    0xe00211904000c0345804d10401142c41d920890f4840040010140da020f01044988840401c01c81d01507941401414031600f00110903500004010b031200782c68411001c8698020b170183c9840003000e40302c1030b05102c044c01a0007a81700b00207140d141d81a6643c000440c0c000e070700c240d440c0007910003a929042c20f9102c5103000c0c188103001600c200c0a4214802c010006202400c9090b00d00341215034141941c040c0c100016a41e000c0c0700d004003a40050081009403105005501600c444c003140c2452101004d95041d50f00224880c0c03000820002d038001c00c0c00e004020001c0d810711940341881c98070070401d0b55503007070030380c107480203caa1402403040c107686c20014a4100b101c41c81d000601110000d03159850903601905950400184605114011403001300301409841941d0b0080c1d0094420395034100c1924003680ca4100300c1130120f119401c5082d40440503c4400402140b840c1c0290003040da00c51b040e125800c0010361024040e042603003c0000040704e450310201c0c28003d4001c1e07102d61190001249a10007 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 693191717 1250 693190467 693190481
    0x131d01050403090e04050c130b030f0309033304020607080c010b010806060313111207030b0901050708010f06141605010605030606010201020a050f0318030a09060818030a0807030609060b090301 85
    0x10300c0300d04020620006c0703440426490007185045404058000c0d1741203451000e45003a0341c2d9541c2c18019650340011780213020004204403501142a90600c01d505020b503444d091800307510f10b02100c145481b04203e035882c244455080740c0000c042c54140007290303882008607171100c0d5841110b40d45445550b1641d5030040c42480c0c0001d412a00a8111714011005034444090064090441d80c2e1813a40d900d01c50310b58051504008410b4421340340400d4603820030100e0b5030001d5420f1811980303401c0000e52201d2182c40030605079a0b0800c0c040f403a1614200084807810410310441588000412261300d2200b04d8080031b01816100c0d20001c1200c500d800f00301810074030014142c0d415a40100304030f15201364002c080300c107031421540e0f0043c0c507a1685c000000345850301e1442300b02244000142d040700550009400001c658980e40c65895a41e6000c0f5180710000020b00321800c158014000710203d1401181d1660380325200d40b8000030f106960745a1441550495481161a80c00015850700035060070f0003168 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 693192967 1250 693191717 693191729
    0x9050a0909060c050f0a032c0f07050301020c0727050a0b0907050f040915030203030403031806030606120216330b0f13020d021c0e01050c09131d0105040309 69
    0x9003000780d41702081d412841113412060403d07603100200c404001503400207010360003031540788408000803800c05640d0b6103a0903280c4030071b1b4852079030001001d2905000f03c40b0100000c5011b4810346150101041c86d4403c118000382c400c02103180452580c04041c450148034100d40000415040004000d2204c07012015102c2400c00108100c42c80310006100704a038115668a2400100b10176040c3e4440003402042d000258140400200041407580c040360200c8103c1c85030201b40940f664880d804e800322201481010702050300c003050415110403c0d03014010307542040b81003d1841246503640c0c512202c542070b81030369012102d04010300c041304440c0401e41e018841d210400c04404c100c4001100d808218617058491000c000d510304c03881e0010b4065914201030104199107640c105144103404070020000070402c1860f00b0144c0450550500400e80194003030381e109440c1c182054244600740010501c001b0b801c035110400301200703130110180c88903030016510002602e0b08040c0b80c01890505194420 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 693194217 1250 693192967 693192977
    0x50c1504121211031305070806090f1b13020c0c030709051e01081902030a050304060804020f01210c180306050103061407271e091b0e04090309050a0909060c 69
    0x142d070000303c03002c41e070f0030001c04649482603c07030030714003507241c48095004409540129000d0191040000914113940090b0300700f40c5450400b002501d00e440520030507220391102101c1e44600d9014000c4c0e00400300300c1d1603201078038603402e007000100e813030812154000c81c107d0340d03920204039074840c1c2006250101c074001400d4942c03552400e9119a901d040201490408a0340e800c1c442d0115a0100880b404682d40281903940703440ea143c2d03002e80280d10466050340619114015a40da541c070824010080d0558040030050b003c0a50515000821fa00390305034017403004075104040c58140203540c001c0110300c1100042a0340d8114502001565030048807629009241c0003440380b0759805c004194400c02005818596143ca131002d143c1149220340d0040d443c0071000b902045583d403030007a0100aa41d5100070038803040c0507005808074640300b40300038031000442c1c032034419007186420b400103415240286410b83e00c8a80382c0000920b161807681c8245802c6a4450b003013401c000300340c010151122424140303 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 693195467 1250 693194217 693194231
    0x60b0c332701090f11041805010f0501063e01110430080a0915030905010516021e03040e0112030f140319140705070201091401020a03050c15041212 65
    0x141c01c444c040804002040010020494245621a5072142d00140c142140842e121107080c02c24034006c042480c0c1c00700da950309100020940c18001d8110181d0280504c210a00d00341130003410031101407030544c9100c503001c4c0300785048041e17880c24010071004200c54014540c0d5140303040c11181c00300f00040d0041b03120050703914070701da007030f120604440d010a600312a010fa5150700e8000101c03043c528035000400e000000c5148010880e40c143d010f550014070031002000180c46a40032401d10034001c100800069101621201d20080400100c9140344084000c0740c3c00c09440ea0015001d01c1401d80140d103051003151500000d240d40080c605954102505001d261907891603400c0b00e451100420700380c09160080d001c50078001055000d079680c4409030310b0800f0f03581400b500080050340078001c10f82c006500c050000ca21403102c00d490341038a0034160010a400801c40d91f060341da54021460704901406154072a1b8208060080050f11961140100550f40640980c005d0001c59005020201081c54054 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 693196717 1250 693195467 693195473
    0x2901030513021011190602070303150f0b0d0b060409140c04030507170c030d030c0e03060f0708040302190c0306110c2107020d060f060b0c33270109 65
    0x1050080080980ca0011000c00c1c02284076450304100001e0b41700f510060351907038414428540e000d0301c0128803e640030f02c041c032001514140c01030154054050901c100041c10032080301042d00810000d02c01c2100030403640c035400d0001c0c2450b04198440c02019803503040720480c08640054980c0d111812014542c18a03041d0707102c80381d441d489400b03801d090503405000b142006004200703080302e00400604580024800f100b0040c094044101d100020a010340041407851a010800502c00c039420804500c00d41d84000084500c4074000e042039042d80140701107402d400c80e13000300c80b41400e400740c01240701051862800f0000c0300c40c1c46410300e08104041c80b810144c01c0c402314460f404034048100c00c0c9651524494562410720454000940c441442d00420003040007940024040e6017050000300b2040da6549040070f0300c0e1160300b83c80704446e00008102da28504401c1001049600c81d4200d504006420301c050051140060700e031200e1070a8a840a4807407282200505008048600000d01141b580c643d = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 693197967 1250 693196717 693196729
    0x30605090f061b09040b0a08011b020601090c0c0807020d08030a020301051017041119060e030f03090105031f0f0e090105070e010203121b031003030f0914090406290103051302 77
    0x48104d911454075281b401c1c00c01d43d16220340d500a030508030000c03c10f04001d0840c00d00350044911100025006681c00083c0768181480380402050740c50b180c0180140380b640d10241c01e50b00849049a0140402ca01000843d5010025504c51a500000103036a0350400307082094420544040e41c080102e0510b203050028121010503410a500c251990f210380c070850002a0b404984200c1c400e0715801075480080c105510103048598601d081e0305807030740d0061703040b01c0301e441b40f04401602d0b01144082020079038034007840b0b05411296803403100420155449140000080a9552213659492000e009000d031401e02803290301d41000c100c2c01d120300030340c883c0f600103500c030700031030501c048000c02540000d070811102c004c4805540e0100346245540386004403d181070112607010907000502508040e05030240200304110a0b108080c0c08040c1d00692201004030042c40200111411921100f09603a02e0413404064440d4a962404008001146e41c00040c11900000c003804104041e600b08a005a103c036 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 693199217 1250 693197967 693197977
    0x8070e091311030a0b0703140f04081b010f0c09050f030607021002210903030907080313090b04020c07030b0105040f02160b102106050a0b0a0501050310030605090f061b 74
    0x2030640c490040300c0b9000681455046603024116141072070400400035810f80c0941070342c4503451035101194880d401001c13080002100d008060344802c0141e4244d95100ca036010100c01c2d0002c001103150300883c40c00405590712244e124020601c0c0e00408e000d07501c1c1038110404012015002010103183c200c100035900c40c0b071083c1c0c201700c81d40d000800501c1c500481c1150030280300701d48020b002034180380d0045030381e0390b0003105c2d6000345018442011409400100813904442c9603201c0c41c0345404c0c1040714003070080850081c46036200303a0811810903402002e020b940000e50080c4542286c942c94502800140c0b41c8554407901017a10420240d22180c0061070100340064002442607440d6840d0b02e09090b2124064202c95021215940030308a032002c010800c02215204200a100301e440b4490444d040d18060280700d54841420703041440b8652050018541c0035007070300b00c0801c4540da40e444030001c654003900e0281c501e40214210350142c100400100d500407013031004a6403120454100c4414902070 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 693200467 1250 693199217 693199223
    0x150a110a080f0c04030618050d0504150e04090b0a060f0f0303051e0f0d05070921020d08160503190203040b07110d06021602041b0518061908070e0913 66
    0x2d0001c80d45050040c0f0554001c0c561011040000c4d80a202c2d40c0c01c0005500081160300d445041c0002c1e40c2a0b1044080e40c00f01e074182d5030740c4542d02d201010165126106110300c0c90700160780f004600c010481028016024000c640d2000401c0e40c2060402c041000305904500216220000100b0003c2c1d0300074111120200b00340c03081c001c039251240c3d445800d4402c0d2000b000303070440080741095100309668040c030b0003440c00e03450b08071803541d484000002c441c848441c0c0c40b91006203d0004409030826403030f500038062080079003500c0d140004041c241103902911082d2160342c4007140000184020b0041c11550301c045000131801d00d0f1034800d01049510070514010419042c4800c03040c82034403001d0820606550007107042d52070703106c103412650b20003081b060264851420104101c40243e2140399408440d00c0c141c0da0545001100e420455a4000c090b03100d64100000300f00e82c030070350000084003a111004d1036886508504084200070310203850000b01c03501c1b40400c00d00b4401c100d4a160f505d080c980e03038 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 693201717 1250 693200467 693200491
    0x160c0204181515030305030c03090f06070504060210050105061605010212190b0411090f0f061911160e0a09020901031b091a21150a110a08 61
    0x1414404640035002001d105240c0000c41c44224041104003400e10002209040b800c0140800144103e5014a000c0c0301c00b5001ca60100081100ca1043d00002c65110144908444110010300711540c40c0201c211030660001e50003280500030703103605100d414610139510b0700034026541040e0010703c40f03200d200b2442c40455080c0b40c182007001400e406450640c11306001c9000d9900e0031f40e0008800c1c0c0b40c24a04010304910b8140420228602803049010f89660000e071941003c0100301130003003141c11400e202e80c0c03120781c44d41c811b00b90741e40307000007080c100c4200740207030551950442000d07102c04c009100e807407565005200480070100510001004486c00102241c0440c2c55940d20540201403c02010f034100c4030034070010042c0f0500e0680b031021854140c01c03001c685541c3e0101d071400c40c1c107031030500801100c0101c01c031030f528645848409540700702062030800000040c03d0300740c0341c500076880c242800e240071000c000703e8443d940700340401400080062880c0080c0030000910b584401851620b80340 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 693202967 1250 693201717 693201737
    0x141810051b0a140c0a031b0c05040f0f0203011203020729030c0f07030905030c060406140a0314070201060503120412120201020d060305070e0109022802031c0b03060a0516 75
    0x80c41400b40a0020500381d03e10b542c1c03641d600c3d0120343c0b2110101030a03000b16501ca00494082d60100041011003034100c0c44c400b01c000d0a0004020143c441409640c0c2ca603520b600448104000f54401140200051500c02040c03100d10f142c00b0b4104044d0354020140c00108000e82e00d96451003000303548000408290301a84c03a0b039210740100e4940100101c0300b08031040403a0a1081580140840045d624201c0c203e401d0b0401c140c081111501c124012400000c00c0407441440030070480f006400f04020509011580340a041070301131801c5011034007000180c1d160f04c0204070504003401180003405003040414503190900091005460030342c0801094500504008148680f0039815540c65296000080c44019500d003080d41e030704d0406024600c4091b181c64000542e460051085519065014046142d10389869106810710b1025900c41025804200107590344108900c2a007c1c0c440c80c8403c000490008880c141480c05500400c2c030307040c051900d000d0101d0122112204640343c1c2c2603292800f001 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 693204217 1250 693202967 693202987
    0x31090606030b070c031808030d0f091a0f0a0605100818070b04061106010f120302070506040f0e070c03050d180609050706080901060b030105060d141810051b 69
    0x30051a8400740032089800d081c019516801008001d08600995820000d1408400713240f4a4058600c21015241d104025a901228080c3c12050a910b185003000941c4105a240c483c45041300a601a000d18841c1d410025544610389032190801d00006041180c241400085103103130240075401c0c0248101d000024848094aa40d4101c1c440706401c20b648800da50b5003075001c0175070070a00425003c41c04120a01c0e02218000410904071002e07801c28081c50303840c0103250103201403140d9043d4118007400c000800c10743c4416000300000c103140743c0c03080112442c2680d144500d101c054010710030450300c4020300780400d41c800160354030310384008800200350212050b1142080807881000b40b40d80c2c00e1100e80b8050240c0454041c0803034a46031180d100c01d03074640420b07900700c41d19405003c207030030414001071269080c51005032540002660700055003100d048240c0c807080c0300459010817400e16683c00c00780305c41400d1001d024680c505450502041c180028440f5801c1000c0d0403174400800082025407813 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 693205467 1250 693204217 693204221
    0x215090a150218040504050d030207080f0304030e01030f0207020906060d0608010e010507090821090406050303070606030c0b1201050607060212040b160c1a090c04020a020a02310906 80
    0x41039020007814544080d1a89010107500400030781c0b855100c2d600c1c05100e050401e802018800ca41c4603005d05462005c5034400d0340290030107002914032080510285945238180d0300118000d81c000d440715441c25907100300050913a0b42c0c00410300c420f14018001e401c016102d402425820100448070035031a40e50125400000f494180c0c01070711a5801d00e5510000a0b02c19070113140140080d680303582d00540c44803d0b542d0b682804281c500c0046103900404040c1d518400041e01400a0040022920030303a903900282c43c40e00b050900741d0721150388600c00c1040040020720342d40103021103000603048c5440e007001e2a41c584030522455000702400152a802c000c5e0582c1105c4624002d2054a1611304241c2081000500215030749000d6880f00d940000c2c880d03001d6540c1c07683c110741c00a00031241c40c0a40c1c401d10b00d1560041c205c0c401d14071405030090001e43c2c03103002503c882c3c52540e00902400360710340100b103e41c2d000c403524548014244800e81001c0d0784403401c81c80030070656490102d0201070a01e01000 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 693206717 1250 693205467 693205483
    0x100e0904060e03090d03031a060301060c03030e1507080907050102280f06090b190506061902100c0512010506090306130821011d1501210f0516080106021509 69
    0x5402043e0172100d4082503003580c4404030a40040b030780203620380c0c0780303c052000c00e00c400e020b400041060560258000f0f4401d0308a03282d020707041c505544d168407c500f001c02e4641810745d20000031540349000c01c440f2800030021140180403d00c004d05110082e01d2030301c2da881d6020349103020700e415964040c07018030111031050054107510030810081c2e40d00310b050000c2150420390b0b02807002c180e41240b400540400340502c0d80a0103009040d5403400c06071501d85443e0000102060082d409400400c2040f03c5e080c0c8910b403612591911019600c003c440d40e040030440d416006070744200d00034030440700c0035100010581d0b8417088201680020b09890b040c6072880340078012400d11140d46004a6040e610200c80030315040341d08035000051148026000d0900400d401c076420440c0030200d940031441588105418414581c9604030f01b0083c40d04001c11030281c41d50307800d801c07440315280c1e010301c031400c4001220a01c04091a1500602550406100079218003580d1451808188282c000c02e80c2c100c01070060300 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 693207967 1250 693206717 693206719
    0x72a060b0a06050702240f0304030e030f01150b040803250503040b09041a03060406020315090412090f1419171005100303171015020606100e0904060e0309 68
    0x71499581c5020080c001e40c0201c0c41280500e20100c0e2a40c0a000030a91850360940410760490070840e40c419500c0313031034000401c01c0d810040a8450205180c03010b01c6481c20440303109001050070107813405014200c408036400304280c1d000402c4108041c01010068640c01c4104c641c0066400d891014403030f41c143c0031144003074070ba800001340000b94000c01d40b0007801c0c00c50b400e85080c8030100055101c0c500401e501038181d50140c004000290004600350700031070703000034441d00b403000e07040041340031412022040310110b40c407411000c00e12240d1600280114028406440000d140600b070a40786820396006201c2c0c0c9000300701000c01010001c1c0e4900c0460050f00302090016040b22591a00355038404103404c00c0c080705450701c030104200320a100d0042c01070365016107540030a080c0040c0c045c241a0720003000f59460030030300c4a0100d1510b214500b10602400180c0c0144084d08140c401c01601039040036a09007408004480c0410644502203003603442070304500c0c0010130990b1402014103511403034803c1 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 693209217 1250 693207967 693207979
    0x100b0a0e0607140709050108070905070c020f1c080301091b05070605101a1b07051012060801050103080705060702060708010608040c0819150c0801051203090409030f0305072a060b 79
    0x17050903030003070340b1460413100c6071011110460b035a0010201192070a5400c04d0005094400c0035002d030500400c00e21034440c020307140340da609900000100b4405181101103410078000401003003612030901440601c0011203140d0292207840000c041c1c032611500030000c0074075886800041e404030a0b5034003040140351450094403201c08032a150810365000215981102e40b0400421034001c06c0020805c0588134054094a41c1040c58881a10720b0030030300d45200b00c095194000424840802c0c02468007c600c100b0a090701d0306542e10f0000d0800c80300803c060708640c0403804010f81c00d035210f140207045075001c0c18040069115030800c81c841d50115089a001c1e072040000c2007843c10310030a800c043e61400381d031003c05c041110140e2501901c0a44c00c40000091a00005010900e415001a500c290840088901e0309460710041401d03a106c460f01500414800b408044040360180240c540c45102403811200e50301003032108684aa8014042800b030541d20341c0b0322800c010490307001e121560b80007015 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 693210467 1250 693209217 693209219
    0x30b04080d15080d08100b090406170a120509103507020d1d040e0f2d01050709090f02041a0a020f15041e02090f100b0a0e06071407 58
    0x3002d002018607114107040351080d1078544071850320825445000e440700c0401103010701e192004040068001010603907015586600026061400c13401d054880314030780002d040099000d06211f88841a901c900d84280001002001c889544494900461900714103122014040041115040c800d800071030070010003a0b09a10740b0b8404402102070310529240e0700722104180f2180003141c0005408141049000c040411842c0914058200e942d01c811088100e0352480c40c1282c1d0b252404005c0d6149031721525031214040300d0641d085400c94041c041040080c880750800c00001804a030345886031110059440c01b2000384007a242d012038004107517101200c8018003c442118109500842d070030000742c032030403404c3c81420002261800154458941d240782d180c0d220345410032100e510f4132001e46460120a0604016a00c00441d035000e440100449001441d003190707041c240c081c0302d4204040c491401d2007001c9085500c0210002c8452050b150795440f5141450840707964003025031512654018200 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 693211717 1250 693210467 693210491
    0x1030f0b090f06040c030b030c0d050f0706031506030c0c022e021f0c08010612090b090604050c0307140103020d090203010618050f19020a0207260105090313030b04080d 74
    0x110702c60068401321001c000201c241e06080d070031140304990454040e000b004001c2082c3c40c240c0c20741c54440d4042c07410342e410070904035007450070008584c005038003080d07030f59a8903c40c038510394450340003505031401c08001d8072556000180122801e260300920520031103040072152482140c0c201031283c0a0655540d200c00340700b101035120802411621500d0095810b0b039000c1c40450302640c10f00408a44446801b6428080c040b0307051511002c034807100c0c07034480001000041201d00c0840c424040c14010302502c6c2043e1a00740d003071000241a41d80310f03600014046c02003003050455100440c0007400c1c016543c60042041130007401e1014000ba500d546062f60010f461500c1e44010304000b4003000c010003456907071192500c2c0c090815205030354004089500c410308160365500501c0221064011a100d40742da55a0100703c0c000c0f40441c00781100003080340d40c400700314240030f0305400c40340850141d424085412610440100e0b2840007500d000d1070240814140f0000d541280d1050030403920a0082c492440 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 693212967 1250 693211717 693211741
    0xc152802030702090f100510020a30020109030203090409050f0703030201051b04060e151303080406230d1119092303100e1504061505010908070501030f0b09 69
    0x418182e000b907004a0000345c0c20641c601c201882550205d20300c450440c02c0c0824001e603e039851082d1415440f903820360b0710114002c0d04044480c0400d2110180009603844180350a0795030740d95012041da818010240d00103900030060f186607038010382d03000036248441d00b031091a2452000f203410312030180140100c1030582c10340005214008014009841182031110122548140e205032030000c0c030b0100b5040300d549445401d48000389045010242072030071f400041c084180c5541d004441920001508104130741d04690300e16002c0c0343d282920541c505c20020800301901c12400210030b401d9480895014503c41081554030622507000701d60b01da4008400054100442401500c0030680320f00440018040d031082c0d09125110080c01a21a00040907408409001070100205050040c60000442c40f424003240074030903401000040382c01000024043c0500845400050400020400034000c0c03e40010b803800c11210b080c60300280070044003550308000c003110480b4562009001c410f00030140456 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 693214217 1250 693212967 693212977
    0x415150225060305010f150806010921060506030a0c050904030908070821040620191104051305060c0a170c0703020c030c1c060f140103060b01020c15280203 69
    0x40c0c40800640e600c030400044050540e01c29028440d601c00d480340c447d140301d108030681003403060600d2580146c072001078854450b240040101c21107240032412052090901405400ca0010b401070448155240c441947e58201ca000c0d00d40140b9203003011400709446905968001c015901c265210686c90312280d98991403e104036460207680d180f100c0c440950240c040390121050380c1c8070a1000c00c001c1d030310105103508000d40d100303d0307001d03250b5410066507000d580c045c146403240040440c40e516100401013100c1c80a0540c90411a43ca08038074001080000d0542d0802c01c1000e24581b0b0307101001040314441c50054070300f0159102031050120b21101078014025042c07007a025590003620b0041416130701c070710f004203496104000c0300d003640e10203051402a0305068000e079400300380c00070a0310740c050569005414444040c8000c400410030b02849101e100c0240c207091000e4050b800d8a14001842030340c828000c0c401040c00042c50310311420030458003400c014034017407082c041d29040d0302d0082d443e5001 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 693215467 1250 693214217 693214229
    0x90f052b080c071d071d030c090903040e0a0e03030f13020a03246b0a080a0e0c0a08100612170304021801080303070e0415150225 57
    0x1450b001c10704c06280d51400900c101200d90320004540d550610141d0b8040d442070f000d40d014040e080c0c2c0d0030616190150b40c03500c91f81c26040296030b0b4502c4c2c03024003049508010241405d2034a01803d20201d010040b0803030380c00c080a500001a640c8844681d4841c0700c8100c01c0084d88a02d00000000030028032134040080c041c844c8842c4103024450602c0481503031401881d085180b80d0400b40d0900c1c61741024044151456110818800c5c1205545280d030507100712041b08240718242000c140c020200124226016200c9031109030800c2010b500207010782d840a03011100441d2180704890b00d0071001c010110b06c0f100000c00560310242d6400740d594560f48103001161300242014004204a0201a508684245c0c0b260b0041f00b04005980c0d800e4117a08003800c203e03130092003098410805508035034001e005e4041070000c0e6549082114019181d05030058101c0e024a050440c60b0651010100c512002c5440c041075035528081c00b12822410400089084200311040401c1002e280c1c62810695041e100 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 693216717 1250 693215467 693215489
    0x90a090501080c12031201051507140a170f1204021507061e091106030c0405030703030e01080f27030f070c09050105220c1815090f052b080c07 63
    0xc00c00131940f00d1003828810b200b111503110041259060000c415280c225843c011541440925620f06180a210030940c900703d071f00c950300789801d000140c0c0d5280b04900e000300f540c0d8035000d030500c030103000c501552400c0c6c003070114000005400d5481c0e00004421014054842c140d0301c0d00c0718078200005180b00e003040d00600c4550420b4090300c6a43e44120f800c0c19400914000502c590030342042840d520080498a50040a010001c3d650b1000c00c00341002e54801e4840289800b0100001403d100c8001c010305000d101c860140f06000d003043c03150303d92041c1502c40840310303d8200d413071035403952007091481c1c2022a400030740001886400100e04041c0c4403030600c00d10607a40d03508100130141c0d0305810f11340c810302d08248149015800c030f070b800707112284510700b000d0cc500d80740c00014154001540d4031615419001118100c4010fa101007504041d100081d910140c00b0300f480003040e02045100f01e0314844507011402c070464403041800d138410007135111000c269581000e017000c5031580064420200a0701d = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 693217967 1250 693216717 693216739
    0x91618140106020318060702040c020d0807031a010e01030e100f06080105090d0f1107032003010c050a0c05070f0f050907080402030303070c140706051c1a010302090a090501080c 78
    0x84030301009412150140c0c021410301584424a2044c60607012001c2d500000400c450001a100d9004124461200e60060404041c01100c0a0030068004241c030007010714082d494070081064440e001d101c1030342840e1003080c451030b410041c0c0c000c002d0034500410070311412000d00b01410554110410f1034003a92020301100c0e588400d211709a51050b43e25100b16040b00c02a111001d102d01e03e80d181030491032401141d000c0e00526114201003007504180c0d600e100a080c98080e005100748619240041035000304070722000c131540200b0354010100c040080041101c802000e01c20104601005010039500070410f143d642c0c9a2402400441c1c4103080c0140b440e0740c00500081d004189992003207401601461961f901d041c03080315180ca00300b004031030b860012100b105001780d0800ca01005000c1d10b88030a80e441c1d409001c95a5400000d90000070640d081c80320240e1403017000d0344070320607420003070a0158940d5610000901540d255420040040f481e0400000e509200017500b091807000c10b0790651000 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 693219217 1250 693217967 693217991
    0x17010f050a0501020703120503060d060504031e110706210509010e1212060d0c0902070f05281e0203100c030605010509030c010f0e18190203040b0c03091618 69
    0x45ca05521001e00000f01940121510a01030002564044402070010306105c840d940c0300d02c102c4000b034a058000500f10701c03228103801200c4003c01d407500c1c4c550404500c00307480b550303d40380c0c1e4514500072141000640d03001310389080402808070244e03050414050040b4688840760030b00812110080200500c1070b819404a01c00b0090201e4040e0b010385025907100741e480300306226070840361120854950302040d20000c1c0368425031001d480c140784544480c140c911540d0810750300c0c1c5450792407541400d401c050390b502290003440f4000e201159008100610007260080701c45401c0119240194140c020351b104410703000341d03981c0b02e0120746082e500e08100041c2c0fa0001141c80b402203001054056101c504420081d6000309285201c0700340c50b2a1801060300b04002051558803400c501226100c0000113000070131401c0c00f4010360b8400d040030118114582501d1f40916158054551614020b001011451811081c0181c00b41c041f00034107038580d1503940c0c4076407403020041e01400b0b20100740b80c01c00340c01368 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 693220467 1250 693219217 693219223
    0x10c110d0f140c0c090a0e0c0108070c020f0f1512010806280906110d11070c030b0903040f03200a051e0f12010501080d091a0a17010f050a050102 64
    0x84406640e0740c0004030700b000ca80074203690700403200c410f0240f140c4400040d00e07649120b50548140b42100340440c545d0350b404d41151178540c48007022414411114104603407182d01039914200d06804a458440c20311600b000307d4401402500c01941000c10034440c1000e200815004080a406103098925281c2c0d0310480c00751203c0013900d18491181940500d100070889012001c0d6280c0311169000841c801c4566580c4215407a60070f01c0742c81c04d200401d5540d0320110a20440c0b14502c25100050315001e0035036650003083c81c0b80d002c010500301400300403518107402081039a0142901030b124100d5203440742005079069046400c0c0402101c000ca030626640d06103d405542283d002414440744101c25100d08960310b62a1105641c00c10351201c0080b41607515110203007002a8110b000140b00c0d41000d41a9060440031416a000e0203a040300070400300040d00691402c4d01942c0000c9511108400411158094039031135600b100d0581c0000810001a691411002c03034000710740015846a0b18001079803 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 693221717 1250 693220467 693220487
    0x6020c100309020f010804052a01090617010b0c030c03030708041e03020a060c03020d0f1a010507050705040b040e0d02010e07330302161505181902040608010c110d 72
    0x740162034000613008650058450b150014030540c180e486200518544a02044c0383d00d00c0c400e12031540712181c03030711540c004802c0303000741015207448092030a450030380d8880800c0c184a2480c14110009400c03c1885043c01035070410500c050580c0e0f96400c0c0b280009081880588081c5e400350000b07049000076a90707110a41c0107082d8190007500e407042c0c60345c80d0b0400408140400c4001c1c10307020403960362600b401d8890308442010354500051100354484c0307400203200500032840c0c14408100840c10103d400000e0708003c85508581c04a000400900402c0180900d10640441440b400d6201d0703055035010740010500e42002400c441e4000c0e030f22840c015000308803424540d00d100519200101556101c2d44050686515040140c9040c1d4540104104088940025121115207070364030707102000e66004003074100c1000348299046007403c03840c8548514007280382455090000c202001107440c1d81e0000c1d4002e206400081019019141c000342820162014101070703805040c00c1d92810b1405990185 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 693222967 1250 693221717 693221719
    0x7060309112110140609070c060507021006030812150d0f050a02100918060608061e0405160201050f01142206060f02010b1503280606020c10030902 65
    0x752500140301801007114a940c000103107184182c2c04181214001c012800b080d250590340042e51100380308101c120018090b014602c90b08030780c8140001598010101d44040f5003200b00043c55442e0706506a141080d101300c9140072504000b0004240142840030f0440c15007022194081da650300140070303d114100e80181c0340d0002e405621f00f030108414800c4109400d01c90011100060580d800003450398a0f120180000118284428024003e13200f100c01d42c4245610000d0050504080b40606248001031509028564455508106003404082c1c6078a4020242080010f410b101031918246180300c1800d0001d582060049000c3c02903078401036040300c00501c440134103131050b401048220a65a05114400e0000c00080606954070344640700040c1011788804030f50320070784e40b4080e081d503e035410a03500c43c0c40302811040c065400c05084a41c40900b901e0b0000b032030030181400070f405850308070049060920b8030502040341900004d0481c3e514004a5080d5529000100c0413800e581c0030070002 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 693224217 1250 693222967 693222983
    0xd090303170408031302131d0d02121801030b0409122007030b040503120114010e04140a0c09170304030c05030d0c081606051005040c031103060d110a090e07060309 72
    0x21740e011045a620740c0c3e000d100520b42c9160380700030380b00f80080e148d030b40802000c2d801c5595082440d5400c200412000c0c207060b4009013a60810034208001c3e20300540b8040d01c254900c04a6600e03042c0e11075880403400000c0184100030040540c20030501e02c0e0b55184440d408200c2100c40651040201180e00181310400380084c1145411a5101081ca80b005002200c1500c0180410340d05404030451950181c0358018060003c0c000040004180c1d51480341440d01948c81c0411140c403409000c3c01040c0d101c4201040440c80c03525952017243c50f50b03001e80c044103841d0b281c0b502e202000d0b0320100082c03040764040e140d0310304240c3c0c0750410951110654000c04011a080322032020000f4142d10107004a500341c2da00090038001c040e120780b01612400c45016024900e0880d042c00303941307802c1c42420007040c103070319040103608543d241007000d80c07102810b03692050002c420900100040110940080440079044000d000d99680540c03018000c0440425203901602d80d0102e03801e40f00740705020400c0e03004012 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 693225467 1250 693224217 693224221
    0x91a070e0a0b0f0a0e0a12032c1002030d020c03090901091404060903030b09010e0f090106060f1b060e0307170708040e09011b050703030e071a1b0d09030317040803 72
    0x10341040da500102e0344c0703010b0144c045102e804956441618400070060101d00308121442c1d890024415201181500d03070709041c1c81c0c0040c1c0c0e480c104130340c502041101a035540007609040c1d41c060f49140111442459003c1c000a011860311001002820750450140d0b100c1c801c59803a1000f42080d195007251000000e07003030301300041c0812007a13080350340082c1c003030304001a0811040001c40c80e45802604000c002c084040144598031183d03425055103c07102000070800030f41001e8006000c8081001250200700c2e601280e0442100c2c8070f0300146141d41d02c4001041800c1140c0000e64503a0000704080d2181d40c04484d00e145440c0100c0b00300c881c459400b58403a80351a04000100040007405005042c140d96601034100c041d407a0a00c0c000440412030300d0321512002240350080503500c003111041d4490708411300c02c0091010b6074040008103481d04544130b07202c2e0216811641034804800703800300140300d0b414100790415008154071054902070b9440410700c00c1413450382c18443d0300c2070310010010041040 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 693226717 1250 693225467 693225487
    0x2d02100215101224020f0720030607030b13050709081e0d050703030902030f010213050406030c0302010e060c1209041d1c0e0a091b090602060402040b0103091a070e0a0b 74
    0x10040f41180303111803c600c13420f512040400c0341c000840386003d1040000e4180240302040c45124848004820410035811405020948401c4058411800c2c0764860b001d40c407250b503504040c03070541c1e044030f04100030714617203607400030b107a50020b2080000300d0107018560142c142008814515010010008059408028004a440382c0c08810103404040d90340b81d007600103076402d00c0440034162000e0005a19180103400c02c01030300ea01c551000d845a0b14001003080020000c175146000c494090030481d050900040118400c0d03c00c6503010303c81d1f401284081700d0030a96400203840300000c1a0340820400480350070400c00c0610394580c4c03001d26800070307208810401040070421070041c180d10780600d1081240011400c001f01d55042139040316141c00c41d140f142480c120203140300b800c15282c1607140d6440d010380079441d640c000d04084d0003580c903184071801690007600203040d0b00b50f01032140d070003000008803030003401c16003510074100103210308894118516200b9003003400e84010000d060324203d4207034 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 693227967 1250 693226717 693226733
    0xb1006030c0f0f1b0b040c060e01020d081b07020a0902070510020c0a0b040804090c0306081618020c011805060702070f150503310506010806042d021002151012 70
    0x12482c130204548100b28000251220100d602640c411204100303100c0c20248094504840d00031101e045510000041c032030154804501a088600718034201081100807185130804c0c40f4103e40a500001c0456002910340d0441d402048154001d1080d0ad40407140018400240d00c90300345480001e601000409010407161100680c10900c95491185081e54442c100c1c0d003a0b9080841250200b40d407400100800401404000c06402c2c0c4078a603034070307180e00b015107000241100e22201404140e0104407034890080c00d50111600e40b06100c0c00b1444158a4034181d44e450604407446801030048500c0041c0002601078010240c514a0000c20300c1a0f60321103088865030002029200d2458400d00c403a2680c0811400700700c2e401100001041540405003402482c040060707201600c0742d84101304000201c2e03810018109100c809400c091000380c1b0302100552140c071441070107503110400c2074100c02c0560300007540e80692a10101780c1441660307940d1030742c0400c205170710402c546c40400e00d0038100003c2e140c03 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 693229217 1250 693227967 693227987
    0x504021305061b010c020c011202131505040302041406040f09050c0f04150e0f07050a0203040b0a030207050706050d0b0303040e15030a290105030f0c06160b1006030c0f0f 75
    0x19044880143c000740407080c29604040201e00158024010b030740102c1d64400c154901e109800c00003545041250a0b100c41c41842c0d500c59a5210b01c81d40c0f41e00f000c1544948100d80c011034000700144030100450a42c013203004410b4a50b03070302c160b180607103440346807036240242400260040080e01560190300305006041907088103c50f03110303a0f1803107888075001038426a10302a000000e400352203403800d00c0b10f6598540011749400c05101e401e000312400144c0c000112800e61390481c0721152a00c1e00c02d142600a4000d18000401d13a006044d00030400a901c403011744001440c1860600c0489060414503840b803045000310381180d03c000002925100551042000003400541100c0d1804810348403040c96080d541c843c460301501b44403842030400f6109240b1405844200d025000300481c015a040da9020080c00b1030f402180301044081c440c4060640070304080340c000c810b61415140c48200b42c0710481c0c0500803400440c0c5419925214140304280c0380d50b0405440d180c1d6010300d40301c244162904424 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 693230467 1250 693229217 693229237
    0xf2906030c07050610030614101e03240b0612040b130515150a06020a0f061104030507051f091809120320030903040e090f0304170106050402130506 65
    0x80003040b0001c0c004100e2288510b84059901800a04614146050751a01010910740305060000d00c94005075051400d4111a698118000806000c1d0030b5485503940c1079002404e1803400c802d0b0f00c400082d0001034503002e600441001c00c10f005d040e404110460080340c09107841d4001c5200094001644c1e0703141c40307401c2280c420344442c20307909543e5801c3c904000600707031110140d13a002c2072004048590726100441c06c41250200151410203c0007951a049074074050b01c0c0f0855904000148040d0341e000c0e651080e0704145099469840c0d04026075503400c1171140c036000c0c100c40940024580790480b8014240481581c0c2c0540251038030701c00b440d0200b9507650300d5403000c0c3d40b4005080042c0091102c1c0d2144101e076240450404241d052a0340c0c20b00c1180c1c003501d5442801c10411200d414044201c0e403d5074800d4840078800c3c8ca4600b400c40c6815400044040c16110000c0c002c1101d044075036000f12090317603280003404030340d89440600007680038440e80d5a41e2400805418801c910381040034058000b0 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 693231717 1250 693230467 693230491
    0xb0c07030206030403260f0a05070e1f0801090513030c0c0b1602100c051c031e052e0302040e2b0219020a121e0302010f290603 56
    0xd00da800061456105440c104d0104404440714681101d038040003040c98615003070a00210715003503110441c64840200400c3d1041c3c1d64000142405001b000c1c404c2001c60054000300356202050a080311240461f10180003040c8004000121a182809a544104000303071160014800e0b65609442c0c00d00e06000c200d403e80d181110108407100610040d14075100e806001c490100d110703006101d08101c8086d9100104029038120030003281c000203429041032240c403210010200351010031002800c568150350b80c07000314200c07040c0b924211504000c0c040d0b0354a00d4000c2d030f03410280c20b9800b688881d0031409400043d0a00040002d271405e54400d4080c0080070082e6003181c0c0400e9211401c641d10148030600020840010300710142c0d041201403114101602c8007103440c403041d000684c02100078420741440400d405130040c10000d00045a1080030040400b440d562542860064081c1c0030000e0841110f52070907041120602c0c0a216070748944c40720307068100004008600b400b00c103603c000c2c80032180e09 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 693232967 1250 693231717 693231719
    0x14220f05030d05040c080303071d0d1401020d0c09150f1b1a0601090b12070302120a023a0b04020f160b06121506040f0504060c080c130b0c07 62
    0x80c8040c001892260a1814001400e02d418a080021200503420101d80707948180308000d5500c0d00400c0b207941d0340102c0180140a03003441030000d1140e907070242e4003c000010402180c2010041500681a00100e102c42481002c40c0d0100403a4030350214810000c1400042924484031402000d00005000e000d1a12403c0b2410214140c010226190022942c002c0411071501541d080f1000351608040e003464101c80385441d081080305180078441722086106031440101d18218020340c1159851401e540e100612883c1c00c444540007508a414040c10001d416901c0c12a03200030708948885045c0004c140100c0701c00703800d001600602140900d6600103030308021071070b8400f800c070000d4001c65201003074140303841403141fa0844865a0180c6018000d4030490615140010007103040d03404030603001900c0c4010ba03181e40006015000380c0000000701440c0c1005d010038440316400c03a12030001e02e9111403116449000105c242481000502d421410803906c06004000c070102c01400b9500c5000c0807038030340c1303 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 693234217 1250 693232967 693232973
    0xf02090d110d0f0b0402010f111b060403050a081c05010e0a05060f06040b2715030717010b03150111030301090e0a140c090c0c0601060507021210050a14220f 69
    0x80481442078030500403884c00c0108560303002e952810060060b00e030448040b852484003a82e6820780c806070a414041096031f07400b0701d07122001520000d64103d0100d43c081e80e004e06250885a01100301c416001c0350306903194045c031800e03002c2c0e14103c40d013101d041701300396441c0080380000781809480b5542c003155039205020030395190009080980f03041c00c1ca0035a02c94003043ea680c88640c0303c0b039511841546660000707145989810204029522004640c0ea45e81d03903029044a64040c40011070542e48031450020850303461001c080c610552007244141d18006500c401984c54800350540110994030410051003240082d4100b21184898031003101c1e407901c0a075481da0400c00d40d88007143c01a9000006e00c01d002d107082e4804581081ca1815060301d0306003440e85941e2190b00501603002401400580f034070454940300104c0310007450301c205649550f40ea49100102401082c0c80c0c40a40b5810000c92041c80c400e084171060203034040000c00da10344550b00000200050b50001e044e41c030384950914040c04 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 693235467 1250 693234217 693234233
    0x20d1110021c0305040213050c0d060801090605010504151401050405060706050603060705070302100203192a0302040b09210f0109051e10051b04030c0302040f02090d110d 75
    0x80c005041d0082d1104940000409440805219a070703420981000d051001603140c4170301e40d20143d071a45002040c560740d4141c0100701c2e03205a030b0b904e04080b450f01100040400065000300603491180009014590307076642040141c0e9501041d020054503611820003442840d00703c9201c0002041c14028241551000003500c1034000340801c0e141e41da207500030080f00d4030b41404881c2c1e100e80385041c81428028941c0307000790780303450f201c1c950383c0350940c0000407c0088c2c030450701005d4102011002800524103581c4074000181e16080400388150854580e484654028000d0310141c901c010070300d9040800400410441c08100d401c444010115411ba00c804101d00b03104c0f40c58407403000c0700045488116454840d01e094814000010280943c0b00382e11040c80020400d0101e10440707660119894540e441c400c9540e5082900000201c100010000b0030841002040e00440e4000c5508010008070030203040180d1203200542a4040c41141c0032500003130800440103911304014140981d1620942e4a90310 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 693236717 1250 693235467 693235489
    0x160215040b030f090d020303070f02151e0901111804060b0f0307020f030a05030117100c111006081c03020919140a050102060c0a030212010b07120203090d020d11 71
    0x403048000b0800141c80c61500c1031941003042c100c000c0908000b5600002c0d101d01004d404e040400c07103c1c001922540344200311210801c0e2511000e00c130b0909103c01141c0791914401032488904180383d00043d50300e9018820751107210f42510002d4a070802010020013a0070301c50106d030350300c00c2d03907410080303491803011014000c00280040030ba070356410b08600203440c1024a008810440d8000c0007261505580401230702e045598900d00d041106842c0420700b0b0070704502c05501424945480183e500c019071040189102103c81402e591008180001c4c3d034040e1081801041c0180e4800e800c0c4030355aa59401441882080307502e00142071149000014100c180611402241130021000030b02c039451407070012600f11901100c94025881c0f81c000080c1d100c0c0310040ca030900400020445144450181d0101c415030a40c00c0f00102d095a11416030f0807940c2c214000039a0b0700034025012031002760001040701e13072080000b040f0140c489566400c04c18541c01c8103000b00c1c0c0f4580d02d0981c0403001d0b02c0e4400c0e01c41d = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 693237967 1250 693236717 693236729
    0x31c080a021c1a180103020a09090819030501060e062a0f0106061214100b180405010f0602060144013602010504150903020d080913020a0516021504 65
    0x103ca00c03c128200600d010300c014500120080322001040140e6402c50070780121094000040340819445c05d0191080c00b882c107000e050481102e40032440d2952580c411070586a268480e541400f10183c00d0107290f0003624a0880450040c01400b18402459107404000141d00000c41c0c280d61074601015080d075140b6842600490620400c103100c44a00780502d80840c0b2142c070720300b07034a80b8100700034800b03504080c401c0b00110400010300318641c030a12130754a08a16000b80081c82a540d486991041c44111403060b440140110000400c243c00f803561a0f9070050b0045104522808040a651103c0456071540c100f003040c840070031160142d03080c020740e181e40c1542c14244444c007031210105411100301c0120b104e0740c00070507840d460050780c02a003600c083d180070b500340440300c40100605a44409081c0c2001e50300900500c0003004229a1034010034440505450080b03040d58031410740420b0340149546940800c5092011180308001900c08009940c00185900b03084c0c50403035001d11103540540c0003d = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 693239217 1250 693237967 693238001
    0x219030605060904080a0e011202070f0b06030105040f03030527010b1002120706020d09080c0d020d170705090103151707080c0a0302060d0609021206031c080a021c 72
    0x800034400a846155030282e4203030752151903803800d956918030034440c44070448140142c03071003804d085234810107050041c2e54546100719030b81d01181c101603062a8000d07400b25810b00c00d05c800034402d400e043c042c41d401075500085441803050595402d4000c0c200040c48541928400e0300c0d05601e11040360821130048441400004601c144001804019000b5214020540d4881c151500c0107010020455000a4102000585480400c031841000d0842e072800a0304000c2c000c0f40e20181d20300040340000000310315801721030030512a1a804c1d0703000038808101d00310b862504800102c0c442d000c2d800134015070070305240000d10740042003540e82210f03102d500034580c404e0340364642d012084800c01800b805041140d00411240c018040025481301144c08003d00070540499462480c90703040e0094005000402029515001518211808030408a82d00d601c01e00c01c0150503079206083c0c0c84212000340c00b568943c0ca241d034810014001940c0203019400380c40c2010080310301c0c1c4988902c56480c1565440f010 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 693240467 1250 693239217 693239219
    0x50a080c0105070e010818030d020408030a1209020a120609060518210910110a05031e030709060302030702070e0c0d0c050301140114070204150e090c09220219 70
    0x4441d003192001000300c014000f5851110029a0304485655804034401d11003504070001c2031030080c254090b801c0a048c440c3d0000c1030104071244040041c01c0b40260360b5642240600c1c400300300400f80c418000000c0c0d0052030f02c9a0611880c445504820760441c02400c012850b81d5070b90b80d03014100d400490f83c1c40e070924907111800c0c000203801e1082e01e604220038652801d100c3e400c481011040d10405000c9480388440070f09148140d40a00d000c1d00001d038845044d102c000a160034142e480c1d5009000719141c290300e002149001c1f12000c3c0680c0d0140c59160303a0911024108941900254800b80901080d441028000200400015104da00c205440017a00742c407140d2045140742550400305400d0f0600000380014010b11500c210110710000003460051944590782050f101d440c4140c00707000e5086410090010143c074402d004c1c0030125818408072803440d90381c0801d92900d5000c070b40030455100700c0310000703d140809022040380c10550350201e040290000340e070028880718242000700104121140c4 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 693241717 1250 693240467 693240487
    0x60501050a080a03020c040911030d0305070206100605030a110c03040f08010b103f1b020105090a060b0402040509250e090c030a06080102040801021c06030308010509070c050a08 78
    0x10600e0300400c086802004160a0f03942c01a403102c1d00c1034400307805943e44200d418280054120210310f01e00001c2c0903030351010300c103d1009000d49001c070b8650b40075114420200b500064400040001c50324a03a4500d821038413100b111401502d84180d0815062078144101070340040148014001071222601c0008204d2600403088d00b50741d0719140705882b070401c1e040c90001c0142c0000b03e030b01388035210084090501c218480e880b0102c0c02a002914843c8981d0030a040d41d00303505511255580c03c000700030b40e90002030500d00724203071001101c44004580003204c800c4005051358003c250b03913140080000d810700351584080392055508940800d05c00482440e20030742d4401c482c88030003070241140780c1060341440c60004142405409070005104410001c0001c12910b200d40c8040007a1000301d0080d0343d1241c4d00d14030b55011350009008510b03600c0e031034454803040388a6442001d040741d5150b160050940c0c03a0108028080200a10b24020b00c805072019500144060002d481d40c40e02c030b401403d4540c08161 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 693242967 1250 693241717 693241729
    0xe03070315090c0f0b0a210c0f020616050a0309030e090c040f0e01030816031704080a031d060c090d0803040c181a060c071d040605060901060509060d020f0706050105 73
    0x3501200741d407941c19006100d0540d01c801100c0f50390096051508900702d9401c054a1f085400c01901c00c1000d107413145881c601d640c0b10440c0500101c2070341c01c50b90140c55016510b500010110081004503200708002862a070007a00301d88101030003070814000601c200c02c0030400c4034004694100c0714032400103050041003607403616100a4031041041c2c501560550741d40030442e00c28424a0240070041c12000410903100d01c10100c0013081c44a00320250341807626103281c043e0402412500803030b003000800600c04650408405084002b4402081c042c1c445a04840c45a0700020055800c1410700c1265000b14100c00000c50040f4410312150a21a00c0c0115064103034006c90aa01c0746981401186d941c440d0840820403040d0108890f0300e40d0f0382c3c5001842d03074604090341c4e00054030080d103070764000c400502a820040c400d5028043c140b04590358070b400c21000e80800d01429010500512041c01582491805001d070385205400061400ac0007680300403583d003000c1021203902e40c0b54401400070342010 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 693244217 1250 693242967 693242969
    0x604090e280c0b0702040f090c150507050601030b0621070501090608010308072a030f0b0f2802091c2013050a0212270a120e03070315090c 61
    0x250700c541c1604192a6240121240c2034880c1140303445001c1090015540d60340d000641180078080204100c441034501128502200e10901c000e00082c035a13401c4840340a4002c4418440e0b1010140c01140e00b180d5900c8030110010f005203411030f22000c8100c140400088441c5d034031200540c000c068480c03403d40010040c604907041241040030000041001031148016520655071201c0240c241c51402c0103070000601048580720b400ca00c000000105001e20b15420300008d6019036003104c0141d03900c900113448010181d40320f107110b00c00c2954078091400b001d07030400042c03140f039100580f070f0005440000d0f0369201c41c8413100140150b4924172004000f11408a422804140c1095420030b0115034001042071622050741e14440da101d40005010036034a40c111003d40401c007502040ca03092000310041240d031000000703a80b04105071010b415034503000440d00c8440d0f6000c00e190000441441080b180790841e214500d405104510002c0000381441d0044007210304c07080e10010f0070781c034141424400c41030b032 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 693245467 1250 693244217 693244273
    0xc050301090c0e04020310111308030304031e02010b1503091c120b0a05060d02030612061302010e0f092505040503030901052203050105040201030f1e0b0604090e 71
    0x25004032503001400c40100002207458680740720f00503aa850010038104180510b40121413443c004040800c80e6036540541078099084640c900c026440346041c0b650381c4800e503800307000326514070920102203810304100c1c12124590300c00440c9850b081c00200e0544602c50403d03040c089004800c204c02c40d8002c120031000d801d805c071582a100d640f50743c8064014514600b40c3e44900e40c0300c01c0a500662200c0040000501c00a8580b0b0360f80c000740c0e16000d0080d001650b50030701c0f600c0384031105102c00400048031402144030f005c030070500c2c24007503005407544120100e0031a0040da180108111a5a81000350303407042d810821400d0a41c000333852500100395500c0004824807005000c18052600d000055611078942801c6c003030f03541c008074a400046c820054060700c130ba0340211500402048419040380740128402c3c1ca0600c4551000c6c03c541d82611081c00f00340071885864003070124441c110750450300c030724100030303012504d05500e903850181a10042404080103500c49651140702c1301401c004107100c0f02ca = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 693246717 1250 693245467 693245471
    0x71103160320060109020703090806010e151f08071124090c09040609050d08130605060103020d0e03040807140303040e060a050a0e0f150a0614160b01030c050301 71
    0x8004419000480c10400014003041260700d1944901c2005680300c0e9045005030003250788645c0d5440b13005000e50700c940001c400099400d03030b000030242000580f003816030b01e907008006019a10508070410710342030307110051740c04240f84200c0c86010412001ea00701c50304040d0360354440c0b0301d48000d002d4141d140803c000415903000d4080034409211001200c840780200c04c0210655403203c3c0321180c9418080310780c25600014040a100c20803038540c0c00b02022604c91410390300c4403403201000361007528007198100d030b000b40c7c103085071000100c450b400350f039111031305050060074500004800c00c1262080f040280e03c0340c0c0700003414481000304002000041c801400201d61440150380829180d00a920450019a040c440032444a036524038840024113405481d14140c155101d90700700e00e000060b240c290400d028000880d441c085e40c09000240f007400036000c0e42c803084c50f00d0001c45014000c40c4224032010340901c1200c04a20100c0c211344009030045580c10550350640c20000c00301841c1d580140e2007030b8 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 693247967 1250 693246717 693246727
    0x12110f0307030b091e07180b06030c071416050a0b041a030703140703050f09010506101b06021803100e190f05010606020f01111c05071e08071103 64
    0xaa800124401941d40c0f1810100040d114904098980401010040711000c1c0a1504848061000910303404030ba0042c0b103480c103c1101c002c07030311040310020501c41c0d800110800004400000050042291511480c2d500c40c103103c078052541c0c00c001e01c07907420b0441410405001c00103482c0c1040d141c80585100c5d01c825203094942842c41c0085007000214040d1464040005040c0700e009074002c0b41c0c401c0103c3c40612040c640128020010070049628950114401001c12084001441000d1155001804442c07183e2102d0071b00782c13242100d2400c41880d0f990500007610018142e400074001d004582c2100e0240820354004140c02c0c200c181c8250088185008894030903010300007940b5561122440c000c0d101101c9609003680302410a84002c2d01641c24500005400c550019225030620152802000340d41e0582d85940103030f04c0381c4031201d01d03c4810705000310201c1c131081d4007007900010f9500340031804210045098010008100c026004681540200b18149401142d00c12208402c04e025500d49 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 693249217 1250 693247967 693247969
    0x109110f0d090507080a080307032f030c0c0a050d0207060219060c121503020301051006091a04080a060c030c0314070815030a0c1a03091207020301090c12110f 70
    0xd409200c50a40d086030b1a200e00000380b00c01407100c00007402c0d2050544800013100e0428000d15882954514002403030000c050411090258019000c40410400358110310301e48054041c1035000505070000f01103042002c4403401004110301968507108401510b80c1914110000c0d0078882c041c3e010702c095421801100c643c081c803a201c468000d5a02500019280b140b203a82140c0c140d030200c130300b41c07a01480c00034040d502d103c1d01b0382010210f0b0700c2200284040c2d43c07420203d40912540d84200c00200d81c0c4003d0074000d981c294261381c030948481c210014106950744489503d00000c45000b554015521401904d00552601906110006d1410144201c10150b8420b180d58080100708104005035503000c580540d0b028030b0098080c42e401022900c0c00c9085082454426985100d9403040f141c1c1d00f040304007444001001e8a00c41e002c81c8010f011080400101884281c0c00b64100b280e16560381c606081c0003680d111001c0018114024600140c036203a45860324100669038401481400b06980404803 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 693250467 1250 693249217 693249247
    0x60c1704060203032406030c0306030c270402030c1f180302010e060a09032f0301090822050d0c050306060109080c01120906020307051c0203090a0f1406010806010911 73
    0x840449441c030342c0c04039181c0c0c445e100c500c80c903003110b68800400400d01280006d03080c01b075402440f048003a6800c10112508010b01d088030f0030700e00040e445030744540002480040c1c4030300d40e1080c00a070a50b50090010b500180000340c80c110200d074000c6018016418840d800801405080585492100c82c241076800191004686504540c4101c1001441001c158451054440210352044031440c100820229142c031400450422101c6100f04c032011a6135803074140540d0740000d40120607503240c13007200300d4192054150b0210700194840d0403c2c0008043d141c01501c3c0c41d00034040c2e400740315032609100070182007420240a2504020711700c0014401c9440100b48404081824240142c86060369110303c00644034030078005d44190b04c040104001c46070848001d001d5244a425000c04001000d080c9001700d0100b036541d008541e0101c42c2c03600002d8400e400183d4524010344001b44448084440d640c82c00c2800d0f00280c40c5900240010460f15581e80103a0400d015840c64440c20f25500c8545c0c001 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 693251717 1250 693250467 693250471
    0xf08040206030f0c090a090b0411160210230301030b0105030d080f070221041a07120804031205150907020a0503090f04180f0b06040e0606090606040f060c170406020303 74
    0x403e0340c0444000c9140446030328102d990844001d441a41d0540e50751200200400001c0750301d80c025814005004403d8114070700301c0c0c0c4091015410003405000640038040c4850480121100b1b00401444480d604070031290342801c0c605080c281942d4943c1103213802601d414040c0c1c041c034000e5020380c2111100e142c01c207920741d82c498200d80c050b05843d0785088049151641804400b034045126002c08003080307140d08020003c1e112440d00801a1400200031031342603114004006d0502e8107030713903109446c2c588074201030b0b41c00034041d2404c1c1c034507050481c201d001104d40076146014a2910041d106125041800100f503010070f007800504401e1406403680c40e2a44144002c0700c0c49030380050900b95490780c41c1d03400b44e210202c08a901640c0b2404030b16109040c080244000c0d0b62500a1074000303040d514060052020605950020300040d44503141031104010010f81101d500410910010841180006180c00106915900c207400c4459504000c0c1c1038040030000029400001c1100348032154001044903 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 693252967 1250 693251717 693251731
    0x106060f020d0f030b130603060501060f02100c1412090c06211f170f0a031205060d060c020d14030105010e1c05100e190b15060d0603120f0804020603 66
    0x184104080f2204400624100a40d070f5809910300c285429601e0103a8040300c1681c0c4034035802c000c5641c03039007800c2c3e0342200c6600840d00140d000c04000c1e54040001c1d040000e0004407828001c9074980601a100d101c2d8014595040c1e4503140d030740c2001007241040101c00310880080d207450b0705c2c214009028101104c00742e10486070140765180454551003603580b0300310f00b03035001400005071f0031780f241c1c4117400f0030306510b200c0e061038880c00040040081001ca601c032001a815200c103101022506010f03005840028421540258048a45004601640030320600315038680d011305105855100080e115410f46510110001c2c01480180030503600042c0302c116103842210258400842c0c84050f44090381c501c0c20041c1306005290302140300000c59045045101d481c0f0040e02c0c5010740c2c2c0442c8101c0c00b8030180010780407032102e502141804090510b59014684003800c03051414141c2d481038800d464582d8001c8075809140001c1b04001c560003c08204a03040e00c0c80c00c3c04150802d60006151400060f007c1c0c = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 693254217 1250 693252967 693252977
    0x6050a031b0e102604020a060e0109062d0e18040f061e02040306061401030207050d0f050403081306090510050307030b0f0d1505010902041a0a02010e03041202030106060f020d 77
    0x1807203140c0c000c0d4000002a02442402203250b5809689464284c4003501d040380034480b40500451024052095070305403a40680d03c2d02d207617a261050803100c46060403a40d8007070382c0c2d10030200c54004d07004003204c0102140c40d031502003030655200c06115000c44000c400c0c480140300d14060000142c140c050848010342c00181c003045071891004008a00c1c1807040c1101034091001074004104050358105030f040700d2660502c1d08883c41c1000055003603220350040105280c1128090190b440d008080c03d1607007108501d001070401e80c5a03502c603082940000e000c4030710140071140030848a80c0c020411000340c901034400724858030148502900c1c0e07010150480c0c00b40351311204101040e880c1c10015549422004140140b03036000c6042c050f80124004910840c2c484c103040021510580c00d000311170440b0351080c0c0702e0131501070044494a017900040c440704115500c90700c1c103035007925040010700301034040b5898501c1000c032a44101400c65030582e015034180055400d200d440e0a4001c01c40d02d0010360f0728105 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 693255467 1250 693254217 693254239
    0x5131505090a080604050105182a210715090b030c270f0f0a050105031806071e03060e3417090c1f030605030706050a031b0e 55
    0x4199210701030100140c1e0002c104031400145603800090090040b4010f5008003d140c461920350800381e9001c00c0000c00395801110a10450300310590100d45c6c4000f04c10081e0500103001c0c00040d51080c1c0c080d82412515581405500005414000c000c0203122581c481e031000044e000000e0018003e5100f1a080054048000380d40113400d0400c03180b0165920000040340b44022010103401660040903a0082c040a03051422505248104030b0a80b80001e210340155842c01e4011509079000801101103605084e03d07000500d0030410401f8001c00c0b01e0784900780110400300c0840140140003c84208160600300100000542d44500c250844456204c006403804030b00c0b1130b18110244682030031040d42c81142c0a8906960201307445110f440c8106008209856403071406a60b0281008103030b0744214514185800804501041400107119003400b0403103964a2000904002c551740c803010105400080e41a00b450745480345561550310341001d050380d161840402000c2580315504180280310f0910 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 693256717 1250 693255467 693255509
    0x40522030f020c030a0c06020c040e06010b0f1b010902030f010207080301180e06010e070e030109110609030715121b0906120207050a0f1109070e0d0c120506010806070513 75
    0x211900320b03c5000750840310010f0b01443c22100ba07113254480c0d075005005141003150030f45000e004502c0c1007421a0002c1c50183d00300b014140b42580006002000c4600422503044008203010012948088602c00040c2c88100e90043c5400c00d10305414141050740b041001c00002a01c601c02e680c1950030701c8070810406402130070101d00504230340e80700c0f4a041c4501000026883e010b100c6281c8100c0465440e04428215801414281c07050b02000409803c0128504440c1c0d06201000d000d80790001001c90f403280365503000315104413810000620001d511230588000d0300d10356002e40e1510306003205191110340031041009003c0140313805101e0802c100c007000203030032000d540c054030041d94100c0c094403001c4603503190045d0020b04d030400440c3d800410b0114141c0a10b88100128480c3c01d086d2601801c00e0300e6101000a40c0c401e481f0222400b82c0c196802181a41c074202e51440b0a5201e82c00514841d4104140310745051300051980c82003000c2045a4460740c144007049408452041c240c54103440507000d = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 693257967 1250 693256717 693256723
    0x20607180801021803072903061c06050105030d111e0f0102040609090c0c1e0213090b040615080d11010f05090d140a1706041407020705040522030f02 66
    0x41e204604560010481e40c00141c51041c0b0b2039409501101226a0380d0380d25803240482c4804509200e049643e00c149150019680c0401035601600051041420301800905403401e014116002d603146c5030f0340c0c80180403074101040350f450a0303101b60812000c20642d01450b00e9885e100000f140c1004c00a84a510410940401070781039059081c0d4000d42d01c9030f840e4000141101001e100e00c0c2e05460402003082d003035900510558032615041401c006140320746400804081e40c5030413007260001c90405c102c11000380284600c1c3e641e58840c5c0d50b009011708007418010240c9101c40494140f000944c10100003602001465811130f020714100703009000c441240c140d006000042031500d00c1800c08041000807440070540c40849819030b00c2c1d462041c0c0008000030000d004042c0658089880754210f50280d002e100b0b1420360100c4000c0020800601842d28184081030079180c078805640041418030661070036000f1603510040e140000340c84103c280c9140200d0410500c0b000c0c0c02e00c5801201c1d50400c62081c = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 693259217 1250 693257967 693257969
    0xb2d040b040c0e0f190501050c10050c12150a090b030102190207030b150904020f0303070c0603051e0f061908060702030304120f17061c050c10050a02060718 69
    0x107008020400c0941c2c8040c0240c80c0348a0000d1007280041080c4c3e400d881e0424515254000090703441d0031040c02d107401502c442d4400c81c40f1200900c40e07898440c94000490092603c505520445151079100180700b810805602901042c100324106820782e8058880d580d0481c01c90b40c0c8280041214607038540802e00901c1010300718a0005c0100940e284c500e50000380c040100c80c420915800c0d40e548001c42000810344610000c2c0d8010200c2c4003040c090714040d00e802000410003000d030380c84d02d0860b5076000e8880c503240d0b0080010a44800402000f1090040301c0800e6a00000840c8201d2818848400c0b262100a0203180b15a03850800d451520b0a0b41e03100001900240c000c0b0340b41070415401c041d5980e0070407a4103c0700441028210f81c9094801e041c05d0b0f20340c01c402d860f810408181045900303890100207240d0f9070880c5c5802c9004600c014140710b54a01c05028a0240a9030400310050246095800700715000740034003004880542a400035089601c100e1034034182c12400c5481d01e40650103400c1e = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 693260467 1250 693259217 693259219
    0x6030d0806040c11060a091a151527030c040b0a0e13200f120c041e02040b1c2013150807080106110d110c040c020304090b2d040b 57
    0x70070003000310f030782c146e0ba0040da101b5000764a04040d882c1c10301104000d202080380c0d501da41c4008810030100c1400e0501d80a6030883c202e01003181000850b0f40c000400c0f031517203081c441c2d8101242031141c80c507040034440c0f031440032000d2301c003440040b61501c0400e070221458400e4810f20744d0103a0009900684502c0c035901d03016407085039404c1c2e80c12001401c407a100f040000943c850594a40c201d802845c0c502180711880d01154090700d81002c440e4200001003400300f0b0082d081030711a40503a4140c001510041019056149025032580e07071030100d005000c140b481c00014aa0726004401c982c104484800c00703001407080c040c0c03031340d1141d88842e46001690b80344c1c04806000100803100c0001d0ba08a25240d22501c0b1b07958034900d240e03070380e0a030840b8801408810301c07a09030004500c00c2282c504c541c40550700301d039043e4212811a603074280454107c072441c0d21600b0041c2c00104041c0201109806405011a81280c01c41039443e0000c0b4071010b60005003069a158884a04020000384c0703580c0c120000c4c501c0 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 693261717 1250 693260467 693260473
    0x903010b0d0305220e041407032a170303040807030e06040303030504110301110a11010b1008070807020f0d21050103060606030f1e0c090801050903040e06030d0806040c11 75
    0x941e5103805016500301c40c0b01005100707070500481111480c203240c2c940460f9207004124400340c689884e482840f000d00b454281c40c60007004804404284e06130143e040502d45810583d00801c0c940c4401c0c0c01c1d5045541100030a00580380c4404c00e014000001d60760404d41048081d40d40316440d16094591405016003503070004000b0800006241e09540403070300c928060054034036070420b800101400ca4006a00d80c2030951014410aa543c502c42c000c00e0030451401e2000240d025280c400154542e64554480030004000c1400c01522a9008140b2030b0080201d0006080e103100d2007401c0c540717402c4151082002c20200350a0b6001c1d650144444080300070001c0d80801072541c40341001c00107081c003401054046401c0541010714048a4805c1c0d540d5080c3c00c0c4591541c0d40028000346020703002a070b038440100301f481c00f000305040b0000e1140354003a1000740015542e0314902070704d900b4101d0009145520903000345008011064100d010703903a004000706c800003008001e202054444000030501208544 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 693262967 1250 693261717 693261739
    0x3091203061801060c060e1c0e04060302130e010c02060c03070507081902010608010e120409050a06030b070f030c0e1e0109090e0307022b0605060310023009120903010b 74
    0x140c005c050026806c2c01481c083c403060011025141c0d540501503007850180c041095142e010500c00c0c42401c1c1002401400818101d55980014080317036004003564030361603514080c0b80580c040912910b0322018150000c3e080d01d2070f00e250400320314000145018244200000d50381c017040340160485458032443d07626069000c2d10045e00a0081040e401004d01c00c0d8030708070700d90b1000740002410a41c021440c0d21068039060800304681c01501014003400c40d09901c444000c00000c1a94203c41d102e011240d80da10300c860b000c2e260040c00d4408442d80a0280000d894450030651150202c0740041c0400d100c13243c600505150048690400960009044c84d103481c80e6805001000302c01007050307500842d4801c3c1040c0081e040703c1c422062005914030200d00010708000000d085070091a84400002e080d184c0700c0c1c0c039a4100070180d912124082c01f400d00b5140c0f20310300b80c08440358201000350441c1e518440d540b804c0604a6940c2c03405070203c51801002140d16540c565094005441c203000180610319a4 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 693264217 1250 693262967 693262979
    0xc0201261602010204080304170c030102160606120b070c0201020a0203032106060301120b07090e04060c02061305100b0303071a01051f0e0f0f0a14011403091203061801 74
    0x1101007941e2041c19080c0078040755858500c14020381d0b043d5503411001d94a400c0c0b805005910000824400d20b134030703004942c000140d0380d8080c806002c544c0380f0740034103c100e1100c1d490318008a9210760000c26049001c151403401141c0910610380c1d105a032420b0100c0d1705001d03800141e1500c110304074000c1d414807001a040c1d401d0b8000da0070458002421444d1440301e0f80b44c0804128980c0070902400c9407025a09110102083c401c10300140c10035614180011020744902c0800403401c4100c0b01660855110000410502ea041016650240312a9076a00241c1201e5448540740c611148205005945905060000b5036052088880039076100044d08001440d10303c031800020800d2041074494490b030000e030100c0203600030401d80ba60704159612620301c1440f204000c000c2c0490102d00e40c1090704d41c2050641d580710345c40d8840c05002902031004141e480000010003182a02004e1041c0c0c0009005010990320002080782491488003102500c171354956000c1080203580404000540c80140000621 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 693265467 1250 693264217 693264287
    0x20706050a0e070909151e0c0f1b2001020705030f0a0b070c03021f021c050105041514060706090c0f0e010b0c0312060102012009090a06030308070c0201 67
    0x9180b9154140ca602559550f62801251044a0060060354a03c0b100d040c4803645039001c8042c540c2c0130316401008400244201013103848205076400420890108091010340100c010503d1544070804400c902183d40e072012516502d40502140744e583e0b012440c03085a0081c0320500240030040e044501c8a80c08102013680c4400720381081d50442286004280098450492413031010703096001010702c0b94071400358405600c10799014000341a03007444400c541d103000582d41c026240f032002d000b049039410030701000200c8a00300ca0100d48421161020421003c030069014655141110110b40b5010141811070140c20680002003801e203940c41e0200d003492407040e549060344c00c817518020550b80c1b07407405104940310340309481155070310510020207000e5003c250168044410b01c00400d0101c1104285200410150b50f07488842c00003040c0368140d406c1c00703171080380d0046000406004461461701d0182484030040c202504002e00e0381071a5066900a045203992880040c130403a01101c4021a2580 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 693266717 1250 693265467 693265481
    0x1c05060906012307051507050c01290603040f020402190201140c0904090f1b0e0c1201120807120509010206060109050a0b090406080111030709090e0a020103020c01020706050a 77
    0x300c00c04060340030601a502ca0040110070310a480b48400a100c1c20342150003140d0442c240031030b441d11034403018800e4400140e10850042040c1c0e141c90b620f4118051150342901c40842d001c1502c09040356605030200d1100404082801054603201d90b01d4603542052100c5c0511725001035080750000502c1e003600e402516076504015015402004840207180e20688014025540441d0144003407050509620b095401003204070b00c60700310f201c1031171030340d0340d82c003000012212840581e40c17091581002094100c141d210f030712080d0824458174003600b000580b55400c03418041e44090303121140d0440b0030420070700100c44201ba04145d444186400c40300c0020140d030701c240b41003401401024049549940a11301c500c050f94001070080100c82e00b40b180385041e81c0c000b6500d1581c400d89840c80010601802e12910b501c4080310030320940c1d68030304001c02400c403502541c0502c405c50b2511403908040e11002c200342c01480d0342440c000d81d550741c5030030351180680030b01507018107102c3c901410301c402c010203644400c1d = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 693267967 1250 693266717 693266719
    0x3011802120703020901140d1202011d0604050304030308271c0809060a050901022808010f08030f030a1d0705010801051504031b0305060103030909140603100c03021c0506 75
    0x2508903030aa1007142d86452041c40004e400450100041c48891001d03203c0b01035010024002521f03808032900c405680b40e02618100000d0703556844a0440041e000301c41103020010781c00208000d080c02d81c4c8503580c80c4641d1002030204003c072000f048021030f100700d4034408081400c0c41c6102c5c1d03520560500e81c4403014051203003040c0503082407010444e80240700c0c840c420076003600039000a0f0b9481003400003400c030041036007100395400c12042c0d0f140f13061000020902c21115160b150504d01c1600c01070110807040c2c101080521017448100079100001045482100344011299269200c2200040c05015803c0620408080010301030a110100040d2074003105c5090341c9451050b640d401c04d0117440c1451404100f2072079801c0005101003039500c04049108600360040d429015034a17100c207820000c3c2a00101c000660704801001504c3d2640a110a858407000f0a04100d047c0800000d03603a49040d1174088582e501c40750000203043c02641514051143c0e9102c0600c1051400e0017003004060464030304d = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 693269217 1250 693267967 693267979
    0x60d1502040816180e120408010204050315221b0e0901060f050a030b1b03040b041104061d04030348050405132304050d0c030e040e070503011802 64
    0x3c0110f540c0b10030110700880d422203000c4c081410001c40e200000d0100c40442c01c0c40c510034940380403181c0e8081001030004002c0800010303100c9080c007040504102d01214110021403d1000340208074007805010f07480401070b41d0702094200c070145400d2455140603c0c00e81c0841c100120000355003949643e14500c10520940204500c3c0c1d00e9030356000c0c555440e801002d0b000340480d40140001038000d50040c2d001020000a20a0003010282c04000d60303100700e07821214042040b05001c2001901c3c5000000320000f12000d210f803505003034111107803a0034800d0401302850300f0b1001c2420305020303a01509150b0f0240c01a0034544058200d01d140300100301c0b81c07065040800702c00c901a40e504c0c4650401c0c111a85503982e500d82440c08081102c0b1a040040318502d4681c2c074848400c2d00d401e1030a000095440c00401c100c1c05203003904003a0b0800d0a10950002400804460303400040d9101c88607001d14a411103000036185400d8841910781071903034000b550550b1038610007800c00300d044c00302c0c0b00816200300c5070 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 693270467 1250 693269217 693269233
    0x714070c03030e10090b09012c150306030d0c030e04090506070e041e0e120a0e3f070305011536020f07060207060614100215060d15020408 61
    0x2804004c500f82002c1000142900405100c00304000e00106600d040525001503030844103030516903400300d0350103071503000084a0a509014100101e02411069002c050982145840b03408170b511010050109010000c260380d0300b500300360041050b0300c05482c010b001040071341c0a615045540f0042620703000003065174034840e105940f91901802d10742812084407803030503481245c0f10780040c103280c0128441500900914401d240c28140181c89065141d83d03c000410b0215024801440c0034003400d480203065601441082d203e030758400b01e0399415581c3c0e42c0c3c1c0d01080e40a6240d800e05045400052441d400e003d003c1413454800500340081d9940c40312810b094001d0319000082d03800710001e500980001102c60002d0204103070703015149080d851038041d813400c9000d6031401c04aa004c2c0300100c3e5460358403103041c0600b103456246541700380b40680c2c101e0b0f940c40403210040c3d42c3d4034031801c0001010704060001241900e03002415682c99621414112a449114540740007035085801a10b00324031541c14 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 693271717 1250 693270467 693270469
    0x2010e06163b1e06070f0f0503030c03071b021027060914120604140102041502010203041109011d0c040801020c0a050f0c0d12030605060d141311090714070c03030e 72
    0x181d22101d18000a0213540340081c2584d4664002c10044c105a4205120072000c8010403400d00085100d9504941041d80d41d182c507100c00760006600d2104103086004002000005843e99010b603c0701442074284910105111a040d0001c40c5a032190b07540215080741c0001101600b00740c2150550346204400c25115000400b8405400d032101a44405540b00d400482c0104400f02802c0542030340b228000741c682610307040c1011440e00844400c0006030760004c200000c1c007580c1400300c8410754080320302c0e1180303501d8003207084c1d800281d080403070b8103c800c0e050104149605001c111401001804002c0d916905a81c841c00d44440075000160b8160141c00340700d81c43c140303000c070b100c128040c03008003810000c0c405501c503482d103607503000c0041040c50740c0c6500201e229503d0328044e0000c8081907a0110340483c48000481c20080d0150030016012200f0400900140c0011180c2004660a43c1c0d948000d41d41c40000300d42034000006000c4051000103400000d2140c4e00c442c060a90303000c3e4444d8980702d03078280 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 693272967 1250 693271717 693271759
    0xf02040612110906160c060818160603020d060503060103060603021f02030409050c072001180b03010b090117070309020a060c02030a1506030c09090302010e06163b 72
    0x2c5068800d40b8100440001032a00c4800b805600c40300e050810700c004030a581e0030445030203681110b0049a00e9108000001e020240c200ca00705403030001070080c8005a140d106405644ea0007281d0900da0081681000e01b80a5801540103100040c1100d00c50751707503810104001c1160b40800e80c01441040e44000c1c2c3e40c1c042000719510503180c0d038020b40c941403420042100828001e0400081038604209082c0407440d12a48000c00040355190301c00001081030001d40b80050144e10388451000150b07081200182c84001c0d00c0c1100d104130111a41c840010004942c54400c502c03000e040c058004050082a5134164000d4800301c1c42500c011701c000c2d444e94070a40c1d6a480c144400be50650100c002c040000b1b2100c00c1920418a81e82c1d00030800703a440713988000ca41a6590041601b150355108501c040c59424001c0e40d000d91b64402c0071f07000605180106204090807000b40400380440078030444e607013a928800c01e103440f0681021a0041c5000784c0221030b01401450180ca20810600d800c0d06d42c1940341d4 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 693274217 1250 693272967 693272981
    0x1203190c020f0d0302030612010f0c03050a06080c300c030d08090c13020903010608151608160e06070809030d0f270e0403020d1b0314090a05040f02040612 68
    0x105009007045250341100f207002e035100920303a52300300118510352003104009008403108400c40c441c000c250203102c40c8004089800080a02030918248041001021004106c0c43d041600a843c840c8a01c141c400010401841e540c00201801e840110703007680010001c0340c2022294401c50a44a020b205140100d80b0b03e10291000302480e0096040b086051030203c0c4e100e2a610170800d4007508209003040083e08543c03107580a8034040c1c00c50181b44a81380e0780340c910700c0e0744940e41224803000305c1a400c030001d00d501c100510540c1084081181d111010b0300a03201510340307600c018191079030340440f89064400c80d0402e5800c030f4000d12a456076500b6260080c6100911841541c2c0c1d1078070100307264908114002d0701082d11404c071164400c408a01c00102081c528400d5001c0c1c2c00620380c1d4468a0310080480d0030b8400070044200d008001e55001a034007501d000034039903086c00e60540701d03400080064030100c501c0e030290343d10a25014030080f132010b154010700103c881c07a4903452402c40340b1400c48819208a = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 693275467 1250 693274217 693274243
    0x40b0406032a090512120703081e011202120607020c06160501050a0e0607020f0a1211151e04080708030910020304150c050a120e1203190c02 62
    0x14041801010700c65401030a003064071801900b4500b8060080703000c00c4051426120001d4154642440301d4104503900f000105044001488864641d044090460150f08402001c0050000c0412103005030540008904200740e030b0154040d50351090ba406040c1001e0b0800c030701603401144007612071400412040d11800498000d030001c003000004120b00303640a0345129008500d40300701c00000c103500f407203080c1c0300b0080450300040b8540107142080c40d100d03009000c00704543c4444418601900042413031103100e58400100140c0152448061302d402c20b13041c421441c41d00c01d5201041900f0b1030346419900030700260683e222400811524003023044000c59014000040402c50440000c00000095a001c212a01550b0400c0c040e1200748042c0c0c0d03c107450035a41d41b4070b5412600404040e0f4801c11550900904080c0d2070011008009000031454802c00030f60b140d40c402c0184000c00302446000380c070608841249036607180070b0311081e020184220070080c1c0d640c6050864402980006124441d60074 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 693276717 1250 693275467 693275489
    0x91e0c0e0901030b1b030f01030c0510090e131a10060c020a17030f0a0201140c160b18031b0609030304050a0b07020a02100203070204050609130825140d020304 70
    0x1c2161581c43d440d02c2c0c0600281c00c103a1114075280340c42100d007005180103250444c7c1c0100c0c1c40d4503508011401c000c0681220b0702c1800071107901c02c02d507a00420610b044071031024000c09250ba0b40c078280a0b600ca209200030b00500c0b40c03071400a0b114607489543c40d00c20107403072098007142070300e0704030450b80c0089001c00250401216001400510444860390b1602c04c1e0349000c13640f8207210046032821340c0e0408050b040160791100740960540401c1c02e122584640d0713007490ba60810400701e660710741c8a100340e1700c00f9280d113240d513021445d0708104c0800040111540c1003180e90ba83e803440019440c241c4004d1454096024100c080307410b0765404801c9038020340e00339009011a1556032601441d4120140c100025849902000c80050701c5d0100c1d005902c044540146880d021140103020a4074402000346201e82102c0003049210f803035058500d1003980e04030030a19180c1b4900304000103c400701c450010702c1c5d0505842d40300104000c0110300042201010161a0481610141a6540d016501618080349 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 693277967 1250 693276717 693276719
    0x20109060f0b0616050307050a052415060901090b04060504050a09020c120a09050d030f031406010212090f06070807151107060c0e0d06020405040c020f0a110a091e0c0e0901 76
    0x1302c5030000b40416001d0340c10b682c5004a9640c0d01454003424850850702da800805945002103083c89521201505e0741c008105036150a0005429100c0440d6115124580c081880700c05648120302140142c842aa000c035039540d1610005003568100384100761044080311000301d0040c4c6a8000d40b6100c0244400030800f400025804030320a40142009104000381550001070326a03034004c0d0307a01c0040c02030721108803500003068001c05481030164141001d5003082d040c85103070f0343d00084003a01510181c006644400d18032001a0001c1055690740340d100c5008030b2400d0910504400411000e40700ea0400312113560104441300a550040944040580d01403020f40f0101c0d496802c800100c500782e142c0714450200190011f40c1c1e00380031940a440940d0301003003e10503420b0500c62504850241e00060040308042a5801e5485040080083c8905580f084001c00c54880d1010a0003806103060140040e40041403006860345c420002c01c0e24040c20105070000d114000c851427a0300f0100540303c6d003016 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 693279217 1250 693277967 693277987
    0xb030c0f091306060608060a080a2102031605030415140d05070507021206040b090a23010b060c0616210903020c182e060305100e07020109060f0b06 65
    0x800300c01468600c1c0041d000481d08000b400328030491001d003a441e2106c000c20b061120a02421102640120800354480030071f080228120803080d8403603032040101942210001c0070100d0a5003c0c08052400f03841500e4906400c10001002034401d548558003144005410500102e581c000d1014403070740070440410036143d8046042c0c000f0391740b1012030304026150074116070100b20705090b2080312881c9904400c1c140410440d031000100d800400480040c03520110980760070004001c0c085000d204460b00314010300e40c0f207000b900800c0601d04000c080703984821603040b131161640b80455800d00b026115082c4520628050369135640610b4142540c143e5025104031594002c01494409600f98801c81305c03840041d656100f282a0074180c0d04080410301d051024900783d0320004402200d400c0c0c0886051a00c40a810001e0b2008890551501190710b803100018100129440d41085010001c00700800c000550150090701916115440812003001026814000c4462000e00154002800c0080c2056 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 693280467 1250 693279217 693279229
    0x3180b06030607021f0c05090d03030b0f100e010c060605060c0d1407031409180a0e070909052109030105010306240305030406050d0219020105060112060e0601080a090b0106030f0b030c0f 82
    0x8101d407d082080c641442c1c00e00003001c0c41c4a0701022000292600355000c0207091a80c0c04070582d000642d800c1d03e00050082d4054000030f059100070781048408202041800401d402c02002048060b04c00c0750384980851906440b01c0c0c0200d04100401c000140c8405c03113107800070440b048941c0560307580503007501c1c100300148964080c8070301c03583c00201d24148506a0103134521884c000c911600700020071490385840700f420141c683e130209146a00e802d15501c04a08041420340400401003011560280d040880c0e180d24001c0d4080740b42c056103000c0010040002d42d51200c40500c3c190081800044212400010b10200c0c0d070000408a410500c020401c10b40070f01d025000c0004180d02c05030810803072880300d90039041d06c042c2035001070791201b00b03025280d41c00541041070024048400d02c601030920f01081c002d000c02900003410040044000303810b4040c2e55000007000c5a00031102021542e65820040140c040d80102280d02c614008032000c6a1400280119109501601102009155404100c1 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 693281717 1250 693280467 693280481
    0x4050405100f0e010b01091d060312030a15080606010c120c06091208131106180301050403020c09011205072c070c0b0f0408031603180b06030607021f 66
    0x4481c400c541800a10401c0c0b030180c000090010600002c20311800b039601400c0d00e0825124a040c00b0383d500c001d010542e10b0361014910401428207100c00394039840042480c1444030104c800e007409000c002d21208400d07a130003064040d42c0452000048680311200c06460700e80a0f00c06a01140907100028005601c400c0c15200700d285034204441c0c40c00084d02c41c1010b03601c60300421034000424441f04c02c04660003010041d00441081400c0302041d440b03590b000c5d4100c090062051040c0004140c0303414000807081031400d1204041d000780228181450041d65807849890103e1040c01020b0011858480d01c050304c07660560020000e00660740f41c050080700544004920b4507078103450408010304504203030701d010b001344e025940328043c182480c2813460701800080c1406151500d144244030201d0106030960f034004d034403225203101d5a0342240c006e5005040a0750032060390040c2c08a510103000034020a00e11825095091754002d03170711128126102d1809100640707410128820842406600313520000c = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 693282967 1250 693281717 693281723
    0x91606050a350a05010e10180b041d0d02120d1a0909210f090402030a0608011a0103110c0604120903080d270503160f0602030405250f0302040504 64
    0x40a10340b421080c030125407082c1d20784a86280074400520410301035a10526005004107420220349080012065811003090b00c0f4603403000e2070051405c291088207501c01280400010010010091824003806ca1001c0c220b2816005014509a4208040c00841c0c0760b80804042810103240c0520411280010155404034081c24810740416256944603501d815004006001c003d003148081d4a00c110004002c0241d19080d54105101c008501a009010b540000074101c40168491b40c070070a948005041701d901c526215170030548000302c0310180c4020b60003d00b0085e81c0a01030210300309207548540c414041c03445420350120000a010075581107107401c00c1000c618140b5021a07481d1202d80260700440c01c0c405555139a21402c6600c01501178242ea000b200e402c49507003044035191503840d00e030f001e0301980308002200c0c01403050400c83d410040c9020507030f004101315184e0801e81400c0f0343e100300d03018800e4004c04654005070184011203c41c1d800301c0704009140010380342140d003403002400700a0821 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 693284217 1250 693282967 693283007
    0xd06020c0631022206050d260a020706140d15080c1917100204081e0a03170a14090a02090f0103110f0d02090708090d030605010e060901020304050d0b091606050a 71
    0x310707240d44c560240c102028008d0302103c00d010010910100070301215510071180c60410425540340c96000b00b0802e080b24558149006244410004281240705268041150511b000c41d1101c000f03000000f000207a9540703804441000304070354140f016810310341100192042000c0420000000710f01c45c0160355103803810176682050442081c0c0e8060740c009410101c8190007141000459024000491048410400040103400c50546002d8108405460326075035102c0c0e640300007118903c444d0400c1d00054520014035400c0d00d0000505c0e0740740d4407004c400301d115070341105c0428008000070b050141a242c019480910070040d20040004111040049941000c04072100802507030b550200d044c0702b160305803191026031400e448441c1c1010f43c080400c030107151070320a040c012a40c1c0031070381241d0080c040d140d05a450003000c0050303180d40920f91055074018400309090701002aa0400759018140c2c1070210384802c0310812030f044100f1118090708001400074003900021501c144203c3d00e40045407148 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 693285467 1250 693284217 693284219
    0x24050d06050c0702330f12061f030b270a02130b0d0e0c03011b120f110a0215010b0901030902210f0609070302010e0d06020c0631022206 60
    0xc9a503065940070a5040301c07180c0503480c000d01039000d1043c424025516405882c00e40041d03108256401000d8110503005c0304031002032032341d03251381c607540c0c40c541307070102c0c40550922507420001c000d440d110f403840b0b0040d0005900c0203000b004140840900300d8039041c080a80b6039402c3c0c4490002d41240150b030aa4104140c40040c1894001008090801c192140880c00103200c00340b05140c102103c407420701aa00d803400b01064001e44095020022450740b4000c1440d0300c40900344c001400740d54564000300303841c0840c030352034440c0c0107801850340c60419020317a905200d10482e214620724003481410741903a8200709104e4150322039440220300a20003001101421300030b000300c10880e03403070003200d4806610611140103242c40804c04141e000e0a0840181449811640006e040121100701140035424180c82241041566016140f40c07240100403200700b4584800c800c0400348d1040b0301c083c4404524003c3c01622010a0361960345550017a00804c902c0b6807140c850301402c00c86040b10500c01c2d42d41c1c10 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 693286717 1250 693285467 693285469
    0x10060f140121090f06060501030c090b03060d141507090b0c07050f1c05010c03060803251e0f060c0518120f0303040b010e0105010c0f060209011e0324050d06050c0702 73
    0x700e0740130f2507015043c00240c0509080014040300d1408958205011020508000050404003140d41c408070640d0b08003a03042d06072030006000740032551084018051410214040d240f600c142d40e210b00c1c03160343c50a000795614505281d00d031042c803c1c1e00e941500329200a1040d8203001144031440f0102502040030300045490940100030300c88000c407282c1e512a05400300107035040c001e071805003040703802461030100b07040c81d611890000c00b00d44a160303140f80740340700c0c1c103220a003881e054200c0220103042c100130b40d181c606444c0c2407214840c200c6000d4540006160068490b9056900201d98843c22041002855040000c00e02458003080107600c90405040b181700001e00280d80100d100b10308200095041550f1280d002d841604681e0402500038907034408604500c01041d021a080480180c1d22280a001200d00d2004a45070806e180c1c503640d000c00d819035065100c40420749010420b07007400d030f2800320760074060000e5200d26544000b031102d60101140780e641c0040d400150308601036251915a034 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 693287967 1250 693286717 693286733
    0x3020d0f0c02370f05030309061e0c030c0a060f05041e0503130b04150201050606070b090c0a120209010503010612021306091104060807020712120c0510060f14012109 73
    0x4030740c903c02ca10007000700600c11030380c02d00f5005080110091801c05080201180307040c01030001d042e4801018482148505c259142121511410036090320303a107900100200c1d07a100c86036203007120b0640c588403912406148a20600d030040c0e92160f1303070940040008144030254072407900700b607a0701c2c0400c100c80da640101440185c80144050403005407900c1c6000401c10f0803042c144090015a41450f00b04070031680c41c0ea0803145501d40c010144207242d03c0c4c201020b85031152140c44030790030240340c0d40b0100710740741080080c0c25858400c88042001b43e80b91000e243c07d0b1002403095101c40105882d1100051510441e00a1042483c0c940010000c0e40c4030114820388400b0500200100c000003424000e00d54042000c40d030000f29070004040b103900e404140c0440c480035410151450840c0e1a4040e800da1040c1e02c044110794100080350020540050380c1c80040c2011f2240e0b1408a090800000c1c0610340700b0184107500c03605860f032901c0e0781d180d8030500340d0b1003404000200d10b056880f042c1400190b240 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 693289217 1250 693287967 693288049
    0x30070f110601090e1204350105070e09060d050c0d080d18020a0b04050603040809041e1e110f03040c1a0a0f050910110309060409020703020d0f0c02 65
    0x70400402c0b4403911080040c2045107031204046404003c200500c001080260950b441848200040c2c7e400203558517001f08801804440e610f4a5003410140700340c140e48a00d800420b0f6800310386000710b640b986410030101c50642c0e0001481c0343c200c444104014904818281441030040300e850b460800001406021a003680340d0100074a98813031486030540c24903d210002502c0c0c13451041c1d2501e42440009201307400000d01c000c002502c0041d048010f52103070f41060003004107a10070511040c20303104041b4050714451683c614070200000307118089400c640201d1190314080c1544510382040800782d200c6992008005444201c00761200041540d0450302d8202c0440c102e0860300d03161104008001d2024000102c64010031000b40940c811a82d0b41d035003c05c90307244d210300308140800d05c0c0c4d2042c42d0950140c0c0300019807200020500056040c0303c0c0e001442c80074482e900381c0d6254a0f58602c00d48a05540002401c0002c4c84185500018140011880000c1d00e0701202e48400482c2000700c59420880 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 693290467 1250 693289217 693289229
    0x601031e060915030b0606030a021902010c02210912010b0612060109050f011e090b0703020c120102070b1303140c030c0c0616030806040207051230070f110601 70
    0x24401080020702d8441c881c0e941101d03641c0711030312120f91031510750364201d401c01340102d03104920000215100d036601d0740c1161402d5001117000900d000b80c000c0040d009204050b000070160103480a22444030b203152501c80c14406080c2407060500811005101120000b00c09510041d0760300c40800c580b5036030304030207441c40d40d100d024490601d10f0200001805000b050b8001c070700034010750108404503a0000b0303c0030b1040d00c0c140b1034041c6040901c032048800307001c0356100001e01400040d0240501d5070100b03151074000c00a0b10a46404401031038404d08034401c00501603d11008a00070884504240701b820400e14000e2801c0e06080202c10042ca92a03400342601119a80c00091000303e00e0b4001e10080103000d41c11244181801004024440c0200c00b0705802030810000200242140d5600d40c10358243c1134000c021199003a1505001c0b1000e0740c841e140409101c0c203414900d00381c041e40c0080640780101500c80c06034040d10fa000060b82c2c40015a01d0000c18400c45003400a0381807010041e2600800f8 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 693291717 1250 693290467 693290471
    0x804020303094f0c0201090b010605070605101a071401060b09090702150c2d030403080a060f181409071403010b0609012001090c0e06010201140105090601031e 70
    0x2202580005000c07900460241030303403403d0074601d06242020206000100203ca1010a03071900070b0b0801c80c01401c40c00d44c02090440001d0020030140c3e03100010b0480148105c0c0c0c10885a02c2e44895840c84d0055840b49000c05420101282c541664100240c42c40500ca01500141000101c00c032500351341007600502040c17540850381105514040010340d4020901e80003a21a041c516000e494162500074040e40300c600c0001000345e00046143c080501c7e00942c0d40c00c1000082c4070b240c01c1e0466074420380b000d90000f008500030503241c09607445008100da01031021103000c40e140c0f10051042c803100300300c035440c1155140c0d4491980030301c0d40d030040e114080603400780c46614201401c496440d000000590f000342c0c5481e0000c280c43d121642224a107a01c2420505c900c00803080980381880125002d50303940d54241801c03a0200314125900c1c00030740740140501c2400b6561400124200c07011940300555454924004022a0070441b000e00c2d08240c06160103c0c00c0c0c140041502c025200c10700611160ba5 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 693292967 1250 693291717 693291769
    0xa180801090c0902030f01030602090f090f2a0702220509010b01030608031201170c120d0e0603430c02030d05090303040303030203091524150406080402030309 70
    0x21690308a01c001528810f03e0443c11030403c50100701543c40140070003030009a00044040140da00c230310307500307885c0744008020081510f41094005494603003540c081080c15400c00d450b010b00000700305440410fa40503200141060040c0c2c08100031042020000c2401d2140540e50100c182e519009461284150750004100740c484032000500721800c0d94414040c5400c1400504100520a1040317070444001050403083d1501da5020306040904607040c0c50b034013076620f0385a203140d01c01c04074065a600c01a6110410205402002c3c0444c52204a41109a1910761030441440c080c00301d1074410980d0407480c803003007080c4410708280001c03c001260b81c00400c1d01c04003102d04501c1c04000707080c01c074499032504609000d040c1021982d40e002d5804001c05254000c0005190300e00d04201042d145010490120400d06204403d807d0026030481c0c0d02041610410340310250707080c034034a420070a51811251601d07161415030116107440001c0c000f285c0c103000c1040890010341d6019211000f105441c64610256 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 693294217 1250 693292967 693292973
    0x409060e16080f101505041e111216090305030c0708010518070b07060b180a050a0920060d090606050a120302103b100b030604080a18080109 62
    0x4a1030550207040d0b20b80c003460003050022000b0480c00582400c0c0360300864082c2c1ca4000c00c1140f0521504901e4009141c08041c21032449021130041210300c030010100440792a2500000040c8100c1c0c081c0d20401c44100f0100c0e0b86d9038401002600d155610b8a8170046044e2a41d46103802c0d42d2240c010f00c107842e030005106016070300c9c0c01e214a41c0c105a5040c81c0c5646030362600c00e50b03501c0d10f00600c16080051408144a01409641c1d0000c5c0213244005115000038401150318041c0f401060320820368003843d01c0001038070300e00c3c0c44c4150b070283c540028400703015908034024910014450003005400100c10301000350009600e010b8020001d11400c0040f907442d04003014882208000c0d80514050255032886a01184c0c0200705d2000202c09031501240c2a610007000d080c0c00c4a103a14801d0440f22103601600320078452003240f581c130880a00580c2d80c0120144000429141d24080040c0d06820540124002504020042000c0c0005040030303103c0c3e800b06041900d01842c00c0d0311000450b51140d000300f0030 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 693295467 1250 693294217 693294253
    0x31107050103090c0302060f040b0d0f06060c030c0209090109060e03030a180b0411011b0515010f14100e0901120201080a020a121a0604030c0e09070b03040305090409060e 75
    0x80c05007840d080158032a140c5407494503006900c0b01a020340b03000100000c0c05e031805c1c0c080300c018104003409695516501c80000c0000c1c020341c216045401e2400e013011610070700c520b000e41b400a415a403030380c007283da003a000c0000074000a000d1440540d41c1319171003c00a962030142c19007813074119002c0c5440e071a0403076261742a40c0d61801080e9007006c281c940c140c00600a01102c40e0401d402034216650703101c1319030060300c0102c1c40300c4000741c51200c66060b080c10064001401d0a500001c1d8980706140d9a940074440741071800d0f070081c0c0e01000003901c42c022032814545602070f15241c4629210400d01a004049407140c502138200041d0480828460380c2907580000045803c0000700c00c0840c6070643c0c0d0300e4000c190005a030070500d00b807600d038140d07100098503e01074035102c000001c05480c3d98658919118500303480b14840c0c2c030040b41c80b0350002054500045865411204407804140c61560341741c2e8116420350202c0d041590040c0d5454001000c00c003540f0641c802c1070403000050030300451a2070b44220f = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 693296717 1250 693295467 693295469
    0x2041a090a0e0105061602010309020603010305030712090f0501050c01270b070503040b06120708030f0901090519030f0c0f270525140a08100e090601170c0d031107 72
    0x1a07102d40200401c443c1d101c038000c03110444c40d240e0008640c035200307200417005001c224402960240001c4008818003130003000900b0001e11865192504036000101602e210886100e9102c48112581d010410755007c2d10040c10003000006c000903211192a181c00440c16030741081e000750a012101100401024540e0140c0005403820072500314030780742d99101103504000301224010002188818030010741044014042c0a82c0001e40c0e88815000041d100380c1c1d0800c02d0310b10b00081a0130400070701810302c08003024003042e81603c280070b03450454840d4529100347c5501203407260303042ea00c005200c0200c0320404014040c1500018042410785680c440140450001c00341194600b02c00c1c4450035030014130aa101d84100c1d01070941c280c81e082d0301a80c0c94101c03985c044620f0000020b440402c43c0c2c0c0f024820784500b45e02d045105c04152104421111140708071a09003a035880707100180844022201443d004418800441e004c1c1303840d0b480450b60350009203208402003001454507003590a02440880 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 693297967 1250 693296717 693296729
    0xa050601141f02030c0124050d0213020a1202070309090b09060d1101142d0a080c070f0602070b06040b100504090b0f0a080606041407050a1202041a090a 67
    0x70601c020448009a030019040800761403010214410000060003401542e08224910340204140c40b07200e0060a2218858100c1c0b40111a002001143c0c0385490004148619005816036052031a420740403002544030300e54110500062904004030780303403030b40003e2107803d02ca03550b2200802e00c6c00b0601c2c0140c80740c00c8081d61145190100700541e90721008032a000702c4e44c12095043c003030b040340001079901020050400c0501000024000c44100300c41d04d00801015040c20001080c0400e00420411801540b41e04030001d034455000c514070840540290503801c3c083c60090b888a081682c8940499002030300c1150407184103010003915103868030400302d2184056a0411081100020082052140380528102117603929031800054554068038844028050310030744e40c1d1516003900d01e40c0d40500b2500280304070f0030100c80d100c0d0b90031442d031810302035003844c1c45207402e281c08008140c032208042d4640b08542c1c2c2c0d0038000010450742590b000180c0715200c80c00c540e0ba42800005100364404950408 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 693299217 1250 693297967 693297989
    0x60103141602061311040504080409092d1a0402130e0f0105090c030d12020c0105190e03070f030f030e07090e07051c020d15060e061212040504021c020c0a050601 71
    0x6032010895017424181c0058003164000380b00c0c0d039070b440d1900090280d81c0080c2a428a071611180810621000200c0b10321618055480c690410420000050381c0c0c000f80180896611403a903441c40c0c141c410440e801510040c5140540c86000345140111500401004c0389944038650044201e0420700c1032a820036030040c0908034035614440071954520500c44220104500b10211900486040e4152a1840305881c0280650304100c048090b008600104001c80d061400300d055a82c01070010841d58000e0b0b2001d0404489911520140d410890700e1420170113054032082c02404a01080c460380e80540a840000039070f050a06c1d058070314240f0b407500418051056128055070041e20101c000c00c0d4907604840c604500542440c00103607168000740403420140c20048045440d941c0b5099061042100703480c08030390303d804025580d5032400d02024040c61148104014090360138035400800009200c3c28440b0040452101c01c00100d0f030101458a4a64000c4400042007040500c00e09004005072595 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 693300467 1250 693299217 693299251
    0xf0203070f0f0519050d140f0f01030b040803040f050f012310090207020303070b090102180303070c0603110c0f15011a0412171809010609120b06010314160206 70
    0x2000d407580c4510032a1080b20700308490b20206561182017210050300c80c04505110038804d203180706120031804e94500314239a503090300003942800c2c9288a207040301c3c0c0107405010310b9255078407103040c540d01c0904241c6405c51911840d4002c41d00400044098011405c000512002908149101419214001912500d0390024054a07842c1581c2070420348001400c0142c2da806c85100003891440340c2400107049040030020420100b00c10740c00751070001c0110301720301008a68101015180e20440b600140503001880c020b00c0820b04c00c0d400150945c07520700c6000e144c20250102c00e0310b003400800c00d00c08140d00c05c018003030426011651700390047c980385d059900100d100088400d03050143d4000c11001c440103a00e844144000c1d035a0300354414011803c056582c414200000701903d050f40003040c0500c195000003c0c803d4800c2c2c440c1030440da022030111b0410302603036449900d51840600380034101500c4107035060048001624070f50050000103640a014143c0a10103420700300010124440e4110280e4 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 693301717 1250 693300467 693300497
    0xc0c030507020405090a0f05071e12030e010315030f1101020703020102061803040306060603050a0605090601020c040b0613080f0f0c0105121017030c10051509070e040f0203070f 78
    0x10954407156030483e404186981c4100c842480c00460460180603500d50400a074180400424800140c1c0c503403081c0c0c20f05419400d010ba60350024144591000140703401907040c0807a20401844035581414540403e424050f4103451040c240c154000707545545105000000300a10001e40d020ba5072028009841403d156400203519848014040c0568801130145500310401c00c1c0211409158040d40030000c041d00c408004004000c2250030500a6103821000300c2c052409900e00b0748513240507801006840b00c03050900000e001c0300b20303030281c00000070310440061408098410016000c944003d24035002c6d204c11043c54003519000a81a6400980c0800c0032664840c0841d01c4041011000c2c80300d6890f013403122040801c0079444207541103035180315002c0c898404001407140c0b4021608640700c6901e6500010220f44040c1c62a641120441700d40700318506040d14103030f5001050307040c070420300410134004c90143d801085400003990340c0001000f40c0e803600240ea0414014082c0342010901106c18 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 693302967 1250 693301717 693301727
    0x60204081f060b2d07030804020907110c041a0d062a020706050c0c030f03030702120414280902070218070e0f0325090506100f08041a040b04060c0c03 66
    0x68040713001c054282d6444408658071904a0b60031001080380d40b03030381d18418100140341a800740c404a100348407181c0450401849500c80005061180c00642140542203040000a0140b04c0c00900d00760b84159560a41d541e801840080e240e00444d804a00e480c0d00d5841c001070613120b101820900d00f000b603442e041c000e230b000442805454580c20300684d1411201041482c16251100c100c0d458403c1052a039201200480514020303c000d4088410365a0071400860300c5d4000c901a101c0e100c0c600400e0340e8510b16100509507030555200b00943c4414261603035021110081da04204901a0005111070031820102000012024981d565680c01d04000c8002080940750306076085c41440c0d0380b00c2d90344030745d50705204495a00311109202c5504611900004030041ca4511400074024908000140c0038201000701d0300072940981e4980070300400548081c0d030800c2c0d001e0420b0b24460100c6c03140b45200006903003410f010300d000c0c00e07118125140500d411810382e150b1034009001c1250030540d00002035040 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 693304217 1250 693302967 693302977
    0x406091d150c070c08012901110c09130b090d020709020408100b064006050304060e1204120636020d1a040b0f0c1b0a060204081f060b 59
    0x182c0e4640d9950f14030b81030004036588a038000580a500c0d1517003000c1441484115141074101c1c0303041c240500a003180054400149000c6040f02c03070f4002004c942a945841200e1a6000f0943c411003403158107651101e04121400700d545241a034454844501000c0c0c04101c048001e25103044107520b000d0400000d07030340704e15491070401c4125444c1c40380d02d211980c0717007002e485081e41001c151410140c000c520128040c150000b290500e201010340c0003410308900759400382038882980381d071441c6485985e155801010003d1241c40d450041d443d1055005d80a02c0040008103c180780060541d03080d07060a404660400210321b0844d04d10703119480801d10711a1108031042d10080c518107480c090b50010401040b210107008140b28001c03c0b107c14800c0344480c0e124011805080c05980ba0754440d203160a080d101640e1003100f40009000010503054628402c044584042080c2d82c044035480d0340e490705076003058201c15626044007045820f030b240c0950205180100f82d100600c5007601c2c00b4403550051040c = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 693305467 1250 693304217 693304231
    0x603040c050415051306031e020306011a04090510031b06080114041e05090d080403170721020c0d03090215071b091b0507020306240406091d15 63
    0x44450380c0700c3c0c09500310700143c02803201514400c4062941184180200010300040702c91604085404034100c1d14006008803443d4041d0040066900700300e8881446692175110411024041001040034442806901c4c0901000d000f5062540d0841c030700301d54030086440c0781d440315000001040050030b07401403800f81106c0303a0398007120b680c0d14800003190150042070003c0f408118030004080390184c140d40300384d108201c0e650030380341100302c00c0c03a0407030382600306540240000700014000c011101d80035106580203210f905114050000840d400508000c1c005004021994041100c024415080c01400f01d02581840d0420455000780d000aa841e40c00d4001801c4900c4080741c0c482c200b100c03d034244840410400c000c403180c0e517a141c080780302621060020720840d58425a0011040f801141030354a6141c1c010050081a503541e01c1c46681000084400101c1004480c1061810340300c0c0c0c45480c024086842d00812810349199800c0112492140400104e5201116030344021020141b41508050707 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 693306717 1250 693305467 693305471
    0x304050703020f210c03010e0304060c0305090a051815012a05121303120e0105070f030e270105180a0203060303130b07060501210204110c0a030f09050603040c0504 72
    0xc2880d004c030b12080c14021203035104d12000301400103c4600060956080c49084000340b01128100010540307a00070fa2041401164800395140e0010380158003601e19400040d05a16803140c0c0e48001442244440c1e4403640310950030700a00c890341144c00740d0526410f8080c2010780c1151844246600c990121488520140340e610000500304038082c00031030b55161804a040da114000301c150120301c041507100031120203018002150b412030150014849810050b101c6074241020750b20340c284040403180c130840400021820440d0140d40341082c0320445010020a602107201420002401c50b40c180c00241c4131301594011003440480059015500c01c100b05000f50f1251a40400309145003c1c1008200c800b0110100201b546003a43e005092421302503081032105980e100c403001d681000c0300c0b000010f00314040340f1440c05418250026801e003442c0100513490500c225890505009960000b02c0c0014403138401c0400e80d550228085010b49422034100d461401c040d521501b00031400c3c46114000c031b03 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 693307967 1250 693306717 693306739
    0x121110f0405010b120f100306202b0207051f110304030f02010c030b031b0303070624090513110f190f1e060e0d05030c07051302030405070302 63
    0xa110411565115880034009202c1540c6032031340c1ca040c940000c8a11801070388844001562403a4081e1a00d0040700300048450783c031415070700d400002d00710140d0a0f10702441014994800b01d00380d03070000d211840d0240c4e44414103644402c0002e69070741c034074580c0003609401841210b004c80d10206801da40c00040d442d24103240030000c0380410240a81c0081940c1380c02001c400c01080c5500500304070380b40c880d16802007022451803881500ac940d520034800b60154820210001c292031148a1443c2e0f2100090842e4100ba4441d6141c0003910784801100c841040119482460a1180e803c000090141c02c40705002038913100380090034000103c1c4001e01104410441c3c600e554440d4001c03040b4986015024003440100700d108407241d101c1522481500c1d50903140700041c00070006043c1e4441e41c114104108810785030040490341c5003840030703400380d0080364081e4800014804200619403118040040d00501d40350008200d141d03082c51030340d00768290041003000006003000c00c040055079811070390001c0c4e83c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 693309217 1250 693307967 693307969
    0x180b2b20130e280507031803021e0f06010b04031a07050906030a061212090605040608040b06031f0c0f2d0201020c1005060a06031e1817030609012111 66
    0x80c0030b0401800c40d800c0180c00d0b01ca841559940240d4460a6079840c14845030100c6036282130f202c1f910120141c0107030401d010420002c0740c1840c4441d45503e410040318031924000050301d0030203100382d04c11900c1d440d000604108010040a40b40e03246201c1d01034090481c80c3ca601c0244c1315100d407541c0241f040c0f5002000030000710075540080e0280070440101c21408500746000982003500c2981740010034140f14000940301c0c410021603042d501d81c1d40ea07811490b20740f550f400b0100d141c007070f1112303a150045007400400b12204101500070340d454418081420204c02c0805002442410004000c0001858000d0725038030240c00220b890304103802c01c040625001810403402400b6010b040b200e140500c500c0e219a40701950415801401c080312042025a41e40100340c0c03c6407601c841c17243c0036800c0340c0005a0151855801141c601469070642c0e286000c141d51002280e1200d10300503904843e010003440a13505050b0007150152066050f25a4511120592418402c0b00041c00508c00c149161440e00d503 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 693310467 1250 693309217 693309241
    0x7170106120603080f0d1d0d050d090f03020a150203281415010201051303080601080907120305040e0612121309060b0405030d180b2b20130e 62
    0xd541210845172504990101c0d1681075100020003517041c0d04221201c01d5591415200014003407d1000801603d034400740280ea203500178a820070070389903079140b5620129103194020340395607210f540a096055070b5031030042c4038041c1a00c084a6000d20500800400d0804101c5042034116007a540c4032441c4401000d120103030070008100031101c1d0680051026805030304190315031a1401740c000b40542c0d034034100c640d901c1160b034081c041c1c002011400480c2495000305147c07600b186050303003907902c44c0c1d0312a802c1b04202407000c0710440c0059000201044500c4a03604003541000003283c0d003258040d540000d1581c1c0310001200121203040024900404809411804000b062412000c0c0001a03640706507002031380052045c580280a8010a140740b10702c91029044100e51419108910170b06085074820190400c20113440c0c0802c204400d41140150788401420094807403038017140c4860300384802d05010581280d01c0c2c0c48000c046c00030068940c01400483c0940c1c1611180340c1a903503400e101049 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 693311717 1250 693310467 693310469
    0x181e0a1502090d03050910022410080a0b0f0906040b04060c030e070801020c372a061121091c0f1b0506090111071d090105071701061206 60
    0x743c0a05625484000c0540103406860451012241c064103d201c2120981c0c45802104d1041c0d43c1040e0030065103140302c0c08040300c5800412181c203602c10070361074640711442c200d0303240c2c4103580c0202404100254900c20081e0680c0c07048417070019000508140c1e54007504124003400043c4696150004041e10500c2070344400c0703001010304101c510032a983c4134210b000f9440202151031b40e00689800716420788414401000042042000d0024000e60281c04100840050411503242e80300c00c090a41101048000c01d0000840e0304207104101d19000020b040340074070074002442c80e005100f805420b40b0b0b07141d40729682c068072003601136aa007009500181c1c4412080c2d04411560218083d030400f0301510b007100300075030781c0704868140604a0040e0668114180c510030319910080c20840761507a544200d010754140310071441281d41440d119181d21240c54000b42c7c00c2a10807100d1000c100000f84240100c0d60000e00b0743c1040000b0254504002150440c14003c440a01c9182d000300d03402c0c0e580303a910181c = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 693312967 1250 693311717 693311719
    0x11370f0f1b0f0812070201050f030a0f020d02030604060626060604030c030b0106021009022206030606080102070b060d02010801360e1c020d030b0a0b03181e0a150209 73
    0x60680d100c44054048907031501601c0c3c41c1c1c0c40381480c0e111001d02120101c400b5113405031036550602d01d12075050240759100500d051205d81d2154008207000c482c40c0003502d1070140126000d6124030b0302c0803c3c80100c8440d030f400b060400042c41d00036410500303400e500021200c0c3c0100e0010441d038400012a0701c0b07206940c0000c10011082c00000248000003e540e4140d503881d5003902c2202c81f01e07030016029600c20704006988042c01c02100c0da4500303850300f030310b0b00c10281125020660950302c2c1c50380b03411a52241e2050300c142c2d4001400718100801041e045038031200840c2c0003504040b00d038000800c010705c14000d03800518640010703035443c481d82640440038812051280d281c0200b15402d03c2001c0c200324000402d60b880f650342c12210403203100985100000469000b8a485010500120041d05c00340b08116000840900c0116a10116800039441040c016034040d0003900c04c2c10350380d89851207680d89083c0c01c9907448031103910424041184140c1c2d503002050103400c100c44814260092042266075 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 693314217 1250 693312967 693313013
    0x8190806130902120d022103090d2111090f0a080c040209030a0b0106090e0a0507140f0702030f060708010b0313020103090c1d01030507080d091511370f0f 68
    0x100d2170349a40014070008440218680590100301410401c413103000076112401a0b400c61914201e400c0d2107013120108480f6290b58055400c0261008102264071019501403041400100a02075082c40120801400c03000d8038002141e52a145615171101801d4041c284070b0350700001c140b04c0076642080091384113604001c40740b98559494102038502110791082e40988068640017850400c500c0c418548980c0c059103031202014210f020840140e030000401200308081800f003040507803000c02011601c07440010040103d400c1c050806812004164001196008201704000803076040084056400e582820007190700342062402030103100d015080b4a1701d6031400c004904054404004081c100c2e80150140c0e21010b483d003a00d19218184007400d1408501a140100600e000d0b03050b0114080c6002c1c50556401c103a0a81c0381400d06004501007410742e9a02449442c60320825000304170010140030a4400900d0301e903564100c124860380c0042c0c240e03e40481000d0138000c0c00d4500300b00c1e0782401412 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 693315467 1250 693314217 693314233
    0x50109170408060703050606120403140c0304170a2001140307030c0f30020c030301081e0106180203090127060b0d11090c0c0601030819080613090212 66
    0x140100c01e4015108240483c401c41c0d0204001d24042d1049901075040070305800c0c03401e1400c3c06580281074028000714108466068036141482204020344a0b0145d144051941d0b0340c80d1034845211800390701404022600480182c00c0011002149803520004021690014a81070700c0145c80c0700410700c6c03100e55014400002c2065013641580485141d14141c1c440c00c056080035441140c144c0343c0b442c05507120034110800e83c4c6006080b1712140e0040d9045034805403074082c02c0e5043c00d00b10340003a07101800c1c0f50f004000f1544100c070000000441014840c008105203460a4610b900304040600052600c0c0e83c00408502c11b65429000302e074500c11048041c0c4101082da019500046c4030622085d20704a1815181c060791740f6100c0321038100140c010008440b080045030400c140400080d0051000304010000c00082e00c5007800b015008500421300d80d900c9079910320a1030007150300030090300c003044004000c01032281d94144c05621001801c81c80001c82c1e103400d101007202c82550b090510301c01d202d1128 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 693316717 1250 693315467 693315503
    0x2d040306060e24010e030c0406030606050111211c0905030331020f011b0b06120f060103031110050c04080f0a0809040525030504110d0305090607050109 67
    0x41001107a0769109524a180e940761400c25500203034003403242842e6a8500b554003e907210360f2050f58120001016910503001d007100080032241258001c0300ea2603183d020030003403580c22100800b110516032010340002034445403114842800e00c160308102150109000a070a451000c10b083c1c01001114108545240c60900c1039890b0000c90b086032141c418403040c0050814038940060003500110f0700718051244590070000b26030356104034181041110b50315050001424500700b281540200310b440280d040000600c210a085440100c0507035000040c29465800000380300da0442c3e805280c01d05541074028201801d0403100e02e0015106410603042c091001c01000081c070440f03020301d046940156541d09116110110490083d0510109110041040c10140c00044d030055003020556910f5620848210b18107a0410a0100003030b60f1f94108810011038490036491510110303198070f0400c13071075070740100188528403420b805444045112001c0282c00d401a0406640c0604140803008441e6 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 693317967 1250 693316717 693316721
    0x51e0f01050f1c02040908070819181419180f06090b0a030308060f06160203010501080118061508030301080d030b0907090b0a0908011509140c2d040306 67
    0xc001c99200d01c00711010300e5102e29050500042654500121000701480d0703400304401810719003c15100c100e4200315007000920726000601e11040402c1041500d44001c2000900b01083d01c02d5000010b107100105010760899a814400c00702c0048031306174003442c008400e118035640907502c4600003000c0310b0b131301d00c40106041d0402c200076220403070200a480e07030350080303003055903d130540b5140c103e5800c18040c4040382c070404140d60300940242c00e03816208480d00105040c0c1d4030401c10104104201c2e084842141360078003032075006052000081c40b0210b04104404186034951100514003551041c1d000007400307101e54100700a09401c03040e0303600c3e036039240030030354803440714685c0c01001a15004480c1940d01d8034007235107405204c81e0756070049000e061a52810156014890390024801120800140710000340641340d2582001044800c00600d449031580554503222050545100c4d50303000c115007502200240c4003100d080b20b541c04011050f00c1d46040c400b00c0160300308651860001800b1092008617 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 693319217 1250 693317967 693317969
    0x111031314060c0307050a02070515070618031b05070504050403020f0d050a050f0c0c030703140f010204030203060f071403010902040312020c030c010f030f020721020d080604051e0f01 81
    0x15150103401010204207a82d01c65070101c03054040c81c401840030481043c07041000c2d101c0e061950045600440d210b800142003030060b19035240c1e00c0e0340c00081403800c11145002d1003030b000c840c028591100450650300175140950416507a003031000f1040c80a000e0000c01c100c0003000f450098010020342c1030608009454003130061408100c0d104595165003501c0c4070b10216840d40303006554a90030042680250303549030b403052440d1501d0744241080ca1400355400d2042c440150310030981c12001c2c000300905d0704e040034034600d11541146d1040c0401c0000da1408500907a000c0b0078881d011080f581c401d201603403401403e250700302550801000221b1040c0a9500030300c10350b4014450114860007215007240e803050444111901500520b664040c0d65014140c00404a501400c0c081341c6407261041580032038100e0b90041d141c0d140400d801e0f8803040841c1d8501225141c0500c0548078a0b06400c901400e51140500030f203000315034540008124ac00d0f01590030b8544098036203009040c0c00c0c0020801003881c0c00f = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 693320467 1250 693319217 693319223
    0x30b041407020105090d0e060a030e0607020f161d0901020f030112150c2f011e1b080f13200117190f0207020a030b0108070b070c05090901110313 64
    0x64040400c5c1440760000302c145220800d555101c3c4241e4403102408002d4006105500601d40c854000150030389040c044c2911030b040341d80c01400d40341c1614402c20b00c1c01c0150b60041020b030940802c24032003944172044020540103504120820394451002a078020300c6900c1080029504c00f00c00820303400210520314517643d002d02c54140c20103a4822429040320301444206010549a25619070780003a820801495031010301f03c1d4880e91044500c00c3e900752000550400c1c3c8503025552010041d03500b6101d09400300301c14280e02c0507201c0f614440503005800140521104051020005046541c0403403c6061a544908419088031108825250280114007074a01003400340d00c1c803107445100c5078040c5115500b0a0109012500e41030001402880b40904070f26005400308501c4015031650b45044004503c142640040b540c50085500e0801c0d071a40c20500e19400304000700004903a6858921060b140c0c21142c0b07030300319118030300f801d030040c0f1001440303040f0071502008001400c6030034403400c04d101d40 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 693321717 1250 693320467 693320471
    0xa080408120408030f090606011709012a080a0e0a0312020f04060306031112030a0e0a0b1b0f010915020d1401030c061202120a1512060c0f0518090601030b0414070201 73
    0x84c6c0030001d6849800860b8081e0001d0003450b80305241c03c0d4280340c030300d412146803000025042005040da40c9103541008000c84281161401001016400040180d01890740001000803510540c2c84a455455a4002070100540e10754001c0c41e90b003580d4101c500962110302203030b95450f43c402001c2d01030090b51000742ca618003e054075040c0d44c14481d0791281200c11003406180361414000c0b040e641546541141500f0110a042c00329141d076024000701000000741e0301d048425000003000c20300d00241d1101c0d1074402d0341003030310311800074080300e114602c04c1c0405540561122049002c4500070008000340c0c0c86610304450000040c0041058020242c0f001556030300e600072811060741d4281d100c1c041103015803580b444005660860594410400d450790103801d904403990b80c140000020b090760505407105a5106a4844400d03040342d4902510f841c01d0030002d09000e04041c6860486041410880c01002050001541a03200b42d000450034a001001017001d94850704c03d0079442d0070100c8160300958 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 693322967 1250 693321717 693321721
    0x8121014060703171b0309010504050c01021219030b10030f150b0706020c0a12080106020106151707141c0c050412062c1f020f0a080408120408030f 65
    0x810a1070440703030000e802d41c50b010740f052009041e40d4032001005110101150300440075110020825001310301030407480002189909140c00e109041815010b20141503601410b141e00c0e03019a000c00391180300d00846c035808000740c2d2203441a009003145407600340e44046c20000d14214240c0551100620085025003049140b02084603070350f003002c2c0c90084070b83c1c4402c203001901c0024169001040da86820f8400e0b208038285a40c0c51980c100d00c0340000c040480c2c0000c0043c00010350921500d0000c15231000300c00540c41006501074240800c05086401c00203600c030018001d40d011344800c40d07e00480301c0d4015580e0403500c83c11031012064540ca9005c030313400c0944032030b0114400e600790382c181c8081c07102c0501701d81d05030741d5031800500d04031001d407d00076100c80761000464001c032601d00140c817910340034250f0a010404440038502a01603410350251051000c2038602c0320540540340c41e402c5501f400502501c540c01d0a260714010b070060101001c140d00c00300f00421030b490f4059402041c20b51503000642e = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 693324217 1250 693322967 693322969
    0xc050f010c0504031103030c1504140303040206070807021908030706150f0e070e0a030b0103031e05090120030406031509140406020a0e0a0602030307020f07080a02060708121014 78
    0x780300484801c100040c410300042c40410b42e2200a8220520001c049078540400c074042141401040d101801c11003200a0800c01031204a2812084100c0910051441e51500b07600048540c000c60801405118002c9020f000b107403242d440100e140310041941c0202c280d6582c0b0069941c1d40721000c215001e0b420060b100070600c400c09108400e0301c800618156000d824a100f9030b07802d00c0d009140c1e42c10400181e500800645405032030001031030007250028581d60460030042d01000074401c0c0407002c8045101c071406013079400816544140300034a00840f207042c7c00311840340e00002461440c0610f000000b40003038400d8140e80046984690721000304040350782d448400e4100d03686c41c0c0144942c0010f00e00010002816507008000701c03912030810602301c0100034003080742e0242542040300903038400820b105030590100105803495100c02d00a142950414196544803003202d40004d003e09070120300f84c2e00300030050003500c0000001100e000788500d04566850003000d914401d803148012070390300d003c5007 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 693325467 1250 693324217 693324221
    0x2190b0307030e01091a091204140a05330405040203090102070308160519030e01020a021b040e100504020402090d0b10170d20010e03090f0a0510050901020102090a060c050f01 77
    0x5c0590031404c60700d00c50304241c8280440e8607000b040e8800342c1c06490786513071000f10144040c06c06401c00301c0d0022401d1180d8414030910300813035003245100b400d2518241000e02c0c403039010341e947d490550748450036003002412090081d002d5900455407040c008810403d00d40c0c81580039280b041c0c02951840c000741c84504030840300c0b4002c89501400584104894001c083ea0708229050700c9580b4035000400861045001d82240c015250041c01078000380680b99050a1040b00c05d10b0b07040007142d0810900181500c4c05a0b00e145400b51400c04548034030009082d569030340d0599008540240c640429041c1070310300000e9400084503180d1090203031038008200e04614407460102e01171140000c011080c110b01e010380b8040c030351020b41f9102e1003a00041d42c8400c0402e00455a0010314100210b455000c0e002c00c100305690a61000e500842c000d03d81048141e907a140342c104029030b1410115a40c03491400100d01910805a1050f0411110ba000140f0941e1158940c8400d6000d28255191b02c01001003c1e17007 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 693326717 1250 693325467 693325481
    0x15051303110705100804120306061d0f0d050d030509030c03040303032004080a0b01080d09060c14030a05041a120c070c08012307090e011e0f0b03090f010b061602190b0307030e01 78
    0x170000349058bc041c0e001103a10301001c0a0480001d055500001c00c4400280071844958411181c58115842c0c140b2040d0301405a5508000d0081c091030070410340200c0c481c1d5a00440c44068101500c2d100300003c41c2c0c52002144140484100440d42e0725030b1124001640d4170010701c000c5480061a600008000d2004920704e43d007100300703641ea030359944c0ca0010121803821303107032000b42c0d4204055540c0c0c8461510400003010031201c0d036290390782c85628017041c80703142c15081c6002c00000310003001251184207800800a0b84042c01100462302c070a194141380c6903030003094204030159840c1c241d1982d0740828440030040c42d600f0741c0c16040b41e80d58032200e00310381d90426881508640c0c828000140120300394151045005020850001d10711680c0e40f4400104218941c4201001d000010510408500c10301424142c400d10200900c401206980801c001e4403c0038180165520000a944115034460354484003040c210340050000c00d80350090004154410386000010a02e882c1d0758404039001806004 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 693327967 1250 693326717 693326729
    0x6080a03080c0a1b1a18070e09060115051c0203010306062711122707030c050405130b0f060f04090213270f15051303110705100804120306 61
    0x3034a10500c0113441c81c0d00d480750300001c03119503090011408840180380380d054480c144881c00784840303e60410515045c00d03443e4000ca000c0c00e44e41e80400211500001c0d0450441d040c144401c076146100c04000c03a128021243c05060740302c1400064801400c04c1d030050760599000302410010310b640d5880031900d00496542c01280c04101c4220b0700214004bd6100e00c0070b00c4d5861182d5031030440a181c42080a050440350790791400d140a1520b1342269020090f035954910382001403003002c0c01c0d07032168541c20f003c40c86401d10550319107001401c10b100d4201254132555110300308030543d081a0752200c0080d6002c07a440c80c080c07501d0359408151450280150766050f03030050148802c01c0342c041160703030242c03001002143d010650141d0303403030b01c05016194500d42036000340c2c00480400d0b400d00d085000400242c0340512110305000501c60352500d0601202545585400d1a4405c4607180381c0f21824490b1507880700380c0c072482580f503d009840d08100e50b070784211300c40c050700301c21680302e4030702641240c40501a01d = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 693329217 1250 693327967 693327977
    0x7030504021804020127080c0603091020030f061003020a0507170f03010f1d040b06060d0f0e0703062003180708100e010b030703081e040906080a03080c0a 68
    0x10418089010042c03600180189071800041070700c00343c41d00e14102c00440444825200e500d0400c01c1d03400c24452150f9020003269402e00e1828807038021507440e83c2c070002c000f545654412100c540d00810f0204405005142c0401581368501526103100315007007260101e010308070704519101070714820320031102c40201586909040c41032076107880000b8a401e60115a0101d0200311903050700c40301e00055030090a0000c00c00a240741401011507078840004074074032440190034140800a02078640c000c2c0d0109007640c403d41c499695103000d001400307400c03491484071441c01805440c265000716103001540d0042e0014030540a24805000c1a50070804140c0d80c00c43c07040c0041010855000c13603e0164548030802c64050644610b407a038200051144078480c03c50751005c001c080307100203000312884402d0880c060401c26181d504e404400c0d1040d601d0340310041403458011105032400300c0c291405800301160407c0620345408134640c0c0c5080e411802c0d004240881c1c0000d03c4a140f02e1f045a466580960764 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 693330467 1250 693329217 693329239
    0x1002030a030c0504080118050d0804080a0309050c120f0c030f1b010c2a050409051011070b1905010b0f0915040305010f050a180b0411011809140703050402 68
    0x11001010b10350b2038003040003004c010014052009005807100c005404464010902092821138582000f1b01c5201c401e1086d54820400415807103c11740700d941c022401c0c08110310f0b00510b483c5080050203c0345951102d0f00031000e402d11100013030701514500141c8201c941041018007095555450f96004007030b03640c0300e0b20b0300304000a81c55070010803444041c1031081e4804030a07074400e080300c289001003c00081c15100380c0c01500c0074124240005150a0354100101203e589449866003030021048215130348070b002448007140000120f0300d426410001c8860b650800700005d0041c000d01e0b4049141c01da04080010440207040c408584010754203040542c54075228500340040349008000b090007021044c0400004180e0a010b084242000380764006072610b0b0500c031170411202c903426075040700c0c802101c54a0001d82005101c030707081030f00001c0d54030180d08548012182c1c98880b1000700080560954001140702641c2c0103520350000340901c8038055070741c00c1d9089046070000c807006540403100040c = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 693331717 1250 693330467 693330487
    0x303080903091c030215010305100b0a06050d150b0403051b0306131403070605010902030a0c0207050d0209041e1a010806040f0b0405161d06030606011e020c040c08010303030b100203 80
    0x1c5401980c071a00561311310b4146c444081001c0700c0c0980c81540d070354011144000000344c1503c0740c10061041141c0c05640c050404070000c1c4079029801180010f103503a078000d0b00e00c90b89240c4a0380007c0c45501c4003903680700e45900d005521018030b00b0301d9503a200b92444901c0c542d40f801290152007221085d502482510842c2c482000c42020805810306a010070000c810115069010b140c5c0680070300030700982c2c0d03410400404000c607482c100505086421141d020305c038950343c0c2c0d0314110900e40c044410b6800745c0c5440c184510052040c030180c01558414003010b00c20000f4840080014810b2261304a40aa903107002c0d40d501d4150441d002080b0305504411f250004000300b40341078005000341c0c12a04020003050b5200030200103504642500380c1025070000c0004008004550f0200d000c3d8082d0000742011000a0210300e8841d5810380c50024200c00401400e1003002240c0828000030300a00c900311304150058080d00d020b00003070300001d042054160050404060001d00e030300c4258019494081d440b0 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 693332967 1250 693331717 693331759
    0x3140610210507110c0d030504140a0f090501230f0402070f0506010e01080f01020909070c03110111130902181e0303030a1505031603060f02071407030308090309 71
    0x61000076406400c080441c00594551086030711034601c2d52035034000001c1480240746803204017071041d0f1040000e0100c1030300103a809410b0300d08a8003a0340185540940311000100d00d04000d810100a42d002c136007000a6031304094000c4d5049401804a444603180246030b05000030134501c01894002c0c1c040c1c1c0340142c07282855402401e01c2030181c040041a0b205a503a0f0324107008007030f4840600b0740c0c012401805000c4082c4003e008400d5001d0007107140504480209603541802460003040c03103400c11201042c140511840aaa1035011000b00b000304d12640d002030098201002c006614041e21401169101c2c03d07200f01e03070404040c0741420441c50f03c002c04004980c64000c0300300c2c4803049540720724022901d00700003131405034061032004146591070500d840c100007030941c4183c0c0b1035400f014108160100c603d40d001e040d40d030801340114101c5808145035001e4860b1050082c0714800c4522031121400000c2500420780b8800e0307403020b500ba114603040507507a002d81c0118942c09828003224440c4401c410b = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 693334217 1250 693332967 693332987
    0xd0c1b080304030c080c0f010b030f0106080a02270f0702281119060509041a01140a02011d0d17012d150c050d0c080f030612100c03140610 61
    0x80d05d0028a071851007154241402030030031140403241e44504040314949002c3c0400003a035400c080c000c014040c13030012040c0d03550152140180c0101810016982c8604401000c44003501c03041300b86403110706250840a90707203981129000014000c2040c244c950054054010a081c40c415062140152098580e2180814112216644015480c12101c2c5038840720640000400d05505c0d1180c48086007002e01003a00c0134040503212103106401070380d001d40c0c1c020b411a0800c01d1981203a94840915800c2079005154054802010052350509424000c01c00203c0550841c41542d4401c0c040403200701ca60000103080c0a541b203020414803061120703106420402c21441d200130301c4105040d541d41001c51915a99041803000a861601c20006006c0100305150180c4030520340480700f0030264590f441c440c06481c10107070414a0010205080d940d43c1d0300301c42c41d070165040c10ba982c03420031800e21900402078400440d000c6420003001c01c441d40c22000d000d521030703180500b80104210096100312010030340 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 693335467 1250 693334217 693334223
    0x90615120b1e0a1e0b03040501020408190201020d0201060b180a03150e070b0703020a0201050a1e030e07060c170307090e04150506030604030f110a080d0c1b080304030c 74
    0x9520074481c42562046600d02c00009003080c0120b40320003420500070302c40c0f020f070481210b8020900300c1c04140e581e024141801c503202541c0384d43e101e0703ca03803810501a2041d41d10100d0a44914900081d00110340e03204002064401d8080740e25030f00c1108010703400e9445600c1010600308044c4015586071503251034a0040ca90018101000152695141c190b4180414440381d034081da1011030480e801801c000c66406800c009001500f0f000039a40d00a40d2806030090090400c0004200761380d6003402501c4174440410000c0c41003800b4186150300070b0040120780112000da106400300010a540500c0f030042100b50002c0406000c201480c2c0c40c44843e0380040c00420400414035030015583d039480a800307004a2180c0c0b80c01204d00e10024143c070540f6406480f80b4801d0304285c050000107030300f01c0da88030002110307400c1000d50f480d17409103564188181c40c1d00c054140c0c3c000050440c4c280589034444a56441740ea11803054211280c8508104c88940f590010803010080020801190150305580c42e4144 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 693336717 1250 693335467 693335471
    0x5070c1a0712060b0d180b0402010e0f0418110a0e06060310050a090c030c0e13200c0a02150a051e130305010b0f010e0a03020d020d05070e1009061512 66
    0x4003041001084411507481301c1d03825503011803201c503840e030a40584683e051b400b50058901c0d50b01500e5800398410041e00c0281800040c0b0340c00d0380241c60716489180602001030042040c100b01111015980d0050003040300c0200118264a685103043d179041401d0742d800c02c441000c5a0f4a000c00d01130341d94005040c440100782080300003d0140c1d105510400501100e1388040b900221100d0050151000103800200b4007460110154464a50b50441d81420840c900d002c2080c180354100d00c1c1100c5003072840c50b407411000003a0f001044c0700010f0b00d030514520070f440c42410300c0c0302240500b129003d1030100700002107082118807075040f200041c00140c0d01040080720701c3c1c403802c080c020015200c180d100b20b40a946800c016480391a18152402a54000b8200311b0084146000094466082404000c0c80740098080b00310564451120045030782d54040c00302c1d03046c1526010311040c0c4100807903065460146c000b0340031a44944500030311381200d543c24078500d0300c012120410f8030040c40c03103800202080e03 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 693337967 1250 693336717 693336737
    0xf090b030a05160603061a0a0507030c0602040b0c06060d08070f0c1e0e0603011a04111303080c120901090e0702032a280f15090303020d05070c1a07 65
    0x540600074841c1c01c2c015200c100460304d1a01c0c4003d42501c01d150b100c100c00039560940c0820200014085a0000b403080c50b103035984004929080c5c81c00c407a1400e0142c1135502c045000300c2c010b041c0800505081041d070341121169038521042000c220550380f0001e02c900300901c00c000016a104042e4000c0500c00d00c0c15003111902c940a602c209441d1110500d4507250307941d000c100ba907800452141d04002c00760000d102c003503420520051012820060a4010750f0b6a202d2558000349a400741c0303030420070202440d11181d90700d04121800703800c40030403c000c034000c0101407a1080480700c202c601c80780c010703120303c10018075002d551081ca0000510080542c00100248020000140c7c0d20780b100030380d021601c81c0c2107018500c0ba5460621000141071915000b06142600c1e8001d800215241c9980300d8541c4903410954a420980b0703240c2a002c00036628141030f0303000c0405805401800501204400c100019940c0c0401101c4800106102511b52113000060001802c080c2c0041d40d030164441c10084460 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 693339217 1250 693337967 693337973
    0x1090206070221030d1a10080609150402191701030b01270e070311100c080d0207020d0b01050103051e04030f140a1806110327090a09030311040f090b030a 68
    0x740d48903194241390143d51b00407401401c00340d0140e0705102c00040d16050311078040c1c134101501943c0302500d054820080c550008000100074140b6028014000c0d00c155143e080710000c113400740c811280c503100464525420540d4002810224a040320f811400c0c43d00c0c16441c124007040f86840303100403000d1104100c1820027090309140642000c002005009009440c80c6051240344521800c00151050511061400c0780550180c0780a203000c0d0064035441d5209000b149101c020b1152000c0290003000d501ea0220500c0190000d0034100c1e2000e0320240400e50360781c848210f001c10701c0728448090308030110124011038400c0804500905260a1007003c00012038078a42281d002207161000080031843c01f0146a680f60031940b0080640e42082205100c23021400c83e124080d40403c1100108145001540c01065280e18004198090890482400c1000206014286c05a825000719060050b201600300c801c804840481e50080300001c101c50400c0c0b441806022a2148a54188150581d032004 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 693340467 1250 693339217 693339223
    0x30f0206071e020906060a020c01030b0f0325080d09030b070e09130309080609211201030c06021e06010911070b09070510080403020c01111f050a0e01090206070221 72
    0x3660a10501410b0000a104002c0b00341001004070b80607010603c42e00d00c005070000b50041d01d0000908010501c00407480c049059810407100d150717454410f115010204a40c001d0040b060300b41c111a0801c3e0594803105c48542d02c80d900100080011000da2082001c612043e8000350402c144d0700c0c1011400d03541000040d00c4500c166103400b545070813041c8203020560003807a5480100201005011249000d203010341d180e03031f540c0c0785d080c0075200501c0ca0042c158480c0300c22036810700d811500040380c40d40c503820403000300c5880703019000140c403489030505006604140c808010580302801003403180c0c207110303070130004e0400f07030040c101724280c10303c103400015001800d40d600c40c00042d8002c10342c4a01d8101005550030010429809201d403006c1403202003907000c51007c445490030309010701c101070480343d0903190408402c0344003601d0089400d0020005001d80009000f0103035020b05004c2920030304602e508940309903100a601c018100812001403c191045260380d0241001070b11501c80144440780c1 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 693341717 1250 693340467 693340493
    0xa030e0601080709240b030414011b08011202091b09210d080c12041e05150901020a0806240a0302090405010b0c151906060e09091501030f020607 64
    0x1c6150080030b410b00440301a8403940c0000c0082804500113244c40c03242c102040003031809011800391b0300200003018040030b2017100d00760f1074119008000ca500e000c009400001d070703208480e0002500650000681651407aaa10809c030740041003034015407a100e144a001030100e1002d61030f000d4051044160f9951001a030120501c00e078042d0040d00e2440042041c24010180c0c4014244850b180a101c000080d440c2a101c0015915076801081d44440c1480400f60076042200006000c5046041e07081103004501d141f880b200d15002a545070b100c01b1400340c00d234040c60f006c420015026800290103032800101040840601c1d550342d4071030355120110b1100c2e43d0300c20354803140800d0700010307050b030181030500c08c03c0d00511403ca421401c24160740ea03020307195000420345e6240301800c034011034805d20800c0c10484070031071102005c00803070b9520640640a900114039891080d0000d40c0050b0840002040d030314511240703060f900110f82e00703584c0c450b1101000c01000342c1e004041800008000741c0082d000c45 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 693342967 1250 693341717 693341729
    0xc040b1507080304120206010303020d050c01060504060b1e03090c0103110903010903110606030312070f0e06030709060e0307060207211b14040c08010b0c0c0915030601060c02010210020a030e0601 86
    0x643c0c0e901c0c203030404500c3d0000032469141154004401003000c640d02003085000c41d181c914006940d0300c0390b50740315400350400342c00c070329031007403034401d00081800100006200501041c054116000c401c3c411034036050208454544030b42d040a800d4144a40c4a548a29903800b8440041410702545001180c21504d86800440c0418171701650498842c204011a9a0003002100210329080f41e0072510f00e40c220300500078609111b0008400d003d0580201c80960000f900508031540300d1811510084c0103c400d403003003402150081002005d5402c000c138169040c0c410a030001e00150380b8004c910412036440441000d4a00710243c00c800010350343c0114048951158201c04501070b0504207628442800c81c0c01c9507225610f0214080c109941126013181140d120032403064541020715911824030b9800f011a5034410010700c1041200c0d89800d50065482405504075130450b83c84503c142c82640c0c01da01c010f409a8031904001200e00c05035002006500f4107468042244c0340050302451500300c081e0011 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 693344217 1250 693342967 693342983
    0xd1104030609030c05071e03111f0503010f050402040e042a080c0109120c061b02090108010207290103150617060105100302130b1806040b03060406060306080c040b1507 74
    0x100d05014082106e8406092000044502022000f600c03016161840c0710041c90441100c404040580d035801c42403150a650140401c0e48152003080103119910900890006440207400070840d420144240c1c1d0039031f4070300401d0156030303100c603154599103004040b50f607001040988503904200383c000c1103940062041c50000c0000d840c1d41c00002d403a0303120641002d80c60307900d00e20103034020072060a02c40d801c865140c00e0241004000c1c440c0d02d640902002800b940004100d0f00008443c10154003c0c1030260203145019030508030310300b041c0c0410a1a900007080a030a84005001040f6000c0e000c03607000102c1c0500103601c0c1d40d58100c01400072000902d1070300540011004004608104450601040c4685401c601d080d0340c04401101883d0719004000140c5808600c0d40c0700d800464821140740e5800070a156142d42d541c01159540303910844a2134040e0303040081c00680345019008020540e800d1101074420b41c650303002804000d100b000c1c6c0c002c0e80089592100d0302c003010b0080003080c255000d0000 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 693345323 1106 693344217 693344237
    0x6020306040c0e01120c14040e1b0408060c031e0403020307060b0303040f14060424030f091e150c0c14061512101e0f09080d110403060903 61
    0x203400f91f49000010003154200440158034841c2803a01802c25141409501c802400d003da849890320079807040300400d0070f110f000c1e000346502c0582c0c3c018080c05404010015509a40706503015800b582000941c071080c0030440c02101c0304080c0940080d880c10b0700d0b0008000e0284454411002e0744481c5840480032603855408590040039862000700b5031030303e108030703c60100d41a401d00e080030030301e010844c0305490110300079854402d402812103508030040710034004502e04440c0c400c603500d007241d442d845028a000d100c2d0049881941d03440561206c1503280c031144074000b02100700d08540c41113003000903003208200c0700d400000080d030f500070705000c6081c0348525286001c5401003265040010307a144011029401e003075120f9000d0420300014140500e0401118540240504824810005c4011580039600125200030252030510319140c2e0b41c0c2c0300c100807907200d040d007180003031881c0070 = true := by decide +kernel

theorem cover : BRFrame.Cov 693165467 693345323 := by
  have h0 := BRFrame.cov_init 693165467
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693165467 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693165467 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693165467 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693165467 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693165467 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693165467 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693165467 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693165467 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693165467 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693165467 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693165467 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693165467 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693165467 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693165467 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693165467 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693165467 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693165467 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693165467 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693165467 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693165467 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693165467 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693165467 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693165467 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693165467 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693165467 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693165467 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693165467 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693165467 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693165467 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693165467 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693165467 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693165467 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693165467 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693165467 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693165467 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693165467 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693165467 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693165467 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693165467 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693165467 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693165467 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693165467 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693165467 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693165467 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693165467 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693165467 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693165467 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693165467 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693165467 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693165467 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693165467 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693165467 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693165467 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693165467 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693165467 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693165467 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693165467 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693165467 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693165467 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693165467 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693165467 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693165467 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693165467 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693165467 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693165467 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693165467 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693165467 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693165467 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693165467 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693165467 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693165467 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693165467 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693165467 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693165467 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693165467 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693165467 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693165467 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693165467 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693165467 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693165467 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693165467 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693165467 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693165467 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693165467 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693165467 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693165467 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693165467 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693165467 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693165467 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693165467 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693165467 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693165467 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693165467 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693165467 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693165467 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693165467 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693165467 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693165467 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693165467 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693165467 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693165467 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693165467 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693165467 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693165467 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693165467 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693165467 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693165467 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693165467 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693165467 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693165467 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693165467 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693165467 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693165467 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693165467 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693165467 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693165467 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693165467 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693165467 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693165467 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693165467 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693165467 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693165467 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693165467 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693165467 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693165467 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693165467 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693165467 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693165467 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693165467 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693165467 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693165467 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693165467 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693165467 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693165467 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693165467 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693165467 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693165467 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693165467 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693165467 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693165467 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693165467 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693165467 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693165467 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693165467 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 693165467 ≤ n) (h2 : n < 693345323) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
