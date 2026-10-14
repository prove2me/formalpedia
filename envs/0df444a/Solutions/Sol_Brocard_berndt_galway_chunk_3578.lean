-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3578
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T10:04:20.482014+00:00
-- url     : https://prove2.me/submissions/98ed8e3a-01e2-4764-a857-4224eb6aa35f

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 643345323 ≤ n < 643525179 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 643346573 1250 643345323 643345327
    0x90c2d030f050607031b030513050610050a08120a0509031603052d100c0309061d0d050a05090613050607050a1704080c040c05090a0b0a020d080621100908 68
    0x42c00030400803168000c2103401d0400c541c6050036066114883d80700208000c143e220b03c00a42075500700d0708491105e503030202c1114100c0c140030585821a1003180101070140d00102e20010302d200e800511601450b000d003a102e840e10204410880d03080d400f40300c0150b0540f1541e401c1e00301001d079800b0f500000318010703006008020321102042d400e400507510140c034500c0b00c02e43e00401c41200030406141d80c03101103400142030504118203402401c400c2001802c0245041003240030002c07030350003012081d02d4034001ea40c03811a140c0015681c5005407810b041c0082d0041c001c030643c500f00340004102d0800510042000150340c1c0e00010060341c41004201c8081d08905802401c00050840048404580d10f2146041c203047c0070340c1a0b03903981c620380c0080c81181c4548075090b89501a03411601640c001034030f013001c81a220113a81220798021541c150051242e81c880032003441c4500340550280780d000340141542d066400d255030418103c80501c1145018012034000c001409100789505580300303128180d = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 643347823 1250 643346573 643346603
    0xa06030812010302040b09041a1008120d060f1811090619020d0e10390312090c0b0a0306090c0c050f0d02060103140a060f050a050703090c2d03 63
    0x100581b103420410900407590001440b000480003150490040703442c0700124000e0b507480301c0d004540030140d0700c806801e0280700106203403446880d00070004929481c1042c04220f80c1c664101d0818441c0d44034601d0f203900510040445143c2c1a00004503000c4054a914100702d4403500040700c0d80d01004603441d107044040030f14029641c06200c0b101c804042402d01c0103041d140c42d800310302d1007015140344030300304540164001c2140441c0710fa1210755006090450060391002c03020300314070403e21070702600410403844140101c15603900410154a43c4907030040161403030301c2c0f0540d41d9030b0000d0a2000034140c640030046004052441412400701680d652900302440c4d1741407550910b4540c0b482400030750443c22101300d1403030300060480d044a0303101d4422244080c6003580b8a04081c80d104000f04586d044c0882d05048110035003105010b000704000810141d1140c11095080361040c0c04003c0c0381085040b410400219000c8004c4140810b1451102c42c910340c00014800e4034810f50000c4441c40f24101d400 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 643349073 1250 643347823 643347829
    0x822080a17030a02071220010506010f1b120e0114090319081c050612010203010806040219080f0601060306080f0d0e0a032109060512010e04020604050907090905100b120a06030812010302 82
    0x4c031f440560050080216041c4107000a00782c2003259590303c2801815082007014100c6008600a416044150460a0b40b110b030b4000b0201426400c41500265583c24040d40c0d8240706c0d0116820020300400810b14004802c3d49291251800d00081e01d982d1030620610083c080c51581186280c0e031003c100040c5841c101d03041100044a4100c0c58465a10600060241e003100051464000340c040321200c10a00c20000f5090342e01d840341d00000c1c224054958001606140096158180d90346904d080c80000c1d00c07042c9259880400c204260010780c044d0021a01d040d0054020740580352001e01901401512503c1d035000014441045103000c20248a400781c4550384801400050050342c60147c1c949186407410000c0021b042c0641e00b51320410402040c00c65917803404440017040c0140071700109280407000500030504d503104100c401e90a05c000540000006c01101041e84d080d00e00490a02c40c001d0000500d02c0341c010170b9500070581d20840030000c1910100034140045540526608660441c414 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 643350323 1250 643349073 643349117
    0x10f0605040e0307020303030a111303050c040b0d05030909073e0a080d181a09010506120d14090a0b250804031203090822080a17030a020712 62
    0x2c11405800500a200041e600807007200c0e0400e281d028081004410802044002e10581612161112555000104201020900c2c03486031303404440800032500e5030010302c02d01a0b08204010590b8008002e5803c65113000003e0582081662070440003409800681807000d900c0c000c82c030421083d416a882016030080d0420528102c0d81c10007a060807603442e504d00505010b4000007680198440105040801d40b440d021200c040d0808810700d42e905040040c545c1c40801a120090706500b0807002a00c0350405080003084401d01c5802002d0520301d60204994240c0207102c450384944003041f1410b03495a41c01d1101e000707000400801c0756100b151b20000034444010010015001021a40d080045100c00080c0e030116900508540c0403a0990f007000c03001040310f010010a0544085241460112801244080c0c17002c0c40c1403a401d460340303c1044039900c110a010042161454004102040503030038050f5401224591001d820884596620340c4460303084514400000d407840b1070168501507180c4 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 643351573 1250 643350323 643350341
    0xf070e10060918020f04091e050c030601051b03070614010e04050a120201140f0907050102031602120f0f03090a0519060f050f040308030901050708010e130c08010f060504 75
    0x8244001480c1c00c0001e851503286100300326440740c8a001016014a03250100c40311200708050055440ba101c0305440010408001301c8080c1041d481c0c00040260014840c00b030041864801c1035003169580700044a26500200c0714400d51142c481110780f2441080018154092040002294110007015401880a016444000b4080601044c80003183c004500e0441542c3c0220a000e46403039148000d0f17000d45102c8200c031000e10321000c20000c02050000e85940180c1452080c1c542c043c0e6641d00499403401640340406005024030303110401072400c03130710400d0f140b10074800b40d0340c03040004070005003081c0c1b04001000881c1c00002e402000d03481d01d115400041d040440340884214004c99a0152042c903c2c0508400d101c81d0071403580a05001d482501e0030303400001e2200303030360b44c0c3c5915040340711380c0051303e981d180d96080c0004a41c0780ca0191a8440c140c4038801d182c01950354998890080341c3c40715500656184440c6400400c00380130a000b074001c100c110050200708039162030700340300403110466 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 643352823 1250 643351573 643351591
    0xa170f0a081206030607090b030a0b090907060909091505100812090a05010906120b150711040f29130c1e052a0c0909240f0103020d0606080f070e 64
    0x1070401c803140f074000d89048140d231400b0740c0264903555681c40c0d21000b40101080290b000d1a80e80c00c001415900156074803d4a00a03070740c08440c0c0799540c9050003a03898440c802444500c2c10030b190f1407442d207198855584900b100080b100802c1c0e444083c0d5003417010300c9000300e400000004840c51141840d41220009003000c1c41c0c2030b5400b40c074105000708990b042ca5200c01c80581c860103008602c0d070719a4a450461509603418640d54600d138600002031200800209016a04294030048807000b1403140d25005410f040c45076400c26212101c10f0280080b0405003584030920030110886040c1500c145c0081500f9620b079203108851240d030b402800f000141c6070307070100542004604030302c0019078000c610003c40141c0d016640040040040e090001841c0b03856009486101040548100011503490101520b13010001e0000d00e41c0003a40c0015040301d1124010361003000400041c100304c00940003490003500c0025500e40c644046c2414130310b03a84d1101c0c455500003a0300744400e90100c6c010079000f903654 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 643354073 1250 643352823 643352833
    0x80108060f0f0408031005090705070b090706021e03070b151309030905010e01021009030503100801060e010e130209010e060f0402030f011205070b03010f1802090a170f0a08120603 79
    0x8003902c05000000910003045072002002003a00505524409406050010310240d150300c0c18410041094000ba0401d4900c0703100e00300480c00032100480c484007540d0f02980a00085401c6a402d074174242c1c106900c460880c0f20400c041c00c0410300001d5a00d015a111b1110360007040b072004200300c1d0807041040644041e9160410540000f038020b01084119442070070001e500580c104010307800c103420910500b65082c00c05802c0020142d11800442c8940f424000c2500c0041e10f03151000c0c01c8070074600542203845018001804451001d500507039011004102c0200b05e80e0107a404560556030a9019041003814401440000c0c0b8200368103583c1c41c4c4041d581107003580307002c9040303040000062180381c4020b034a00591605114050041c0d1002c2e240e010891560b0f560345029008158059201c4d085c0210190010b07039402e44881d000321154200c0c0100350107006420a41038528480546454005901c40c1c024004600030051081a0307078076014209039a20f4008000c07040038003a9000b00258840e03000 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 643355323 1250 643354073 643354081
    0xd0c021b061602100201090b0c040920040303050f2a1b0d060e190b19020324010207051306051f12020a050d05011401091406090607020a09020a080108060f 68
    0x481e81c0314888141c3c04a4203010442c2c2c80800136401015022000b0388400340e12000c000ea404c040d0b40080084071060b060811003040032100000315401c4078202e8551007401040200003007441040504080000c403403d05242404040d05a42c4a0400a0035003005054010b0582242c0c03609110801c1b4000d88003d4203022014414000344460301440001001c940d59042c1d05c00459408000c60034458102c1f5a042c0385c040e18a081201070700208480220b07010b0020a06514019010f00a076806080075154a0400c0780b4001d01c903484220360b80500750b04507c62968002170594900984000345007213940001040740c205818040c2184800c0c80d000480100240305d59115176001081e50b003c0441c1c0c0e81d005031a100300c02c4044929118550060043c50700b44030012803940130320810704204003001d0300d580c40816920300d0030700380d4125100d0605900c11000c1c8170b00b54403420030500800f000d500c0109501d84945c0c480c4003407412600001a401d0004100c0401440710300c0082203410f0300b019010340c1c002d00c00e00d0 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 643356573 1250 643355323 643355347
    0x6071101180b0907090e030c100c05090906010e040204140f0d121229120607020c130e010203090127050601050f0301020705010e100c090e06040905030d0c021b06 71
    0x50941d4000700318003400000511610004c1c00b0030310207004000740a00080445011480c5d5035000303034240f028036014010780039890350428403030892000070644840f814103041e40704100703030404001c0c0490b042c04484640e1105980e0340748010b2024028540d4040038500c03d000070b2181441d48208268002c4030a03007540c0c00804c4c060b00307000500c0030451903c0c1c06030340f0500c035042026005202402c1c011085448809001c02e039110b0203407915440a81c2d10140d60300195007400d540d80c00c203a85a4005da080740c4058040c6007800821000d8480c41e000c40800c221380f0b00c0d1041c03402c82e8812145100c85942d0f5401d03c40074901c8035460030303100841c440490108807001303844080d1a01c40612502c4e110b030440840d075189070b8500307405030f84010307030041e0080200c102c80083c1240c07a0300140001000741c03858404903c0358180100c5050003600e50a400f81078441da00c0c003003444000c03c1c5840c030030f070381601c001d01280038903080b140121964805541d000d0706140801c2010780c2c400f0070540d04203610450042c4034007041d0702 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 643357823 1250 643356573 643356611
    0x61e010f0902030c0c0a0b0118021207051b061311010c0b060123130f08010c020a0206030a060305060717010e09030319020d02040f030c15050f03100f030506071101 72
    0x610704020050703881c0c54050402026101d01e00c01e070070803802004040030074001e041c0c820a04986e105660b403203040c011a2906001ca10850f0300381d22141c903003100840c002074071490180c0b41c9603560140a0801c11740360481c1c1031070820210f40c13046401009880000801c280c41e050510900000e013401244200ca942d00c0880b0040020003980c10448822103000109100001e080940c50265100076941c0c109111106052041c60240558020059900064066051007081160402640a4043c0c01140e81c20041039601c05407011003c0f80c2c5030307000030000c558240812070050440d0b448204440110010b1482c0c40c10050384030500404d054400c20201050120449a0116054602c08918403110240c14000d01514000b12071482c800f02e00411030089400100003a680a801d035900540d5031003016903014409a11a800004c031306100c409000b00da54000745810500003041c1ca2800303600c1d05880c50b400180ba51050710745a0104041c094040d0b0408140601c80071503000030b00480b21121203d280c1c40f = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 643359073 1250 643357823 643357829
    0x2a300b060f071704031a07080612150406020c030a050d0b31061e03020f0301051006051608070b070e0306040507120311030c010605100203070c090f021209061e010f 72
    0x9928619003d201115411040b030f00615800f0410380c041800004c020903581d50100c0d08900030880380c00215099141c020000c10512885c0300091906118002e80508480c50140c0304130ac0a40e003d0298801801c818009020045040c0c3d883c1034903035410041a105846900009601419000b905110455a10305c0107100120300c140017902074401d13100c1c22a0042180740d02891616a030150f0400001d9160050b03c0110303802251960b140301030722400c00d401ca4a007070b246220b03042c0c1030503410090f01d4003e201401080c0845810071415070540d85032003900758480706040340e001c103040e010000f80a42251b4541d80910081d401070805180c566100b0340e4a48040c000c0720001d4860300030b10410980309040d40010f840708401940e40354400d07901080d0103004140105ca1080403504840391140c1d00c0001a152180d40108500210700d28000c0014014080150070b250300719000c1000c1c0284503103c0d10580c1c080e50125001340072910700040c06480c489082c0a000154120f0701c001088880d006548013015 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 643360323 1250 643359073 643359083
    0x9150f0603060310090302010b010906050c07060c0f06060e0615030603101d1912170106052808010806070912060203060a03050709050103060b042a300b060f07 70
    0x20342e803103040c000f91a001503014805222428100094101503041d00420284c8601380c0300c506026072221011b8500e0f008101c41d98400e03501100080140304c0c81250100310150040308041103012041e01c0f0002074681a80003038100020140910405041485100c144050f078403035501e045003064000a0303141c1041824451b41e10762210210a15032506105035411481c41c2c100300c880000c40108003010280c186042925003080659030170400714040c4400c1030060b04552a0700e03c482c0c0c2024015551b0b6045100e852900da450003540040c05524411203440c05444c1d51528100740d894103650303502c1e2000c01449101000340a103010014200300e20f03a6a681c40e030340803101580366514036010801002050b44041d0452090304070000c0c0101196001c581601d0084400b0300c889110641804203075000717810f03600c030b41545000b840d19024041c1440032280c5500d62405031980d01004031284060554907099108455102007102c070824003c1c45404a4882e05440c114107011101940c603215009804010784 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 643361573 1250 643360323 643360327
    0x90613050a1d0f0a020c07080c03060a02090d0b0421081f08070303051602041b18051819020d0b04060504110f03100b0a030203011d09100c0203040f090b09150f06 71
    0xa4403040785c0c040c1c0c1c920045100c1110301752950707491240c1d501d0340010300050090040c0404581d00c01e40038003c81d0000c3d07902510401107002541d990418610009005950aa0500942c000c5541c020031403084c00e4009940d9400031800d000900c1c04070141c1010007018000b100e45800c111450000c80c0341400c59402d030820980f80c001c00c040050000750030440c000e41c800c3c909403280c606c038849050300040038080d66031160355000a00740031401c203200750b00405501030000d510141c10120741c4c1080030b510207202140e05030200340c0600044140c0e00006103410015480720707426101c41c2018441e9100034030088805101e8003040c00310100d09442206460041d26800000140113556800c1c42e1800401c040300c8616683c0b200b900d4028000c0d0405e014140d0051803181e540080b104040c1d8035035015491180c05820100c0810040c0402845000d0720b03003041d40018800010710000c9015110000c0050300004611501d4030000c018610710014021071120414030a45401502c030781c40012804003090f10380c03603 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 643362823 1250 643361573 643361581
    0x909020a0507080c010212090d0207140315040b07020d020309060315011e090e06090f1503011401030605070306060c030c081804021602030607020109081e090613050a1d0f 75
    0x9039940b14100c4003410042001a481400340015070082c40001d04031860070049490700a485500c0d90075140796000160300507002800010610381c5854031030740004040340c3c51046002c03a0004120300480302610001103e41c1003040543d0140701c1c00f404001d4610166107050041400100f5601020b8001000d0b00200003a0036140d0340501d41c03100d18180301c2000c40704403918070700c40242082a18000c059400d035401000c03903500c0c1440c145441c0900070320780d10460f9503501c5a045108948420b441c04d0360564a0b4401d4486182e8215061030103180510740110302403811900103020750710b40340c0c011402c100b03240007094086944065207000444e031108007290340f442580c24a000d02401107625541c003510000d00e01d1807910340d4454200c2c02074802e03802e41c3c6107950350030420f901700c424031240275103001c00400c01c49120020a00c3c51064410103e80094240041a40480c200b41c21003400081c0400e04c00c0c00501103454090241001007503103410003211508030440c81c00c2500005001d4103200800034001c2 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 643364073 1250 643362823 643362827
    0x150519181e05030f1903090201171f082b020a1b05090106030e01060b0301050105091c0f0302030403110a0510080a090602131806080c090403050708042409060909020a 73
    0x1e8089600070040700e403100846120082164804040e103c400c0790b82c030040724100c9019010341004590140c403096840c221420b0310311090000241130800c50298a400482d4035114441250054120034005050400e611b450300600a003d0120300003440c9504460045126030001c0c51b03d02c0d00354000c4d040d414150182e010002024100c1e0041c1e50b10810701c0f00046880792740341d407003050701051141c004d0011656992201600303100038010940000d42c00c220251082c01c1030003503244d5040c0320034541c0c1d101d481030f030310340c00b441041101d811001600006030030414003103400c2030f0b25030a1100f154004004c928007000110301071044060101846442000188020300c40d40c011705c49030390440c609540d201c4490305202c0400d41107011b4014034032041701415106814910461043d1003c4070010014006803100300030003600010070403410813a04104880004215402500043c081c5182215840d6107000b252100840501050020088014801c00030540d01c10103800480300b01d64001a5504060842 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 643365323 1250 643364073 643364123
    0x50f1314010b09011d0a060c08160821130605090a050a21020604052104030f0b040b0606070b0711070e0c04060806030f0c041815051918 60
    0x5101109603450000086801d5407034001c00725200240d035580d0510541220708010080c89030107458210426a409004043c054403001c5111741c040d120590500340a00d060600001040c0011035a9010206000740b0714820380080c41781c1c592800d0302c80e40d030038544000e9011041d019400007609054448020540884003403243d9001075411a058828040c11800c1403202071a0741c580303034070340481e4101010b040d852001c603903203020315400700141102c0d0107c81c820b0340103107070881c0c08103032804402c20001000840d286210000c5500c0b82d800314045203480e043c403c14902008000c1406440100503000000d0740342000a90f00c104181012030350f140c001c020a0346801d64036040b0481c40350484040c00140401070001c0c000300c80e0700d9503400480d955070314107050300c4401c0505011503d50004203000c24529003034100c0c400c2500840b011092040054135103221121214208991160b40c400c144000d2540b0300c2040e1101d0701542c07100703104182c425643c540603a02011806000111002ca91000784005135107 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 643366573 1250 643365323 643365341
    0x20d020d060b0a0501030b0d140c100903110409150c0905130603061a0d2402070809042f090f120f07122d02040f0c120501050f13 57
    0x1122821540c001d1400304010038101000c54480d0341c190f0310000e8291702c00d01414141ea6005003076900a498103680f4a04201070100d0240301e20300803040040007944441c502407a80c1c541590300d8210151540c1002c0c2c0680c2da034800c00c00c0c0580e0500045e00d02080c54000101e012050380c403000145513081c0002141c998071a500002e030707c0310030011020b080c0079458002509882c010361080000c1c0541600510b1469100e840300303900040300311032507008214481105400900d855902081c40340304a50844120380c40060b00b101d00040200781c25410742170a100d621030405441108e02000f40702400700c2901c188050b40c103810750b0040080c1080198460001303210031000041c1000c03400302448030710251940780d42e8401d02da4a01c034400c00020211103c102060100d80c010031070070903810b07036418212000c01003020040364401541d011440103880c0d61240c1500c206080c10001204d000e0707070100a102c48245c01140350240c0c1420014002d80e034603c410022202801c43c5c4030f0300320306244807050307020b0300e8050 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 643367823 1250 643366573 643366579
    0x1305101416020f0301181e080708040e10180908040e25031109010c1115130b0405031005100807060f0e090714030907270c0c0506060607020d02 63
    0x11901ea0394004400000c4580c0d64400c0f11004950916041454201d88a842e1044001314003001c295012900c03d51096111013010b4104003c42515034842c22142d5204000c11602d4030740c0000c080200411401d11590483e17541944d8018503450a000112048a118010300156990700940c4c402c0004100450307004142502d442b1a0364a04054180d400307401000b0805c028420040744901d600d131180c0f0410340980706080781d1a082030b05010045034070344e80d04182200e441060908a50740e036555040d018410140c40f902c01940c40500b00100020020b083c3c1c4440c0c0644c0051009006503a03002c112685c028105150000e141d030f8540c4180c113440240d82d804090315028604001c00e0503584654030b80380083e807a07240c00e64249030b62410310145010850303582001603003050a0b1201804080700458109684400301c401c100d8844440700002411110890b00d401c210321140068514070703010300e00999100d801c10180740a144c0c0c5070a5100c0c00002c04d8684165030000340c0d40d04650302c04401503038090f005 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 643369073 1250 643367823 643367827
    0x30e0f0601030f0203070b0412060f111c06352d01051b07030f02030c0706080103021f020d05070f14030307030b10050f0c01020919030b07020313051014 67
    0x70303042c603189840e0034600985c040d008645002ca10a08401c089804861254025800b0b0b41090f0b140d5000401001c81034000e09511459030440103001040940702540c0da645030300107990302c81d21071141220460303800100e00a060131052402c0340030b0b04280041d00e42480e081e4054071048c82c1505820105007447c10390003a402c610030744201d00c51040c1c0c280c48013800380000b048240c17602401c05d5140240014414240c0d00100100c2d800684941c0803101201d8103801100e00308104120b94038200303041d9401c00800620040010015031030089a00c03c04d4140b83d050b01440c03013180f004000c0d00d074280f103466242030181c00110b503000c014010000314800391b0420010491603c1c90381d60581c07260b000f03488181c00242008d1019440f8a07024040071501c06d651b071515842c180341c400e02c40c0c540e608110341d00025550f00780071241060f19229441450b200020003060074850551500e1840c84d5400b0b0620811075100b800300c541ea10100a10f000c0c152a0100d925950026061600b00c2e8207a4003100302405d25040 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 643370323 1250 643369073 643369079
    0x1b1b0b09030406020606150a0c02010207090203010b120a020307080115050708040b19030b01120903030204081c0f0323090319050901090918140f03030115080a0c0906030e0f0601 78
    0x40070018005551541c1d003900c1850b162a8104168900c102140200c140d0f010081c0c8c86c1541e000c0c641520000d0300c10300554150580d02c43c1c480080740c00981c000140c2c0903001074400112404d0035a5150f01140c075060441c111304204034010948031050140d0300c41c0540c0d400004180394002e005a03081103070f0121342e4039520703912024185166003189035258103445080d824003980302d009002c0c8007003417081a034605007038504c00d1204802505641e081038060581c2000b02050094003406080d8011403031a903075800040544100600542c4402c41c407004151401d865120804441440c01c181428206c060b10029160600a1400c0d48151803a0803540c2500d0714144001c2f942100150038640f50980f01d2000c0c02d030365603003520165104c03400c20000e115400c90b10000050003018500f100710500c0700884150707107407020019185130f200f070308440c07024007541107000c5803150300044a6600100e041700c01c1c8820480b003240035001c50207901502c41410348034421170b44811400c11050007100980c200325121965 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 643371573 1250 643370323 643370341
    0x3040e040f110105090904120c0606030803010302270604020901120905061f14040e0f0703030503011e03030e092d060a0f0509190902180a0f1b1b0b 65
    0x49103001c0315044080b08088000d58042d009551810b0703c06440c03210b065460b0390340c480d043ca00760300105040c07100504000c004214035224003405103100e0300da116902c0d4114010820b08891040d800440008150007801011660f02c100303e401034015a005a181c600740d000584411502c00c502e502410320785800b000034860f000884a005407190015a180d01005030502d880e80c900500a5061060303000072640024101030f800a150b04890a044e60400308202c0f00841c204209a441a0300141000c8014003c01d08042000382400c0300000c080700c0300b11300d16500a030483c040d020034588560b804800180c02103201c90b0900040b8000707040ba20000c848142c10f031701445582550b21078080d014048000c0b40481c1400b021500340c2e18010108840382d500d00c410040e5020100c919840095181c0c0c1d21080141c480c48610140d800c0100c80c81102460030b180c00d001141d42d46140568194204000d005680f071000d141e0244203034252600b4010b4a0b2804420010220490801400b00359001e01300a0614 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 643372823 1250 643371573 643371593
    0x20c06190f030e032205030a1b0f0f1e150f080f01051f02100c050406020c04110f0711030a0317091209040507022a031212010b090303040e04 62
    0xc5607511507854000480a04600321000381045903010307401009100700c102c24445021440c0b20042e0644014540c903000400e043c000c0b682000c0b02c0000301010b01d021340d80c15a02d16140a0310183c9101c1da0341d286460140440c4150510414041000c0d10401c0842d02410b402c0da00301600703129510005084601c0c100800350304088900200060307002c0d000c00c0d08072020a140398100c1c0c20003010080100140c008203100d8000d034600500c150310030034094a598803414041c1001d80b100381c0e21150349661400c0c801074100113086c049184114500140a031030b21a80b60180c2e816180841c205a480b810030345404114407044400c00b96061060a980d5810103900840c84690f040310943c1a03c415210609001d80d140030300c0c85201480310017400500b500f81050f6001d19801811032040304c4414002502480740c1e2150f01c4181d207640265040010140d080800401c01142c100c00e42840c90301c87c4030305900c07103004810300400604403000076450000da03404105070380150410042d1000c00c0d0030203241c807030320304 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 643374073 1250 643372823 643372867
    0xf02160309050301230a1d240117151b070807060b060414060904091a0901060b16120c051501050315040203030a0351080319020c06 58
    0x60760800d00d10b01c6055200300381c0307801106418000c1d080170303468401c11071002d8800a0700322102d80d034022640802121041112000003102c454580e02c0101e80c6d40300c004200c440580281c903542c1850819a102203038001080400c60f40c0c0060b80304010b459075100102080201042513201c0003020030207400303010b030701c0f001800c405204d11804c00c00c00c030b0303008144400c2c2d019921a0440c03440c01d8004515440c10050014504090000c200080d0040650740360004003003052540760105211204000d5040d44c00d21070000a420102007075404c0051850007484400c100c001c00420089030b0110031044a402510b071106020750020030b0352042c0c0194034902003040c009100780d500c248202803a843c480112650b00350701681c1c000c0d000c1d40c90120f442d04240c2c064401c0d010010942c444140c82800c250008130401000a1880200f24000038860030703040840d0300744042c89180c1c80c107031071404202107500007044a2a207034074a920b00703222800c52002603003016008074409401250020f508451140040d40c5030401c = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 643375323 1250 643374073 643374079
    0xd0b0f0a230102010b0a03061808070b090c0a12080d151517040c0e060a150302090915090f0a1e0c0f030c1d031e060702070b0a09090f0216030905 64
    0x101114001c012400d86803c4540e40e500907414200030301c0402c6450300040c2081c000e0f42e00c05482e55801c1d0b40c40c0b04c3d4075880b011050b07403203458160078410003600034001960f001c101241e5201c48507040c03010442030088070030b00051090740000748100c0c14407500d810001301c800d1003c010441a541c3c030b0040311001840d80022400013980f0346400301402e0808074000b4000c1d508410049081400c00454aa2900000d404190b104804890009045000017120070f010105035a0241e00e94a540c001d102500d800609800002c0c02461009000c649804c020581e0000f180b06004205845640e03000000700a200c041040309400c0000c101c20590103078102a101e5821665801c41c0754241d05001c0341100c052100710380c0015001c40307483c0900020000e02d0b0307040c500000d0690f0b0140d900700c601103c4403d40f00c020107825800c003008001c2c6854060000400801c10485034510307021041c0b40003041d2509600036404155038803541018266000d0741601c00ca445080d030041d20070445030501800780d45444c861944 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 643376573 1250 643375323 643375379
    0x12090b091c05190503040204090c062c090406020702060d05010b21160f020f150103020a050a060c060f0b060a030e011503080f030a020906120108150405030d0b0f0a 72
    0x40c6910500032034005086a00e50b10f03041a004600480d03059101070016640079403034403001000303c3d0100b203190009124603100d0b1402c403d103c029648610111222116009035907181d4142e49880e00801644d020b40d03c502d0060780c605c802e1000488502031606039400061070807001240154000b0000c1440c41c8000107a88000e40450000304052081151000c4220407540448072616000c0d10410b02ea464075070060711030350700141c5241854640404009207492004000410030340c24004815009001d041d659815100d0800780040c10803c0c20600007000190380d1280d0810304d107560740c0300c401000700090071700d690340c800080010003030030104103c03a02d0b42d4a42040341c00705040c038094070400c49900081c00382c14030401c002c0c00e0344035400c02803d00411a4003000716004565032800142140e4072100c1000c0120350610103420714200e100380c9941c0142400d1000c0c030003c608004156404034456440c0410f1204180c00810000104500441d03040b00f4403610104000d181c11044540c5004035138a120 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 643377823 1250 643376573 643376623
    0x40602060a27170c1b130204050a1206020409110702090603010501060f081008060103120e0a0b070f0204060b16051c0816020109080a05091003050405060712090b09 72
    0x601498260a081100900e07401e1110000a0803d6805040d54141458003410180000101414041e800410700100c60303052010300ca46240c524407100491070600400c40c2050f0821000c156110554000d44042900f1610305508026090301218050301c0038040c02c0c004081d60b40c0c01c0e21941e070803251003240300e00071400000e826428144116812251565034075a01d00c10440c50036101c82502900d4140100d00700c240205480340100001d500861140e0b08008104594402c024803404084e80c0340d910031604890204541200441035070611501300d008140002d8075480060700134a0310341c0c080100c200d00450904079070408401c035603001501402c15030398050082942e03030403041030520508000c6081d080c080b030010300d48000f1240b029816800001150481c40d240e240c46500a021440c001440004414400d4200700030f0b04044184d8505050220b07040543d01c0d0380d203801004005104001038180c43c2190054642c12030b00c0310a410590340c1910f81040000c00e40c0707403101c2055410321320441d1884a = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 643379073 1250 643377823 643377851
    0xa030c170f01060e0105071b03031d090a02090d0c180b030705030a0b060a0b0313200d03030c020709050a02070b01050904030207060f0e0405070201050f010801141303090b040602060a 80
    0x940315814641040c1d0590382003500030744080e0116404541000020300c034400c001038452846014501080c18103400292543c80c00a115508140c140c02c1da01403000c4040480380c0701c003030800383c0050f114100580c5070600388000c03542c1c07a4440d10b000b801c6548401400201d03030403540c1125200c1200c1000034032400e00f00006040e40c41105109040c0c041d070200803984c0100c5d0f520403005030001c00090046c210269111280c00c260340050303c4858608502c42400e200700102500c103801c691000c80c540d00c0e00075101d103000910820b000b49010342459140c103407400740c0b0361007400030b80050001c03c10108a24108944108025002401c00310740c140b40380000402c1529004080d10b1107a603256000340350329401d000d0125804ca049043d54414007080140c0c1d034509030b03514083c3d28812240c99000040602d00b0691154400303030184e10900f01a4504417040c40b428100f410741a9211076000da00d071880c500c60340740031651441940e01c502400c0c2400b04010450700c0c0c1c0803c6450251041e0b50061101e81080110 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 643380323 1250 643379073 643379117
    0x80f070b0306040207060b091e06090919030509060d0603020f01081308090d02041b080f0108030406050309070909080c0106140f240c0d17011a1804020a030c 69
    0x1800c22152001c1c80019014034094006040c0da0384100740c085640e103d004042008028141c410407140d2401d20840061000c910307103074590014040b11254a941401b140c02074031b4081200c46d2800342c043c80b00c1c4840034903000350116040104040c014a82da03806594029000384942d02089201789045284030a9030342c07081003028003030b079901c00c06409800a9960385032002c0d072206810a800503403405507003000d030f0b58520900c910005201c00c08104015250001010a80f00a1144201d5a8500010f1011030350000540d020b881c2c0c5c50800c80d651741c441c00c0d030542c580490b5500c80d080c0b1600b004201d00800c82e04002420020341030400a10945450b0b000c0d801c2c541c581c03d019150800c030461030445003854040701d80c0e000700240481b4565109801042034410341e2204420342c2c400d0744868100b00d500e03940036543c00c25401091107491465410143c040b440a0311003495891402c5001c501c45c0c80d4030328000020054104020130840d0f460351640d5014020307050310b083e1000840c0c0703110460003e040030001 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 643381573 1250 643380323 643380329
    0x30f010204061e02010e0a0b0a0c02060712090f050708031e1c230405240c07030e01021608070f0b0a08040201030c03020f0f070506070512070c020103091b080f07 71
    0xc4404216000c01c040d1822150f142c90a50115902d0768a5240d510724103101051400380184c88241061403e2403203101500c640110f01c0085501001c200f003013803a8450786000006100c0c07180441c6024160070003841240cc44c0308017800c02c2c090b04400080e6010b001004165617804902d07171741d0b54080d000041c01b140e4080c508a90154204c50802e01152040e01d500010019070300a41c01c8545658085484459200464080710986d009400714446056151968219445400c03c3e04102c1c0c54131040301c001900800740000d082c8030740d04500381c02d40c1e1300030711a0086181d41203a400f41d441c0e41d15540c2c5a940c140b10f21801d0052302c100394000c1a491080007c0702c2449450703803181c400c5920b59034011002000380c06c0003201010f0b030030701c02541c0c1800310b0001007508c40b0b1151080780d02c840d100c1c10b1246c1000809442c0c1c40621400b08900442e0000344410aa4001c1c12424208401580d07400140c0c040c0c00960001441e04448120740d030901341d11403c01506440891003250010f43c01007420f030b5a1400300340 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 643382823 1250 643381573 643381577
    0x3030f01080d090902030a110705070812040f090902180f07030b093d080f0c06071203111312210212030612150a051f03060c020a020a14030f01020406 66
    0x201405600e21342e800031a0040009007000442d1540c111580001c0c0e0041e00040350103401200040020180c1000340040311480641c01e00d02e4107242140070501d00001d440f42c2491992203840800c25580d07003041c504219101126140620b203024134840700600030854044011a00e0085001c4460802ca80c0013445144409007800e2903007202d130070340b1100501c08950701100b080201c0c0d900146980344030502008203061001045440400800c290402c0c54031030341140503141c2804540c01050640312045240012400c00094505c035001a04059110b0510740740c1e40580012800103824441c262200d40040c0038500304242c2e86101e482c00352403d45100d5201d0300607071011120301c921341d090100440e04848001e01c940c121044110003e8201503803500001d0018100e0400c1000c18003250081d1540002d041d40001d00c10100c0303604081854030107000c09001e4075540d4002000c0780b130007040000701050f00208240110740d80c2d0700e04c281a000408a000f03019000d803404c0180340940500030b580c10750f603560b = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 643384073 1250 643382823 643382837
    0x39030f09010c14030a120f0e03040506031009090c0305061b041406070b0405010507020d021f0f151401030e160302090403090e0c0a0f08150f030a0b0903030f01080d 72
    0x80d001141d250740080c00650b0300c0c01020240700003014041005100c443c10a44801c00baa01d0031800020455200c084411003060814a20b03450020010007140c081c1c0320b08807240c0344c032a1103140c3c41c07806100c403d41005150a2811914005204075000d6400407a4820300c204c518656400014903400411035100c10700c040b0040c001803000d2917055030502c0c00c207c0040c0901d414590a43c4850024000079641aa22079544101341310f4405d038140500003284400c2d0000b000b02c50071418039201c00031194001a40c1c050340c2e5021107040c0d8440f036080303100e2009000381c4101e4410b032983c6603210303000008001c460100780303000e0001c031002c003010031550f1a003174011000c036030028599028001044401001103080040181c0c021600d44150b40c101806800404283d03a102d1410110140003078240542c0001842103680801156090b01e00c034a180c600b038151051203010071030a000c00d01d0205074100003008000e6410070006008400009144640c940099094550f680d40030ba840e1a41a074010748400501c1c8 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 643385323 1250 643384073 643384087
    0x902010c060b010c06110c0d110307080310030609030e1e030a0f0204020912010b2d0d061116110604050306070302160204050c22080307020103090839030f 68
    0x180d8052050b000040c10800c00c1241d4030b6580303c0c103d51180c09802140310022400b290402020003100d481000b0a081200b840d014030400703182e5034001e2110080c503401d000400a8000c1c5044035a2348000c42d406641406500818540a4641d540036102a802815141182e00343d81c0130360011380001c0c030b00280142240c0d5581d030b25407940c100b0700400d09a0300725800300103914140e200c0c241000000804c0704000a980f58000d000c1004c3d0100c55840400c3c1d4010805003001006056044507105220486148415150500e0400041d080d9055070700394451010585500c55040356601c4114207220310107200400600b401005170b24080c0380500d40d0142e00040010303210b0b5010780d006042110700000800c0060b0481e130700007000d44100b00c0310741450390808154194542e070361400d042c92903100040b20072502c508100c0503c0e501d000d410390103030401d82c84014000a0120f610f04449001c000d42c0d0080c1d441c544d08802021440c1445400c05894060100865903155008800e54040c80e01c040d50562030264 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 643386573 1250 643385323 643385333
    0x61a0d0b011d06030603010b0d0c0617060105041e050a06030209130c0804021005090a150f02060402010e060f070819020f1914190b0709060e060d02210703021c0902010c 74
    0x40101700300d815660f00c0d80403078055600ea541950201e481828043d003c0c600b401e8008044d801141080400e0709000818030035260b03041000e407002c0c3d600c00c140c01095024088903e80300003009a00158002010b11004285164190010440c200b8181c031141a10382303140032030f40c00303c038003402154001503694000300c0d0061801607104041f0010a1400900f45044000000c002c0c07405a4407411062621b02083c668890b0030034044500103d841c00a01030340d20300303600081c0051a4405c041031113000002180c443c0d0490f003005a4000b030760400f40041d1070b0741d10380190b011481480d0850801500c211034140032000340000341703040400c03015102c500b021941961416921424a100c92040d800343c1110b82c4482200300f24041440c40c000c1c03401c5c21031781c200124054405031103600103178104000d25154620546400048420074107900c20016580c2e000340000306000c0d0704118020001c001d1290900214a5140c1c0250020710700403003c814803c2c0400c1d610780103e07995070380b009012a4003481c0c1c0c034000c10 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 643387823 1250 643386573 643386577
    0x518060402030d2708010f0b06030402030a02100201021606090b010b2d04080a26090901030b060d0f0b070201050703020a08070c030302040807120b090105010b160303061a0d0b011d06 80
    0x943c040c0321043c4c141e2049600010020130b5802c14041070307640d2803002e4010b00030742c051806002d000740d852501c0c500300b03038003c6901c56201a9029009000d01000013110703038401d50403030304a140420219408400645840c1c0040e104a501c1600c02d14070000010454026080441e402c047c4500c402600400c010803d10841c000c01a50882c00e45400b8003000440382024880c5402c0355218600300e4030781c0203014014038181250b1f0040b40c844010706210310001511107400c0141582d40240c180d43e190760303980c4000350700a0271200703000301000091070701c00b01008628890760f4010501d07034009004130758a4103021030880c00340c10642c0000480c01e5000c2a9098060007810580502a284c0076141a8a901541d4035000c9030794024462186000d100f502880781d028031150b000394800c4001d00243d458000344524a0040080490300781c28032140300c0c01094000c0d800000284212200e880b06960011801e080d41c1d0000c0012441300c1d801d000c4280b01541c4103203200401c103815601440140c1c0019410b1010503 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 643389073 1250 643387823 643387847
    0x20a0f020a050607031e03020a05120c070215030f1f05130e03041502070909020303031f0503060c0304060b03011e2721050f030414030702040f0518060402030d 70
    0x808182800466107440f000000c00d0300700d0280d20351000c00c480440d4041c030b0030940c030441001011704c18002c103481c2961060491303030341303c03011081c1314904c2c2c841c000041401e03c543c200c020750142c8900000e18006405034080e52240c9000e07181d00d00507644001c0d0041e0b4806800341100801c00c0190814021440e0004e8100301c0c8640e1580006922107502040a245921981040e02c50880d0305441e0803200740d04011040203406c2444040c0004070590780802e0340d07408094054074030710700040c03241c504402c2c20500e0708000f05001801c88000781044034250040c0d9105070b50580d0f049080015002c0c0606050182450040c14904240180c2428100010042184c0303540a03000081c0b080c40044d007000c4107002c0f1100c10380214682400d00000a0f01c030200c0000e81c50f4021306120b01070110907406412038040d20762050304040c65901070304036001800e00314815890000e50040c82d140d03400f05224540d90009206120403403810551100e200a125039900c0200c2c0c00070340c0366001c0009565403078410304810000c = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 643390323 1250 643389073 643389079
    0x312190305150907030e0c12070b0703050d0903031a0f180606040504060b19020d050d022b06031401020f0313061404030302070b060402041203181a030414060601020a0f02 75
    0xb451018000618500d0291080340000340c0328002a8036410085c422907131408000c40303a03036047c0e40c1c207114160348902441c49440d034512000b02d0b91b6014540508104d4004001c4a68204040600d80c50054010625803128803101850038424003500d09103881d20700e40c20400203003c07450003105d070b001c07400e03100000034a800d402010502c000592510f480c06030f2000382942011072900c40324018044c40341c0140b41d0b007a650441d0300c984440030743e840d041012a0000d440042015980c0c45410f510900444030a03040d9034611003c100c40807510f01c907d68841010f4a200d80300d004061a1824282800d03402024481104c562040011034041d11840003205410f910400c000b00b5103030030b000c26906656408072401e4000c2a0006290030810560124160303000100b103504500303050801710b1031003000c21400c000800380b281e940e441003078050340c01c80d0940041c004031304148034082c2e00e82139450407608155411070301205078080b400039502010480c1803241d081a4014106a04982c070b80001074848440c0aa030 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 643391573 1250 643390323 643390351
    0x3040b060a052706030d091403120309030a020c0a050102030919030f0b0403020c0409110103020a1419141612030603080a0f08070c0213150f0608060312190305 70
    0x2082e80f20351280354515464035840809086201000641c8094010075a40c42a0000710426003180d411803480c10a0359000183c0051128945010a1400c0c01d0049411200f02d400b204110351414000028803d01c1c03490343c26a0620039007239040c410b403c41c8600541d40540c000380300003d80d070b040900044d44540032520440848681c1c9860b8400e81410301c2d1000d503a0f807058a0108410315404016030303a1a1081580c080010f40903e4840682645620150350f04250700020782e54505031140c0c203110016001e1801040d541c4511645d0f520411019207403980c0880c1c051010020505540b40070b548a05029404000120b80c02d9940e0741105031a240c031201c10305035250404000309000b030300035041151060300c441550341e00c03990000e00700100c0140320000300f10b6000002c200584a030000092140e8000030701250032401c40c1380a0f0801216a0020051300328012000541a41c1c00320700c45015290940036500c10101e9035112006030f10903e4450889801c240d0b10344240580f09610080c0d01105081c1008 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 643392823 1250 643391573 643391579
    0x20d0c05060a0f021b0105010302180705121503060f09070609050d020118030507180501080609121602090915070206041a0606071e0501064a09061b0c0303040b060a 72
    0x1740341c00d100d5070100740b46039580c00040c0110309110111a40814510503030b000e02d85880d44000341540300701280c018441e06100e010035104040328a0210350504003d0540b5400d103841000e9441156044401c0784251160a4000952500582da48826524060030b0001448040d400564042c0049a58205280c5072a040000800d8050060401800044550f07010a10039501072505950060700580e05640000b4203008031150005100d400030042c0700b04494554601d44a5407014102c0c080d402b0f50440c031244108a01c5140104a400d810030800c00f00f4119a250400202da4442c1d04550040c6407269204440c4021003000d00050750004009125501d402402c0e030355620800130303901c0c6020882140300700c86002c0140070300604001e090090204811550700c60341c1c1d200c99081c510a54a00d14401149850b400c118400f0360454040382c0808000503401d0104500da5101e104807500c1d40450010101c4400c0f00d00928201c0f1000f071100001035095407a01c0d1501050010050b220359031140c6565800 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 643394073 1250 643392823 643392847
    0x20607032304091a01020a0b1f17060106110639071403180918010c020d08060901030b0c0c0f10020a140c0a0f06022206020d0c05060a0f02 61
    0x1c1c00040003204440703030300c89103043e2511081d180702c0d1611420b80c101001180c0a00c0e6400180784454076004a8204100e86070303a505500a07040200c20809910060500071504013241f100c10a0300c1c078524021940b06a98904080391050700300480320310103800c000d0101d0942d8580d031200b05411400c124100ca00c1c45944450080c0800602e80783e10ba0610021071003005001d12985840100b800f03c1000e1031506075030a904041d012a40522a4462140321010410519907070345440c01020419000708040d4803081c0b40039640c3c1d10750220312000218101c0001300a4206511003604032a0301c40030140c0c807901c03014400340041d00a508004e507148104d0b08480203e007010000309a08490507000160340307648031100245030110600340482c69440410008001d0100010700c94400c0e9000034000d18000b40f43e19100d0040c0c0324810b0a0300071020409041380e6150400c0d805481110780075022100c4140c60b00c0070647d0034005210700580076402c40700c009240f101e81a0401c1e0180301a801e07005281085071085 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 643395323 1250 643394073 643394117
    0xd0503040e09101803120b01020c04020d0b06390c04020d09050601150e0a050a0e0c04230a05042a02030f0415030b0a12030513030506240d05060402060703 68
    0x410034100049894101416040003d00b01120341807001403041e0484030002030742d1000840d00301800bc2d540010002c111030065840525403010040c40c0c940c2d207a42c42c1050036808150780034440e5400011080e60342c0002001d50401d0041000300010b0207c0202080c10040250442c00340400030350b442d560148000b40c020302a884c041c08116517036080081e00d10070700405031075004160b85e0041450394000d20040e80d07401d44103001c642c800c100d8242c240d514003090520300e020f242d1240c03980c018200000c0c081c040240b9123080c2910303803e60701c50024ed6642c804000c182c481c0d101006110800480c0408175900041c2805185c6559500440b40351620380307034a07002a40d20690004803405844120b05016035130601070729a0007130f01100c01903005800c01c144c0d09020710303680700002c0900000050380d1806111100d80d9030015900b1a055031420b2a0041804400555040d51241a40001c06500c0314a20300303042440583c0f81c020004010300d50f20383d400e000440d807203107005400f030058034080d1340381034420080 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 643396573 1250 643395323 643395341
    0x10e063c0d0906051e0604020d0204080616260a090302070b0a0504210c060503071806030f060e0c040b03190207051b0a14240f07110d0503040e0910 65
    0x80001c0c0b10751141002c41c212000605207100141c6540034800032a074403280510340040c070803100141e03030390f2072609003200034869a807214000d0f000321020004250210b4071080b0b81801039844150410304c10b956102001e1070320071600000303416038a0103e4551b440e0b03a440107420707500c00d00407103116035103551540c10550040d22103100043c000107424004102c410803d0031515a1100d00700e25281c40f5552480801c1d009402524100000480040c80d81c1344a045204804044c601403007070880d80746c4e80e004001e0003124114242550900070001200035100303d006115500728038950f801d01e400c0c4210344105034006440807c80f07141c012540c1c0880d00d03007440102400d03840740e4010010b0320900036401380c12102094003d40f00b6803201104000b1200310343c4591020060807600c480345000429118030980002404000d1400000b141070400300d6540170051444a0003035a40c0c00e078032006002005485403941c0c1d001891908144400c118082400c01656046a081e10580da0064564010f241c100d0b11201 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 643397823 1250 643396573 643396597
    0x31b1e03020301140702030913110412030e030705100507150e1e06070801151106040501020406020f01020415230a0309170a0e010e06071e02010e063c 66
    0x85420800c6107024841e10030141e019044110a51815010294072030003040b40b858064000d483e0010503101c2c113640300904000280042075100d5071110007003d01401e200c0002c502084c03184030039508034900094007500b111002002080f980321500c5d400c44140d0400e0a086840702c0d04e203e02c400380c0344240d0092808500022004110680308490400c003164203100c0d03040e140b60000b00030b100c14a503221140c60706494002000740350304403103010210307641c1441c2007012949000b10400e0004000040d0001d0003280c0269085890109800688178200d00c40d6108480d14040304d1b07074481d510381c5c1c018040312450002c280502e8407103d05920300000d0310b0340084245000265140e010400704100c55481c4c5d011125600007071800d100214201814000035092568144407000b6120700307940e0b54820480310f005600c0f0f031449500012101b82a205040203c004a020403001004c03018941400b005a4000e61030b600c41c480845070314281c642c48070042c0403031090f00303d10100403200c0c141c1d00320310020803000c4051 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 643399073 1250 643397823 643397879
    0x50d0609020a060c0305220801020a080f07020d270b07060b09070507110f030c180108070504050c0d0b0105090919060801290609030106080304090c0e0109031b 70
    0x52041150301c02c0107800c0002442950010500840c1e1b0004c280d8403828008845205004205d104030910840b00c1d03400759411b5070000500345181540855594011180101e54810645601000766116000c0c181c0040000310042600c0c001e25000d82caa90840c03408140504403695117901d0160450b520001041d159142c842d2400c1d841804c0c802e07d11944609507140040c204100c5640b035490444001010b14032072211044084402e580034083c1c85038074403004140010300721206000850102e02485403410501403080c0028050034140241ca109126000d200341c54515054841c00083c68400c041030f04001c0306021104854503030800b00e0340a004643ca02c107100f440c20345020001e4907126000001d4990500d1000c014508404c1204041e10203001400b00b140003a010100d10035015011419a05600f441e50018003810702100800c01e5600c24a0f06120b4042e4404003a46c020145101890004e8004101000411032510308003244041340a400f551442c1d4401041800c004000d91f41c014851715 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 643400323 1250 643399073 643399091
    0x120f0d030504110306100e0a09030c02010c0203010b1215450105042103090305190509060310030519050a02010f030f060605191404140a030b0406050604061e090213050d06 75
    0x501d0307034056841803149030305101c8030a42ba0b900900c4d4a0340c00000030306026020004204543d408e4100c541c0301030307020b030402c1d03207030070a03210450307a9440f0340f03004120305a1401e008691110303020741000199080018450b5907a0079480c5140e4100c0740d510212020f01c442d5074a45480710300382801824051030003040041410b1146205803005407a44444460a15160201400000360814260f48960f1050440f41134142d4480c40c080c2d600788520fa01b0107a0004000081050301e0142d01c00d0441605e00070350131030745030000641e218a00410841405422a07008120b0f040042d803154808520035601d52401264907070160b4408000d940c3d40b5003020010a40124200352070f2645141e030b15803000003074504030b101c5a0361486054024440c03030041d11203200d001200030b0013076151440b21304001c2d82d100c02070b00c02c01d1501d41015002008280e900512990034040c2c00622a100c412910445019103d80c1c00750b0146401e00100c0254401070b0b512403a402203080024007503503100955880940a2070001c901401 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 643401573 1250 643400323 643400339
    0xb0714030a2a020709050a0608071814040f0204020307051c05011505070c09050c36060c15061216050a09020a050703050c1204090209120f0d03050411030610 69
    0x7120038061099145035000c0b068406500244000455511201c002061b403140a6000050542600820028459501d002800342c0111100500c5510412803c2045080c0300c400c440e481402078a000e8010404001e0f11005445c00b940290380294080c10603e241055540b1200e10f5002004030071441c0c0303656800100010014041d00c401c1d451107a203001c900d800301d980d554514007055070040d0910161b4460006210342540000c54080410400c903000c3c5544082ea10388210381100444204200400c0c1c44030303100d9003000400e5903060650b9001800c20780c8201e5400d0601c030080203041d00e41c8800540e410301c1110506110351610308014010208200e41003000303200701811140c0c054088244104200c000d0380d03038040c0680b0840c6500d440c2180d5110004100c1d145041181070148401d2180003a002038013610540c000c0071a0201075520242c0380081c00321968440b00300d0041070600c0e800510b040541e0503c04c0c0d104a0b07005200d2100784400c0c040400100c2d103044070481c0c80340f4000d18030b080c05116481c = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 643402823 1250 643401573 643401611
    0x12061a070b060118030b0c090d150608010204241431050127030804180b150307030b0a080717070e09030913020c0f07090f05130b0714030a 61
    0xba003820036814200366000140495426884080d00030182803000ca05810103000c01c903811420018116081c24081c0c1c20081d0f6544003080c0010303242850910000307490007042c000c0e07408544d070075500c101c0141440c024060015200e0000d02003004160001c80031041c1405010300705034290020011100540c200078182100a10b54466031004404081001140c1e8040289202000800d60038520003c00d050503000a2002d41c0009002400214002c81e00c1d0b4084008408003100c1c205040c001c840c1c01d2801d01c24411008130381e0000410007000020100c90003900200c10084001e42a0f20103a07541d80c21090418595404c00440b0070401001000801c00c20008a0083d01c4a0100c0400e682002111541d8920580e84503900584030f401240180451540c10384040300ca00c0c105031403074804984182c40e1108140e00802851034036101c3d900348848090710030a480313581d2140e6100010001ca0302c072a5075500c3c00800540421140e4208441d030000010041d50043d125a003001c101c0845500d00d42202d9 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 643404073 1250 643402823 643402831
    0x612022a07140603040506070c0f0f03031e0e07090b0d0b041a09030a0c061104081c0206100e060609030c0d060204030203010c110a030f03110a17010909021012061a070b 74
    0x80d01d024001d005c00f0881c040307501c64200b122402d01c049800340a01e056a80c1030300e1428040c000804007900c0c1400c0c145c0541200b601900b00c480206006018013000c80d040b6210419801c003950310510f0244030251540e440b42031a184000c0c400000c0c10203541c1e512403030050490742126030702c004201502c000e00e41102600c3e0018050005117003800441c2c40c0043c089240e400380604026280c8040b02940a401d00450700a045000c0540748190b0510622580020302d00c0340001c010f101c0c4000041c2d540745030352012425100d1402c403c03091526030004000b0076400c5480a1076050041c000c8003211507940c5501030714001e100d04070250b120352440c0100360840700986034030350030710103128000c211030f800109944602c9540340c01c0c0040c8601ca8000220b00420b440602000008000240001d01e9034100c0740c100186507400300780c00496030300c032444407041c1c616583c0001d400c50702e018020001c2d0340c0a1684a80d5042d0340c13060001303001e07030303503110241c18603003501c201503101c40000404d0310a20501c0c208103580 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 643405323 1250 643404073 643404079
    0xc040207081b0f011d101e021c0507020f0c03011b0809031b07080c01020c0109170f011a0a2103080408190504030212062403030903030a05040f0f0612022a0714 70
    0x1484480d0034031f07800d9410075007040245440e8000380d080c3e030821071000074207610821210104904d02c1c020302c0c00b070340c0d07410508118000c070b01c601c000c0800ba51505018002500e40c941e1558a00c413202d43c2012354100501174030483c0c80e40800c0c02410388274a401e8050007625020440109040c629003d103060409419110741070454020204640860341c00c4039642c0c049400c0c0a0815400b980c040e900c0c01c0c02c0025908030800a542003d92180480121070304a0f003080c5800c030b404010485e91240e410030b0200c400740454083c1082c050341c11011900884400303510501a0b4031076860280440440071400f14040b0803040070610104052056060100178243d00102c0c901c001c0c03000f0b041825400840000c0c0c03481d0009809200a5084c007103440034401c1d80c105a401400701c1c1d441e4900f4110182c00d94102c0d000c2d214403024103003000109548000c01c3c8400b01e07800c1d61a000c0c50b0200c8007261001a40c001190b90712451070700250004049403644203848140c607610b028106103410a0540d1940076201c09400d0300c = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 643406573 1250 643405323 643405331
    0x111030d0c111c050a02010b041a3c01110706020703060e0606130f06050306150f09041509020a03140105040c09020a050421080f0307020c040207081b0f011d10 70
    0x40002d8600380703e11610b03038201641c5800402c00700304c3c003500c07a0041d0541c00c2070910ba29120414403040c65141800e00c100e45440800c01030203510804070150421198410034240085c4100312141c3d00081c1d0b030b040f4103141c500c01e51403101c4100c0e446c01c011507000b040107a00404013001402480d01c10708110005950181c46203080034000120050070942c0401d00081ea00e9842c440a0a4140d01001c010200a0180d8449241c6800e070380c0c00040307000c84101c0c040d4860f00c42080903481d10081040c8038641c0200c200c030749a05401040700081940302170481e04900c0081010000c24541403040c0110032020001149514161400c521030500760b034040302c0d9090041c0802c18041d80c00c413040e582941c803036611070010500242a004116600c084001e02113080c0020384910554540740203500c5a8899001c4406001c150420b10040780710700349010344550002d214a0108500c0052000c0c0603640d100c04640c143c2c1805042142182c00c8c1e44420092100201000c3da01c1807400d0002030058408068104 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 643407823 1250 643406573 643406593
    0x210118031b0f20150328150e04120206040c031103071205060a151401080c04120302030d060b2a01140a060e25050a14040609210c050f0111030d0c11 65
    0x250661b4000200340e800b00f60400008030003496074051105e80c034910480d07010256a5081c0d003580020281d4040d1134142420141e00b0809000244140c000c65020b000c401d0304501c0d507111140300c00740101c11541e0602070200002040c111402c2c10340c26407402907010f00303224204181d0f807408036105400240c0031034200f0031080101020a0100d981110001e0a100b64540d0391030558200d20301c1207030464801c030000c0106407424554000040c29040e04c038a001000300c6074643c81b10380da131402100903484c4c42c18404211901c42c841c6000344541a0640c0301e002090b044d680084101e070b181c42c11616154080d955682c1000190040320030103410201100a4540300000455000c540c42207452200051000c0081e100c10740620500740c640100880c20040c40d259074032108010300604483c400e200798001d00c00c404008214030390780c201d04101d6010081d0340e03103507151406220a0450012a040c14400c00c0e24942d46100412310007009400c03080c540014155000d954080e0080c590300b6002c7d030f1a940198034203 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 643409073 1250 643407823 643407841
    0x60d0206040614070b09071805010e13060f0515131803180e011212050c10050601031415040509061509060f210118031b0f201503 57
    0x9800b80d607100c3ca01005030708511500141e80340b049000040a040e802030030080201d40100e0000103070f42440100b80c03000034422020360f00340c0344280216050b508034140419604080f030140100c010340328200115840d1038455055040720b200321001000780190964151281c41d1000b4401c42858185408008410218160801c0f90702c0301e45000f070a011110008005a03441103070030100400722a0562a1706684a001040c0540c0015070704654250512a40d01c140d0360088c003c2e905981c0307800d0010038103071094091410180c81e0183c940707414565501520202171320b407440c00034401c61401d01c80300824006181444216600240b440303886802840c244113900f0589280c402c41d00d04c045030301045c0c170340f10000000d20a207984003c0b05d90110b010b41c44044070702d1503103040da00e004113000002c000f41402c1500c4030007069a0f42400900141240f000b450fd600010b09400c800180603406404502007240d403524030300c0c400610414100000400100002d180c841d2400f40d440f500c6859280c1507050010740 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 643410323 1250 643409073 643409077
    0x20a0c051606082202090a0c02010510030506062107061701050105071e06060905181b24090303070b0a0f0218010509040b130902010e030111040b180301050f0708060d0206 75
    0xd42c011340d03a401020302040c5024082c51040c15002040392070070741440f611642c010071054017004003550070b240005000f444602c9150007126000300241c0980d0340d904c0200401c80e00c10301a51110384240d0026003800c03200800000303001e042d16881d550349081c1c400c014114103520583c40b00741042002c0001c4000100281c01e580200b050310030014507203c14510300744010f0700b000e801038603166160200308400181c6a11962014415203003d44040e056041003d0410304500c0c40601c1e040f400c000245004118502c0c0e414003450084901a414803208400103419940020b9054820a048400b440079542d003030700c10b04803403a554410861802800c80420603d00760414542418024041115043c80e02c4507000b0b5039035050000c1c4450b0f0038843e821341002c01481c0e900d00c2a40042c54504810b181801e05100f80d6601040d40d10010381420310b0260002c0d29588081815070349005442081012500d003400398502a1080001e044140d1a1a1100070815400140064030500c000d2200c10b0142c2c03503080c1 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 643411573 1250 643410323 643410331
    0x1501020f072103172707030803061216030f0c0902490e0d0314060904020d06090b1503031201030204111605010518070303022509020a0c05160608 64
    0x2d062680400b00e040c00d840ca0703015500c900540c1e056030010001024004035007450700c00c490307405130b82c01e00c0e00d00c0600658a024900000f030103440d08201003501481d059100b51900c52415088607800100954044003406059000700d07480310900d0500d0081015681c48080131340b41e5000c0850820150301041301c00700c811140305a619041382c008808402c80c2280c9001c0d9010b42d5a11076144410484150340000c0c03c10400784c440e14020807590b21030784c502c640200d0702061020070004000b510380701c1c100100b000010700120b1340a29000440c40010b162400381420050140100480310b00d070103070a0840c5140300b0116644a9041001016000c91810304404e042d01d4042c0e400140c1c44801c042180450f1048018050801e191417894804001054203c24441c911140104a6804400350101e980e12018000100540c010322048411000201d0ba81c20b4980070324440074420a0399541041c1c100da12003401e480018401d01103d000b402010030400d4403035900ba20110038500d02d0b090000300000c902034 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 643412823 1250 643411573 643411619
    0x60d030504050411091f03060803072612190605010e130b0103021c0614150a140f1207080129071104111209070b0409050702151501020f07 61
    0x450350610130356030020b8480f1900003034030104000b1103000400714400d0403040070400007424080301040441011051f15100c0d5404906841801d21070015082035004032440c20105400a1112070342d40d05c14200030034014402800c00340544540c0b1312800055400075040f00e8184071040ca6103401c1900d408001c90031240c0c60309000140e010610740120064400e210080b10940409641c865484040c0c1e44848101e4421091500300d0120b507030103100c1e40901a0848040405040c445082080e005813500701400340410f00c036510f85507400580c00203c0c2c11501042d040da03103002c400c000311f0701e4000049074050010102500030710714024070f034407400c40701d401048040301c03c0c00f107980401c00030341c80800076001d800144180000d082e180740b40c0d0500d40003034516020203001d14011070003564000c210282911342001c140741c40d11307080c1203410002d008040c00c49021445076022145081800207181402540252030030714071503181c02c000a1401d46450341c1c01503e034010381070410516800c9850710003016410 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 643414073 1250 643412823 643412831
    0x12d06050f06070c15030609050a0b010504030f0c03020604171005060a120309050301060e060901090c020721050709050a140f0f04080c010612031409100e030309030123060d0305040504 81
    0x284c030b40b40c0c2850046920103140500d0090b00700c1e11407600368004406070382c00400e0400c032656a10300d92030191504030042d1030102d00200400e01c0821205031401424a0003500000354903680d0b640400c001d0f03800355112b10010328100c12406d421034803d000c00c0c05800540d120600c803a08046000a4071030341c4600c45e5030001e40c800c04183e0101801060380b400200310040003001080c1d61041c18040018080350380d03600c0381214a00224071f0b00054810404800e0066000b0100142801404440c4001940f901c5000701c807007070081400540200301c0352000d080801404103c1d401c164000700d040d0b41440d00f1807076100b003d100c10415261241c0b140c6581c07000811700c007080b040e07c1d2814042d88030700c00c0c244095455401e10300e000c160407130781e074a00702001c0348a513869012410005009840c00c0c00340c42c103c26800200c0364501140d00348280c404040700d2500600740c9190224090002c1d085408550356100320229121080310840c0159030003c1c1d004000b0f032100c10411301c40380c1c0c000f4a1840307140500c51003207582d = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 643415323 1250 643414073 643414087
    0x703170406020d18150b0f04050411030c010203120f0a09120c0203101107060c050c0d08010303090605030f18070f2d05090a05190513060608030a0903030e12012d06050f06 75
    0x41000f4880c4c0341f540500100002e007400c3c10200f00400c01900c2c0140a4810614800d00c030754030002c01c40f118103546a17200092034960182d01000080090001c01c0c009840e41d44520100e085901041c1e10741005480310384a0306180d00c141814a4411310a202c1d203103241401070f0715031040c4c0b0021139060075801140010121a1044107943e00e005a0000c48100d203d0186084059034101e002107040c0c07030007501c80c13041c00c035a520000c4400e4842140c072852102091408168480102c00318500005d03142420341e41d03100d40300c0e400c44001c1d42181e0300c070310380d84d5005481a42a488407503259901c4120100d401c00102800d00c1c003c25055480034101d4040c0e00d40e140001036080081d446d090307508429861080c003940c1030480350500c0c545652042a280746145c0b103400680d201001080350038582c0c4035102c54cc112490750301c1c29a0342142090609800046e40344440103400000e1150304032084e20140d0445c0380c080e0041c1f02d2a0151483e42003842082d20b05041801341d82d40300d03003081111071022240703507565641c = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 643416573 1250 643415323 643415329
    0xc02060f0f03100609090203041101030e100e0d030f0e0d0c030903020d03030509010b0d05071e090e031b010b0a0b03090c0d0302060a0b090402060304080703170406020d18150b 77
    0x10a401c054000300001005110f64000300c003140004450240c1e072140240c0b0b49841e9480e0480c8016038008003000f07440700c00601d903540242c01140c00304600105491031000811090004d40352004449c0c5040d070400e0746c801803082c0c4c142c0704c0c00c10184039442c001c21a00d6490305007160b650510640700020710040300c0130041058880d030000c602640d40502915540c0a0920303000c3e0217400141d4070312481d9401c20b144a0202d081004d102c0440360f8010000705140d0345049083d81c050228074440312804482d031303000882c40903014020444003000700d400840c1d440e000b0044522010810302114055641400f601c04013503922940108207030340380041030340e41e0307511000a91b9113401448070322682c20190401ea04010325802243c2e06201b51004442401403100700c2041140850007120025480101800400c1c0070400882c050051310f4031a0804000f010007801c0203842d070010840742201d090b6000101c010b509106402a0b6110340f10380610320070303a60000d9684c5d626070148109007014490b80c0311a00b0005075 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 643417823 1250 643416573 643416577
    0x10303080c0706060e010f0e060f130207020406030c0305070b040602030909100512060703060f0e220f050a120e0904110a09090f0c1505030a09030c080a050d0506010f0c02060f 77
    0x240c3d10050400581c0d5440c1050360480745c091003141340c52586131500080d8001403044680c0b151038014811200e1421001c2002030b900c078090104102e141c1d00380152401601c9601c1581e02460050059152a5146103845868441c0c039030084940f480041c84200603658000050705d28050084500952658540c0029111351482c0e0340015400701078401b81c0d048501e00031900078040c6120340c0d13050196a440700c4640810f10b07400e00c5545241d480c581c00081d43c1c2c0303400a0703100d882d014034448242030f100c640f0740710414041c103600b800340d5444d0040340c07500c1c0400c14007850034814110b16013030040d0500c00410000e03944010040000d850b461131400c50642503600c07200124060850150200311081c600d0030040c103030101041c0100d5410021007400b05048018010303070042500d0b10394402c0d02c0c66845100c1d0710050041254100d0500119400c1600015100f45c0644603a400b1a5212038440258403050300648030080c0055051150890f0705500c0e056102c0c1520b02c04076015145107a80b1100440b402c107181c = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 643419073 1250 643417823 643417837
    0x2150f041707060516050c0309042c06010e060f01081303030912021024061101060b04090e0c1005041e05090a0e160513090503090d03082706010303080c 67
    0x6407070000380e0504000d0142d00c004d0013009120640e00180d403100d0300a40300d5100781c060008aa0344148418a0146403d4010f440d48504080f041c400c0045400130641c0500301d100744c0c501c0c40b50014001407090346582080d003a1300c848100c071b540e16070214120020781682006803802207a11640d400120615000e130700903407002c030fa10508540e41504501402519103e80e080e2100005003000c0855805040e07081d2710320030030329072120342c014540c0c41c002c0d040c0d62035500302080c607001d5501d80c90005561070315400540000d003180a004071303200440d5a052400d0030302e4414400d01c0390440390f0740100900e074400300356020703200084e058003d001c5e41880750b0540d18250340e1210b548410401c04020425645410104111440e00c0468040d224000c1d02040945004d01408d41c010500c2e82440740c80350700907082400854080e2058a14000a500c04034000c4641d08000354040f600a03424040028181d4814808182440003000c6550402c0c4016648900c01840041c042103680d502042200c00b20004071810 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 643420323 1250 643419073 643419113
    0x50310060507031e080702070e15040c023405030613020f06091903060e030a0f1409031b0f04092f330c1e16090f0b0102150f04 56
    0x5007102e130341c03402405070100301d030544010702504400280e20b072140070351103015484c802c5880c4004507030081480010030041000c0700442c450a029455040a60350344c98000c04030003210581d000108480d010502d94485d44140e001354841e4007009250b40003ca0701030007055040710ba605049200200059460080d12802680003010410304d00c030902c010300c4030404132441100c080c004280c84400c03850300d0380100f0b040d00012411811049401e40d05c2a0301007112198000401820700c540740c2d02183c600040114640854401e103ea84600c1d0319001451407010f09080320144100ea40c00d903586106100c0700f800050511004580790b140d900000200b030034960b00c02414800c440c11000b0024407401081c01e40140000c0546d00203042950b031000101d55065101130000c180707610201403958141d607001c04609485003e2150126404035001c111040241201d05000c1440d00b8251080c0049619050400d03043d035004500141007408000c000a134444010260448541d569052407000880c5174482960 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 643421573 1250 643420323 643420367
    0x240b0406080c070b0f04150e0a02100c12120f0e1f0605060f0c01063c050604050d050705031606120204050a05090a0e0a06090b06030703081c060803040f03050d05031006050703 77
    0x841d523000150034140f0758002c031010707200122450003c1c0d03204019420003400404c00382c900641010300805001310710780d043d050000754001c1e608508a0403584200030804842e0400f0346002003c43c0c14000c0440c0030311603e0b804120b042c0c6420000b84191180d240900c60501000c034070720000390000c2d80325000a103c00c3c200c0c8801018020000d0b03807010480030031150340300500048640d507003003418400c2c420340d100604041c1c1303080d08180801500381005c03031040f641d40c0b046800c04540c0b920180001d484520594000202d0107080020285c26441038443c4966164414001044699110b01480d0101c4030259054803d586410012002400303072600d24130f40a2140802c404204038903036000b50081d5006401e00f880c0c0340c4132401011340b142220311014010500a000c1000401035003802d0000c040548078000414550314110241150040d1340000c1a198402c18104184a001d1086920000d140e107403c4c1e2552502804002a498440c000c2104110703020a206041501038211541010340300c0030140 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 643422823 1250 643421573 643421591
    0x10090804080a2402030906040b180706050a021b0f060f1204030c06050c122d010b0406020c0603070516030516060614060715240b0406080c070b0f0415 66
    0x440e400d0840d1440f410084070005446250181c40c07080c4d030702a490326000340040b43c40d242c507040311003913000d441203207913802d0000b0f402120807003000a01d004040311707119540c131001d050740003900304002502c202c01d0200b0240c00005641e580c000464420b210200d6585889143c140c0c0c0c1c1003410302600400c8a038150700174080c00f09041c0c000039250342003803003000d040c0655900d51318621040c0c0607118074440d07010f180304003007044859211103209218507290009028802c601c8040d030341242c030070381c0302c141904c2e40000c060200036810b1021200300c00090701d0580c1b940c1407000000f0000d1044144101120000d8100641018490710031100190000000702207841040d0426900230511885171007000c48250101000c1c60a051040c6c501082e000b19880005a07581070610014060000c040c11002032910b42e9018544000c8110102400344800030a4440e0f0802c0b20190008102400400266009100c071500183c021200150b000e6007035018203a044d140c0d890800545858000003505982c01e00b9411 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 643424073 1250 643422823 643422833
    0x3010806010f0603020a020d08041106041d01090c050a0305090102121512120405040f060503010c090e010602060c07060b010306091806140108070b1b1e060f010810090804080a 77
    0x125040c0c442d814002c4901e240d0307070300c0198105d11400c80d20b000541c000e00d10711061980980001c5903c640140110010016100b001441d10750064004e03120280c2c000503842407404110382c000d4050441403408014004107131202400701c0c020300712110300301a00c1d1400200c180c0003c0d015076141455980c4c45400d58104420652200003400e01d03c09c0c000c080310444050115400101b0030340b02404444d2042c6001c0c1002c00784000f6005103089d0600c3d96864500000303203178509100d0034148a506a549081d024101200f8194031b07203040e44001c00315031003841808900d036403940444211aa1160001540c101c0200050380505415802104802d143c1504112a0303500341c3c046085541c8904010007030200c03641c6000380c4500c02805121803a51082c01300f80803100951000304010100100402e03200380c3c004420a290100d080c0d554010343c1c14407400d80001890030010141c0280256034584010341c1429081c035520002001402c05007600c8881900c280240c1c035080b01c0151000d0010b5801c24130180c205 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 643425323 1250 643424073 643424083
    0xe062d0d0c020106060909182010050f180d0c06030c09050306090a1e0c030503070606062613020a0f0608092406151611040902181b030108 61
    0x100411030404100301d400900c103110b000190b070542e03150b0011590070000b82c14000e0240c003882a210b400c1b4079405901103a91480e450031000c0020302d48211541c03169040c404818181c00c500c2050102c10b02443e00f416500c40140c542440b46146e070203008004d44070000d00d00b0710358144082e10070002d801005c078220758560009010f682090702d4508070207640e001455580d000031203410305290001a48107001943c2d4152551030215080c00410b030a5891f900c42015206060381b0445450b030000650400700300c0c040c05204d00420840c2044480d242025071851641e00030035412a18160800c00001c0d880e000541c0c04a0000d90080d00c4003140744e45850604401040d40c0c018900270414110020b440e0070000198100c5600b1280400d40e0340c000c0c3c0c9030010b500e0301009020264400e9801302c810764000341c1c2c0c4026050900030b59000080c0c01d011820030f000440c0084851a000b14140704a820240e215003200c2c4504605100380d01c42d003503455400c4807a403a807040010303807014440040000754070300b40000c07 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 643426573 1250 643425323 643425337
    0x3131e030f050114070f0c12090807230603040b1f1508040c242a03020607030506090618180303010312021006030b010b0703031e020d0612030e062d 65
    0x1300c0b5074443d4540200c1540c003504000c4c0c01c0e070000340545035054001960728404400711145800c2400c02d031500c0b03007143c5040600f960032100600c071500418004c0d40080e42001400f440040c0d501d00d00d141490703124810010b00040c01061b50a1018410403181d00f4a1a0000000c000b100f005690040c1110700042c5060020b80b801d070361946084401148501003650302514603280c1007028121000401740a440318482059a55021060764034030401044c10741402c442c085100380d001c2c14503460098001350440e0b5001e006103006102d00710401190341c40341418070158487c0d400305010540e42d009030110b50401e05004503440b60102200000030401481e81c203040703403400c58080d80d521001070303a5003070102c0310107100c040c082001e001c00400401003c50010300101d4041c3c03070f01060300c02d00202e0544c2000d0080e02c40c00303519039000444c84480040b5205003805000c1c008500c0c0710214441c5c034010419084440580e00c2a0000078248149200841c4010391134503801c400c1040141009096960a4100320 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 643427823 1250 643426573 643426601
    0x2150109020c060c0405010e090703060302060a030626100e0102210403090605072315010305100c020304050306010306021c0c030519181e050f030903070803131e030f0501 75
    0x804901e81d00300141c266416a130040e960b006c014523114003003042c0c20704045e20b80014542e84100100160b01c0700c0e4001c2c00503d615840101d5034506e0306000e0b0f02e044c8a20303651106540800c0d15044030001010540b54040d1045810100390104501a254024425001c54250400580700980001da1200c0340b241c0c42603010f6107070f40324220303036410b8190380500c03c0e100300074442100c10340700e00c190300c104a800700f01000c282d00884075884011103403100300050a81090700d5540c0540c4c41c0d000d1040b0180241052100ca62010f503041516040c080384c7e9450045c080100500d8010882c03c542800d440308101e00850001028007115407032800c045c00034003050324545e10304103200c240c41096011502481411451440340c0011441d000d447d006203d0130540f007080d6090300000c1601010580c10400c1035a035142c0000903582c0c0301d03401c0d000c02d46003500e260300c40007081d0002d00c08844d16011403640d0504070780440d0310803036040b200b10f40307541d9042a0503003000740703035a01499100c3d0520005500041d52030b1a00c1d = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 643429073 1250 643427823 643427833
    0x303020d1d010e130f15050307051522090c1716080a0b0411040b2203050606210a11030c040504330e100501320418032106060504060507020102150109020c 68
    0x22402e200585201034001c030790b42f80c003c200e01e91243c00c0380c40080304214807614540f9599070f19204d0b01c0d4296070005944600260008030401d004543c02c8800503040200f004603071840c20070036200601290b2004081d42d06240d41c030210300c0040d1300d035a005400141d0700c1c07811460340c898071200c001403950048840b040070b00d01400400000711400701aa4400da07900500100350355520b0300108413640310781c01005610140c000e9060750014008000d034000c03251041200c84048000301082c1860040083d50712441a41041c0c180700101d82c000300303811000c8240314048903403a4954031000002c80c49450081d0030303c0d840c01005a141d0100860b4401c1d0006000c6824441640e076584c00e460184914641c491030044c0b00641e00c5914400c090346c0600e20840900041882c3d8006201440c004020035401d41c04240310403074003041c220041b0100c074001446140b08111b00f504084004000340610b00405090040c0010304006581c002c0040a03400385240c19000403070368450038250041d41200401d00118131036 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 643430323 1250 643429073 643429079
    0x23060f150c010e0c06120402030a020a080a0209060f010c1b080607030c08131205070f05060c041508130b07021f0e16030512030606130303020d1d010e130f15050307 72
    0x4c1002e14800364000c21503400d10b007406850b6000c80a0142040747d051003a4901480141c442102600007004180040c003c64034650042c0122868006e0000340b19003400151050035030307005215180c104d508014465083c1140684d9a24906810b4201c0788581c070030340307003000b1100340d0540082c44502041e0792400c406031a002207104034054184001403007070000d401c0d8540324030302c1a0042c001041c0181d4548803861040c1c0c446504003401a82c10800d58080050140141c01c07040072070b60381002031032810303032240d217006400311264441075400105621210404071380300c21f108106180c2da103100c10003544412508085500c00900e200c1144001c18014080114964000c0c00d00d09012240c000c40a800b0a80e010f02080e00b50394001003200394050790501004154219407880503010b14401d800070080100c243c05c000e4041c1245056a000c480109a16000d569910078442c183e6040e041d00d0401c0783c000f00e002103102416845030b554002034a0701c0411640000270000100864800798181e54010340c07 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 643431573 1250 643430323 643430351
    0x80a05060a1103061008060307030c1206051b040e041a10030302070b1201052403070203071b082e140103060f0204081f020f041805090123060f150c01 66
    0x484d01070750f00c040140ca0080340d0b54001d003c138030b17882400103081c1e4840d147c6940c0e5801c6200c410780c101c5808070300074048010030805641f05064010841c402402c011082d9403a00840500c03503030054001d500c05d10004102001003001848190030190b40e0320034014a86625040c0d00c646107480294018803d80d100011100402c408480b010701d01d01c007030240140e00b0301c1c003032009040701c1c100740140044105441c00745640700350010754060301c600e5001e142da444e1641000b81c62140f20070700070840e0060038402041407a000090b02e00442c044031001404462001e28a0300c1c5884c2054103a6404074140000c090040381d24404c454142c0e803040004020600400c88640300702e02890042d480d860380641004145030030000c1303240400e106015405441c0110443c8400a5078100c0d0780001c018161403066507400001500501d0f1384000c0b01002013105c050361001e4001d201c070b0a51007464940d40030802091254903101104203010901030180043d60609621640b100e0f4829869080e09501c0e10b504ca2a64038 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 643432823 1250 643431573 643431577
    0x7050c091f150e040506030a0206071a0901060e07030c0c05100c120213050607050a06110703030c1719140124020d05040303050f0c010c0e040f09150e0304080a05060a11 74
    0xa9055a036004004403c03005000040c0300c00f403c40d036814403d90080300d0060350f4410003000361900c1111010001000e0401d145256100500303440b03c180d0401100740b0031743d0b890400c010303400308040c50089005103550030182c1c1d42088019000c0c005004d00b0060910286140d00314860060f016590840ca960341417902e00102e004000c00c40300c2d0030203015420411803400c0c00c080c1c19a0b0b80a90180d80c1c03483d80303076900c480840b016040004020100854020145505441413604528160070120900103086c4203d104a8800501c00318400e004002c1038182c01c0300550120038001d02c0324a20f0565561a290114542900d00c0c141240d2161a8200c0d56815440801e07080b09240e49503c4403410b01e03096540c2138556400c69000c8625490007803003803000c3d001c824024601944010344a11464100d45e8007407009440100700c03021003040c2480c080400049182400c02003990700349800181e81018812040c2c00c500c120b5100d01c60034403540069400b8400040340c814040c41c2904030801041c0d122111424240c = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 643434073 1250 643432823 643432859
    0xf1a070507140114120f01090207050607030519020d0f0608070605190507200907020c010e0d020a0e0109150e01210c0b040905090d020303040c030807050c091f 70
    0x3904140020014921529032100114070b05040c55107540991410304900c60b0030020140d04001c002e1014424580c840001d0781b809483e04940c15407404a0725110156191000b410700420103981301c001400c05101000b40d00d1458540c54801c0d0741e1000084001409016041480c0420740d1038400000340c01d800015038202200c145498641c10300040003880080100441c05080a110701000a94002414034448090f600c5000c008464801d60340030a003c511640100444195402a890340c615aa000081c50104400860702c03090381c80d2a41c4007281c03070112280c2c09503110044400021403d6200341e00058500c42003100341c080c034603075500810b029061003031103201c40700003564100030542002030104024140c00b940307000c042c40c6d68504006a00303074007a910078002300e90742d5028444040f500348042d0f0305c100c00902c0210300b036007000c0e100e0741070a850305e100083c01031034001a07030820000140412110350500420302e012903d45006100c1401010512034549450401004600c200c0d1100307542d603032 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 643435323 1250 643434073 643434083
    0x25030206010303030902010e090c1b0d1403090f0f210315040f110a180815060915030703080a0e0d2006120c040e13150c050c070f1a07 59
    0x96403031030f10154010900700c4070981c1005101c14541d4030a44801689901501c15818256619104200071500014800c5444001500301c2e10901c9100c90b4001d4030950345076030200405e55641c0340d40d50906e2900c4010b810301002c601904a10303900340b100114903d50082c00010450b803100c4a0f014940009101c100c1d070340d15030184440300206581c02e080d4800d05103029140c00010b803680110a5010042d002b0f040c51200007040d88c01d20f00c0302020300c801130030000c1c000700d4010a80c000103190201c1000d180244141e01959400700002c04c04e12458101d00780e25440a020f4410040e121f060090265001c0c001c41c101284035514202501d00701402d14513681c0350020141144440290080368014842028959002a09010b1000115008459140501c441c409040d540d140380202240c01410001c202d0503204a1500c1808049100160407950350070341400c00007244103104e01d007918240900a481c464600c00e48101040036010081030500703490712908081494503590301091842d220300000204 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 643436573 1250 643435323 643435333
    0x10e01030b0a020d0902090903030612190f08071e02091602060601030c170112120c030806090a060e0901050f1303020c09060312190f111911031002250302 68
    0x101480340e650103040250354480c1d010545c0721303141e00020319103081500c3d01c480701d0f0030000c14010f007441e1480280d420300500c140074050030382c40d030050100c0360000a0b80c0905413070408a145000c10042c2421903600030750041c070140d0590300342e130b1800c2146040e8807012401201c02c1c6011a07011624015000c61101c00355009065940c0d0b2140110003402109a5020034807190160110300c4403603400040e8080d000b03004030510803044170709000c54000c454545000c1805841b90b5503c02213a8010340d45580700702d050f41d440303025450701140c3c0001000c2a6000010103651001480080e00040d0001806101c0403480c482d1203031224400c0769a055902c0500a015a020542c1c0480509104d040302c7d500110090503503451000007110b81c0c415a000303610b49014030000715140c15904da04864000301d000780c0c514003240d02c00d0031500820341c0c0b55143c0004917000075502000e001006102040c80501c148098240c070300c0c03680030713411000194011f0380031107081340d103096501d100070b405080003140220740690041c1 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 643437823 1250 643436573 643436581
    0xe0a0501050405060f1c1b0e161407030c0f151b030b03030409050a06050a0b070501061401140c0109230606090f18070306110406020613020609101e03090b010e01030b 73
    0x880b98640c404000c607640c00003003005e404140008020f11004054000388d0031410303d0040ca400c03182d4048114000b09025070f1100441080d00810140c0d50125454100f40d4440d1a13a070905900c607800d003500060141140382214031906501e5080351070480321210800c1082d5110300382c1a001e40304480a456010f40c0300348002c0141d0601030300aa60050300201d00011b0903504c42c00422030001460b0400c445000c00003c03000c4c204002486040700030401c411942e4400c00e034401c0020040308204003038900b24030020502c1d4081c20310a40c00380d00150b6101141144192940c1c0701c07410ba400740e28140d0b045900404d0000b462030309140143c81c0c07042c0c2012a210741c10380e880110807001285c000c5180e04007485010000300001d5080d11440d124440d107202c03401c5d00e840c0750040091600c5d03401007030750964510107946800143c032000d007a6403050604440801c0d0440c2622400c640441804904003012900780307802443c026010f80c041c0f11140e005907820640b07a80ca03913001181401080c88000d2100c41da0700005 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 643439073 1250 643437823 643437859
    0x5010e04060806071805040504030509092401051b0109141e030306060a180e0f06010f090302100302070f06020304031112040e10080d020f0f010b030c040f060e0a0501050405060f 78
    0xd2003414117986810340483c4d1180c000c501241c0080b9401c602082c00007071070f146107280c0142d50701e51101600c0b140f904010100038005100d44000701e401d6050000128601d510350405030040c0c078150241800801242c00c00f8107181a0136030310044019014000c150081078607403122080806400303682d8004516540364003003402010751201019004002c5540d4510380c88108021101000b010280d120503004e060040803078610f8040942080c0c180000200c8600000f908081c8000460f50101c0f4800c11041c0d2001c020740c080c0c451040000d042042035814a010001d1980c017440c05a4003a41c0d80e012640301c100d2900c0d42c0c5000d140441502d1841c140000c001820140d0310365640059044002011182c1d6030361101d15204c490f25401015030019640c2254994040180101c8181c40c07a0003807040641140209449010805809004584a460040a07170110380c1104008020201c1c0c40400c0b0300e80300c8613200003020203010706440350303041c9008114140303045032460800080003400c08041c00040840 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 643440323 1250 643439073 643439087
    0xc021306080c13140a051f030203060703050910060803180315130501110c0309040b0105030106050a031104080f0a030f08010e0708150901080106080606182d0106050405010e0406080607 81
    0x2001c0f115036124a01800b00d00030400c01030b40141c03c2e002c808541c3d810510f804055455859095000c50301c00b481c41040513035000610b9940102460400088603112039040301e0400702110001d10140e41041d1000503454000030003403102c02c0301c4a4151044059200400d51035100807208503040c10400320103d011043c00d2022400c809103d0000000c110003a048640d0f215084400b02802e107810100e00c90109007081d005605000310b003440c00920350f41c145100a003c80c024402c001c0d08140c0d4903911210408500000c9070007500441c5d0443d804c200160708140e558521008085000079018209252410f004008490680da01080030040301d42d1403001c100c07400e80000b400d4455036420a202036039640c48200e1814003a200d1540040b4030141010451450f00f04040d0640e4024001a0f2640b09680640544bea0308003014000b8419554500320b400042d0032042c00a80004c0000750303000061094002e801401100d0302a21003041143c0e441c01000b040354598803a0038095000304001408441c41044 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 643441573 1250 643440323 643440349
    0x303030414030403050109060603021009051e010e120616021f0906140906061005032716091e0b0d230304030f0605090607091a04080d0c021306080c 65
    0x308503410f1036603079151142500d2040106998081c1e5900c414015400c1c00340100020750300c00e00b080d840240c07074240840d02d90103146000040340c5000c4111400107030b208894002c00c4d058001c1c030000d1108040030f60103840d0f400655160008401c1800c500c0c441c0c03400490005c1c4502ca503046003101b038000252000000e00002c000449107a56036030700302269001090540c2e8043ca0080c0020461494488184586c0b80c4c4010540d4050140610070490f201e01c4400c1e41e06007102d07054204074020b14508040e01c0c80d04003800400c01c581e828580e40401c020083da808404040340f0100c044004090070020303881180d60f050285a0400d618004480214581d03503001510f082d07410074001e6061072804000760a50700b10f0740080302c000c0900782d41d00c81030000c6e50140070b42000410300070701650301b40381c000500720f81d4642c4620540c401c44554400000084001602d00401000f0261002042144c400510303481e50150100d01c120140d03080f03194030501c24440c1106494040004001c150700041c00c1200c0034010039 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 643442823 1250 643441573 643441613
    0x9020f09030c0d11060a050d0509071403150c090109050d050c0f220509101103061e1e032406030f01020a1409281701090c0513060510090504060e0603030304 69
    0x1320341c070000309c0c03103102d1140000e040070302004c50805640d400a8100b111400d0300c031740e1080d4100e001c00789480c000250003090354001d07243d03501c80382c00c010394103001c6c9a032049900c0349041500c2d4050042c0440d801c80e81100c03c5070030074803e00ca55010414003440100d07401c18070940100c84c0884d0404954000c642040c1500c2c112003500c21178110210542e00c101a0240c503142010003031050500700f009181410f294000316003207d400c2d0304400b00d1420412800e00009a115007400705249460901486450004c0200b0030303000448a4102c24500304c10a441890091144260001c2c040034113109580f000c1801d0b80c0c1d10302058011401c000a6a00201b4005510142030071004030344900303101c3c101503450001c1c1143d54041f07241401820a402c3c0c0e100c8503542c2039050610020000350128040029100200c4030046000340764500900206000e0b008983c000c007070600d1604050b40c0081400c400c03940110390501c1a262030301aa001012400e46045405038024404200002c00810740103208812072 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 643444073 1250 643442823 643442827
    0x1a04051308041818050c06030406060b030408180d0201230c030304060c110706050a05032701051803190c02011e0305061503090601051909020f09030c0d11060a05 71
    0x160320707444402d078481c0e40940400340e58607140800f03c030154050030f00780030b42042d10b1031509012a156151941040301c2d9091144e5000000501000a1036000801800680c421541ca034036052502c0030407039003e0b030040ba045200f503400300051850040b406034100d981c1a543e440b0000803c0307030300c0c1241412820000c080507900344821448010304001039441640580700115a09400c41303406000841c0c10b0405040c1600305a0f420300501d0741201c1100c1440f0079600d09540e5943d40d160010654100307084404134101d0100d101000400c8054010600903606404034500c2e000c01c4200043c0c2d684a00c0680640460b146149000d20302c0c055200002280d00604110504140c0004042d000c1c07128020500c000c281d49200744200c1d0f003454401d1202002c000b905061031400c08107261a500c2030140700d454490303c1c540c280d4001c50040100316200420749524259180c1c0010590034021303420139480940288164490905286440400f0b00d9110703402020400c0e0401402040c030882d584401010414000c0c1 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 643445323 1250 643444073 643444111
    0x20106120f060e030f070b0c040305030d2702090a02070807050601080109050616021c02030910030221010506040b0f1b1c03060503301c0b03011a0405 66
    0x1201510260396105090003034030058146800412103440300400003450b4810b008003420001141c00310b42100740c00820148142d9104a91001c86110315040108107001c04110560b510301c080d00400844034000c04150000600354550900043c43e050000e50f00c06039840214204100c20350060642d0b40c0a01d05951600b80e0a44403245001000e80c0002101e131744d90302814050040501200340c00100b004141808074248030380080d81c90540d4212468201900002c94007018001c0088400031a40503100d800c845a802c1e0303015000350845000b0030001c5c009448580b80c44900500300c2c0341071318002400c072403c190908040a0440d00103450349100310000b00308030500103145510a640c0110309070002e03c240c000032600003491584030724043d420306080a100303220030345d80400c0e0800d800c0c1070250078442091102c00050701c542019010f004505100155540100640041004061b0308010081c044401b5440030305080345c3d134007240c1408a01c2482079419061520b41c00c155000050f065450122481c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 643446573 1250 643445323 643445339
    0x601020c090c04120b07141303030305060112150806060a03020105120403121d2415012706020d020d0903020d110406090c02190b0f04030909020301090b010306080307020f060307020106 81
    0x4695800385e036040084420418159030204c040880141c42d142210300f00132a10780c06491210050000505250b1120005900c5900c1254401e040800406061082050340c41c401d5491403c0e500407482507000c2c05001481c1801c03c011804110fa82c1a50740504c0c20340c1e82d483c51001150301070421001c000c46d40300140407944c0d140c001d52003d4840034415040204109070500e240c481d500c1c64503111100b094643d100031001c8004026404170944d401e0304038144046004903524206240704d00440340f440d040c96102c09440744c50800aa40c175070340841e40500e41c0700500766550b12075441d4550004265075828001418550005c0c1c000ca403080d1f0b0f0380040c1482080004003684c4d4160031880105541d44507003126940c0c104804180d031054110145100c6025840342c0c03117450001002c0300c504440c1080401e04040c03140021030020311040c1000c544035611801c00001411604036918006030400c840852501800710458852a0f4010010800c0845000a0010a0300000c2000003507550321940001c2070b40b = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 643447823 1250 643446573 643446599
    0x303011e0803070c1401030516030c020a020612090606030304032f0d0f0303060b09011202031305060708011a03010b0313142e061a07050a0f12030f050601020c090c04 73
    0x9215021300e00180b41480840c001d0b81c00b00c80d104904050038107040c40f8044030b101402c10100c0646280104103450b29240c02e0785421510700000303412200002da0341d0300aa0081030081d0080d207040d000c2e11502e4980408050360f034080c03404060024000e440603400382c240711620758074402c050b00700800c60600c103400001d44049680401581e66403408418802003690511480700079104994145003405071000c00280345114640c10a040b156001002c601681000c0120700350aa5000b002c8071268900010001c18944080c13080803001c054070080802005074120a980c140d41250350058155035850410301944490f125013910420f2800880c50201c210501c82031031b0781002e4000b0480c0f000b90403030399a694000a0100410785514165080c0b15004000d00440e405600100344103845280d103041060a121035860014035200fa2040d10300d040011306400200018080c0c0c50411400c0a190440d40c240c600464007140180c00007104100f161410030001d17504110006c100303034107090315042c00140c40 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 643449073 1250 643447823 643447837
    0x6051c09020f1e030705010f05090d0609020d0507091107030f08060114040f031406280b130c02011a091f090c020f2a040e0109060906200c0303011e0803 67
    0x8580003803181005080805c0f01100900e0207203404400c001e140c180003000c5004802105128030704610f0518240143c2e504600c4000c0e400803e00c03c4464443d151165651541c4c0c4038210701581400001d03c0c04900090a035001d1903010b488800048502c60f00c2180e2100c002440681404111500320400703500501c0079001070900032200715031035429800c10840e603001c20181e009143e48880b0804c0b03c0d100c24581000e41d1200014203138002e14620ba8401c81c017500044103410380200c5103c07200110950340ea080200ca80e003040c0c00800c601070001c2d140041c040340d011406900a1000d4001c180603851940030f0401580b0a64441828191100104070903906100c40680060303110074003c00e0f502c501031001c2141c0b58a203614403651421001d003d000501c17615190305100e05c0d0346002a0018100a401044074076600c2542040361101500c1c0c40402400540d50340b181104048000c1840540e18104659440c9809401182542c0ca4030421034942d094400f0b562581a400c40000242a20100b02a010b4 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 643450323 1250 643449073 643449109
    0x1009030e011107081209061204030302070309090b030d110114152107140402090402160b010f0b0d0c030e06040605010e0a09020f10030b1e03060106051c09020f 70
    0x109a0000405a40601401560541100c2c00c100101e11000802c0f07140700c0c800c40724150306c4200e5200010001e000790111001854085400c220030185c0c50b03802012003e200341c0f5a40201610303030500c03804440c0e070f0141240d0554031050b10084081e024940001e00610f00703d0010a84007644982003840003015203502d10b1400101040e10f900c0d20b03100e06500c280002804d0031554440e00000d9940d59240c4e03500c1440100c9620303010801050f211a012151505c034003030700665a0300d170080280f46010400038004d0301c440b03c110002298070310440004004454040395061308002c4920718100040000035440c10170700d581c840705100c60400920110348a5409018002100d614103c41c4903203a820081c07494a140c0d1074400b00780b0060b550011000c4885000351007086401e074080c80b06400804140c090294010310901843d04507003c24911032401e005c080d410782c0c849980e160400e503102c2c05089107803981043c1e08209144d01d5262030b880115182d0005000c60181c070200d40114070000f2a601e01000 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 643451573 1250 643450323 643450337
    0x9020a030605030c0306060a060507081902060a0c08100b16020a0e0a15120807060e160503120301030b0417120f0108150408042106060608010e1e0106050705100903 72
    0xc902d01441300448058058001e0704062801800103002c10400d40241003d00c000071424800f4000740000340c4602e0b00c1e5000300440c0351606000041c6d03032030404031848800182481c40603030b46144a010707014024040c550314100a2424680c46280640006062481009919981d1030140e6190201c0100421400034030040504001103094180c40d0300d07900380f41c12143c8960303040018440c0d10403006a072580210440383c031041ca03840c5c2000070b081b1400c411005403091260100303a5003c0307016800202c801c1201110409901c00044104034002440090001c00c00d440c0000c3c00300e01c3c01c0140101444203803103420700d454025000040c207030b0700a40718807860320b80007030051000d28000c10084081c3c803011307031055001c2c1ca171030794901d44a8071903401703071b1843c84400e04c402949240111040ba245d5a6200109110701601c9000080ca403030000d1040210264084000c5070101c494141c01c001d192855034102d600603801c010003500c56078007003a01122248186102001411000d01c0b40607142482a03072201c07 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 643452823 1250 643451573 643451579
    0x6031b0e010308031303051e030712110301051908030f09150304021f030b061c0507141602060d0e0106080708010c05180a050306101a0c0307020f040609020a0306 71
    0x1080452504400351051a000c014400b0400c4502a2948202c0150303642c440b01000d89002c0301ca03030107601c0d102480c03403414440c114400c46803400510301c2854240c1d108100c00300000001c100b0b0320703030541c01400310120800060119080c06110b40c00704000c0d4407002d0041540d10312030030f0b00d181c0c0b0520020803d1030300854504410314180110481c40a404107025041d814103400281c0c501d0122282101d4100030101104401c45c02034003c06c0c072144004101071f031504009800300503d0541512160070840c03400303000810940c0034100b0040aa440380d0051400d1034060008a481c083d00c0420070f03030b4440801e200c42d1065042d18001d482100c610200003003045440d040c4034a15080254100c408143d0508a060075169400403c0e44c4c180182510301c41c00035111040072800c4600c00750012034050044004105e144038034100c82d03004440d8915040c000b900e01c60401c02c04036008021072403009810402030303540945011210380754114001400020348a07550b280d981c040380d1046400304003003501d0324010 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 643454073 1250 643452823 643452863
    0x70218040c0f0e01051c3903080904050901050c0409051f0605070b16121808070b1602070b1c1b030b0f0603100b0a0c0203030d2c0303070e130603 64
    0x9105150300007000e001101e0510303640e41e140d01c03612101612820003010710f400113424144051701c211f013044d0003411003090703141c0c201100154072461130f00c0e0150741400c001c00c150320814480c0c00e00ca020440951400c0074101050b68010b407130040e00c0d040000543c0810b04021654608240004008a8442a99440f41ca20f0000034000d070041c03105404100480d80c4003181e5404c004c00a01d441d240c0000012200400354041c8102c610491028149a002040403820005040503a9002d8020728030b807003070038100302c5104030303070394030207405095038200d0140f280300070f408030040407607003004144280403031721114004001c0602c80030b54540c0c4d80000d03111541208107040202360001c0d000c8082d07a1492451401ca00003022101a920030341c0d103420380c0080c5404050340308140c0e83d0506a4010183c9584104050254025002001d0140798522813512180360100040000085c6440000055400d40c5d603281825607143e100101060b8011103818007081d4529a0f610641c0091885090b5010504d4421800 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 643455323 1250 643454073 643454089
    0x51006021506030d05070303020d020a230c0318211b0409020607031103041d070f0806031c02030f0708040f06091202040c03020c010203041a060402070218040c0f0e0105 74
    0x503240726800d00703200303210103601c021401c032181c0c1c540d608102d40e0f03a03a10340c031b4110000d200740081d40c06001e1012944102042d400201c50b165000c01100000c1c80000034a640d0049100303203440084140d004200c002036540c402c03800403140c990010b1034013035079045890720100300903a1440c1100e810340003450b817001d002d03650028101280c50305580c2084596100d6020442c1442403a5000c2c09006a604086e0071b0380c1c03802c00850700500840c802e6032036810441006038200d07900c141c40035004658140c4c0304200f81441070204078422607004000702030b19030b0350f0641001400c43d410004003c5000030082082028041001440c01c54842c0d540b850b80c0d249440d9120764216002c2e000314080000b490001c00c8a21041c03100001c8031074048031b001401104560041c1c00901c070303920030800d0359400030003080140903007480c0443e0500100c0302c208886a440c0c07000c000803807141a50095020208140340a080721207e24642d50040c0701d500301000c50744c0c86119200780280581d01403003c1e2003201c40180154106001c03 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 643456573 1250 643455323 643455343
    0x3030516020706211503150b2706241317030a0f031d030a0314010b18030a050105131407030c060f090b030a0c08060d0b01030201110a0605100602 64
    0x301416050342000f00007022640750825050112105648410301409030b5407210034000d00250301002e00c0c650b03e00e00003c400300b2175507490394642d18010100c00b850a003050080460311400498240001407407040341c81000700501030f80e17007040f100c8100203403000d10030078018040c81c0c00a1010f9114104010601d4a0382a2608000c000c21040643c2c068a15000415211944041d04008130030210b2450100d0040c500b40b4400410b5108120542c2d4084034003000a1040702484c1e038051045a91540c201c1242240030700c681c03101c050b010070182d035400c4e4024140e202c01c8800213054503c0d4844a40f1054207540082d111040248100b0040400f00a000b0141ca0101e0b020b00c00a8084145035803140c450300446449180e06020040001c07540755807089800e0005880300c07a45150712070401c108054004e008113a40d40b07020400d0b200101707186190001c009490143d011210382403607130071540110b4024a40107032040b030501c9900c1c98100020340b076015191060758261241d40c0001d251401c02490700000803 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 643457823 1250 643456573 643456577
    0x318060905030615090f041b0b0309010e0105010311060c0309040e030c06090a021e0315010603020a12140c0f070804080105041208130201050c03040b030a0b19211403030403030516 79
    0x30b0f03c0b50805443d98441c0550189860700c0000d81b650b1182403011900c001010b50100715101944c001c618441c6200146d40100f042c07400802543c0003240d00c0ba0300303d401c2070101410410f00d04941c1c014510b01200117100c80442c0400341e0307051022180100742500c4000441e407226400125040303810490030007805a0087c02c55004119600d4940c012030b0b41c1449038000762000490100108546840422001d15004072400c400a62580e4614008000303400c40500a00068800305411204010501918401c02030310b0344044401d494580c0725a6240d8000000c0c0e01402d94180311800210b083e0308041c00040c0055000428a0f161609d04121403402c00321002d4148040103082c00b2204803030120b02c0c0b8180340d081c02c1c2566600d504500e05440c50003107500c9088865000030400600159030381003015902c1084d0303101403c20340002042c80080d0054010581004003980c80010304d070703c6154901c1100360040d141c240c01c141c1ea4400342400e5031b0044405901003501c0d1418001e808880040605081d5094 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 643459073 1250 643457823 643457851
    0x60602010b0105040e16030b0d03110606010908070b0c0a05120a020c0103021c2c15090102030f0a05100b07120801050f06040338180304120f03180609050306 69
    0x8446501c01c0380001a11440b580c0d00c0000c289500d1b14000d5000400824005105546194482c94002c200c003c000c502c60079240281c00105110354084c07261541660710102c041c007032060600100a95681006032038031414442d00320941c01145084c03020300d91008107102450b031349102c55400a403424000d4442d0307c0c10180b04000c69407007601406c21388141240101c00110326541c00c50058643da00c11102d8001401060803e0400d1501c0c1c00149080d810302c0b0401e40c1d101d01e83e940b01e40c0500303e00080301d9a1507561250702c0090800741c4558005680008c3d0705a40b61107140d150a00100c080d0050f0008230740003a001e42541700030503000546217006103c11518000701080203000308242e40903d100080407101c91003004002c14540e0a104500e0440c5e910b01c3c03d548a80e4a1442131602c0801d6034110b882038040403240c401b004c00801214203031111410901c240c0802e031b81d00c2d10108444070b48150200190313803032a2215040c440c065400140010380d10200301604100c00c240c14103001030a0381e6017032010b07 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 643460323 1250 643459073 643459079
    0x506010b13063f0609052203090f030305090112090c0b070305040305010207030c230705280f090e060112020f120f2407090302121f060602010b010504 66
    0x1481103100152019441d0000d40c00ca41e0710b40d40032043e0038080289000d001c40740712441c540c1d0444100081a82a10701042c02095941c1420000302c407000d48440070a01600d2000d00078441c100c0d0101201144645002203605548500030000c41545800440c0012000140742e102c541e40078046410780714807000e017003001043e11303600d14600441c4c9200e4240302450100f401030170305000c1c4090350025908030000395036814451800525072481364070110303440040d04003141072901845c84800034000b072040c028103420342400c0c03c2144d10052041c40001c0d2803846c03c00d802582d080c1d60304100003071075032582003043c0c0c07424202d522054503407040512106900030f2004000e4214909824030143d501555065003500c87c01010900054001d10041a075114121524400c0030001650510850740601514003201510104c1d42202c001a6080c5c3c000030a00c40b8144090724140da40403100c015528115a007500e0418414001803402c807108010a1359100002c00500d034080c0035050b4801824a002072520781 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 643461573 1250 643460323 643460347
    0x16230601090c210b031006030c212f041a0109062a030215010308042102010203030a050a02091005040e01060215160c0807062306100c110d0804030506010b 68
    0x14034070090500b00b64541c0413030040358406100107000f07241103d07024080d841d120708007008801d9040c42403000c50720101410b101000c2c5065900428180d1100100700c4051400014800720708061085e00d40c9034079084503618081d66030740b1078509040035595200015804903000501940903590203002800f02c40c600c0544082c210308990001800c4105801b40c1c40c160b80d05040b8581902e8103128910701200ea000401400740c4800079104417003c0d0101040356010406419062201c0d61000a001d6030061001c240440b8968100310340c007220450700182895141d0001a81c0700e29141d103c1404220009404e00141a4000140d07000d800300340010150154412452964880c0003050f00d01240a10100c00d15070070700c15080c0e280d140b904010b0b881c0e203546290402500801d01c0e042c44001c90b010740f640219601d850800001e100d60002005425800d90381d1070240c4014000130411030720103c69a610a0040d81d0f01d644200b10a030190410355111802c44c6405072400c60b0681140b00c00c680300380548001b1030 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 643462823 1250 643461573 643461617
    0x8070515132003101104030602041707050105040530010c030f050a0e0a1203020d020a201606180b0408010b27060409050c0d1b050108040816230601090c 67
    0x215101c50005040902404540031401b036a00000c008500010740000d01c00c0035004051041020f000c1a540c102e90b031900191103a108074864283c0004030108982c1041c07000c40180c0b080c0610040c4010340c144641c144590869011081a1000c03954455002c111403029106a9600c00b424a0f0b08205030b810100400d03a880301c801714001c4c04c111752004085105071285e0156034030407d028105640721034890744054200a03030100702c48503250f01d40c41c8110340e0b00c00c001240a00d0000c03208142d07003c903017004811101101118010000880f019100007400d000c0c820040001303009103400050303c2c2144a04110600c244000c03006003a90031031000d203003492031448800f60803080c00c50b0002a80307a4a4900749051047c3d040c03041798018811210b03e814402d5106041403120000030030382d4400380d2078800542c2c00343c00665010b42019418403100102030000724180490034000c204507030542180c000c18203d0b003030b1074145000b11604080010000c00705d10b40135015130001d0a0914624241090900021030 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 643464073 1250 643462823 643462843
    0x902030606061c0c0e090a02070c1406041a0d06080a11011d0306040f0203101103060607260d2904361b050d08070515132003 55
    0x1076000160f030f41950422240a291034445a0006105414603d08080c25040018210350302520300080054440043d1784220f03042d090b444400080300c1403c001d9603407501000c0448403500040208004181c0e000d103a81d860403810140c180c49951600e61203001c40540d101a4003010301030b800300d8221130002d15010010200c481081c648107050508603041c25000ba590391004a4140c01204140302c1480500d0150701c0585000703404541d03448060a10102c12503580c80d40074400e2040c20701c040b072005d19001c4028040a4041d69200c1da0302242100e0400b81210200d40700d03803811740000b40c1d01510200c2402040e10000c0c1d070741c4e110140ca2000d816070704072044412842c94440c6688040740fa100300d05001c0206848030400c400075012862003052400301d41e9000700e0a403240500040d00d20031100d00c1c030100e0402e5070409000e5522171035082d9100301e1540c1040303100322510b01401c4410030840d802c01c04014810314406c4611000d0801c07034204400010f00d48152900010004046803210752800218018a = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 643465323 1250 643464073 643464079
    0x190f020d030504020427050c0a050a06111c0c0c050307052101090519060e01182301050735180c1e010906050c060a0c03021903021c0902030606 63
    0x910f60380d070700c0040c00070701c4d01c05c81d80e80b11444c424140030780b404202e0f140460310920030801ca0f40c51105050411504202d40e01c903455111a2105041c04000d03c58554146584030700e0080f9940c000c450380b0900c800485e81144600052020104c2005022214203104010300050700940712a50908002c161350400009003084103901c41d0440c1000b00d0000d40c80315148170740200644030b9403105100032148a001041054903101d0074084a2100e0f00c2c41072150f042150341814800820000750303510010600482c1e42d8080c500d03482c4c001d507400c4041084c05903603c540820b41d02c441740c00184031545603840030245010306280c2c0440351010304018810f19000c1c0c2010b80c108480c0c8913a2240d5904600c0c052509030301c1c40d006001d000d0304081c0030b01c20104214155800740c8926070040c0c0c56640444140c021652109004ea0119000c290442d2103a8013400303e0504500c1c002d440c0000b50744a0000c0030380b00960b01e90000b80e000811485401031050b945030408440b402c14840c00645400003562403d010700081d00c = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 643466573 1250 643465323 643465331
    0xf100305100b0616081e03010e01050d030c05011503031d0a1a0405040230090a030c021f1d06130306020d060e0906040b010608040312090507050d0602190f020d03 71
    0x48180c2c0c40b0750030381d8551402004c9a06854281e031400e20b1542d0025400400c60324501e4243d0050a000002034a05880c1300b18507002c0c49a2030203040200580141109906000403540c0b40720100d802806140d410000c2c5145222203940b0b18030b8014407840038171916900380c0c0c040303d48060030359a130101c0740c000302c0c0c91503080c110001032000c0310101d21f4481d960045030301510021712a4180150a6281021180804040c1c55411000700701400c0000741141c10b46201d803c1168407000081c094000011a180060080300f07090900d03920a0a07810740003154180424584280d0b0741518510b8203c81081d0351094581c5420144e10100600d81003203603000080101d500421a1011424280e0014004004128015141d414005030725519558203880c01e4428034110000031819600a4100340e000da0f600d541c0b0b48040c0360f04020f408004083c1048122054000c1010004e010750b10b002d0000c0200f405050700681c0c621155410b549409024103020051003144000300d2095074000c500001c8940060501107 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 643467823 1250 643466573 643466591
    0x6040c08070f03061706010815101701020d0207060b100e0d0b0a0e0601180501060f0507020d0609050f010e1c022a03010c0507110a0e0601140c070e0f10030510 70
    0x43c0203071803a60000391200e1807600082d03968200002d03c2e18100d800704010713264000071004c0500a0000101d406482c03482c81003504100c4e800c0e0440c40d0f1054001071000060404102001100c16684401030584032603803605168038140c90000800e0485000c03038200030803000c6c407500110307040803280003002e04030b019103d00003404856503030090701c0c88200c10416141e0540e192400308401240d003480546413103281400109045000b80d8007880780d00300544aa03800d0910036401c1003003042048004968540d100c0040000007801041400c1010032180004909000851422490700295141c80c00400071240d03001e0121540100d2810a14001a030303020307810010034025254441904400345415618158180c20f03020f80c040c001c3c0050902c030705200104044690b0030058094081e0107200500b2118a0200340158082c21303810907100c1044805074108a0340004c01410401030b81e00c000503030007550040200345038805107840e52110b07891040c611201e0031500c2d42c0d59200303c1c4060004000d51350754006 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 643469073 1250 643467823 643467827
    0x1d0711010915090203160e0108060c18040e1510091a0f0d1e03050a141305060c1e0601060924080402010c120906030c0903030e0603041b090e0606040c08070f 69
    0x40d04a0364046088403420941c2c5202149070381f00248079100383d6000380f0300032864101108003264210340e41c070580d18503c00341600401c0007c080960142440d445400540c10941150691399442592021640200c10b40b40080030016036620545c80f40018800007441101c0380c0d02c9200f08048818150f51b00d00c81c4560516040300200400460b401070900200303071250804d54040014580e40c103140c0c1d680c414494480e1840000d134000e0134000c030240304080310706002a003003501c094454800801e08840400e1400c0b510044001304410000034070390040d800600845800c00c21000090a601d05003011030304100180100001c6034562080410020b0300208080d0383c801d140131503003107402148200f100070041102800303414181c41141c01203420302e14002c4195000e0a14081100e4242e02c1d14140c6554030b0b010840c4c1984000d00032101e2241d10351f40c43d00e110300b040c86910081d010941c80044c0c0b03a040c80c86060302c2d003480182010700c50740c180000041da05900080c1d291700560030303040244e4689512002 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 643470323 1250 643469073 643469083
    0xf0a02011b111c11010c0803130305090607200306040b150a0b1b010606020616080c1902030c10051003120c14011d010c02060705070602041d0711010915090203 70
    0x224951102d03002050f049039620445140c00c2d03403071003003a00501d0320034404015100ea18091002074141c0206100140d01070003a511050705c194072038030b4010328000d042c1000a125411a14003929040021a1003c1c2108445501e01d80c40b144110010038191038030395110284100000c0c90319450122a03084003030305464412400029104a280864907850b01c80b59580200031114a50240c075820441c000031442c2c00810214080d440711042014000c0100105940c1c2510140842c500307600c3c01c0101e040040c0f8a4440c9107900390381039001e95a1101002c030820710b801c10100301c2e400e440f490031040c804e560341c1c1c030098a002c5030340c001c0b007003172590b200d800007a55014451003020b4881101d00e91180450b8106501c00584000f00c508111840075600a240c0d08a0307104121220242c2e106001003500ea6018502520195129600152403d9158140b2004880c030f040341c60320400c0f80314414026100d800031361503074003a847c0710020001d003200d030303200c03040644424109401a1076441406200350340341402 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 643471573 1250 643470323 643470353
    0x17180618070b160c24090b03150109030c0603051f08030403060c0507020904060b031216030305180d0201020909010605090a06200102041502010b030312011503021b0606030f0a02011b 80
    0x900200e1155035401025220880e4403540350700d56055036540d0703451740c00350310b040003502c007110390769802d41d682c1104d1034505c0c89501c1e120505100c03500030008001802c10344000c01410307055801045a0420200f00074080c0d241034038400b0503405c00c100901004100105803005c403900704201064a20381c1d80d909440e42d00c0ba10001a422503131010030803091100d5034104544e8000141e0480300c18041502016655000d140d4040501080080d0464082072084e001580c1018020725449507811040700c190749850f08071032a100240c1d4020503030340e400c1d01e8804041e034010051400d0540c42c10910307000040f1000101c1c0038103030900402814229918994440b0000c64081c018021551551a0f14114000d075601200d040c00560030035483c03a000e41000710a48280d0400580449110303400c20304002800b04c80404044200742d801d20865a83d1000120100c0c0303d0b0400c14060125400c02d4000d16040000088405143e40e010f040c1d18030060b40c1c040701c64900380000c2401c003150388085251441402990744 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 643472823 1250 643471573 643471583
    0x112b1502161a1e01030609020319200f0d0b07050405060c030904050c04050306010303030203091212040335040203011b02060106030608011a060a17180618070b16 71
    0x92070004000741600c811032105868034500406a035010250700d182510003042411008600c030040000800380c0c0c00c4041c0c014801010307245201d540d03544040d0f0f00703900e00788143c40c070007400e11107403014081c42054801d010702d064a004620100e81000b10b00e400e88403010040441d0010400940f4003403140041d6000303000000d1583c0d03944c085200003141e50b42c01601d5024415464407004c9902c4020b1402200c1c1101e4001c3c000d00350b00da182d600c0c00d4000350001000c000107400340d21198907500c844078005015000b0070303110703102007400c181c10002c0000c4514515004800c1c90b815544024544828580c200c0c540c009003010010303600c910210f80506405013071141500c02c403541c280300542d004500c050580b200365a0030001150759040301400c1e10700c8400d0b000620442052001c509080c1b100040101100a0070050000c0500b28000280c0074821a0a801c1c01c01c0d6030f90840c40700740800c1c0016900044120400d0743d41504c00d84080e51203041c2803041c40390b0500c0c0090070075801d03c90880d4280c0d21640103 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 643474073 1250 643472823 643472857
    0xc0b1f030b011211060406140d02090a0e15040c0e040c0c4e0302070602070b0907140105040503061f0e0901020a11010203040c091a03030403112b1502 66
    0x40d0341440d030b0010945034104c039200b03040e000c0e130092420030750240c80894040341c1c4c90345400c80340345501220703a5010a0750a10302e15007c200c0a24aa250820318500400b540a81030f400380c500f49000c3d0382668141040302d80b05900b0402580300e016440007071100440411240010750b80d00d2082c0680c1d901c0110366000704070801030340550047c140d03a41061b24103100c01888a070001f60084012589490449444c2c2d030bc80402c074400c260440d4460f0f806401d10b248118401860180742c0e403a01d1040c00e0048901700030a520416080c8a02e0000519250300c4441c282045400c0c9805c1c04002502c801004203441e1104202501448007651058808002805214a0041070303007071000c41c05000c0c1d48011001c101180b0050380d2807890840500c2224401c903042402c0780410303800c0c10280ba020b01002c5003581c0e081c00808008064554040c0000c000641c031030030700d0070100e400709020b01601922201d81c0c02044040b444010404d1403540180a04169000e000100d002e01d0300c6250702c000380a1449000c0103e105 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 643475323 1250 643474073 643474079
    0x5030f0106060806010903050601060810120b01080111130314190b04020a051e0f032a0f09040c140d0f140609060601090302061b06070507060c0c0b1f030b01 69
    0x1980030704199855699003464035038500c0015030380b603095444020b00703d62041d00104600742c403904004c0c0e00060450100e80c141640d5800c0603040010b002802d1381c140c03501200401c5415400d201e0162810034181e4503a00b4500280040d01c1152410310014002c408a41d03164130040b6428014801d0040c6540e080c1640c00c243d81c10024114942142c0482c0680109403000ca224500700491060361040055640078001d458001c2c0441501038501e101d03014803400c4030061240302440c1c2c0320b0010441c5130001e002620107050420a000c212003414501505a040c10b01002c82c20098024080d5400325403510440e05081c00420b0000d090210050580184290010304108104a000e0b991841c2042210b02c03d840f07041105449603401e0759104d000c44d02d00d1a0070001410240c0c00740107812034203101c001440701d405580747c1c1064411111000050000140041040b0061051030402c00a526140050314000d6607003035103418000e4a19404044050861500c0b940360390b00300b001555128901d542c103965 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 643476573 1250 643475323 643475353
    0x7060203040c060e010e1c03090803032a07020627100309230c010c0c0b0a020c01090b030405070b07083109150b0310080f1f02120604020901090503 65
    0x114001c2e00c00048a0b61801041c0d9072041001b40c003010710080400303440c080600c915a14401b22103004030b05102c0000740020b1404010b2010754400c00640002c05d00d0701042810742d5101015000700034060000a0201c4070140e2038070070584101e00c54901621a03440e1420684c0c5003e07084e0f008080d0340c010307220411198000e51503007100c1041889103211410b20205100d548a10414600c280d0b00c00f540701c0c103403240042d84a604080d540c1401105021041c6899282c888560703880200c0950140e80440c490754820359100030010000c2409110742410350610747c0d5401d17214050751040080d1100e0104800c1c0901c100c240881e8207002e001c119040950300c403111804149402c2d6441c1060702906074000180e4540c40e4080c0da4062403c8101ea0310005041520079606900080c00340e1558186624010545810402c052400808081c00410070300c9040c140d030400c800c100f07840c0c134414030340103020300e122407400500c00541041d804c4502503140c0351440e0049410345d140340d204c0c40e8075224240342e450b8098 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 643477823 1250 643476573 643476593
    0xc1201020a0215090303070e2e030b12060402101817070605040f0905070504081f0b040e0c0d03020307050a211d01030e0c0a06170a06060516061b03141506040e0c0706020304 76
    0x94000cad182071001600e0007041246152a4001c10011074010b13500217801072404403005140301d54a814080544030000c0c10840b01e83d403068000d81c206800c0c511845081c0f5804001c540014025440c240e031400342001003510710100207105103803034203858202003140c1c9801038007034a01801030305049078038440404000740f582130284072044141d18a0039a40c0041c5042500842e0f400a0304c480c010040140c0e403a080c890101c20f044826411070109020200c0001c409001d10358245009900840c3c400500d65004004041c3d1001070b1003d02c00c140e0680c4101002d156250465283e017403d00243c107081ca01c054500340440600100c0d4010564030020400c1c64101d5003407000600c211500502e82d0384e86100344005c45103680114404600103014071690b02100c0101d840e48544101d9000c900c8080e010844c20380304030101c41d114080303a15080c040a0b40900712405582c451003a0340350098011868020030314520541c000c2600d92140403000800d03004102044801307460b40032104655a10340343c20304503071034 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 643479073 1250 643477823 643477909
    0x7050c040b101d0a1203080a050f070c0b042a230123162301050f0a020a0e03030307031b030605210c1201020a0215090303070e 56
    0x1603480c1c1650709500b4240a0200405038289403280b030800c02c00c10f600c0ca080c0409584465500005203d004910403008142903040180700c0c1e00c0380c5425051044c45041940c00041100407180484001c00520650050b0015001c40e0001094040d0340c5950504405280080c40c0c0c0f500c0300060107101c5015140070828080486460714090b0403d610300c0540310034041c070002015400100700704821408201030340b0307200300c48070456201140360032818903a0591031440800151540e00e65540701e0208401380030b40608600010344002c0000c0d290006004003962000ba00c41a44283d02090386000c0c030340124055800755000038100c4e500e92810010007000f6002044641c405001d142c00b00c3c000a9000e0b000b460142c840080050144500b281c1010000044502c45040c141c41030360b040040c1074681c060305000b14180c43c1d00150b80c418005d0b002902d000c07030070005041d6814091080000610010080e2600940d8901d000340040340820b00050320000e1080080701001003116243c41900180d8048a80c8 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 643480323 1250 643479073 643479079
    0x4030c0b1017031c0e1c03021c2003150a0f0f0b12150a0e13020a060c050a02040203060424260d030c021015030b0105090c07031404030807050c 63
    0x7400c42e1a02e4540d45902071414800021900c918962200300f4583d08101100f103012021181200949050700f84c2c0d05408100c0c000210354006000b40c0200000612a500000c180b0000c3c000010740740410200c028034081000c810300c10220202e11002c104490b50300f0808002040d01c05002e485a2000800f0100f80c4282220040c2210300001c004444800703440b1502891148020303d5a50f410f21800002007080274a5440040b40310086040d100c0f10160501845140c1d10a1042ea80d0314414004404116040f00d400c1c0022000382a002070750000b148444a07034150350140c3c9a8440c0030103c1c0c044e1007c1c0c2420300c07850b4040e510031000e03280300992000072200b10642000c01a142003132100c07079441d8440202440794004c0c507d6110072038000d4000180c6100d140c8100c0700c0c20610f01445404640ba104415000c01c450f04100b00103001e1610702c0d20380509821600007025082c440e1180d1824403031410004d040c040c080180d011696199070a0b03900031034101c035510303949503d54940b541e00c440e050103003030744 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 643481573 1250 643480323 643480349
    0x902070b0609160819140a050a0b0103060515091201051f0f0501352d072304050409060c030e0703020102030d0b04091401231003060504030c0b10 64
    0x2e0f41900100d20541ea0310292a030308010340303410351440100413015904108207a16401c511003001108400d2622408a000c0001341c5070500c002c000c2c4c15a60007800b020704050800500340701030380c0d503001c03114803811079002030903640c00c0d0060204542c6880300c2c126482c02d5203031900700420450200b8502d0106000c8003030744040b0684601c6040241e005d1801200d002039091a200341c3c66a24000740c045000c40c2614044514201068a01c4846030f811103510003045101c01e0009280301d40100420b2440104080100b420315010000801d400c1d82c1c07a00003030707a038403694500440700d180d124111000f42030054001d001da0941814140080c1c1520401e0301d00003031504029510036823011400e0340540c2e0303059015501d0807504580d03030400340c4412005642d00c50340c3e510307651000a44408803000304941d440000314404070500794803040e0b803040c0f0f000781c00d900c1c06241c00c00c0040d04002c02c1c060b050761b50018002a8544036400d00700d44028000d400109201141410300c0f801e00340140c5031804039030000c9860a = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 643482823 1250 643481573 643481581
    0x150702130504080a0f0309051221091207021f09050f060a12020c0c130c020c0114040b13030b0405060f0108010b031c140d05190b09040605040305040902070b0609 71
    0x82116000c0b00c014056031828025007100601c03a070100c2803060754074500070a600c0c499448160401340030b07800903c104000080d0501021480020781c0c0c8000e440c2403c403196a1920240c086e07128944100000c13480300c8000358a00c115600d02c50b000400c214400300c03000c0189404d00c0090040186400b800348100002071001d00e003850004200c07a030f03091007542c0d0040d006500150035006508054824141801000c3c500c41341512420401c00b1040c20603130340820084200c11002c1d00704184103c030705041207090a20b1031101d0020900f1501110106064079654082010015285140d2500000d2003c0c2c000c03800c0c0414040700050950084000d4804005240d80e11407019080750080c80360a901904071455501f008031181315000c0788000c8074100818100000140c0c2c8001d54400404042c1c0c3c207503181d052000340c00c0398080301d0f110088505000c000d620303c4070300001c440d02c00051000384034a45800001e42010720407019a0010000b0300800d5454007581d00d001002d40700100c07407160003846150001 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 643484073 1250 643482823 643482859
    0x40b0d14010b0d050604060504092d08070f03021011071b0f0b0c0309030607080411191401020c0a090903020c0613030206071a07030614030d0801060309020f150702 72
    0x50480b80036042d01ca1500819100d010040c0500400b1030f035100303079100d40004050b2100d01410807450300c10440d00803411700f20f0401d095421540c1c80709045690902560200241450080b5694140c00400c0e645150f04240f80491070840b41103050b0a8003030401c1c02425624401c0c1029103420342c0324540c1c2c18a140711048100002c00090300c100c0d0700300f04807150200006116a0000c10180b2401000c2da0301e8943c100010038030380203056450800085440e010041401007000c10103140b180704403078030781c45020035040d03540c01d1130b1041c002e030364003076500f099030744101d85c000c110144a1960240c0740c24a16582d5148080080c0140d40094001d402480204a81485c114044556410111321031828050458081c04a42e41050b0012a0740851030b80743e10901c241511600c6200310342da0f039030104c0ca003801d01000d60a544400b02c0b01a0180c2d103c601c0702d0040740c3d0030000e9141520058a070006001d00c40f400000d8030300000b8100f480d00400c0c01c14003103015642c0312004040050003901c0480d102840311900d = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 643485323 1250 643484073 643484111
    0xc0717060a0c0e1e0a030b0f01140d0b060111060c130b0304021305041b3b1b070204110d180308070c171303030f0302070f08071403040b0d 61
    0x600001928140112905213004103010384074401e4a0302485201e0086808690500c8181d002600c5085140c810044c60b0310ba041303041d0340541203480c0b1400f440000b14000ca6842034107400000c0101219000081a6034810f024005a40384154212051803c04511000450b07114420b10503692150ba80080b4050315010200c07030240740c0c05065001c2c4140500800e400800000d00704071a41101e02c2c8001c1d00c06003503a10724070060f14043c0c55a103d04002a800e9516220103088012001800401f82d9050800130343d40d040c2d404081504002d0107510405580b64652041002c000c2d4014542904500c0c840080c40103440d003070040c414100034010030030440c405100c40381000280040c1c00340e40042d940d030f88507040c038000b2940b141e04d000032000b0140e01440e6807038200c8940341c0c6000c40c90030400c2041c507a0012403040c900301103003021840c0005030b40f1200c90300980440081c00e00c0ca40040d4810402010b442580420208a425241c640d501c501c0c000390740741e100b03604801c5454100181c1d00c04010b54a91 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 643486573 1250 643485323 643485341
    0x1c0c020d0c0b07050f0d0c0e0a06171015111e06180304090905030d051b16110a06081005030d09060305060a0906060c1a010f050d080c0717060a 63
    0x41d07042600c005969510000e2400070120703404c000d002e00400da903802c101c1e4042d02c00600d0410003c12400d50182c002410007081480451044480540400c80a90032890b15803070039170302d03e500c4861a95020744a5820940552020700d012048030540d0101a5000d140e244080f03602c0307800d55805440d1826100c1c07140d80010040040d40d0006004030f280c01da6140b00707055500c0302e60307015242030a6a13078072840d044841038442a100d40c0c10004800f904c140b0540309140d40b00500c844038003c0da60b9015a0110680100300b000d9080c151307000345840911088540005101d20f0040c0803408843d220000180404820345a210002d4040c10000c00e50340f5020850001400309030b0b407210035892601c241140070308400340116070449521400815002c8a43c09000054406500c940d010301e4540e1802914451500640d13644880c043c10040c0720100c1610109812220102c45018000e4031504251a1a120b00104400c1038402d04400141c0c104950522a400083c1a01070340c0c3c565032450765440559213419 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 643487823 1250 643486573 643486577
    0x20303060d030c08030705071b0b09100207050909070602151e0601230a0f050c0303040b07110f010633051308120910110307030819021c0c020d 63
    0x1100003241400e2a9014091a6010740790100548159880f59083c40d84103070f1302c8000180d0002405070501080041c104501c4811200e000e60f000c0c540384004586006130b041092151501402e4a01e045100300289409003030010000502c509180202e00d070b80b4055845600c0150040206070046802e400c55094411403e152081c0e1503001071207189444c0b464000d00b01c6050040b85031080080c8000f0565480c0d00c00d04d034101e40c5980b08015107001d8107548566103105c0400c60100044101d8441c0070050344e4000d54005c3c11006c2a40300c140c0c00795400144a01c2c002410711414004148640c0150030560449a0091141029520000f00f81032240e0000c220401d01441c51981040058801c2d002096011102040c140344161100300d41420040440d0001505600128405046141c201c0d06401c101d0f402d400d004104100c0406000c5d02c0b805005005410b000b84800007500940c8810100d01c8035490b00b800440d501d0190140390581400683c0d40074040c50710b0801c02d03000c00ba0000800c581c50384203503 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 643489073 1250 643487823 643487827
    0x6222405180c03040309030b04030801050f0d02031b1c0515070507051504031101141005060a121505120109060f060b1b032206020f1b0103090c05090a06030b060a03030203 75
    0x81c0e004400a503c05041181080070800c00080031070790303010200d4081c612960b2910b415524007070820040000c00402c0d40d2240020111503001a900080c03209044040b8079036007070fa110340b10400962951454903030b04a50209151503c0c0402502140d00d02815020100c3c2205588070303018125064020840700804a5000e60043c100b86606600c1180d8080d1203840c1c2800c211058001060a48d8106503210f50181869001d1141c10400e414902c00601026103015040c88002c00c0001e04400d540044540c48a41e07900842a807122000d0602010b0840a071884260015480406000f00020b500a40b20503107000070008442c04a8009c1800b00d0728000001e0741002d058414020440b0f01d00d4180f2001392104210070901c19150700d40d41858441d500c0203c00d940d61030020060b04001507d1a0650141c20204e0003003280c4100c0e0000149041007880c0024150490385040307804c2010079040300d43d1259543d0b0400038529601e810000a481c820310241c40251034600c02d1296200c043e0100401503041 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 643490323 1250 643489073 643489081
    0xc2e0504051302130b04090906050f04030c0b1b0a090509130305030c090103201e0304120f120e0102091813020402031b0d02180f03060622240518 64
    0x11500a04010103400c286903c50384e17500d0644440951041d841250100d45074943c200502806200d810b9010411400c09042440e1994004005041d8804028030180350040440c20007021100c84680c03840d4501d90403543c8a50440340a444c1c104103200d1070b841203000740001fa124a1020303030100c2465515886023415900d800301014a40c0e0401e0041a041580d507501401080010070403001d00f0751481920141c2d41c1d02041c5034034120118040083e00404010405d020001d03503d04464204540c0c0361407c840b0382d10310031030121440280318040303903030541c18030300260031010065004003400007084842c052410f1002403440203c0000710703603218100d6600c015404c00f508164008590140602085000008022044484e9504401c082c0708000317902080b800e80300c4100301c0c1382174204a801c980340110041c0c050002907035038600034141406150008000c650220981c4204984020251406d01004070910b4050003600705030000ca06103981c00d2040011641842c104000c402c03180c40b1412419a69 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 643491573 1250 643490323 643490359
    0x90f060b012607031509050f0601050c0d210c021e07080c1e060f03010501031a10030b0102010b030d11071d130c1d04050607050a05090d02030c2e050405 67
    0x20004194005241c5c40d401c400b80f050410780d960742c000d020031400000d50740c10010034194050340d00405282c1400410000c840f95414005064030205402c2d02c0e209410780901c448901d40d50081c240c0c41540d69051203d00d03000e0a4003c16035101c0fa590f0014181c06180192038403a41e200390038800d00b4690303000b42400700442d017480c84081c03001203e01c001d0001c107a405240031410030f03071280400b000020300210041c4400d40c2d15005a640b41c0056406440c14445403400043c07103030400c41d00c00c02c00e00d540c941c020140c1da4002c3d00014030b4104003c0035100720503500c0c6c801400015140c1c00d03180c100d020703170b50012410501d403851505a141c120348019405e580c814030390040c1c0b12424035083d9030754070600c840003410a6800c4d03048080c42803048a24540c41c1858904149441c2000e80404140039041c4540d4880a80c4402542c00b0000c013182c4003102e141d540e00109041000e5604201d40119850f02040c013038900303080c0341c1e81180e02108054a03034203110603070443d041c0c0510301034998440829249070900341 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 643492823 1250 643491573 643491647
    0xf1401200a0c1b030b100f060e180a0b0a061215080c0d05010219030c020f060903030c07020d02100512070f12020d0b0406060f0201060603140105060f0d090f060b01 72
    0x942526902d20801340c5a0702c61401401040303455107018000c0c00710502004a83c003001d50000e01281c00e103980c0d00200d000004403a184500c551240c42440107000903c0c0c1c03040d903041507845082c0038008074001c544400f401401821171280065010b070801819507008612514107004503201000540f54150035003007000300d8890288001d40340c664003400720904484040d8280040c15070b1607200003c5d000d64020000e800c2c201c2004004101c1d4104100b00302d10f84801208036070744090107036920b0395642120720006960141c401e4010b90448411084180529000001040f0b0303032505101000b038941c0c0750607003150802c003108841c10015901e9103c143ca41c0b40c40f034001c2e0035100c1c104a000b00c1c01e441840d001c58111010350303105600007018464200d2180c0e4081c41a1f0000d02910718040c080390701400078401d0105010b10640d0f01600001401c690940c112005132845003452200500240c4a142040c83c0c0044035044162410352400500d581598029008001a82c051003d0040490b1803604150402 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 643494073 1250 643492823 643492853
    0x30111031e04080f041202010905031c030e070e040b040b090f0d030506040e0f0a02090901140619031a0a0506010f08060d0c0f080102030f090c0a0b070f1401200a0c 72
    0x1d110180400f104140c07112000c0c0006c2c280451505003c0c803910b000040c1144070b04e5200d00d020303400014401c0c2c40003888441e4461010090304000c510311350a0a641e83c41c0c000181d0150800e6080c1005120402401140d0113004500070100c07107400d51100d0421648032040b441070200c59a024002c81e04080b80030382c100c681d0011000304002a101c0d64603001c0c508082d00d10707658076125045401004110301c1c06006d010713084001e10008004465101402d040140c0000d452188200d1580d0801400010210581c0d0040d692042e41c081ca9038441c0c0042d10b2400000307a5420325014140320008603c2e5108440020740100c50b6500c00301c045e2900e50074048089a0308000751150941884040b031000c07590902c47d4000c0c00302e1000180c0d40d2500d650810000f241c041c0140480c0c0d000604049115a0361201c104c040d1064440388507a070311704c180740003088000440c41c014110020100c071034202c0300066020440102012007040d919000550018400f80300350b070200d5010442c100c40b80404502c18070750803582 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 643495323 1250 643494073 643494083
    0x1a130b130b030d14040e07020d110f0a02090a060314070603060e060105070f020307080d170a090507030b0c2502041808040b1b0a120215060a1503150311030111031e04 73
    0x5001d46802c88144222021a2807401503030149d00400700150f801b050070005444404c01809000080c421041d0b150660b1280103482060f03080302044c80b207522540f00744000d581c48000a0401d0074001c1106031180c401f031080b03c000c00e161240014007035a0241a440c40b50301c05965691070140e0356030340e19070111160300040e03825114000d40881d4044041040074030490450f00c40700b0514085414112040c0d800408050030142001f4213040001d070300250701001c0e00d6000441402a542e5400010b0540c0100420411803c030700d00070720200000c01c1804201841e000344c1d8144035146440518114042214000902c0450208000c0000c001c41c000500b5014002c9100349850003141d040041c942080c0d5034040d160943c1c1c074494042155010080125107441030103022001d89014400180d220550b8400d50044180000f101d203c0f4034460360240d00051142d50034090001d40301d003000a402400c4034103140c041d40c6800003840030368800c1030175644510142d050740000342040d136514000c80900907200710380c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 643496573 1250 643495323 643495327
    0x61d060108070504230c03012c0705031f140915090103020609180a0f061203050304060f110a08011806080307080a140409050402030d0f020c041a130b130b030d14 71
    0x83d030007201102a50140064003c0d01d40c0f07235410040109031034656625101d410320786400403074510104200d5800d9001c185030409940365580e14440c6c0e0340807c00e83c1064540101c2e1060041114142100003c008240035121000140c3d03d044400050341c82c11107000e640550840c00400051421500504070a40050007880401d51040c8030100c2d0110240e50100b98140c990445d040145031612410000703010610300210017503e2514098030610025201900d49a100c3c071000d5420b0f00c4a030080d209000401000383d035a07a6050308001c00040b42070107115a407442c25404031001c40b40c50f004140075101e80102441c40c161480d038510780e45070b0040305c04c142400641500700304000304510141000303044400c0003140e0ba203072520425042c102d20072244000d1141000c42071204940c00102915107810558000803c13100c40b0392090384035840d0391850740c0d00a4091a900441c65034a030451850590306449200c1c1c42c2c0e082c810100151000000700c0d5405a00c00c002d001c075070b00d12859103190009850a2814 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 643497823 1250 643496573 643496621
    0x51c0501060b04180f0c09030807062309010f0605030309220207050d080717280c0e090c0a0804030f1809060e071d060c1009061d060108070504 63
    0x60019002540560f400c00030400c000c2c49620810b00509003103011700c541c03c00941e0f041d844050401c118a0001500c41a0701146920400503035500901000d46007520114002071440300b001c01a00d401c44a5a800c0e501b8007000e04495074180c01040c007035920003800b80d030411100d0801c4c03010b848191002c20011071124816450510f800d4401800072030f00070300c007a186a01011001034190704000d00a1410082c0d22684d581d05c140c210f035105500244105d00e842c0d02c030841c240126204614944440941c94501050b84100940000c04c0e4850860152459886503541060007003a0b40200c843c05008034007101c0000380001c3c498003483d0124603150500300c601c0882d00c5030a04076081070b81c011044142da505400d018003e0b421010580c4a4040c0c50411000c0d081000c548440201e010155401f8100214440742107400501407409000b120460804c5000c52314144900604206100080c1e601c000c0100b03101d00200100e8010706881c401c0008099003440d040901c001030103030b05031308202000b51100d20 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 643499073 1250 643497823 643497839
    0x152c102705010f060f020309060f0a02101a0a0509040f02060a230a080610020c040213090f02030f0c0a090620030304110f0402070c150509090405010207050610051c050106 75
    0x518081e00380000e00d0749407035040c440e000e4591780c40f04400005550080c011064607545601c11180c0c0c0811042c4155210f1404c01c10507803510303001c010303204802c50509428842002e121070302d41b590b99500b00c4000e00000d40c3c0301c0031700c1480a401e0710060b01d465100d020303076400740c140704000303103005042c910f0500c0100c42055194030305143c3e80f48400362a01400134015506d40c1d8840e000c1e94005c881210781012864840001a50307600817102a40d001d1600464200e484514211880004000c0e0304014070480d84410321050095100320350003601c407489140030403400d0300d4041c02d461806020340c80c3c5644081c1404401c1c1c400300038190400b0b00e840c0d4068000030b05020244007460207144941804620140301100304010500e203491054080c40c41400304002060460310300c2c9003101c50b25580c008500400ca40300319180e1203600d04164100300c0d10000d02c41000070550080282d40d006005480303a58070303400c40b0350980d120944122a4030107101c0c82c0706400c1000c00c2e1042401c04d442100000b822542d14404 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 643500323 1250 643499073 643499081
    0x70b04050105040b060a05030303062e02100606090303051e071703070905010f0c0b0916031b05190302011d04050a1d01060b0418152c1027 61
    0xc48099450700c0a21040000300c0311819088070701250404607060501000c260b80e4000100407600c10302031075400004000601d10202d049800545460000d11070b240720183d40c4454450091039842e00e004d400285080c440c00c0d08000341d99250b510603182c8201c0707414403c1d040203d141c1c01004503800700103100000390000790b201104040e00000765202d2a10b801c01412070309007540200d042c0701000c04403035281603000711081070302a44480400c2a980701c50b1200340c0b07010941140001c40034040310700401031004400c2035010318885220710b0345005448000340204500c400f00300803a80210644103000541c01000d1070803015140c0307600750180c2c146480000d41940e10544403580c4140e0394100c0d15640305c1c1c510b40310060403280d00b4001e0054a14040840019200d14403840100c200c000444507400f2041e82c00039030400b80d00049208180c0e444203440c02840702011044641095880701e8600070b5880e0451951082c100c20034441d50840c0303000705c03815145c41580030b2031801000c5008004001045c0b0700c1 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 643501573 1250 643500323 643500331
    0x30f0a0e060a120e0c03030d0e0106052806020109170703120501140102010b0631080105040305280206040305030a14090309120304030b1512190c05060a0e0d08070b 72
    0x950758080c3d95407954210100c58101059000c560002d000b215905d45002040301d841d04a1044c1c0041e003410901c1c4c0e01401455103401c072b181c0c4507914020740d50801ea802d40681282510f14a01b0b5204d045c1e8900c02039080310301d10384e0010030704c0d00041c000c10421403c030b81c0588010b074001c0c10200d0030110442c0d000000c03150309070059444031001c50040a800d580c24850720303403125010b40754103140c4040581c00e007000d2500c80108556500001e041d000c04030f00c1c0c43c40124020000c1500070710080c20507250149ca10303042050b000c90841340200200701a001102d0000a459a558024000d20b8070380b0f84048840e544010020300d01039846010b1a5010701c000c4401034401c0b84408042d5407140f00c02c1c820003241504080341c1c0c0c0c80f194418401440801c07101c0c50116008120203028801c1140c9a002140c001801d2a010340b009004420040800d006518080101c0701e00c00d050220203503449034200034550007406084000540345101f5000c083c10521103255030a80a44a41800d141e1690354038461040211 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 643502823 1250 643501573 643501577
    0xf041b2106050109140a05060120070603150b0d0c020102041203020601080106060e4005060108060102120a0e0d080a050d0612031b060b0907050a02120c030f0a0e060a 73
    0x2880c0300d814401d10784203881c00342641d500144000302031016649944c001c080d00c0444115520300100c0c2060303000701c100550303c1542a550345c452281c01407419468000754030400010134144501c030b170344803000ca034103507820348400304282e509045588030114010b190311100da80c190340d82040017145001c003400c400c0e4041c92080d40108100c0d0b050200c2c107820b5401c1d0368415800c1c4420110517014581c0c8100401a000c102580e02c0000380f8002d20030482e1900529071400007031554400783c03616221064004601c94034007030300c0c2c0880700c0c0c58074001242c2d1101007a5a001501a0034400c20350b0b190300c1040b0394412540024250320240001d91070341196a031029203680b000c1000001c0400c03c482d607500400f0001c08107200a521034006030786014080c01951510602006680d40401c000c002d074650180c2c80e8000054a41581ca182504000d0700590040d1102da0244c401c04914000d0954001e0032120034440050107142000d00102925900e600a25440c0c0c090204a0746100c1c3e00f5111207001d000e040c2060303 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 643504073 1250 643502823 643502879
    0x1c0212040f0f0203030c07211e0f0218010801051312260f160e01020c100c12020609100e0a0206030603030706020c1006050d03081902040503070b1308060f041b 70
    0x10f105140d4907010031230030026509403161000c2403909502001e0b41701119043c2c0a401e6141c41c0018004030740c5032001b036100c002c0c102886d1491443c88005030584403408002c006540b940002c0800d1980c18a400920b4a0000c1c0c4c0049065071040c0e203801c201e5600d14a502d051a0701644280d9601c0c24201c1d1040150300078a010059007a0144921012650080c1821a20f501c98200005e480c1d40011075968042d0188281c003030f0506100b401c0c10f40f0600d4002c018000c0b00010300e58002c3d107554041d40c1c03a184a1045494070448400a407160482049001005011a0700280c0c00e20455401c01007038240d01d0f02061100b2000704070180020005142820083d01d020148803d10a085400e9600320174007421202da20b00d0b001030b410a002d15040785600140e0111540361104200c064441c41e00003e40502841000050128041c006441a80da810314a0344130981c4800e8400d0741d44400321042c1c41911880700100d004102181350b020988500f0322401041039486502d194401105180205484001 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 643505323 1250 643504073 643504079
    0x10201020409020c011410080303011e0305100b01020120120403020c060301030606050907140306090a0e0703110a0801050618060303130b031b0c071715010b1c0212040f0f0203030c07 80
    0x14030070b0031b503a020184100c00030345541002c800c50350364001409003114406031801110f111080480201005552007012a100c1d60007201d5404c014188042c691800b56003060400020701d04069000032519210070381960130143d5455480302030020207130055080d07004c2c1c0b082020281c3c4800c4011400780d8080c00c0003040301441d020601020b01d0004001804020f131300c2200b030500e01e610b0030441e078201c20101e64141c03030703916156445030060102c0d401c510b100e8402c034800041001f008117488500b01d24106ca10849040d41c0c0d000c01800c0c5c5204440482e0300c07505041100c0c21000c148004c030340c1c0203007000e01203a080180c2c183c4100c80500340368210000f03041022007000030980010249503040005c05d8030503818800107030b220682d00c0001d80034007408181103621546030402c0c100100303a1000c0d0580001625940e56282c0040c0c0365018490500440000c9240c0320b00500c3c403070080321455144c11181d844907680350344480b80c590f00260342c1104e1040c00b090548001da9030400c09000c00404120203041d50f01d10b = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 643506573 1250 643505323 643505351
    0x15050f010e07030203040305041509150e040f0612021e0603040f050f01060630020307050a140c1b031e0102030601030e010e0c040c050c07060309290114010201020409020c01 76
    0x100030b14007010540100100700010394044143c1d02110001a03082075510200c1e20140d0781e076003003a00144004d8070702140740c002c2c0650116045540710400d41d01008000c035101c07c01c0d0107540b41b5001c0c100441c22000525001030810303862111042080003005021103140130001400e43d1f00076601950080001440e00060250a109144100f8045002005a5490510040c280260102017003401d11049000d048802c0e4602c5407030800c145003804210741e40c1c5042403002e0440d8204c140741da0006010300c06100c0c0c0b03900711081140c00c82c042440040a102c401024001c06042486080e41c1c1c040c0a50b030398400560b000301c254a104014050300158aa02c0d00c1c6000500300c550005408000b6810f01d035001001040200f0b010a44082c01d87d008200f0403040542070703505200b104071005142c8501c0d031001420303613455480ba80c410b034450030700340c060b0800c0010013045034000c0c2d071021881c107c0c0c00340041200030800002c071403d1030410b00015041039940c9542000b240c000110035400c41e512100d640d19501 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 643507823 1250 643506573 643506599
    0xa080a02010917031512030906040306060e010e09150c0403060c0e04050604020403021c061814060144070303030204080c0405160807020c131a101b15050f01 69
    0x1010f5100703200e05500e0103010001c0c070403111a20041c05002c6e54641416002c005104803981c10301c0150070507948690302d00d40f2200a0002c0d20940701280d51940003c568480b0f80400341d0300800303d990040080501744092445405400f03042c51411030000c100c0040000c40340e0182c05104005500c41006101646060000f80c400052403948128410002800140d40f62a16460549030000c401901c208070752070104000d0030f54040c0c0c101c012554901d243c04020380042c00c5590140700c071007030b2503140c0d07600d444400d5078030f00700300a60785081a100c03100c45c00005600044443e41c115030142d41c0022001c081c4507400c0c61103039001940043d400003024000700c1010841c10760400f0094808202501d081c0400f101c00350070031a207210410041101041c5120302c00c01040140030b0b80107100048115001d002c000003000b00c50400b110481d121010b00c52149844e504100d0641e1040d2559a07080d02043c1c81a200005844412560907111642e50020001c0c00c0c0714541c0f28600c1000345648950510040c92000 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 643509073 1250 643507823 643507853
    0x6070806150403030c020f0d0b011502010b180a14150f0a06020601030312090c0608061305070f0c1a070306081b06161103060903030109061d070f020a080a020109 71
    0xc1c461480e00e001d52004560455089a4151801004400140c8001203001c0001d4904603070002894170b0740401d0080c2c1c04007060484464a85507610b4107520034007a400d80b20090074055004001804025065458851159000300c8400e000600e1180f8003664048210060382d034820702030501180190581040c00850b0003164003100ca95030764510745079000795502c0050100a003000111101c0c0d8102c80129040080c0ea2940031036001d95540d200d081c000d0003c181140c00b184940ba84881c1d4406000281c0b25440c02110180d8a072000d6080ca1a41502c200e0191b180c121680580100d4a0500d02100403002d40150f842c3c0e5030104045140206003490a100003000007003070044032103001c92035a58241100c144503001508500c8000780360400390500d04414210a805014020420400c0e01c80800154140c640207601004025110300f598000061100e000c51401d405120110b20b646010b09807000030300a03140304640ca4030740180d4901c40250000a0034401503915800d01d2010020145045061 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 643510323 1250 643509073 643509079
    0x7081b010305040b061203120103060203070813030f080709170a0c15080a0b04020903010203070c050f030a050909100f0b0d0501170312060112020708040f060e060318070e0906070806 80
    0x2a007866101d00c00135010140c48030b40714026030780240c0e25802080c4103030b80041c0254030441100750fa4a003040c002a6004582c0d1000013811000003404031f284102c041c403e4207416544a10368842a80b0003030f1a04000a002101030140081d00099242d200640d03014203a805071003c0e040e4580a8640001c00207125000040c0b12a11140c40c0707580160305c041001d030700c00c0c240800880c2003421003000c500203224402c4078070b4243d40000b040060180e041802c001c819403050b0115000d070703001c4100319600e9010b203914a8000602c200096070091410041460700800321004506100d036035100750f8140006c050b030105140c00306c0410401c0410b18244146801408142100e9590706486619262644600c02d12407983c116040003184e040e0b445003200c40040209160119034800941c10002100d810a11421840b00040440483d541c0d10640000c0340c502c2c809000c00307055403a4141002059a24217503458507600c94000c00282c05010064142e010f201128094290790a000c20001c1c05420b0040040e80 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 643511573 1250 643510323 643510331
    0x1090f0b07082a0f0301060f0e06031509190e060f06150a0804030207150203040302120114130525060e15030a0e07080102070b06090f010b040b0c03090307081b0103 72
    0x4800e4480f2100c600041070214402d01203016000851059401000b4410301c2801c4040004031310290000e00c0b514010b48680c039032402240300182040018401190780010105030521404031506140702c000e81c1140064a00e081080280c44031081210b495981001e5a03902002c1805190341859030056088a0140c0b010060740a038bd0b030312403465118403403082c0200f004441c00102031501c00c0c4418409031102c02c0c941010000781120003542c81d00309000c180d11603143c0c0312510154200502c40c0070754041e007280d48240d07580d0358503200c2580802c1e50902500c0f54002d90f1540003032281c950040c0348034102e0300902c0200c0d00c1d0500600070318401450300442e00030941254810809a56401980d5000e0b500030008a0081c4403043c00030306003400c56001800039070002c1400b1040102d07191545104040a464100460340c500e00c0e407045c802c03c21311801c202200c01300000e100414900c8001c000511211080300d11b0955454003082c6407003910703030203034a440d0040003d02014050440c1d0f91030000c8003d00e4280 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 643512823 1250 643511573 643511581
    0x18010f0f030b060d080d0606200c0a21170d1a0d08030a0e0708010e2116030329120f03030f0714180306100803270301090f0b0708 57
    0x2408501d400f0307040610686403130800100b0007042c44212000390300d10302001d01099a440c03001500640b10000c0369400c1d11100341c41c0c6003042e080051080080b0000a1064000c3c03407074160039000c80c0902100c400c620440300302454010410a00d55003020380841100b00b130303407001001213110840344d00c0c404568102d4400300144442d0368411910102890b0003620096903501c608641a0090491204248450240d494009130302d50381988001c1c61030100c2010b031000240786080091884070001940021500103004414403c41e284a0820b10244a4100068070714215915410003030b0b00c03440103038400e4110040c500800c1c18001d0899981400c006c1c024094400d20411040c0c690000401e0340c815a1030f00000100030b02c1c0f044280c00401c20446124036a40d601303040c8500560b5103000a001d02910610000c500354a040003101401c490240700a14248888401c120051000303205016011480c0f0290000031550203111301a5014807448075400311168134500300d80c4506c00200031200b8049090100 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 643514073 1250 643512823 643512833
    0x10306060c0b0c04080106090e06100f030f031404150908030a0e0f0a050907020d030e0607081f0b041203020c040204030506160314042003010c0e010f0c0218010f0f03 73
    0x1d11481c5500c120101050780d603a415051060040340d0000300550f0803c240000c1035207466220f009d00001a03003d45549960746000c00c805071955102d154811000c9000c100701042002e81a0480346100e8030300b060400c0005030a00505400030380041074070032080b100d00d0164940007904980184110000b46050803440400585038030f01e0700c84190f001e4040303040000d406555a01180014040c01030010b051400d000300000d507034851510303419021900d030041c05110381100060701c0d8800e0074a562482c40d560785600e4081e03030200c000c0400c00c00e9144984804074100c03030104060406005004501c440d03240060500900e041c01c5008414011441000b090011a1005c0341c2c8661081d40c0f82c2c1e80e00c0d200020b001d000c4004010182d10b080124000d45c00388810044210b05980e01c42442d503d0b03844905001c0e030700305422180c0714180e040209010304e0b1903a945501072314a21984124900740300d54000240e0700462183c003c0c0001180c4041940c0c0700500c1110440350100c800340000e502140811070a40d521 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 643515323 1250 643514073 643514087
    0x6130e0c04090204060b0426060f0601050c0a170a0210050c0f1309090602031501081e0910090c08010542060a0905040c0509091902040b0313020f01030606 68
    0x9960041d521400302100b95111900948020704040001a45e941e0307540700400005446992102d4480c0c0d0564810303403091030b000407054090380b0000074440c2c050301c422005458990250640e2500307401040da0358404909402c945d001191102c4910584e01d07800e05030000c1c1015840742d00007500303d1800060020f9031006006544440814081582e5540c07a5011400380c1744007554001c056603402c141650041000039006140100540c000001c0070340310180055034981011100e100e48180c010030341c0c1c1e070f03040d044c00c1e51542c004000601703a030198031205000030140d94030745030183d4078524601c5080101200900c81c3d40e91140044209825803203000a41c0e2100350b44160000541403108000f00a62b4200700080e00c5150300c0003000e007035640c44003040c06400001d13540b06440c400e51400941220140c01141280c4821400038071003c503503a0388608c01d40d401d240080b891025540d00713010110b00344284000071750162807850f8065550030040c0c410400040e4a1003681c504050510004211160700414 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 643516573 1250 643515323 643515343
    0xf0201030501061d33070c06030207030519030209030f1b030606030706120228080106030e0a030c060212130b0106031506050306010e0303030703140105030a08190302070507030b06130e 81
    0x505821034041200d002502141407034600078583c000b002c044620644e0580140782171b91103000f4032814075030382c0c0c4010b50890280790005030210342c0802100542080d1807842075154000e500b401420501040c1c007091500740741080005455000055007c0302811580c00d54699041c1200108460300d13201d800300761242030302d1292100b0b00040b000132240284c10307074040e2540548010384035070f80b000b0302a5500007042c3c0c4144481010500312000800ca4901c030f03025003002ca8070301c0401480561150754040381d0100203040291502c50382440010a82c0e584190030f1405085480798880f0004c2d0203040202d041d110692221082c14500204c0055503605141b10f10112a254246035480b6600e960040c1c55103020090300942c180400010040810341541c0070805291b545525407001d40e898105055070385544001c060142c160074030098645069240c414018010a031038058100180c2e0340d1345600d48900b07600129821603440c420007080d418440e403180c14121012405000441d104400107461760a414 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 643517823 1250 643516573 643516579
    0x6050303040627120c150f0e060f120a0203010815090a020d0302030715050106020d180e1009090506070f0e180601030207080f0310050604030c050105250f0201030501061d 75
    0x1682c814900380f41000240e00510155440e51001c103100c0c03924241241850249003052140d101e01000b00302d2165210b113031020307400c5d1180500000b16104100c4c03260403044820401c144101b203000b0401c0102511280a500c2d0300d1409038881d4100342034281414141d08000364450543c4040005641c8001089968190152007a500319011418124103500c9054800303458150b0384030005405c84415407100381210866400c0d240c2c0303c41452000c4038072002e01085515090101d210501c8a6101c0c407088507007101c0d45e601300404040c3c1d0350254100742c0da501350042d10f864012008003d10759420100e0f14400c0c82552074418601d44810700069682069400044141c1001800040f0039900980c100c031001600055201d480707560a8554901641c400c651400074100d411a0000d244d080046c261000e90f0790114402c09214201801150a50003c18007400b0300d041810f142e06035422a0b003041c0d02c0c2a40141c00c0100c0c40c0c0020300016050300d0040c0d11640400c5445484008902c088217802e0102c03001c11 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 643519073 1250 643517823 643517867
    0x9050402030a09060207030906020c100203041401031d0c040c05030f1503010213030f1106070c090207170a03240f0501270e04030f09060c033b04060503030406 70
    0xe0b407948070040c40048002420720b4400070b800c03010716030004000d9088600940c212191002da080a01c0b0340680c13007200d0080035038000e000500c600034a030f03000e9480956042c90000b42c681c11901c81a10801210116044190425110720780a405d2a001d00d03191612581030103030de181406800b035900150300800255180c2002c1c2a0324031169001c0d01251040541c5c0c6045031211601c0c0c1c100010408102841110110282e0318802013500340a015a86865045000500d0840c030f8807040002940c000e66049a10a60040ac24400d4001d07007005002103104c15a000034049501c141003005e81d200c26018049024070342030f81086a0080f600440742618403e18111440650a100303407076107075840d82829100f0286200340031550800c0843c2042c0300350700954801c1c1c0460642401070f100580360b4007070b01000400c151201c00200b4003844882c154200c0300c42803090490100ca0344042100220307801c065510301c2016010256241a0082c00054039013100954a49446c0c6035000c0c00781034250074144455001 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 643520323 1250 643519073 643519081
    0x10c030e120106050a081501080114040308090f010525020a08160201030b0603090f060a0204030302060601080402060c0114011a1306031806020c2a28050d05100e0d0905040203 77
    0xf90031110090074060203583c0c1003902c03070045030380321062600b034010002d0542000007086081401400718042c4450140180703603d96880440e120040104240154424001852a080824402d1512494260038007012039281840301010300d8600380d00c18411540903064020201c0d070040111a0411010003d00205000e80e00c01a00a80070309042954001004010840e0001000c100c01501a001a050321034560700d1080080881c0294003010700168000400603140354004c800c0e054000b4001402c0700c0c2040140d07180203080d501040691107c0101c4c0c800108044280da0304c420103c0b40102580c1401e10b0440e000e6184158624461781c0101038652142d12007488010032209040340d0030010940da214400300c0c130950b45803d82100001c02460303c00021000a00301c800c0100340c103c0080040c80820b100300b840c031300c0c05a0340ca40844481581110005010b03540c03200d105c86814480d00207030405402c003030192011a03203c413590f0030444c4c10106000007c56400003982c010b03920110340040c2c0700d0f10b0b = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 643521573 1250 643520323 643520359
    0xc080f150f040e010c082202011214040614060d08120402010e120303100b07020904030c02040204330201050c0f0d1e0e100c021f09021c060b010c030e 66
    0x101e110380c0305410030314207a0034089110040d00820200030054940c0340440c1c45540700554482071160109600006950b50342e00198401e40384070340c0a04400740c1c045005201030004c0c600052056508407145a9038590810b01c48cc024094aa4094401c4034503600c1c8407440c1c0c0b00e84066110f80100340d00c0e4106c41c40005000c42e8014244151070001c050079640303990192038002e90307880d4019105010b000700c030f4a8000841009001c12a100154054804480c1c0d46643e07406503907000d0303400c00c22a80310f9002e0201054030448003038100032009036410141c1d01d83e03100c10210415500e00820010840e410441041034601c070a400f140c0f0101c03030110006583d02c00a003070220090421a003030f003880240c41018031400080b41c1e000b80c00c0d07668a10058401070481561007030102d50b04402d101d40940c1088154003504560007d410941070130800e004101c666242d40014a81000c410228142070f0842d05040300380400340c41000c0380c000c1d0070b0a1514040c0d910345c4000d408a01011100382c030520180c21004032040c = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 643522823 1250 643521573 643521589
    0x10e060c030429070311010b0f180a140c090906090405070b0f0c070e0115020a020f010c051005010e07090915030609051903020106210b0c0c15070903060c080f15 71
    0x1200300707515584c442145180c000c2c209403400e0300071900c960070302001005c54a408451442461802040b1000341d200c0c2503c542c4c40a50003d2140d4215507803011034548040920242901c0740c0201d0600d150743d4101a000c1000074072000c0e0038036005a51031400c10002600001c0c8400c00e03140b880350f00581360035101110070554462680880b0b154020102e002509402c2e484000307060780c00c12100401100c446400407643c405e032500300a90b10000d41c452811180d402403540340030b10f90262040d204400e800103901e0003502d0302030f4091401c03910a8020841d40700ea00c13100100240030b840005018840c0052013881040b440c0f40400b074039a50780d4002010030420100010720007144000c0604a0301d00b118100a40200654807a19010b403d1240050400940000c080c0303004e60383c4001d01c200241c4801b240250700350011200312150344180d00000c0103a000720441c05100303801954030a07802d1401c5180c00740c143c54013205c40c02c00b4044501300344180e804a000505503ca001004420003022542001070419 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 643524073 1250 643522823 643522889
    0x16050d23070905011409040b06040c050409061d01050a0303080402060a17040b04060501080d021c092711030402030a0210020c0613090b010206060d0f03020a20010e060c0304 76
    0x1881101c0001807100d059802040c121940400c02e9040b000040c020711440003c01c0b140208101c0c0010001101da203019840640c482010f0300d0190704158454081204603151904501d5070020507000416450350464207003809001c090b038880c0c0c4d9892840d03030090144d00000d003000f0320658000c500500c0042c42608103180240d032805074103003603040c181405000d20000741e43c15220682403030004180c13101e00140c031900c080555801003038002d01c075150440360381002e00b05810400c07000000008000138000c0c03d5003c0001e03145895090a080031042408a51070750075108039200040c4104009a50b01207040b0f103045070161505001024515070890502903140d89455110401290b071244000150ba1590140e41a5442c10000d4602040042e640d035041110010ba00403e4500b04100041c0c062901da50481d1003401100c00545050352050301504142600c0d00c2000700d0344005409560340015803040901d0b095500a280070804120151223110742d02070081800008081e0f08100071950481d0024 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 643525179 1106 643524073 643524143
    0x20d0e0a0b0304020307090c050a09050a1a03061516050705030105010b04050d05030d0606050d140609180c0d0b06012601210212030c16050d 62
    0x415400100f0480c2c05004810000a603008103014a081c22095925510384414400d00b004148181d190300680c40740010481c104109034000300b0b6600340710190303001716543e59034031804100603020040c080e41420600080160705200034680b800445449001a544400c1e5540304160076220207004040e45103c04100c00c012034508452100d4000d0320500940f4100744103500030400b15080c6a000c030000c03460008801c950801d0703502c1010380c640240f00e0303241181d04180e0041240500c006003c00c400411040c400c1811400c00c0011000311003000b800d0000d901200e03d025130641c07000303603015404154411038007660100e84810309541410040300800450f841d0003c8011070300400d400c40501d03011040080307005a102c1e8500701c40610a4403005680e10201004003600c0d1515521038000e1b040c0f4007400c203114070b54403a0200c0e081e0781d8010507511201480000d0b0818007500c11011010 = true := by decide +kernel

theorem cover : BRFrame.Cov 643345323 643525179 := by
  have h0 := BRFrame.cov_init 643345323
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643345323 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643345323 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643345323 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643345323 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643345323 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643345323 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643345323 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643345323 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643345323 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643345323 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643345323 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643345323 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643345323 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643345323 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643345323 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643345323 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643345323 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643345323 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643345323 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643345323 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643345323 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643345323 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643345323 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643345323 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643345323 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643345323 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643345323 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643345323 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643345323 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643345323 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643345323 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643345323 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643345323 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643345323 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643345323 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643345323 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643345323 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643345323 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643345323 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643345323 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643345323 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643345323 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643345323 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643345323 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643345323 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643345323 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643345323 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643345323 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643345323 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643345323 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643345323 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643345323 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643345323 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643345323 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643345323 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643345323 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643345323 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643345323 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643345323 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643345323 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643345323 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643345323 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643345323 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643345323 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643345323 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643345323 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643345323 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643345323 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643345323 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643345323 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643345323 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643345323 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643345323 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643345323 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643345323 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643345323 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643345323 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643345323 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643345323 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643345323 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643345323 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643345323 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643345323 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643345323 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643345323 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643345323 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643345323 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643345323 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643345323 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643345323 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643345323 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643345323 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643345323 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643345323 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643345323 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643345323 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643345323 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643345323 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643345323 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643345323 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643345323 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643345323 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643345323 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643345323 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643345323 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643345323 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643345323 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643345323 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643345323 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643345323 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643345323 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643345323 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643345323 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643345323 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643345323 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643345323 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643345323 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643345323 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643345323 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643345323 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643345323 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643345323 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643345323 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643345323 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643345323 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643345323 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643345323 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643345323 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643345323 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643345323 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643345323 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643345323 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643345323 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643345323 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643345323 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643345323 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643345323 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643345323 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643345323 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643345323 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643345323 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643345323 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643345323 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643345323 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 643345323 ≤ n) (h2 : n < 643525179) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
