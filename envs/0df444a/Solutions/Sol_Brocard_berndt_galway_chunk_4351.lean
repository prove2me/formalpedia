-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4351
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T12:20:26.772813+00:00
-- url     : https://prove2.me/submissions/a3b9e862-95fb-4afa-90a7-167cab0332cc

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 782374100 ≤ n < 782553956 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 782375350 1250 782374100 782374123
    0xf0d081506072001030b011b03050c030301031209121e05070803130306060b0c0303040605091c0206040b060402040b040603051305061807080624041d0c09060603040b07050a091214 79
    0x103140c40303003908042c0d070060194840010102d03d888c11002e4246030469003803103800d030034200500010000104202d484190340b0541035250f00c03107564042c0c650740014200200358801400ca8682403072605040c1d084011100c01d003e008006842d07285445000031442d55008001c8501500100501001809041d00c44d04018001e42003032a0300e002d503501c2805a49000203000030f0061552040414108502082401c06c0260b0000c04000d240140301e41c042d481e0582110240c90180c850400600d5604d40343c03080b6010b80703415041560825007040411001000c005190000030302d500907414010480800006118000300103e82003041d40100b060b604103002a400044140d025105100407140a001031009641e1401411110101400f0028002d440c8000a186000030140d0514030140702c08213a83d072703807240140ca220185840b45001c0c802c131031100716000b600c2c0c94240001306d11130511540c01070a16400354a403c8008980351a1450208081d9910869410a030300c41c0001200710b05100d07007840f84 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 782376600 1250 782375350 782375357
    0x41512021e030a02011b0c06052503051606020714030903071d0a0c020a0b0a05070f0c0f08070c0e010902090108160c1217010b030105120f0d081506072001 68
    0x401c510001c0b079600c1000b24402410f0250a00b9481d2202c0751a4540032482c076041710300850308036a1240301818507440b2003503040c000401c400480d6180a8000388090140340c0c55920180740c6601e14a80f8411000b070310328100c071256006c100610100d050b10100c2c83c03034083d040025540e02c000f5481010703d01040c0b80d01c620411885060b000a484015a550750f070310030001580032405184c2200c007241800c3e80030100a10541d03810f000e120080c0403640c042886100240c488a0620b17124100664a10100800c000e0101e41452001030004100c14081e2506d288034221500d1500e0301c44030a60388000b8240c00141c00ca9901040e04c01c1d6540e030005145412022103505540d610b1054070009169030803030f5101614100303c0c0001e200e0f0b03691207610075800c81400034543c11819611034581c800d56a00a1056500c141c0c8000d904000343c0702c3c01324060b95403007181c0005216448a82c04182c40c034100042c41401e0b84d07441d4048540280d21000300400b101031060354054031440c034501148000320014204035040 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 782377850 1250 782376600 782376649
    0xb0a050925030b10080615090a090c0e0604060201090201031821020f070311030f031201140301020d0e0a03090b041a09030a382404151202 61
    0x403944401d20703200d0051410074640018082904141c02400151503020781107040100042030296000c41c00c5401443c0c22141031030f4203065207050442030f01603200240d074411031310031003080204001c0c0e102c0880007543e803e02c003102c1a007440000342c180d08240d00c80740150b51034030000310442da811700c40c00c7c0104417500ea01806600c2c03c1d8540d040f00384c1d480a082c07418150f0300c900c0000d10a00070402c070514030400750304030340c030305906c0c5c0c9014a62041e030442218002e11039075074082003c0e100402920080103020703942c0c0415030300c1c003800240c80211101d04907406560800101104003054044d0b0f200e00880310b002494052441c1c0340c01820b4021652144481000a010500988400d0380100219251800b18643c0714241200002e0400200f00802032034120410310040b0f00600340242501c100c81842c40d41c5d0130192000710301030041d000c1260840d00c5101d0b20302d41c02c10721151020700c03d500380384060800500d80c5400724003496840e410f07400c20b0300140301c00318041c4110300c0c007501c0b0240b2814841084c10714 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 782379100 1250 782377850 782377861
    0x70b040c060206040c0501050c25061101270f0516060806040e0c0f1f080906090d2f0129010c150e0a060c0c0b01090c20150a0b0a0509 59
    0xf031750240e0054504100000070a002003c10410050000499107400641141e03203400c0e4841044a06109150225844104d00403907541d041c418402d00120003103100340041e038420b80380c0b0074000b503001e01110703521550850803010803001c1142c494528a441410030400d410720102030001e5400911580c03181d414400c41c0081e10350b0105400c00032000980c2da001000e50582e00195401a0802c514502040505c0e055144582d1000c9400d001d920740340192042030700c48081c52629401240038100204081c050030311070b0880740390680240241200078042100700785400c0603017500c41d0603050000e0003814a606203405514a10003c070035190900b01512a800c1981c1c50704605010b40c0d61a600244d55050b010181d04030500000301015403000e0204108400d02d640035242c00d050713a0003500c4c40000c403400400c4180c00740c0b050f03400c2d4074815100c00c1c4000309107910403082850300003a6500706009032001c500d91081c040329413034054181e000000c07404540603c2440380c0406a03512441c4141e43d104180320 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 782380350 1250 782379100 782379113
    0x50906070207090f1808090a06050f0a080705120901090302060106090e15041806051b0f030f0402030705042307030209280b030f041506140f0a030503070b040c06020604 74
    0x441d01c8440c0d010138001c40d00c0c0180001450200d0381c0d00807440300b25011030200140301000303180d040300071074408595545801e03041710301313000e0350f000c40c001001e003000f0741c02d90039002e208180d42c00307441494601e02c0c01001410704000300308140c1d011155030f0b4445d4212002c042e01400031034007404440c503121420310700e42000190140005000032aa01d00740c0a09030446898541000140c40c003c1e08003a12124210b140a2004080454240c04c00e0f921450711070062682d44012661080e01040e4010b05540b500d4442401f003400c0500200d0b410b01ca5680e00141039180c0e07006020120300c90487c2d00c00c0b5000984111504044024144003c140c41040480515a102c3e0018082c0400d00c0c2901c003a44002d040c4080c0f81d2003001d03000906517070404801c202d114890003150300e1055100c1d44200303120600501a102c150ba07014018210389603004c2c0034424441c03c002003040050440100580b18a42c1c0e01e8680b58210b6101400c1036400b90006d00402c0180000c09003003030f0083c10584004c244030b1801d500d510 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 782381600 1250 782380350 782380363
    0x31a060103020309190c0308070b0f090328030b040f020403060b030106050102210c0616030e0c010f1b0c0e0906090a1a04061b030606020106060c08090f1f03020403060509060702 78
    0x4417089001105c9910074030018a000304055680074800a640340b0440c100a03001c0d0b0002c03140311080c94512000154840d0001c41502c0080001c40c485d592204030f400784c100c461090703600c4403c0800d551061000c00c82e82d00e0b8024031140105103000169240d0079424982e0903100100c0b5583d000c1ea042560401090340c0c0003480041090f003004840c141d50851103c20074151140900c0480c2c00d1240d4000d0207400344820000d682c000c19503480400208103a0100030340c580302e000001c24003040c0b4100c440c4401c94000c0580c3c81c0754149010000e01071403116543c92100032919041001906044020010390381130800c01980c1080c2c4c00310041141030116614100c1d00341e2070360440e10b000d01020010400300301040e00221428242070203941207040d14004020700408107031185400660030500001030081c01003111080040d040181d0301d1801d1504002e00402c12007000d241504802c0940170140c90800d09940b48004140a65000d0313600c900d5030401c40161030028020190315004401840662900000c18 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 782382850 1250 782381600 782381623
    0x40f1b031409120703170405010b0109051215071206030f0201091d04060c2d1404080705040b01020309180a05071b0f112107080c060f0903011104031a060103020309 72
    0x20a91381d640d2850104c90480e100c07500428044144401d0104114041d04207200c00356007a680d54003980d0f03941e020400040c10b09251551a07030000d850451200002c0c1c0c0f03030300ea4000a1400c1070440c041d0321406d903808840c455803043d1510000c2e6030444d41150f03841500c3c08000c181c000c0c02c03a800581e606454054074000508020402d5a0799440e04903010702500c4042c2d04a030490326000403034a6113130441454a24000e58100001302c11484192081010005403000d803085403009254081c10201071000a000c511101415132000744030342c41a43c0e640c4030b0300c21509420140d01c3c10241c20040400301c141c44000e0480e0041c049182d10603081040700203100115181c1024201140403030505041e0381c24901d880d8443d800c1240b82c00f959215030303034055103103090b500c02038112042c03281c2d03031000c250704c440300810304940c0300400300544007a28200102600e00840020000640800b05003c082e8140d48607502c00ca42c101505601e001c000c4050100c541e51002c02800e05524624092407410b8840c09252103 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 782384100 1250 782382850 782382883
    0x13051903121b0b07030b0f0102011808030903120c04030c0605070f0305090d0623100602032703031315210905070302090f160504060518040f1b031409 66
    0x1140b10103112802d1910b601504006810a00c0c10309042c0100035098400c001801440d458040038060751052050704d030410901f03450064226120703510741d022a800940145603500c01031150300400049100030b640a443e00c140582c6d5990700d103180070001d0b001e007a4414024010103102c1000420506429000756a6051820301e541c0e001c00400601481040d4001400349403801c2c400034a0080d00d42003814000654080005050703940301000c460520031030142d0401600300b4442d5400107001100e911404d80562141d90300741440d044082890758200825024030b240008030200401c42410f402450760b40d0040c41d013030480303101c41c0146140520399000c501003200d07665450340c0d05212052000c00041c580c01400c42d084c0c1d003090189030032540411381c2c00546042e11000482074941c00ba504880888880d52a0181814200c10715183d1034010800c0580d0030a072100e41041c0301d8200c2c1e108041c030321140e212920240c02413241004003103d07800340e41e034071203404c2401c2480450100014094074030503000c1c0 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 782385350 1250 782384100 782384117
    0x628021c05090316080309130b060f0c2a0a23100201020c070b09120303071202031b0a0207030501060503030406021c050f0304080706050a0216030f141305190312 71
    0xc2c0801e28014011800041c00d148001c00825103150100c010304184404a9108403002c950300c0444003290240200c56500c0002005800710500034000500750280281d01034030880300450165201559000203032080b0521030120035582032a10041c1880500003040300360400d44502c0ea0211600001d043c01a44642c10544c05000454800d4040741c5801030701c4400e8446480e56520440001d81003401501d1080d561034480aa0070480001600d02c150f08541e02c80a0384002115044020b5001808880905910307070000d100b600c41c0d050091850035469401011742e00d10b941411402c60340c070740e00154030031b410801080024590000343c182d0034110040c959084003e90140a684a10544090142258010040205000ca03440140400c4d6020b0101440385948400c01752003203201d03840c10b1840c020311424075900820f1207190001d0111696040c04001d6401040c40450590090884107580c407100040030701c180c1c20b180d50801251584100c0c1a0344d00713415036441038500c1c020400b0800c04c000420703 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 782386600 1250 782385350 782385367
    0xa0f0c03020c010c0507081f0b0f030714040204030f11210c06131e080609070b071e020402160c08030403051f1e0c020c0d0b13110628021c05 62
    0x10300115004000e0a401c8804401e0b00c0c0403203024208042201400c02352030310480300e581b42888501c04000381b10040c00703451042e04010005102032941d1360007070b402950038000800000c541000c03000506004496032464000300e4030800415903a00c10748001c0b180c080c001507120303851000410030f00004044480c01d4070f8044450820b245d40c501c81e07106c0c110451103080c140c1e1908041d84540003ea91541e01030728042c2e61454240b540c2da0445101d88a102c900030040900400c0300038010500300180e070415400724194540004080e0303086046035030401413080c12281c042040c40e42c4000300810420000c1e500307107855510f030301e5200c110f0014001c5666206040c07140d0641c1e196404400c925440460428410f40800c0000d00200b02e40c05540300540318812014408ac601140c00c01000356100c0ca0b902a41d540348103505458815681c03040321000d034500c00c1e007595035a440c0090507807180c0c0300c2e0401c0f1700c59111000401044100c0072403401075400c10740d910449070100700a180721543c9141410ba03591007a2 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 782387850 1250 782386600 782386603
    0xd06020706140601020d17041101120f050a0b150a030e1f05070e04092607082106090705030f04020f0402030a0e072c0a0b1003020a0f0c03020c010c05 66
    0xa1400040c6114505404000c10310038140142c1e005100c02c1e4201c51206140c41c0058501d4a103403408108045000000207000800101640004c10310624100c8408800c24006a050381d07220000c00e66030f141c40e0410820080300a2246003200f0750111561595000e6510150752540305071075080d02010346904151101200802c034584070109004040d2401c03c085949000040505860400000314408020300c26483c0c64040c0620a41c1c102060070701045015400c4207110078440b0342e80490312070901c0120086510000a0322a00001442414000c61300b680540f0389081c004240d50311440c9001e0500c007250b540082900d6018890a00b240d001d62500d0001500f4201c00084066003e8000410060092000d41060100451000490315801d1302c5e2000001d400601d200c259000303104e860940c2094600d80c94289070803d004440008252202901194212410407500340200e500018541c0c42c21f948144440302d85281450b203e503140e07545581c000d480b0448041d00c90b0411480600d030405100c2e0 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 782389100 1250 782387850 782387857
    0x1e050f090c160f03030b0108061c0c0b0a02010b030c09310803180c1c0b060d02030304060f080a0603020a060503090f06010602010e060603071406030403021002040f03022d0d0602 78
    0x382080d151100c2d062502d4442c0300110002d1040740007a003030070051001c2e135018200d898041e000003010308034000d13034103407007081c1140902c40c09880c902c209202c0081c540b20010001d0644101550010420320004001c1c90700d000d10000da12402200c20204004500b008450748090348003030740c1c020001d4034403102410004480218006003051900209200b19488010a41d0202c168000103490105c0e05240800c4202d000d20b081a8030784182c0914103034005440d07241d040c0e43c4220000c056002c5c03c0c10b280c0100f07203140c10540100010035600c4c150010059044110180d00c40d0180d00b00b0f200842c21a03000c6194250039109400c10b0060100c0400d100078000e01242c40c0521105d02141e4580da91000300a02800fa051807504da1070080802107890ba0401044e84c1e810b981d122480300480c44026800c0c843ca540c00100b05500b107000e1010550780c01030035800240024096070840941c05c60071801001100d4042c0006a0034101c00d60140b80402d604c2d80c0d10030710300080d044407100e0290085040c400007910 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 782390350 1250 782389100 782389117
    0x602120a140f0d0f0e0616020f06181b0312090f0409050601230a1a120103030e010306080c030a03030b21100e07080c100c0501020c06011e050f090c 65
    0x403030100b04450704482d070780b014080308041000d06004180344241100d048a4160386400c480b07401100015003155103421001440b5104d44c4100c49075584104011401d100066031040200d0070100c00310124050100310745212030100000440c0c1841601c0000303550754000c0d14000f1001100030170741089a0313849110aa50551020f072090064162610b440c0d9205e1400740103040c03d4181814014450201e1300354008050700003d085213140e40e05142d404074600581004490b80e0242c10091aa9644160b0707200c14002c0d44a9110310718440e851800240a40d44203420055881d44502440c4156940c000f80000700c50f41c042c2030005580c4c8640f004159143c001400c0c4e956080148241c22005180004460705000701d1507500308001140e04c8041519400144182d10550f40080c01c00c400b1480c01008168045200b402c1005182c1850350300c072800d80e0018944024103400c482e004002680000440743c048440140d865001a07082030001080410712103800c5006001c0361000a480c2c82c110403c540081 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 782391600 1250 782390350 782390387
    0x4030e0909150c0405010507080310050310060e0f0403051806130b1206091003060b210f0c031606120f020708180901060f0c06060f0807031b0602120a 66
    0x500c0c2604905540784104107503102c0c101254000903408030744440c00d03107050b6041650740307518284882d00d42c3c48440d00082d0608841017842180010240d404200c0d070103c9000c030300000b2a000e07181421040c11072034020040d03028111b0100c20480003a92000440f0014a05801040d68550680c804240d0030301900c0c5000c500254111300126061041101800011028281c0d20901c0c0d82d070b110600045001c281d13400304049001042c284001100d0b50410410b540014100254503001c10704134003850440001c0039007050b081424031464009041c485c822054a0590042c281854502c03501000e1504071311410041054a44000c440c0b03d103590400200410010400d40d120465400c1583d450b9110483c07072540c0c1d030000350500c1410309001000300c1c100c401c16103800c03e010310500000c0d21f855840c940e00700c448954551003c43d001c640c0258580260179540d00812000341036186c0360105e200030f4101d0710151461030741c080152075400200b0785d0310110002d55403038a030358a05900351400f41050381043e005 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 782392850 1250 782391600 782391619
    0xc030309080a020f101503022b0606030311010e06010909050c09070e10030c080a0c0e030f0d020f0a050606060f040e070c03090509090a0314090619091502060103020904030e 76
    0x500743e00040004080040009885103400c3c104c00c00411640605003211200302c1c1c500040001d0314010981c5a41002188200c0303140030a20881e000350040b07a031000b00c4075640c0d00c1205005066000e608000ca01107540c0080200c6031819406903505c460500c160885151074240e1003040203420b00564401080142c0142801e0400d02005440c1c240003590b0680140f0040d8100d403401846405031294020071615109030946404076400080c0448d51305210903c003442113004400d440400800f02e40310614005041034100c00040241065004900c00b09a40c0c041d001400100700b0110356590403060884001c0c1d07075802c42440c0815036010b164085c4494815100402080ca83c10000907030405200b0f07075403005516100c02c10040003041c1030710005c5441d0700c000a2800040d008261003416804908803807420060140d0000b805603103c8010b085030742000f40001041f16820030784a201401c2e4006c8190702540b8802c000035610710052001034800e0350003002013024507028502200071103201501852a = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 782394100 1250 782392850 782392867
    0x81306050601090e0c1206010906080a020f0708120a050c25110604080105041523040c090903051b0708030a0302160b151e100309050304091811100806010c03030908 72
    0x1140c02842d40540807560032800147c180d03109400d0345040e50000d4031044910b45032605880c0003500700b1381d012101c00f5020018240421480409000e859001c03116000e0a80740c40304101041d0741d4040c0c0754035108401400401ca40004800e0921100d500d10b09040490022a0810010f120001e0f0082500207a00141c04981c088064010f1403003039000303c902080d2003c10b00d07042c008880002d040c40b005400c146140c00012010a01c4083d0010302035404243c000751202c0b6004211412600c048010500014403070a82014240c410b84002d02c00b80301a0003207902c1e2044060300c3388241126002010343c0081c88600c44607041d14945541798008c3c1e64469945821841c042d0003400c0840390610616102290320003500100188880341140a8913401c00c5502500c02030b000341038802821502070009120202c0e56000302e11030407402140700206020500e01c5410600300080e03820341882d024510409841d10051b810002c85a00310500703103083d00c1c2e0868103007001c800404030179134004e018040014034620f = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 782395350 1250 782394100 782394121
    0x1a09030c19090b060909270102130f050d020108040305070602040f031202010b030106150f02070312020307170405030c0111100c0f020c011b0209071107030819081306050601090e 78
    0x81d0b4826101c10045408414100306007401541d0400385c0c0304400c0030024298112094440c081e1404040c4080703a0684404c040c1030a80e0441403c9288040260504100d81101d445c0e0060007800b060b15560403078074031900020f054205c000d0014040c03050000d10320b420004942e04880050400e9482c4410107a01ca103000503250484500400040d1300b00070b05205a450180f00e1413007128030004400031248403d520540703121160059444c254052103400001061294090460f1000107901941e601c040f58941000c080d0308940d10902101c0052209200c0c42d1000509165085802d080c90400704040301c04144c038100044000202441c10941c4c0451403030703000b02420b03c03c2c245035020f40b9600134000c0700445401100f40c03405d6072504000c108480c0541009000d007504100e00f40303040188112261125480e2000c60307401150f520000050b4401c0110b0410181d0b206094546000c400a04001c0d40c0c034403040452a401800e07031990b42010440a038000c0e910000104955151400185425000b21 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 782396600 1250 782395350 782395399
    0x70b0c0102130b031302040e120d05040c080303090c09040f1202010605120c0a15050405031c0201050f0105091f0f090609060512060c070f0c0306020c0f03041a09030c 73
    0x926282442080800c1620060084d644500d00085280c0114210350302080081c004010048801c0e0144c1161400c4422442004161214403e4800306a9041c036180051000a103580001c0040d001070040c44028a00419110460f09040b01c612403983c507281000042c0c0c068240780200141c3d41d0120f115500c3c0d806400110403a01c1c2180d848070b22030b200546458842012101c107039400f0850040900c103095422484540c0a00140f1b012414030707498101103403800011030722000e03500303220000280030140e09000d500d5000552281e00c19480d403600300407400c80c00c4082c2c1401c0050400d00d500100340824000450020402e0f018506000e0780d542c0180700c01800c190052207201800c201000c9014144040f00d1500105804000c14280d80c0e1401c005d80b00d500201011285100103c10940108640340200d40c003950281e41d00580d0307420362010440c50115490003c0c101900305110030405d5484a010a00202d07210406095907a24988000b07401c10340a07a03484d541c0100c921400e48501c00305d90300c00 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 782397850 1250 782396600 782396617
    0x71e0e030f0c01050913020903010203010b190f0806010c0609060515030106080313030201051c050103150506150301050d1506060e030f070f0b0a120504051606050c060c0903070b0c0102 81
    0x540341910741c0c1500094880b04500400340c0032440400c91200d044c1018003640120841c05c0c4d0380142010f851100080c00d9a1003a440074489190210304104095402c1c2c07012105084103003031501d01903050b5000540300380d800400103814010400c07512000d00100d0342100004540c0b10104103c41d00d4150800301100307441000140c002c0d0300c1c01c000031940440000445d4003c0059454248041345150300442d0283d1041000704584007444290501c40340e82ca0140b01e0280d4401c002c141001c15028080a044400080920b481104100b141441440000c02141d054800c2a41c5041c2c04c0030706400c042c01140b80700ca07000e03500d443c540040014003540c044001ca00b049011415620480e02c5100342641e9841039004501001d04a0318041001a040704000e00100082d824112192080c4009442c00c842d0221002d460030b030449200c02240101c064250360182426040007802c1403ca00b030001d41d220001071075500c00040028045100d680d0800c41304000b0803c00000700c1d5600f00090305c1d176002c0c1d0031032400d = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 782399100 1250 782397850 782397853
    0x110d06051e0c12070909020a0e180712020a022d1c09060e0103110a12110a142505011a040902030d081b07060204030b07020f1005071e0e03 61
    0x1010405a20049040c09020030212240c101030070340701c0c04000820f000c1d10101c14001c1104000401a20343e0000d01085413180d151820f000c11030f82e050000c041c2d482050846143c81020401c030031590000350740703200e018120b900103855070b28200c0182e20b0200c103150300340000409403496a003010501c0d140f0548460904064031190503c04c84a00c2e84041d80c54a04c101040241d2001e02403a440b41401030400b1105142c0402c10b50300c00300d8070a407143d1051402c80300103540c07146a100c00c200e80c1d000b06a9030b441e142e241c0900e07142880c00c00809032500c50a4001c801c110000d6808403c0b01082e400f1001d440901880344520f01c8145043e43c0206046e540d00b41c2c401c83e41d401100c0891810348501c0010580103806808141d20b0044125440c0200a100c3e650307082c0440403d00d64402c0c1d5102525030f05208940060792a0309600b00b840000800408841c110b42c001420781510f2070000c00c8071070291509807008680d42c6c440c1d8a00781c1d41d01c0c08808500584000382c2011100443d071100d01044100f80c16030 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 782400350 1250 782399100 782399131
    0xb04051005090102060f1b0418060503030f07020d0c0e0106080906070e0607020103051e0703091e1e03120207080403140c240403020a030b2e12110d0605 67
    0x10303050300d81e80509052140984c000c04001040c81e1001c5501070750044800ca0401c814042c1c0410180f0b06403c00e0308910041114450442e0829030f05100345005403500324021400d1603e4640441c00e07034860581c00901541814001204200c100d0513450042c01c812002c104082d82c40d804028440079048806c42c009110311000b1541042c050b081003030f1580400f0340800e10b0724039250015405083e02800c04460400e481044007101904240d0303507030295000c4e540111311300465041115240d03088a000c42002e4507816080340001c0c262081c00032641044104c45040d210080c10281e8a00b0f504905c1c0710445800090703a030040169460041054a2141c0b64045c10700030344c0103502e80d13035a011200b40d0790000340164100600340880200130710101091140e05152503207960200c1c0100c1c14581c0201c0e0000c0d440340900c0340b004010091808400d441c078009820b12250b102d540d0701d9400f40c0703100b1003404880c03015104043c4000303c600ca4007010009452401907484928124004141c211481010f06e860350 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 782401600 1250 782400350 782400379
    0x1501090b0a050901030522120f08012102010c060204030606151d060903011e020c15101503091a04050d0212250f050c0a1208120a150b0405 61
    0x21007510600c800c166520b5082c03441e5400150024a00070300120301c0c1c2d000e82400300141280940021040c203104501004509502c01ca0141c41209481c80328000d014040e8014041c2920300d03c03040e89124070418804202c0ca10034001626030401d1004003070031107030001602000707204407608058101c89070b11481845400c1440b00c201e03658a04e0140070180f1074850300d40380c00c1d42d25198005e01013401006000040d10b0040e080381450007805100741035413481c1c0101e407080708e4603018030414880c00272480e10801c00b8581303441045119526801032024480a4100c3c5029003840b039442000c5c800e0344180e11440c40e1081040314400442c0460303048540744038504c441c0c8503452000c81c0320310f2190b811a681300d0a11000720303030401c4841c0703620280d050519080744614012038400415043e00a0054000d01411a0340c07100780031852207581c00c18045059122070010010311410111041500d030000c40348455292211000c0140850b80c240c20040080036901041c2440b11000400446404840421200091 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 782402850 1250 782401600 782401619
    0xc0c0a0605090117180a0615090c230f2106030318041d1e0601120f03050a020a051f0b04050c04030825030e2107090f1103150109 57
    0x71102d40c1d6001418100c4204510300d0541d0324103802440001c01001541d12020901c0c1c60704c54004003c0e10b078980c60791017484141030b606001201030080a5002e00050420550190036010030344a05030240840c0b034908515035140c0001d4070b80d1412144d08044c3d0700c100c0c00c24a07485000100364065403444290700800c140b842c3c00021101d0b4600e0702c943c82031000c07000808100040c91081d2010812010610550110350300034015251403010000036000780108814405e80b80c080141c0044030040c04110428000c01d258000d40c009440d41841e00e241d0762907920604a09000022000400600c034480a10000794043c171440c880088003c0000c000002d06202003005403041550f0710f16a442081100744049088030000382030000c6941c10244a000c2e246486016186940e003094000400e030a8007114240740810700c1c44141c1344120b101c0c0e54800303030b0014015207800480c4210044c10356103201d002480c50741034003e140d1103051103001c50b44030700d0b0810004042102e8001e010340010208140032404408 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 782404100 1250 782402850 782402857
    0xc131715090c04020d090605130b0a1404020907170420030a080703110a0c09050a050901090507140f041e110c03040501050f0405060706091209061b02010c080c0c0a0605 74
    0x1000003400b2415a14060000030b41c010110700d08078035112003582000c40c065009071400f6040803800baa1000e112814690140080505a080e601c0e08010214010701c580c00809900240c04980314429900c50100a6034180c0b529181c0501c0002c2031403c020078004003d0b04290001001e10600d4055002e0104050701c1d000c1a580080400f0800c1c809180460f124003400d8069032041c0c0222024002542c880303100c0038203168004211203403903030b04000002d06c480c0216900545044001c0c006c0000981c2e85546405950066104103c1c104d61003202568440310005a101c0002d04204404c4a03a9110583c8007908000117010150400800030800b4511804603030740c00ca028406541424241801118107622480c1c03030184086082c000415140c2e41c901c01030a00a100b00000104c1280c2881e1030078008846444001c18410b01d45000c1010075003003034041c0054001030041d060340e0b145910050b01c0000c0030034005441d007400801c1a4825000000d40c055403990f08a816042c080d90b140700861f2140f2 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 782405350 1250 782404100 782404111
    0xb070f0f0c030527060304050d020c0406030305030a052208030f1609061101060b04240503150105070510090c0806010e01140904030c06231305030702090c131715 71
    0xc40410010350100c4165074280c8608030081311440c0c4001c4501e00059198006032800e0300c2c4c42d0403a164500c001a01000640812801a94107001d028619103024010340001024070750040d8485d00000c0103801888102d07031003284804981c603111103247c10400f0442d00110b035964030b4501118040740002040b10445404910303143c0e50140160b040c280c0c102c640311003e03000700016640307680300860040004c0700500050102c00c000260303943c864180003565605904240002c0c00010030900814034140d40000c07010f10028200075641c0d100502e00a894202d030402d88003800392501144104000d50f40f201003003244e802e6400c4034066600c80d80c0d0f03ca0212070a02c21102c10141000c041c4140342003d041183d4028041d0619900c450920784038141550002c10001d061003401c0600e21000d00041d040342c41c1c01c109586414580042181d43d003607607070305c11101c01910a1600b0000258041d6000c0c0890304012094015800441e036125a0b209942d04207000c400c1181c0104c0000071510703418400414881c0 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 782406600 1250 782405350 782405357
    0x50c010e032b11070f050a1e030305240d05030f070b011a0a0c2d0308062107090902150403060c141315050d1505011e080402040b0d0b070f0f0c03 64
    0x34405503184907420b01c2c01901211b0301d006100305036001c101c00d00d03800c80310310700a1242c61040101d02c1c0340050071504000d02c0c00200c03c034903424210112088100108400009641e09190800a418800c0c80c0d405400f0b0034550640d00082e28030204100c1d01d01903412a9482001c4011440da440760185503030190a20107000651003c81ca003021514002030340c403041113001042509481c0002005c040c0c18035070304d070613008110700c0c3d014086103042c0040c01102c04490001500c825544050300c003520307402c3d680b00f1107000c0c0c4d403203154541c15075039084841c428010140c0c804594943e500d1500c40040c0801141440109401c1482c445411002c01c00300c61040d0403070702500301000d08240c07803845c00481c0c40000108000c818019060b10103201d1155110040d259081003219500e0580010a0200c0c0301c4603100d681d10701d401d8000000c40e00007240700c0e04a50704030f80100e90050400c010994080d00d11401074503000211041c0400540c100001c0c64045003296078030101410441400d035504956080010f001 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 782407850 1250 782406600 782406607
    0x90a0501051b220504090506150102030408120d0e03120402040c0804050309040c030e07030b060f0402040605040b070201050d0f0203040303110301080a0b0a021b07092307050c010e032b11 82
    0x1500307039407000f03454041d85800c0300104698803600403a08a410114048849501040034001e030881c2d02011003040b40c80c240b000b18545400c0810301515001035840c0c02c91204030114030745d6151202d40d00460024040b800403242c0320444801084807a41d0169400c1c0e000c0d40c60100400902d900c48c1a0841c85603400000031807800081c0001d11005060a419203420155901040800301e0070078810380c00254002c486082060510404100300250410341061065204002c100081c50b0481d06481c00c4814201009441d03105c6400166014415180814132640c43e24001c2c0b0030110075980614040c5010703550400c500200c20b900988684000c0c0980b1440f1340c005007c44000032445140141d1080f8070280250526648212241080841c0c02c00c010b0306400c00c03a42440032000320700c618010300c0b00a02aa00c0001e4255a05030480807002c0c0c407042c1041000560119109003d40261b540000d100007220382e9008940301c0d1a29038100000702e0180b0994010402d1083c40b154001c0710003c86003869480d24 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 782409100 1250 782407850 782407867
    0xf061303081914041a0702010917010b040b060a08130804050a090204140121020d090c0801020a020f15060f010201090507140f0901050306070513080f0d091d012606090a0501051b 78
    0x805030800346c002c80c104003a0303840111710200d2958840f101c600c61000042440d07840303c004c02c0192811201e00a02554042c004041001e910003016608440c941000d0035040480b410501c0d9039128507005250800c5075a0303000240000e1a034000c0003201c0400c4100c15001090600460740c3c986001031503005402e507418148140b040550041c20b51030216900003805c044a603590f400402199400000790340d501184411070140c051020200307000505014014010041050491100700a003d00c2c0c011801c100d20b61810781d000754042900316400400711401f40e580d88400003030f090b600310b02950041d24560032012042c03c051103080d0503510014040c0c26190341e1420221817640000003c0740c000300410b6030000d070700c2d10305224200400c0c42200203840c040242402c05030005002d58052680c921000750101807008a403205a41515950220072038542e601b031503501a41421501540c4403405500c00b48000384d1000a10140307014031a200900255541c201c4601c7c10021004040c141c2d00010003d080 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 782410350 1250 782409100 782409149
    0xf041e0905030d2f16021908160e150105090607060c0f0f0909050c12130201090f031214041a07021002060f01030f031211090a140f06130308191404 65
    0x301d505402907021000041a80021f00114100000700e500020041c1d014010124107105400d40e00e040c0460026115282524084468100601c0f1800074020fa0184e944160301c1082207030440c00b802886a81c07a01410b08004000b030041c5048400800c0a1030100b13120305010700700ca64090380e03403604c642064034a00085100904801031400300d00303040402c032101e4001103440c03046000d000000300030752283e1030700d20000d841c2902c01d4200e0030020071206420000103440c00801d0980c0d000344e1501c2040d91400a9038911940070b180c1003962403030307401d2840030b181c840e1703440150008600032103540180c4608590180d0300c903c0e090b24002850100a0014001301c0e5040144256441c07182c5051400300741c000c0c022104840c0b0b03801e040d01d026640051b51100919280e24044058101308400d21a9941400c001a140080c0c5528040c06840049200854000d0702c4480b0401150884031840d41d41c0400080c01508000304c402007004240142880078202d00c05400344c40c280c41c510514a01500444055007 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 782411600 1250 782410350 782410357
    0xf140c0c210d08090708030f13050301061802090d05100f0b0907020706080403140307090303021507051c020c0708012c060406022809080c010e0f041e0905030d2f 71
    0x21340300d40f08088000801440800050411424844c0021384032851614641d0340c40d90380d03902c100e210383c1c141003052050301e0800300020981c1441250042e96020068040b0310400e0704008040d015004960f01507c0640490300711070550f04c1e507250104000031040b81000340e00c138000d880e1580182e204103010b00466000b06922504031303019040c203506000e0a880e91841a42c011144400020386070601001010b030100900c482d13003444403c1116036840d210f00d00910600070048080c2ea05040b810540b1051040d9a0482d1070300c0100c0000d403130382c5949030303010107018000c02120380041492004681075255000c1003000c0e280415400a418507840300e440b4913000e0740003000d4045e0b0807260a05003203110700022240101c508803507260100b41610b0a0001070130140c04c1a4114184691000180681d40e070300300100c172141108807000998071007600038500a01c9a0a80044203482c64030100b802445000400f519210190110600400e864006010090030039002c028028a03a0102098102e60401018 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 782412850 1250 782411600 782411611
    0x2d03071e05041a151b1608240c07060f0c080c0c060402040921210b03100c02010207080a08160905061207020f100519050c0a0f140c0c210d08 62
    0x40905010803609010308840c010310704c003680b580c000c5401e1584242d904080a00400e26003002d84481c40000b5400e050710f0400b555904548c0c496a000102070118480603110001d030449006c020141446010000409003803425101107414440007404030076040044030020410040a011180c032207500f804040c3c0007404040b2014000049070218080c401d04c0046d11180690780e40060b00080040a140c0110000c203060800500b80035407210307a9103001440c0d030010000003030005810b1410781012402030003000401090160001070b507061081d071101000307015520b1040c080100040e0508281c0b0f48427414419281c1004092101e20a220004009550721161a006542480c0191701249040600000c40304201d165100240301d10314510400c050b01d0007038010310400190404454071202405810f4542040040d0b41c031b50501400d00c07600c3c2c9014882014040d154a403852800300c180c5500c0c0050b0050302561003141c3e042c0580244c54040b03e1517000081c05000e011601c3e050803210755038010823 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 782414100 1250 782412850 782412889
    0xf060f181504020703050a030e060105030a1b0e0702030a020106050f0d08070c0e07030c03060905060f100509060a030f0e0c060f07020406050904080a0f020c2d03071e05041a 76
    0x2001075034031140020101c03107202e580c0c1c1c10341e100030303400001e400c9912003601c90b10594040e60041c003450b01c0c00034448001c0380d00b015031689690400300c1b2240e07040c5081d40003003414980c203000740040540c002010f40030100c0c29400a0011075104c2040c0810070030322a0080e0b900480380542c070008140b43c10000c00526000d055011342c4141c480709001c00381002a10b0400010790741d0b8820700c5400e58144201d0001c3c0410303140074405c606240001401b540d4031449154458001d801072800c00c0741c001c8085400400000d0406c41e200e02c5081001380041001400c810303212424002802691440400c1e8402500742c003c1620b400e01d00100e00b80406900145030072604107070754140100d0f4540d034815405200e40e1061005a5580c0c9100030010b0221014104020541d807001401c18a0340c2e4400d000315040f03001c100f0442e07000440e09405030b03a050020b80180340d00740c06100808540c071681c8000445451440a502e001ca13203a86809100881b00c20a045d0889101c0ba84820246403410420a000c1310b5001607 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 782415350 1250 782414100 782414131
    0x180303090a081018050d08100e01030b0a060605090a150309080409020d0c0906080712062105210d110f030c09090105010c02030c040b0102070f0b030f060f18 69
    0x40c04240c9140c429048845554016550b40007021118040e070012021084030303580804900b6550b090b43c0b00c41100c560002d01005000103680103500001c2200101000f814415955a60b07040401c03040301c0030380b074520325541400c01c00b0036114040c40444100080181c9210200c42c9082554454480c07100c41d00020591500c803078001140108001c2c1000e40015800140e5414100341404201c0d103035401035000380310b4641d800300070054000c00056480785c0103003007a120003c1074007180001400250409201d25405550b5030000d801c0308500c0c2102c0c64820400c0740d2200052042581c0c5007072650318442d1030b1010400c00c0c0182c0c0c03e080c0d00105500c1c007800b040b460030085101c142e000c06800850b500d012201000c552120b46160680c0120700401c401e0924521200c81600460b481e0450702c95014042ca444039100c054592007008a0320050210240d5002c1407a2130f41300c0411290300c1503480800321810580450443e180c04102c150071514010314010305a41e0b240007102c28510010205441d042058 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 782416600 1250 782415350 782415367
    0x2802010c140706091d010312080c0f07030305070e01021207021912050a051203060a0905060d02120106140a0e1b0f0706140a150b070501020c01020c0c03120f180303 72
    0x2c12004001e4a441d4450149150400f542000e46429000081340001145001040890455820300183d0760803071914802964603c0540e20482c401c0c000c3d40f18803a040040c1d80002c0c141d1582c402405107105941d00b045402c111001280d484003146407083c0008020007080c40145052656030407a1034038048042242595007a09482801c0c02d680180c1d620342005c15034908015082c0300010600c11285450b42c214182040800c03403034401400b641d1881960307880810b20665517100c031079290550082c80c218402c880100d120780604080e00c10a08005002807145070245000e080305130946500040042180e83c41031004030744545480d08106c0300440c100407140c2000c17194002000c000b40505804200130061070545080708200030204d0355000d240800103034101d9041c2610b141141c031203d681c03503260401402c04600a1040c2c1811010035031000441081400d80424400c0d0881812001d0710901208003000b0040342c0700c1c011103005416010000310446c0c10107000300e17505807030002c0c08990802944 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 782417850 1250 782416600 782416603
    0xf090506040e3c061e0f09030a0e1c03030b0406080f030304020d14160303080903031b0a090f030f030807051c150305060703140a090f0602220609082802010c14 70
    0x58800070803038468039042c405017001500300981c201c60342000d105078610304980c3c2c440d1240103002107081046210321010005039a0b24003002d00401002503500f4100350a894090b004105c4165801c3c01a41030070700018000002151030703454128800b005d1840c2d99566802c008981c0d9040e54101d42e501d03007004c002c2020500400200c625411002d080258003070641c200a410248020704005040c0d10800400c5021152441700700c9c0c0305902d440340309865002244c800c0d0760100154000d0a40034541140000510001807082c1a8880c080e45813002c1a0720344400c04c44861003415208500f00003c10302c00c1b00494600d620005a003400985a004861344036a00d96051010650744540080e817140740c092017000395490380741d400402c0d02d4000c000c0400c05a0360002c1c0c203104102e01a00c3d5070fa011a010300c800ea0044a9000f0b44a60021805c45031034882002400f20202c0340500000c03481040e84224075941e0981c0300c00c112031311240031404010601d0340119030342c4120100071500040b1200f00321515400 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 782419100 1250 782417850 782417863
    0x90602120403110105061509010c03020319050904150f1401020a0b0a0509250918050715020c0402040e06211b030f01020a0806010809070f090506040e3c 67
    0x481c0c1d60f4800a14081041c540c02d4901c017070401c910402c20064954103418200003126103500007070a01e80c3c0106100d0030140d00b103005010100e0340c1100d181c5101a0595031050041c4501c081c2102c08014407900024095020402801001c1c801c1411040038044000d244d20f40d182c00c3d03081441255a440815a14000e12a0054a49420700c0e51034000b8005a0390091150780500b075989c0301c54045000400300142d00e00c0f5001d02c05d000105a6400381070100d5209001007001030342d0803004036509599102982454640c40324441d0340140a64a0b150006103414022a400c031792510340300d41c1c20390312030340100f2103880081d10000c5085c4500c900c007004d213100d047c40001a4114524295500c8803201c00c03d060400c1104088100c00c1e074410040001026040348629030032070b07000c3c6040c1703c441d501e20303254503d04210342d00071252a094003840007a0110150304221f01c01c03801500d050001d00c405d8250720781d89c1c5841081185084640c0c0b410140d80392a504072108a000162460f2400444048130701402c1c0f06 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 782420350 1250 782419100 782419103
    0xf05010e01110306040509060f0c160c030302030c0609030f1801020321060a170307030809031c0b01141602010509060d02031305061807141503071d04060e0a0906021204 74
    0xc808000c01c82030346054402e0b00e501c621a00f01a003889d00d4640e50450700c2500c0105000360b02d0201180d1600e0450100c00c0007521280d0000006000c141c803810065030340d812040301380c200c070700c5060002041c501300402640c3e000742c0d0790300825040c11030310b041d80d0445039082c0010f40d046120038460306c045c0c42c000e807100c2c1d03400d204a940d0645450074600b05100141400760000c8444050a10b20084950000811505415050320305400e20391030310802c503800c5106100507240f108024890b040c0079110707958483c0840d180700741c0316021008464030400c90203016007071411400011501c44040503500900050040c4280244034a240080c0000da240c100d800c25628076183d00c4041005500700141000034507080b581e074003004240d40c010902250340d500c00c035015000c054a08844510703041d48801481e400444090b8901c20f032645004440103050000300044480580894031018410781841c1c03144106480b1960119000380e0f0340c0352a1600906081c0360b044800036400c020052070422840259030065 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 782421600 1250 782420350 782420381
    0x6031819171e22051914040902030d021c1707030b040609020c030909011a030a180b070c02090a050c0a03050411031c09080c0a050906040905070b0c1c0203070f05010e01 74
    0x1203000c0301c0409043d100c0d005280200f40044034090360801c80c9017020101d80108816800b40e06806004c14081c11450f10029094030840520380b807115000308285501400c1c5950b04801400101c81c1142d01d003400c0c65010f4441000752001c03442c40ca00c46d0304941380f16130010380003040c02e40d03485526100300d03801b01c0440c03403c3e5000859203092900d4604c10329401000f41c2010107900d4100100325960601c8050700107134160743da0f090b50915a00000185e9596582c0140400070760340343c2441c0182295405200480c800c06032400051405003a42c400c0c00c1c01150060041800c0c0490488160010b120140043e600c40e0200c800f900306a64003000f4244118035076200f030174401c00414002074544c007001c3d000f015040c0c00c070002040301ca8481c82c02100440d002151046c04e103071203c00101c0e00034000000068014081c88101064550f0741e0002048440c010a00315240e21305520a52040c481c040005403005030400c0114402007196119401829409500005640c0d061008a5400c450341007031140c1d40c5 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 782422850 1250 782421600 782421637
    0x705070302072306031509190c0f020304170a0804030c060909060308030c032508180303040507050f19120201140306240906031819171e 60
    0x10036a050040c0c00040c40c90100030356070f081d051255103034018100760649000300380100000b60040c24484500e0682040a0401e98003400c0180c10700c0700001e408148071895a0402d003940d50203d00c5065408424503d95024500f49400c040400c0307040328400140c4400c030300c2230f001740e0800309000c0002040218403440202d41904d01c2c0810107861080c0c254002c00d03c03185000d1003000860b14080481e6408824000102d950340e942200c01c0c00b2400d0320079100058141c07152000c0000603006140c19014030840d880d030302c2c0808030f00c0c250640da91004a5004040d5044007804020794103040e100c000c0c5170200104401c04081d4110b41214030082c055005d80d000010950080742956007040000c507450150744080b0703180d0310b010004603650f15142001e458003802003d0f42d03907010b01606000d89045450080c403441e0b6034207020136281d0402c100134442c0c0d11103008509a440092a510079443c04181d0300c040f1003010b00c1e0715040750720850b4009180180100c00348100341d03d40c049900b0014104203100c0e042d04c615 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 782424100 1250 782422850 782422853
    0x10302030c0105040b0703031518090c12110603090a0b0f0402090f160c140a06060e2d0709031a0403020f010506030c04110f1c050c043b070507 63
    0x6049820001c8a0500c0030400060050384100800c03a40910b405040c0400c0680203000d400065400c0e603444100c0186850081d0456400142c000c01c0e0b03568002c121003100a0340750343c454510b03000c6c2614020004452a51900c116050140c06941d1202001742620000c000c030307403600c0c001d03264100e4000050243c007004020440c5002003c4540020301c1003c86502c515101e44401c0114103010b004006200524100c102000213064103440b0f400b206c0019201c142d082d600c1d2150103080503004d003503001c841c001e000842c62166504088026194031249111441c14000c1d0070311080005408041000700c00c0001102080074040f42001403007885404281e28074240c2002824100b185600c404039034102800d011140c0e400090402010380c044600080c1d4600c100920b0f405441154441c0b412454007244145140d0446200e002d0300001c02d03401401255180300d07880c8014810703402071110024440391240c0d0040c2c8250301382103641e18074140da0b104100310f0740111030364810121209000590005460300 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 782425350 1250 782424100 782424103
    0x140c0a0801091a1905042f070804050112090614090c01030b010e10020a05010e010b03070603021309050402181602150f1b1b391e130501030203 63
    0x30300404000104110a9203800080a00e64450044080c0701c0c0340c0c120030448400d1900300c4c8640007042c000b0010081040708415822002c11018401d450300c0c46550810502580d0550403980355951041c00d0328030701800c2800546050070074803081090305907a1910200010b03058460310019000c1041b8444080c5005580c1515000021003503a04050501000c3d0031281d80080c003004081100310340d058400060b00070102d14180c18488080d142e5800c10a002070b0705103042d4420b07042c0301002e40545a0082e01e80c00107505a100c1c0224584403607070000d20401c81d80f2011750003260041d200400035650188890b0484203603580503901000d00d0440c0440511046404001556606aa40d12554030610b049001d0410f8144024401040c5141c0c103c003903c03040304100201c0c2d50000014469099281036180b241d650342610159040c07840312800322821400040c4130004403d03000d411019160403500c04140b0005140012409045d0100c644d80d18101b035880342c0c034500740d8580940c0002a50343c907500416 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 782426600 1250 782425350 782425367
    0x180605010506071101050306120712110109080613060b0301151e120b1e010609050103380109051c050c090103150b0a050603091c0f051c140c0a 63
    0x102e1040d80100b10748800528440c05914128009080c0703d40c480c2d403400d0202d598003507414880c1e807050241d210049034040c44a6010740000740112200315220010200541e20402c040c0160403581c3d01c1600000c2e4020180c0365084581807248002280d210004004a03081d00c0130500503404401800c907041c4030441117005c0c0740399800d852040d150000c0c0c1c9050b1181c0c068032150b0700054040010913000401d04000c6807150315160102c00c540a0340e66a643e14020451a00742c000c0300c0c000317400c001a80345400e48291108032350346406204a0502c0c9000030940e18180c02c444d41c0d150504c020303940300154580d80d000c003001940c540180d418030010b01500c0c0180c1004160f070f9040d44641e1035440140081040c603083c4a10340d8540c1c3c4800030320760180d6400540000429030000750301c03010010401200d07403400704009e164039042c0381945401820510041d07a109084a19000004034188001d1180c10090407003d00c8100d025040091030701025401211411400c680a0307034030150010741b140e0260b5016054 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 782427850 1250 782426600 782426609
    0x30720031b1509150301030b01080607020a0309060f0306090216050c06031e1504050112060e0c1f0302092e020307030c08070809090f2a030109051918060501 69
    0x451482003a1071001034190210070108210148003c12a16000d4903440000042000310031511500c070346e503d240c21440401e090040030558040c40020038002400040d502a0466041e00e40404850800300100d88681c0e1a05001c001c058580d5800035200381e10f0b1005010b811003140341c00e2030103401e508007949004894452907006030000c0041200c4401032181c0c2c0c1100c0441c00c21026170580300d5404100b00c4407100a15158000d00e01000007580c0300700000010714041c4034010600840010110054880c40c0500780e107a08140f49006071000c84120002e600180b0040713050050400c0500c00c003050032510130f03440f40240f28945075440500402c02c44a02982c01c80703148011407511103250350080a9400404005001c5140032841c0c40800600e078060b1800c0f500301502c0061903180c54202805220380c00e43e5080c6220030403690300501e03094216100303040010144006071950b46001d401030000e03c801401c0300300031030031801842a9402035020ba081c030510340d1400c0040740412401c1580840d10180d10 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 782429100 1250 782427850 782427883
    0x9020901151103041404051905010605030a060b1617210f1f14040b2710060c15090803040506010e0601081e070302040f0803041a0918060303072003 65
    0x401c205c82e00110b04c01204041054070041129201c0030b090604040e1030380f0100d04000d0407c800441c0c2c803507206019500c240b0507c0c40c14042c0d150348004034502c1e482421003595035004809585808103859040500d01800c85d48001454000690200000101c46900400562411106000c0a06007500c0c80f143c20075141c2c0350101000305444036074a1404418415111498500d028201881c1d61742c3d840019059000b074900003a00ca604400c080003500540c0714041c2c1023521101061131990a003013080d080e11500c0d11030b411040969140c0d02400424549080101a1070b11b0080000445960245020b11b101c1d02c01003085504040c0994454a4001d101a04101806040008000454085060700c200c0c40616011a448001044000c0d12030341e0040040c010090000051000002000f0f1007201c241d00c5e843c0d4012a1034503410700c958031920060b15800b041003000e65032810030181707149404c00d5008046a1802a40d0790750010308a0469081004400400c50041e12605050181c0c242c540000803 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 782430350 1250 782429100 782429107
    0x10c0302090d150f1a040f290d0804030305070c0603050402060301062f0307022b15020c120301080f060709150341061e010309020901151103 62
    0x50200d051207030b06a6000d000380d002c1106080c00c0f41080c0c1d004040007800079030f00380f10000d00300040c0c1201520001e4894003a038981202e03a00103400c148552041c500f69545c0620281004589100303545003401109130f07000300c0d0307428004002070880c0300410045120317454aa40350301640c00e00d1280c0c20019400101410308210400c07005941da581142d055940c00d0a0040b841c00f036200075020407001618000c03c0c050812018403400c2e00e0000050010325108941141c07800100ea14a9036180303e00d1207000891010800b0008001010b20004446da1141d454006003070607400700300949803a01e0aa206c2030880d00020040c00b002d5014096840000c560800424640c00c8c01c081c020030582c4a4492003c88904509038241101c3c030980180000a0345c0a501d105015000c0380e082015250301c0300080c040519412030116184c5240c00304511808005201c00c03106104500c0d245400c4c4225000b4a0403da81c400340b150042e510580064080c2ca802c2c13100000d00301c442c85010340140b440c240f42c50030651050 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 782431600 1250 782430350 782430367
    0x1509030d0f1b023004230d350901050a050705030a03050115020c0d0605180604050609010510030c03150902060c2a0d12110d03050a11040303080402150c0109050a0203010c0302 77
    0x119000c440700d82000f00301403c40c02c0c0032100c82d07407130300040c07140c0c041c400f9821001032014023a5500101c0781c0d50b1007603c09071200380d041080080341151011000c09001d2050310000e6001d00090310301c1405a09015182c01e090741d6489086920090604002c284d4074401808480405090084a0102c0d4001130110111201c000b400110a103440100995100d000248800b160340383e020a9002401046840c24241031802ca9100d210031680b000e0705600e03000000d00340624000d01d0b0300440c3e421480d01e00c0c07010704648a12000d040c002c501d60318455214030b01000182c0700d600082810ba04c1c1c92000d00b8184400e446c05400142d010180341000c2507001d03460030000e540300c01c3c0d1070039804d90200307460503030260202d02900d004898040202e500d0240344034104902c0d405400c540d1040c620000c042040b15409005c51000d4010b501001d0002040840050018200081e060b0a07c007100250301d030800011a1402d0f0a43e1035160040303899801030000c910440c10240102d2520310b10500381542414140d = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 782432850 1250 782431600 782431693
    0x804060c090501050d0908090d050a0212010507200c09090307020306010806071d040f020f03010603060f061224081f0624050d050a0e1509030d0f1b02 66
    0x801d904045d45039a560803443c20030104600b2aa000c41000d841358002c00e049040003600d4030075050003640206030420f0b560680c404184107203842011130340c407600e02c41021485060803000b8504130000c03640c41080000501507603011002841000703650000c543c2c48a0f103206050a10380c2c1a0700a42c501c0c0d1052003480350403600040c014a5640518089082e103008000002e00504141400303441542d10024000e00c0080c443d000644c180c072381d1614103005440e81c1d40b4501c92a16401c3c4a00c0001132114031000f0201c034400d400c08044805400d20380c5820010703007200343c0300665565002100a61250180007585000c00c01c0d40402144003140401480e4136040c503038440c5080204901150b00055040d2041550042054903e4640780090030030240c41c000c0d04800042c113004181220522400303020069046000f024548916040405181400f01e40444100030b032000e40103103221291644104180040c241041c0034141410ba8001c0006001c520180d50307102d0f034101c2e40e0144881c4240c8040e540901e0 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 782434100 1250 782432850 782432857
    0x23070f0b190306060f0c0f02151207021524120d030b0409151e06030f020a12020d030815030a0c090c0507110f1c11100f0206150a080d0804060c09050105 67
    0x5e00e400c0c45401e0529500e0809006074854030025440312142c00d020364400c2d480c001425903c50300c4c41c80340c0800e4540c0309060f61303030394907240e0118000c22200d0006800c005c440c8155103801e1000340c81d1107030f54010801c0050503040214140003a41d034041c2030f1412499906006098580c18169402c020129150f190005000c0c1140d04001d10203403a604191240c0c9490080c002081651000030001c0035201e1a00000c110442c5600740e00c600c0c4a03120125042c42d25101504941c2c1c0d00030484003010701560760030f640c4103000502c0c2d00704070030140e01d0b84810740c0c40034091405001d104552070302c280c5d03042c402d1544c211800704000504029007800f480001030350b101d80780e903c003540440310110780201420000302105180d0710a09060b0b41c9808840040160001c4945400c2d00d08843c40c2241d05126001102c00c581c80f5000c01c40140d100001182614000c4a400c000604020745102d81d030b42e488004080c44e1802001068000a060b01e081000740003251003141103400032072400c0c94100d032501000820303500 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 782435350 1250 782434100 782434127
    0x1020313062706020c0c09011403060a052e0510110613080406050309010b040c0315090b15030a0b03010212010812040608070e0301140108070e01080a23070f0b19030606 74
    0x950009070715607803942c10001580c9401b40180350445940e15442c16240f500301c507d0381c0030b00900c06c51011416040342c1d0300459105010304100f11012014400015201600c03240070030746032203040c02c4007007210b4440a0507a1520405a00c3d4920210544c6010b9458000c0c000c20028242203c51564000a91480100e0301165201d10b082610b03910f400280034010190484480d601c071749001c01c0f03105c9054046c0c0164002106006002c0303615075440c10043c1c00d4a850410540c0c0c4911038010b44107001107480e000e546c01001c1c0550001d000c66504012900320390201c00c02080007446513004014055080001087c03d0390701711000c0d4100b81c50024003820000c000340500e02441190a030300a03081d00c0942c082940c510480d05a4216941e44509184e140e1030580500c64030b24120100100f86042c0014461142c241e000381c0000000740d40341901148015814481885801408400105072580030300348070240c481903c0c001c0da90200c007140780d4451004010103c06060901030100200ea4001c840800c000 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 782436600 1250 782435350 782435363
    0x91306050d080717071406070207050f130906020301080606120a03050405010c03050903060f060406080c0f04050c070c0906060e0405040209060f041d0a1407140d02040e010203130627 80
    0x898071132a0404008031620b042d850403240c0400d2000520451400480300840d198080c6c0310983c0764048201e8550700325010759500170320030f007907010460308154001110158a8000002d1140c2255642c10241d034020b070303c01001640310781e003402080e1406c00c0741c2000c003602c0c02000f00426596954080c0c891f000d80c0c440c0b9410711000c408030005060060044031030b002401800d6400c0b0b40343c0501400d171400303419a1020b00a903c1e080c0086040310b800504c15081c400002c00340044000071204000c01b508004001c21103640051141c0e0000807040303940c800240c5524000070800ca410814001c104260070b0300e403035110300d041105000158544104041d002201500c41940010621010902410300c1c40104c084001c00454006072100b00824807502003880303180c620420710301d0b54807219500c0a0900a02001c03081315040d81c01c00c0e14011a40c080f8252002c0c00121740a82d111140e18220b0304115404a284241890180304000c4035204000c05e40490b0380c0003010142c60450203c0f1941c42810f40203009 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 782437850 1250 782436600 782436607
    0x10e090403230c0d0215090a080708131701060510053c04030506010305070b0f040e0702120d02091915030b0d060612060606051204120908070b091306050d08 69
    0x400506007160b03c0c400110b030845150b60300d48080259520b814500700450004c411020a0180d0000306421308001e8204021600303040d440c1d280e101a551200c00609042d03d0b0161000030380030240a0150004c14404000182e505e14020038080103e40155140c81001410400ca4001d50410701440040c91075441610301b5244644043d8503885d01d40040103e444800414000100007000800c141620b100750f080c1c4e03076019510007040c0018000d01c4d081c4000c400081c00f0070321110741c00302c40480c0d010b80c8600c100c940020f01c250141c01c5580c0030724180b2803103580002c4c036540a030409221b160074080d040c950700c40c0f019140080440c1c601c50344000b00320816403503000480c80c030b030b85100e0319008494100340200400340d036860080384d0941820404031502c504001c000215a0f0141058480c05154184060308030398440c3c1e14200080c81240c889014444252008117210500304503035006403040410340d03562280380c2020807e0303400024025801046c00c000003400191204003150313030110b60010a054a = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 782439100 1250 782437850 782437907
    0x90311010c02040f060303030e0f0a0b07120903050a030c0e1e010905090f04170307020a030f050706050c030a110304050a080705120d021b210a111b010e090403 70
    0x240c9198080002e54840c0c200001c0088001103940150200c91003a02c00f001403490a11059840c1c0218580c000c6480d00205000f10104102d210340310350009103031034070340740030000d80c008001201d860403001d03400204041039400c0c08540520815000301e2042c18806031940c02680001d00c40d40c6038501361701041c221401d070030005034003ea010b480a4140140049510320f0003280350410707100c0440301964100d0740c030100d503005d40c10343c8001c4034040c0c143c0d039002d0120450700c0d45050ba0f2059010183c030f820411708101c6003000c200644240f50240c514240090b03924184550800705403410f02280390f2251030b003001440001000090f80c0d40b111548003440346d84800d02820f0103802c1c80300150141c1c600c2e800c00120b0340710020541c0e0003003482604440d0031404964541000c03030740e9110a0080d6001c8000d12516111080da211005070803010554a0b02040800138681c056091009800101c1c007400c1800102035150340e00820341324021041541c400002e86025100100150300d41030a07040409401c3c1d180c01ca = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 782440350 1250 782439100 782439107
    0x6030c050d0204242a030c020d0b09060106180504090c050307090c090e090d080a0b04090b0f0703140c09040b180f0906072001060e1e070f09031101 65
    0xd00c1000c01030740440d10340b990791450301c40c40589a0460b091070803440c0c0800292038040c000d800342e020720341707012a5400d50406080c8000744286100c00e4060280c902c4546c001a5160b8120254003485800443c07011300384065100e18151043c0c20840601c151040401340f8104400c03107603401c4840444000c1401d000398203140824200715000f994060140020209902c0650b070804100610a66038804046035254201c940e00c070b00c151f41c1c40e08e40750468000c1580c440c1c8580d800c41c0d00421410400680e041c0500c0010f0115079403c4030454405045100b004072104407002c8099001d1006e08040c000059001e83c0001c10220042c0824920380c0c02240c130000a45982d8040d0004240150a103068030442c2e14025803044001c03200c0035941041c0c0000900704680105895000308280d4a594160341180201000010b002c5035000d03c0c40d641e0380c000000d058041c07218150150b01c407807005407a02c00c018012407901d10002010403003408010400075910540c040310031405c480c1c0201e044803454030740c4230048 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 782441600 1250 782440350 782440357
    0x90f0409080906130612091e02040b061812011b11070f32030d0309050109022701060e130f0e0a051c021203040f08120a14010501051306030c05 63
    0x80d0300414040b4400d41e5131010030300e0701415101d140d152680d020408640f00c60a440080900510000301d9032040d1403060306c8600c0f1844d04510081011852101034004100c598000c1d081c01c00408038030038061b04580c20301c042c2d50180030745144001e000712410302085161183c00780f001901046000c038031000b0344450501000c0068244441144001a40c0c2c009a29004492900804800110344103041c013003c0c02880d0000404000340c064034800050311810750040c0640c0c130058030325548424911005942d0407180350200917490322301d8080d00081c080f4005078003a050f040f450901950312401c07071040d520b2030300c3c0f400d00c120980c201080352003501d080000580440fa10040940c8202e900b00350410401040000c507040132172182028680203240202d0b9114890203100c1c0c000c200800102d40810344001415040c503005400051030b140c01c8015114000000719044074559a5403050364400c44081c0d425180100401d01c6c0107420160350052115041e8043e210710014103607101c002d5000f05c2d010718241c = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 782442850 1250 782441600 782441617
    0x30906160b130309091a10140c0304030c050a0807051003141303030c03020a1413270c17130507050d150b040519151205010b0a0b090f040908 62
    0x41c11141020000001107248596003140441c0300410045034843c024070402c0408074080301e9409400000a080c0040c05185915000400035800c9045d121858004c0040503c4200000115625491818000320654403508180e2003070f1440c400802c94104005046810f855003100c0404045400c0071044d070041c0601c1400180514020b01040750141e030300250027404070300070b450a100c5601119800c40403441020a0701020034005031244504201990141c441500d101c0384241c05203840f100c0217651901d000340080f0390138202031503910f080e0707032507004001c03c420207400c0800c01c1c0458405a2034030300704024411050000400c1d1242e082c460100407440042001074200c04501c1c80070704060300c0f024811510814200e003800381d1810750b424684200307803013400e08210f03228901284881c000c0c0075089007880c01461480074900414225540c07007003459501c0c400c4000040069802c414401f44503070301c1d486070b0122401030121103d261510310b5800d40f010700c225400248840e5901d054910703401010b45 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 782444100 1250 782442850 782442863
    0xa0b070518090405010b03010f200304020a03081201080706080103020f190b0301091d0a0b01031502040503060106050d0c030506150f07082d0c0a06020f1e03100605090303090616 78
    0x43c031060201c19032204c3c0c5030200560007030084c43c0c00394481c3c0090351910030300408042c49402008810500c0780000e190814070007008281550740e26110320185800040e100308a8030310000040104420401c000302c0100030500b86191341c0d40c59500001d07400c10403038a131a40181c0f802c030a80d4140c89000ca80c541d0260400800035034070b03961610440d00c02002c424a08075684902c403004c580203203c0018098540c580e113740310341c800341e085590301e141030811b0044200c0100e809010208965500340b0402c0d0203059907a56050b2a060201107034400e4440600401e028585400140700f00c944841504a0700ba0104403520b0780c0e1480d1120f40031045206003500034046107004035a8020050032080c0301c240b40d200f0100072486812001c20f43d0900c0740f269203d01c12059004c0200400003075400e40281c00e00300c5000101d6800c1820b64415074907424003084101020040010402c01808501d00711400685040c0c640b443c100640203022a6580c03103907104d060301c80e100202d000820122903160341511103a0101 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 782445350 1250 782444100 782444119
    0x160504050c0c100b190317091201180b0129160c0b0c0f060115031a0909060714040303020304090f06031401020a021b060d0b060d0212010e01080a0b070518 68
    0xb50903001800d40c10b280501c00c0b61007144e6020300da0800c102d44c0054a802947c8a1080b80203021607021580c415030905400c121480040440481c1c00c0c401c290b026684984500385440d400d1500442c0200c0581040002e00201443d800002484901e2001030002c21405141c1c1d40ba000c454011000350359110040c5103095650f07020501030756820240c41d01000b41c0c400c03181c0c103480b015061b5844410901402a5650103c4031040006100342c103c0000000d0354440c189400c030f00742c008644045401c0f0751a00b540ea11001c1400f940e01e0380140240003119180c18650b00b03050943d40e00940740d11407480f0320180c198131204510108121688050300650748612044109400c0d000d9540c003075003250b010342c8050b0149206011714903030f10920603030941800030412440d007405080034a0051907040000d640012044c407003964144420310050401c80020b44000c2c0003585425000051118160000c0540b034006881070400211107802c06034018105040a540740c40901a021341c1c90015071242c90751081008 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 782446600 1250 782445350 782445373
    0x17180f031c0c0e0d06091b0626150d080d1b0f0216090f0e0102030a0213150206041202030903150405060a050c0a030c12230108160504050c0c 62
    0x9806002000800341d9040c0000c0d0b6030003000f0341c0d0343d10003922010740000d060000a0000b9000d540014200751240701d04c01d00c40e9240300d8180c80b41c1c4626411001c00b00d04040f5034680d400581c6c2282c1400b907142c141c85003800f0b20780b407190005c643c230740030654034018620409410f0400c1400070030345d078081d0720401d000c20480d8160382403030a0b8418102420008903034201c81c0e0000c0980302182c0741009868464a07100c074145001042c0340142000c1c40c4950800d40d07980b80742c1550740b800380029800354041200141e114441e24032401d0301c50003d544022241950141d03035009940e0089195903010b070f00034102040814600805a00310300c600050a41d042c01151203074070510755680d06140c011400389007215020750f04c00d050b460446c3c1c42130321110700b07041c82802410030140c030179044120411000d2800f864241010780c0600280c2c0d444441c0c1441000f0520089420408030591482c01080042c000301110341c2500400342140300d5900884e8016620b4000081c00c0806120480b1034800c2024110782004d06003 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 782447850 1250 782446600 782446627
    0x11a121c0203040510030c020d1b0f08090a051f230c0114090303060d0b0709030c14010305060607030504090b0d0f2006070c090f060815090c0117180f03 67
    0x902134948158403001802d001c0501c00d00c100007001746c00c0c0d0010300f400b8214244c03c0d50f64258500c0710318910b003031b06440d0a000412201c0c50250140c45100304c1a03e891007181000403048090300624010f00400b9104458408918014400a0003078281012452261118040071000310384c4124580c21002511f0001058150300c010311403141000c104080740c4400900c0c5441c0c1c48260754499000b9880d44100b0085400050001e400c40c03100e003003c61403907503240c0d601061b00c510359001942500c0382104400381c550300b5014103a407103c4100d400c4c0b0729210443d83d0180490045001e20440c0a942d01001c83c07032601e500c420b0841440d0041300203001c041c41c502c0d0801100d42d02c2001802c1e450074810b484401030034100240c8080c0c5a201c0b0152010906009600c2d0041031640d842c504419180d01b00042c004170140b002000f07ea980c40c2e0862040c0c03a00c4c1818914100d04080c55604003c850344111030301140300f0500c140c00c0901458110b215503207804605e45001400074500c80700303000c0010100344c107568 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 782449100 1250 782447850 782447857
    0x180304030818010306140103270f020f0a0315020c0a080c06060102070806100905130816110a0f060309030c0b160e090f0c0c0106030c03030302030f0603011a121c0203 73
    0x600d1466441c146256070b004405944e42ca12401c0c00f40140680b0044041d8001d80040d01c030817418610a0000c0000c0c24849600490035050030781d00740403203199802c01e40c1070105841403030101c00d544511507103166607144031031001c0101c100811294007068900c6585800d0100c2070465400c107401e207031110700950503e602e0300f03c01d41d1960b001d4402c013103000a030a2808502d59100c0c000030882c401102d480c0550000181000424211620602c2d80c4030500086285002d0034040711811600501c50a55260004202428641e4540b14240c0640c0807c00207824225080c1913801e02d01d000700750b4031500c1c070b8256a17034000d83c1c00050442c04035404015000c2c40d01c030713511400303418682c2e070f107080030038186040c0700180f074064500c0601e8400000c00611481d9040008080a0704c080c400084c0241d56a00e40206c1c82550742c1040b00040c0e000420710007840b07075050b00d0641100d000c8008221100340300c0c199041d01c2210340300700c0c0d0103244a23031000b00f05800300707010b070031010304d24485013480304482000700075144d03031 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 782450350 1250 782449100 782449117
    0xc030c09051003321c1106010302030d110c131a0d0507060807020a0812010504050a020c10150902040b040317130e0a020c1b040e01020a171803040308 66
    0xa140070005200c0400c0880c0d9201100e8005180b0450b01451807a00c0c0040030015a01001d5030b03000019030094001c0421100028091003103100180000b0050020309814005082030650780c0034030300500150380d01240c500901103a50070121541891810b4007401c10340d100601946c040d560801c000980d0310541c00500b418040031a41207075140080c2d040041c2c0e5409008090b10070750018200b44605070040540c00e406c00300c0d500441d003003019660788215032903105ea130800d0a01081c4000401c42802c160283c5c58003c50401c101b5420035420b40b694a50790b0031000362440074162030300101140c0504a4402c04080c000c2414155134807034403440780074110f0788248002c448074015507038110100c2c0d00d00c005641540c01462010400c4d01d00c0c010031080c08140103172109000e650b0030050b0405800041003880604c000c030000c0c00c0b01c440100741c2084100d405040f02104545d004021105156a2056281440c5002c1c158400d00c10380301c42c0d4240c83c01c0152042a00180e100000e004824040b00402801d03a55 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 782451600 1250 782450350 782450369
    0x10051002011d030f04031101030e0a080705070509010b0a1404170c031e0304060f0e0a0305160614040512100c050d0b19180b03011b20060c07050a0c030c 67
    0x103902c03810166492064803010070131142c080c0414070015410018074040040145400b10302142d881d10103074140982c241c0c08941440d00011b507601000400d00c464402010101c50f903280c00d6140c001281d0007407141d41140010441035000e204a12814827040d540034003503444140380c8880e0f10385081c41c3da41107503516140c401e10400f200d0498403802c1c4440e1040720280e6001560070305140c0101500c1c81c50020140400348104a40c6d02005c545030340c0203450086005600a10f01c0d5802c402100d8420340c000d8015008100d12001c03140f40640d182e6040300c0480714180c810300310180300c0070419030819252030030345c0182a00703155894041950140203490548032916082180940000c100701880d20178440815240008060422080405c000741c1545900d4030000411500400800a0b0850f64205071540f01135458030081c2001070f238014209500307500083c03e05279161f807442004a5076400e0041c80d19a9000d00007503080300304041408203038061544a0300428500d9124904020002e8850007104031a = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 782452850 1250 782451600 782451641
    0x11b170109050601051209070902030f220302031803070504050901150803070210140912010618050615130f0b190c0b0f1008070806160f02060606031005100201 70
    0x55180718450350b4000c401c16101d0354030f800d40e4145401c2c401c1900411980b02030107042d00000f1000e1030350008502c240c01c0e1a8124030715103044403517402440d02046001c4142045010309000080d0000200c07880e02c4040150110008401d9001a290504c0743c3c00c4503800604110520584d010150402c12461180107041a405030f2074250465981c003804034040c1d4410f00501454140e41e0142c0c050320403241180c90f00b00d103444000c0c0041010f0707140c1400481c506070b64400c010440741c0000000380c2c4515030303161024002030034500d000806d59203056400143c000d00010740740b40751080542080300100910907107055003d65a0b0640d00031904450940d074149031a210b9400c440c580f180c4181d926080d800f01c4800c0240e190115000101800200b0014001c0781c9101e0108900c10100900340080804800815007440d00c030758000007894001c40000d0910002c2d0048401c03051700861011390040043c0c40e0681c03641c5d140040c2d00301d1a490340d40016005069400d50b105040d80c103420800b032568814142000 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 782454100 1250 782452850 782452859
    0x30a09021e1021020f370c02090c030702030909090109231b03010204080709090c050d02010807030f0605090405030c0610051c0203030f03010b18060a0f050309011b1701 74
    0xc009001c00d0340d0f030314070224480203400d140718240d02400c00e800c89032180c941400042034200c40540d90002e044280302c140c00e4400c41c10b04010720f00c602c01c40c00161520320007255240d401314100d01c0c000b6100c0f0030041404000920842c0c130070000d8443c0300701d005101603e141070013020a07000302408141594001a1903e071500c8010120440048004083e00100040684120710b010031030844c110965055408000000340381000304181000340c58443c030001011000381c81c180300514110f5005a020782403e40c002d501603a08401d10560280050030b0110b5030f0710303524424100410003908019840808031060005002001010f0300c102d8a5140c101c58aa0300d8040b191030b103480483c4511540301d1207035003002059034040c200101d10b06101900b141d04007140b4844100e0b041e002600045c04140001c1181040e0034407544020a0000c0b05071281403600c0d017192401401e461084010805100e000400315001e40825400303070b0724059294940100203100c610000306080c0e415141c0050030442c050002c00c = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 782455350 1250 782454100 782454107
    0x90b04120c02060a23130503160b1e0c01060609061107080c0d031101060e0907060e01050403030c140a05060a140c0a0c03090b030103030f17060d08030a09021e10 71
    0x440e41ca40040c40e050820818080c11035050aa048280d80d4022480381039070752548541000d071086030219020a9501e504003402c2c1031800148080440d03844000100c20465070f51100201c0720401c20043c2d0107450400c1400c1c4000342403180c0015601c91750301c0c0000c00036005600803029800e039421075841d00e0794440760008065507542c00340206038807034100107814001860300c0349000700224805e003400381500081c600c8090071a00540e02c2081e50952003c1007100e241d034284000c0024018500b00000c036800080c0c0001d00710b0240380402001e1002884840c01030141100c4500d40f109018412a240d401251415907261030003a200521918240600c5104c0d0020240c842c80c802c6c0303a854069414400030440403581da090f05d580c10303018400c0035140402c0071100341c00114040d500a0b141d0200480305100010580f688040c922050b00b0700300014002c40d55680c0100c1034a01e074004030640d4898030b41102c0e40c0d0080901c4c0d03100a42c4107442c01c080e003003e1892800e460200401c1110f049c075145160342020b9 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 782456600 1250 782455350 782455367
    0x1208090906190b09041e0c0e1f140d15050a0801110f071a130c0b0301080a021509180603010f0b09070309170d02120c04080a08070213090b0412 63
    0x1d0742c1d80180820240218801e0a0141c403000d5401840440c2a400c5001005c101c115403010307151035075840d10801085580c0007024040d04800590300941c00d442400202c0c989100304003868402c0203120b10200c2020703081c03082601d2206091002c1000351449011038001c1040243c0b1415004001303000740000c5009044c45000c121070790b44603880c3e20703201190000710003a522000382190b0154116802d00b540520100046100315107803080749000c801d10381845101c405950388985820072041005000c600404034a410500d9819039148070f020b00003040d0784010b400307000a803a41001101e0062904420301e610204d0086409600030807989020300b07042015110a1111113421469110204400310b202c0c0c2e01174000d01d8011107940c0060b50343c0c24400707091a07000703640103540d881d000b00b820340d40d02c0750708051560840c1c403445095150600c2c0450048c1c85504804014020b004045002800d5440c2e41c21114828409a03904103c024460f29003202203242c00d0b0341c01e03030b100718050360829066401920345 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 782457850 1250 782456600 782456629
    0x80a050603070803040e13060603140c030c0f010c17160c090504030806060d06030b0c030a0c03060e0a0e0309040f060e1308160204020c060a05090c0a030c060e0105041208090906 78
    0x1451429050104c90780c20306d500a010b05660720303030443c00000496482d21522010f148030f5101801241000050303030f840c07d0102d951443c03007a0403004107104e40d0b0303a130f00240b21200c02007800e0800010b00c8508000c041c2c082c005640002c10440040d41c2e01c1e4a956084181040e648500c040019854403006001c0c00c41e042110300402182c0a84007090803440c011020703022030407010502084664403640c0d04902d1080030740b08920f4042c004014405412000d0140102d071828600d81000400c0c64106078014080014004400f195079500201003002000d004803000c0280250041c010029180c0030b04008020300d00c1000c41040801d8041000c4140c0c94000c1c54030f40d5007212100d420b0003841400c002c41c0c060540d03000c13030b88560b08000c41d041031501071240e80e100b24058200010145401c084690034022040045441a010704106000040d1582a28020f031fa8807403624070903209038007006803040e20030f82d0041440303001c80c1d5000b001007090150003040c01c007001795200e0540c0c0d02d900c41032103042c54140b00c1 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 782459100 1250 782457850 782457853
    0x1603050f0a0509100626060601020d030f060302180a0c092d0e330d0b0403090803041212030203010b0706050606040f0e100605090d1e080a080a0506030708 68
    0x20075150401d90700100d402c4040d40054500701d0b0582e060a10403a903150707020b20500c8040794199981e440c901030401013801203060151500d8980400002c0d110407001e0910b005143d038642c1281d40e0381400e070b4804005150b01503c41d03469142a02c6252100d1003089550244403800d0542281c540ca1280003d00b080356041d00b580c40c005060414810915244002d580b0300d004107105002400c090b4041c20a030082c5584403050100031980e0800c6881c031605c075031340f8010703031407140d41c0020b03140d121a50040e1120f2f82206900c803980d00c8074a8200c3c0d407070b1a680d0242c8500d1101180c0031a1030110203030a601040d1265440e02121051018240c090780424412001a90410301010010403404c0c0c2005a000600038480c501c3c007922042019040c03100da4019100d4490004200101c2c0d888519400000d001c583c02d0040c140648040041c4400b4100c04000345030120711421381200c551500103228210350310402d40d03916840001f50040440c442264000741c03031410720b00403d0180c2000704858003594981c40 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 782460350 1250 782459100 782459131
    0x30d02090415150c03020312010b090103110406050a030f0902030d170901051006030e0c040213030c050d24020d02070b040308061f050a02030d0606020303100f0b04030303050c0d06060206160305 85
    0x41c02921310f4966100140c1c20360204105105415858102d82401707412040c3e1001d03140d21031040010125841084100340b400c20800090051940010a40700f01030b581c0c0c6400300706000c2e00d070101c001130505404000d4042c45442d00d08000340b500080617408940700b01e800107001e83d40f000d5071682a18019142401c08100c040f07012b00150b44240c01410b00d49210034111000c20061a02140499122182c420000410954140200700c01d00825200511084416445450194a8002e444410306454451a50450482710030900b400d40503241e01010701d04d011901c4000382c5c1031040940b1000c40c0c0c106c00241e60100015078a2405149841400069526440320780000b2101594141e00c5104804250b11050140714002400740c060880640f8803030340034580700d051444c120707002d030400e03038000d0b1902d401c41a030140f001000c884c2c15103041320342520340030070380d61100b1250408502c15100c1d0340703814034103090000c2a4076400144041c06141d20107101004003102074400c40413103006880d102c1e103042094 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 782461600 1250 782460350 782460389
    0x7080414011b021e1204090b01120203010f0314150f15062110060516030c06050a1b050a05031b0f04080615010309050a23030d02090415 60
    0x303090390818100c02000207502c4a140340c18806160040c5003040050303001040311100010307035007a49601040c80c80d00505080440c003c03600e9940c021805005056a1b403203d003a034880e8450603d090201510000071562035840f54069031fa00240341c0826a585003841e212314096540c0010f890180030814080246a40c41d048030300c0d5107600c0050503d44c40c2140302d0354a01402c2d40d4810041044d0980c80034400302010074450022450f032801044481d650480800c108032080c2c020045036002c010301c0400d0380038680030781f0341501c01c0022003030050040c500c0e003401c0040c01621503009801507268015010b440d03840c16607003210144030304800a80041c10500101e00309011100c0482c1e51a00e46a44890409112954160454126511805090313006405100100c45030032840c00c800038082c6401d118520150f03d03002d68600720110b00a040800302c0607004c09501d0345880d001000d000343c806695403035204001c8480a9085090050310592a08954246d03000c101c0c16030742d003102c510b0390850540441d0f6 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 782462850 1250 782461600 782461613
    0x60a030504020f040e010e070f0807060302032502010b131a060904090803040506150f061c090c2d080705060d020f0d0515010309080f0a1e09051305070804 68
    0x2a00c1243c01c014a0441010195500e004103492208841d0000a0390794511000718a480360a5001e10444042240c09208001003c0b505c1c0342034480c04d04001d6980d44400c2e83c0f0125503103203c14052101c811005120701c00c554190800041c1c0c9200302c4816451200206005040f501001d4414130400c9c01c4290b101c2c1c60307080c108003500404034010300c00562804980c032049141da00446007160190070490170413001000e24404003440344403d980d0810085411b07000b00d211441000f08014040c0000080504400902d401020042d41d1005084980d80e680740241e81442209290003812140004c42e05da4003032800c42501d4080340c1d00d080041c08000d1a00003405155442603060b624455002c004020b6042c0d004002070410303040d4610009094607004d00c1d1540413001d1b80d21b400d4101410f0001041c0403ca00d00d00b500c14600018045954406e81040300785c4180f541c40003500d80c607a01e1200d901c882d0a804c180d003d0100c950680d003100d01d11296966540484600300c40740c801044902c3c0100b40071500 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 782464100 1250 782462850 782462861
    0x180b060a031d030f0903210304020607140f100c0e060a03020a02031204050606090609040308071d04060e0907050607031706060c061006260402060a0309121d0f060a03 73
    0x1441e6007004160101d030400500f554082100010210f80001da040d010b4107042007103540380b104000c8001400445c401070340d0700324480503002074440c81c00494071009110651104c503094203903010480c0c41044070b0301f9095885506a1411740000d03890300e0010351280703000700c0c40c00b107241da0003c0c1a02d292000c1401d0039402034000000703050840c4428030500200402c80f02c0e10707a00441c010401414545094010041000c0c0010400c9004440690a00000070f42100c034858000034282000d248250306000041c0f03403408d030b00215aa0241c2095000a80c4600c01d6940703e005028000030354010030340300d00c140456441540c000800045014030b40c150f24640e0210741c0c5410100081400346000300c10811103141800a440d0f0a8820b0080d0808110158019448a00103c0350f0840412141c909115010381540c0c01480a8041c9000080310340b00c5070312981c860461294460b4140032444030080c4010702405019081c8030420400100d58403151401c039406400f0070380700802443c130700b28071100101d01500 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 782465350 1250 782464100 782464121
    0x8010b0a03021201081501091404140c030307060e061003150216150e010c0915080a020c0109050a0308090616050d2009190303020616021c09180b060a03 67
    0x590900140544142409183c0d0003403040710014003000010041c2d8400f040f4040e0300a20000380f07442c200d044400c4080b9903241e4001c0c0c2042d620380606c40161815414040141d28040e0b0502002500d10100209a44500140c001040c101c9503a503032000c10702c1807540040d0201a02c3c8410410f45a9070101540c0c0042c40400012104079040d030105035903c15109a807040400449034981d1900b41c0320080901c80d44000819614160340c015181903541400c1038203200a03101005080300000d054420160112924449a00e0003041180130070304010740c41302d05120084000900d1440031501c0d84400288860081d0b00414007404c185007506c1040c0c070305510400c4415000c6850315030300c402e003a07042c0d100000415050012950b45000d100b00700542062990914013150103a0707101400400e90000d000c6500159140c5449480324008030168030f0001c071000e402984035914000132030010751000c147d20482d03003054030b00390b1150701c1d40c150f8100341d980d10504250014010710103400c549100303400c00c403050b4 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 782466600 1250 782465350 782465357
    0x50d0b04030c0807080c061003020a1403070b130e01061103030f091009060606180e0105090415090303060905070512070e060403061107030216031e080d140603060a09020108010b0a 79
    0x1002e003030760f0b500404d80000100703a80e009000300700c0041040d010300015500c605041c40307502d20607040d0380c00560a03000500505440c080f2705140c1003c07985041220b0300140c514560320300d40300c20079414142000d05150090300084505100001100d41c01080020703411803414000d5415176a429066541d00d1070000c29082030341c82080042d0390000c1892246000d110b01918010a4a03410000c2c0a481403540c1a00741647d40f4407107900300a00c01101904c0760555004030707500109526039080c880c1d0044158206541d011b0b181940090405030150300400c100d6080f210140101d58845005032120701074054014414002e160006140c18030414251121a400034490f904054072515403c0884510020440200d0720014813002455010000c180303e00c25840e420883c00741c03e40d915019000013269004410603402e0451100300000036090703540540c2e8406040003003a40710541940f0b02681038030500d001e4012080403400849031400f8881c121a01a1118080c2d40d1074494100060f0b40a4203076081007 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 782467850 1250 782466600 782466617
    0x702100c11100e040e010c09060c02032a0616020103050a02120f040201031d1608012f0403150b041125020a030c0b0712080112060f061503020c010b0a050d0b0403 71
    0x49135564442c09034943c05010000454000035507014000c10f605030045002d0262039400040180d07000036841001e141501690300342e0b00c85100820410b003401443c001d600c150081782030030a0401c8034611810041c006d0ba000d0003a40c0702c5c00701c520100d00c035a00311010801043d00c005200110880a440e400a1042c5800691600c03840005400d02803541c7d1094145d07089806200203080382428075101900c140b8008001c441c000590460183c0f51242004c4151140d0040c600b03003200017403055400454109450842140c41020f051005001c04d020040c4143d00d000001c120b15240c5d001a0f078044014a4482a440641d0708800c0408010f50403089034845500c06001c400a04803c3c1c45900a00480d40840d80741c14070782c80c00c41e408003290a1000104a81c035070040154886c040c50766104580c115400040d6114000d02000140185400040c0c081000704042150313598540c0c000c00345003001d01c00802c400c500407020080018041e1040701d501004503541d1300e011540e800c0307030560014400c0c10702c21407 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 782469100 1250 782467850 782467877
    0x3022401060c24060803090a090b0609010f1206031a0901090209010618080d39080d2406020c0f030304091e0905060f01060f080412020102040e09030702100c1110 71
    0x1901d8841e08080d801b03810202e415099820062044400b03084014000e0125000f500089071042c051a401c03076041009050140c5e030341038047c8400c41c800c440c0300c2c20240880b944a041488407420120b88210107601c51400048000c9010311a5240050b0700502003d4180d1800f00300300c030f1101cac11043c070b009102800100019418004c01030001e8020058072900003082c0c83c2070640d0256112001c50a00e07603225007045810720b54a0019460b41d031580700b03000585503140c0840740c00003806071720401050428101824200c041c00134443d07d00302c620507800c85100f01c62031000d0240c843c941c01001501a8070910003400f0845217078001e14240301500b14900c000405500c140d20030344061502c10b58031a080507041c0301070804041e140034090403441c01c014850700754100004012500051000d806408040c0d28040001e1007901144e00038800d01415000d1403d0100d100c91b113070b42c800b250807845400e40400180001d03006904030594650401030000e042090f0109000c250f0003090798000030000d0300c003020a07 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 782470350 1250 782469100 782469173
    0x90301020f0c0a0501140906010306020304150e0714030106141e060703030c03060b0a020d1103041205060f090f0d0c0204020405101805060f0d2703022401060c 70
    0x8940b4610b14000d0045008904000342107420106e581c4407520b110710100080326900242d0241143d03031103900144c2d42e580b00d0421640c03890104a136210f405081c0051056010000228041a03680c0328080740b5112445004042c01c9038150f12400340d6010300040c42c0106481c0100e0020003000ca8540380007400700c40100090f038030b0b612080040700401c0e030b14950702060a0380743c4640b1001e402071040817840d1994840d000303542e5102c88141e490030000070024021a01a0034020748006103d0a01541030031101450b2079520760300102c4550342d040d000e90000500d0407000140e0704040e014084007034034042150030401c0303400708000d00050345c103d9000c01c00050241c0315910380d5401c0c07080b07581e180c40d5104c0c6280c001003100d001c140d2145100302400c0c005000900b003001c1c01c48841c01d03442c035000076003040b8094080300c10302c10891100c2245102d824110051640101c0d80001c41c503525581c0120708090f02c003207130b01c421100380a050001080440c090000408101c44940140f00c0c0c6001d00d481e803c0d601142c0d1 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 782471600 1250 782470350 782470357
    0xf100c0206043606030b0613090501020f070501110304020d0b090a050d0e0102010b1509010302090f06032e0f15030b0904060c140f09220f02091e0d0305090301020f 72
    0x90320203d600308200d0141c52403000101001c1415001480700c0b61641e00c4441c84141c000d41020701c41c20350b0034030000c400d5803154080703070791503502c00000d5442c3c01c6a03e9030305009402a0344141d40355424400c0018a5844500072039104650007444030660000640760034124580042c0420f066105914408000c16010800886020006e9403855403441074003000900355510001440e004541d5841c0305002c5500d80015140f1b007104c01e280047c0c03140e4982e030020700c681c540792400c01d4004030000b003030102c00115072581c2620750b030030054043c180000d9000f4000e001001031041d0a06098480307005d02162403141c00c03c070f480c82202d1401041c890400000111040c60550b42102c02c5696449960341154103e0000f0100c9000210154103010010440e00307094450f12030010310a907500a143c81091280d43c06580091b280c90604200071010b520900c4025400302e551244244000c280580c0034009020283c40740e4000900355090064683d0313010740e100d03080418110f9140d502803000d140401e8661016 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 782472850 1250 782471600 782471639
    0x1c020c0a05060a0c0e010309170328020414090c0301030204020d0624030f060602370b04230309092d0109141006180306050903090f0f100c020604 64
    0x40c004c1c02c16001a00c41034104959506040c05d0109190128105031003180d40c2c0c402c96442103950340d5805d803410b60020000d010b0b490322503000b610280c070f03a200c2941c05001565500d0350070300d201d48840c07000c01900e1007086403480e0012a04000520050402e90054400c280b415030001c1001030b1030b086007402c1c900c00c0c03e603020701540791810481c02480e454000d41a5076061060200522414000700a4503840303980654135200c8030310800c0c50340c108144d03540c1e08040f0b078420100344120350040c0340404401c5c00940d400d0760080401000c1c5800e11403440110038504001c00015481e08c2d0164051001c001c90042200c0a810107901d030700702854101d040c0310030100045151150b000e604151076901100c04841e2000040009202040b40301c0c0c94118881040d54000e0803c1c1d00308000305000c180100c3c2090304010040f904181c2804428540080908a000011604036100c21029002d21802c0c0c546d10002a912509031070200780e00c40d0041d5101c600640c000341035541303030546403950381e50030680c10b408 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 782474100 1250 782472850 782472871
    0xb0607060b01030c1b02090c0d052707050d06091104020c010e010e01150612110a030605090601020a0c1e08010903050a08070905031203091e060109060b1c020c0a0506 73
    0x1080c50781c0c0d40e898032910b2184030303080c00c050105100c05c1c003181c0689800404000d001e240038901082c40013003040151072413999642c4040c4020310301040c0d8031200e4032200d40303440502c0c201d00600381e030f80c24400306038101034a0011b0441c0407403803840c0d1240c40150080f20300950f880e01c124000b4803d00d0303c40d80010003103004050004a5145d8030101c019084847e001c100494030b900d0031040071101541c0382040d008480f02440c010240088405a0f00000c21b142c45105107000000500140d486402d0f801000407600700f1600e0300b1490b1303074202c0160f80340c908101000b420112146414040ca50382e0001214403d1035521030800c140d82c91398505400c40d07105140c1500800e402141c030700406c1350720100c002c2d40076040f0310344400f00e2403528022964800d20a54041c0726800b0120001d106030b80c1c2040100c0d0b283d66051012085a4001c150f5517480360000c2c0584940c4e14188140400c070107034040c0494805d0007201c400505480410241503000750002d4030740b180c0d90f004901c01200450b4040000f940105518003 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 782475350 1250 782474100 782474111
    0x120d0e01050103230703020607021011010e100c02030a0c030f050d0f0e06100608072d1101060603021c05040302011d100b1203030a3b0606120a0f02040b060706 70
    0x300400718800180f04e07900c11950001d071003400142c64013800d962400c0d5040e1211040e02041d80029120f031800220240100d6117010000322010400251001e1401102c88003000b11b80c0e1122400c0340c484c800c60280101281340c1c45076100c0002d1244400c0860f486031440c015042c842a0900001901c854448110b40a519050f0480050405010294110030052220401980341082c05000454002c00860922203a02011441c400050b1801150407001086201040070305840c05401c4402c845d41d50102ca600c0c00c00e011468078080d200b2601000314400000e9540c00624400501805c40140220215520380d0061840c21580c900040104060400540b09100b03130f901041040301d8000d00700921400c4842e4100300e00302e501000310f9030049070500d008241e5206500390402841f640d601000030045205501d920030111812070080c4084401c01039441c0ca4035101c0801010005450030280c0c0e503046000c1c01070000f00c102c103c803809203101400200c4c2142e80c240000703041d0740140100740d0f486038448 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 782476600 1250 782475350 782475383
    0x122820010f060b090a0801060305060a0b0a12030c0309091a21011815020304020f0402030a110a030608070b12070818100b10080903090f1f03090203100905120d0e01050103 75
    0x3640f8030046c00404008004240c03450315030b0f9035120303800b40c5004c07880d0380e40320307440d401a07150345001401601541810b12039503030151034010840d091507031090300080c4100031302044100c01c500404100171084c1407485407840454003048035040c19607850160406400c9246540340000f8060361461884100c08040141c865040c0603800c03560b183d20400045204004210042c1e5403041082800300c0e0135280103072650355502203000102b21508120114002c0401c0804800350f064000b20305540301c000c1910a180d58402684a140c0a010008082c407242507000844061082000580c4066210f42100c0c87c42d482001c2a0304114124400348146925211105c4107820030440f0b003201c55405140002c601d1610f80002074503405040ca45c0c43c0f14200b8a1151601070340c43e00010b2018a070924400b0403400410103000e0024074180c00100d002c0d010304840701c190304c21144182152030703410030080c001140d0360320241001070b0310280d60303520200e6860421001a202c2440703441d01a51140c800e142400081 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 782477850 1250 782476600 782476609
    0x100e0a0c0e0711010c0c080a0e090c0306041406030c0f0a1802030103030801051f050901210606020712150b010c15050105040509010608071a0903122820010f060b09 72
    0x106038550980e8140017a5641d0302d07a0012100d2243ca81000b41240c884449542c100e402c0c6040d594607551020b80340050000202c0b045c0002d50041e0403c88041041010405959058074021111103501d038000b01c4402d6036a08040f511560f03071200040a10403030365100e40302c8044241030f02c04c040305103584c080018810940c001d000d66000d1b0a044074403401d18005035081c860000688900320041000104d20b00840c3d9000c0c1203880c0700c00c11600045414500c141c040000200a0344c4620b00c010f02c40e01c540080d840d41081011202070f90001b030105004002240041c0251800c03108032070410032802e0009022072103030701d0040403071410f801012805501d00070401042c0c40000d0004400387c0d142c8203003000440000036545c0c0803100c03c1031012040c580c040f41c12000d40e000e45904aa0540520610144008e102000500452900c00008001e110204450400c95807810034a00c01007101030208510764141d90400202e545200400843c1e01e0313f20102840a50b0b16991214180b200c01041e1802c03146070 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 782479100 1250 782477850 782477867
    0xf2203030309022409012a030528050d1104031406100e10062f030307180e04150e031b0601050312031b0702030d210509100e0a0c0e07 59
    0x1c84040404d003025400304284440e00ca40503500b414458603c1d4480740c8050303044521000040c01803203030800b8043c07608014000790b1000c06028204c44909034503181603003500b03082c060985480d945060801e550310800a0081c0007003408120381d1901403000100085d103008040001891802c094a614109941180b148854941000064030205001c001e60b0f0216103181030203c41c0c243c039202d45c682280d08941440078030941c2c40d00414484d44e00041001c483c0c000025406100c250361800190302400280c00000721650140300e1001d9002004140070800d03800000e02d83c2c00c14800002641c41903017001a03d180d10110710302ca503104000311941c680c1c003c1800f0342e600404060b009400c0072840c1158460603840010047c1c6040d22049884200318500d1405544145a019040b104103000681d400b51000c04498801c0781c0550b105200e90400e2101402518000c02c0040000c00341c000500c82ca44010308940038445007140325110f0740b00c02145283c01c4501c000c001240304c019003800c100c0d0004100c141e = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 782480350 1250 782479100 782479129
    0x60906051f020303070c062004031401150e070203130e10060e130c18060201020d1d0a0623040c0503010c050705121e1c0e0a080f220303030902 63
    0x6080c224025441d5402008403507012003240340a000700d681c0c510f0488000c02c0d04504061101c8586130011114240d6040104183ca01401c201b4a011103100c3c0c08030300b40e0307500e20141c3d811182c0c1280104104030548030300e81d401500c00d005a07405c1c50740644540c50090f06550141181c2084e00040c054101109100c10014011601d80095152840c90100c2c01c1c070b461008403103a107141e850341c018004d18071038100d81c81e4003000440302c01980c40c1c3e00c00b4000d011350403022901400d14a030983d8820380c200c0000000d40b810802030b02601e80311a45072686d90041000880b9025038a0055005074452030355600c1e614031036403040712107110315802d04040c1400c40b07084090240134890208080382c04030700d0002d07a0b1504681000d103031035590302040881ea090500c92072007000d5111300224070600180061220340c1c0300d41048800800001c00e258140070394400d01c2400140c00030000300b11490207080c84a00034401c8000e0100c0c0c540d503210b0b00d054040e40728a8564019800a960380d0b41050031450001c0c2c4622405 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 782481600 1250 782480350 782480389
    0xf05040801180309080106050a1401020309120d0906112505030d05120f0c040e04020103020d06031a09160b03060609091f09060e060d030201060503161e0b070813030606090605 77
    0x850230140460841c0c081c034018152407050083c00340c030603a032082080b12074a500113008000211540c00281c3d0766a9149480c00006c1230403c900898040d10821028030380e00c590100800c1912116404000c1071000c008a20503030b5964a04041000e0300e00300306401d00080d043d91102d0340d540650300581004400584032041050784402804452080c02c0c0643d01512900c41e40c00b4006e0300c0710f03c0160000d2040f002013601ca181058400000d01020031940303054400c54002c3c0240b5980d401030215240c0700400c07900d4442802256051011b926250042d540c0200081c0145182c90001000141c0b1740b00d04603011084541003c60750309500009005c905c000740b1060405011142c102101010000002800075000f000316074010000e051007500110000c200c05029502d0341c00c50301c0e0322410840d050380112103982c40c400201d5508415480b20140442e4220554a03040030380ca691230341c0b060b81c0710b2141d90300708420b40c80c40400030030305612603200200a640300000b0700c60325250600078000448845410003 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 782482850 1250 782481600 782481611
    0x1080f070f0f031e0b10031a06130e21190e030d0503040204020d0e250e0103020d0309031401020d060803090315060d05011404060b150a0f050408011803090801 70
    0x2102c045005190503660300c50910140030b003040b01c54a21020302194064030359800b17035041c40400f80d12070b2042e006a034050410a440c132400d140c40121184020707580c85800c00c4084d2880c810021641d48404403001056003034400c000d01d07500030940b10f039450103c4083d5040c000203807035000b0310143c0180b2030807040500f42451109240000a5200c05003e51000c1c103202000001504642d210750454034030310351b03003042003046908503035405a0306e9115030790000c00d1a81e0b443c0c80c0141c04120300d400d0b10441c0d14804016180ea0700b903a080c442c840f100c0300c104806010f038003240800011001000014000300402c00182c84817569031000099554960001c0c101ea041001401c1080d01d002c250070244010320143e401d00c54036418046074a403a820680a0415480e04800e80d541d40d00c100c04060041d40500400d0241c803030708170200329800884054404d0040802c108118040d80144212401e21080f0b0a000c0d0030f061743c8161040c2560707051843d03601a51483d08410b410503800c001c4a101501904008010 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 782484100 1250 782482850 782482859
    0x120a1403030a1b390507090506040b0a17030f04080a051006150f140d0203011805010807270c050d0c050a050702040209060f040609080d0c0b040f021801080f070f 71
    0x58200550013a440c00e860031a1040007000d0701806444510301442c424140400403030600f1901c81215000c0c001005003000c0c040b400c145404d001d00005050010300c0c0c82c103854517100d2950b1080c000c11003811054001031000e2010480054080c200034810304003c3d00e2201c1c140c0c03402034200000308209a2240e803030244248000d40040c00784204406a1781400a40c5404004069851000c01640c407045204c0c00107444004c1031203900603604039803a1208040021300b05907050016240b090141c1405030340000401c108101860241c401072045090148403845400304c2c0c46010f440020702c61801141d07000945080c1e400f40c0f8801c42141c01d030145040c50a041c0d2500b0010700700d206640c0080c1c8990340214141c2002d40c2c83c0b00803640030203041c6c043c0c04d956940c1d84178081e11400f9070384202d905501030600403c40d0b0754003410701d08148650003c078105071390b65196116880d00080d010160f80045809003209480c00788860681d02814a4000030b00c0c0c0016410f0401d841c0c24020b4201704c65040c00c0050800 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 782485350 1250 782484100 782484107
    0x20c0607110f19080309090901020406020a171c0b0f040c09270c030c0f08011d270102090a170706050309030d29061206120a1403030a1b 60
    0x415000048403000315030b40c1240002a1103450f11150315180d0018a0400160000c000008040c2084c0903564070082c0d607070b0003242c42c1c201d0180e4420b0710017581001c0f0b41100010489514042e460100c000720b941400544a40059030038420001010415641d00d400400346c503010495000307418003228180185850400c00408115003445001b00606039004280501c4402e0380c04038201c00001401008983c2803000014060a07102c000000880e401c07070021046c40b845140c01da4143c0f01c44c20700518000044249410760700c14000c0240c50108141200e0f031480c90105142124150000c00000d40c03109007034010405030423600e6216181610202c08031140c442c2021542104403941070412903240c0d07443d114041d00310701c680d0300c042e28403e00c3c045000e403041c81c1e81c840208030605006005003d002e140406d1140c94800d0f00d802c9043c017008240041e50510b0088500c00101ea814020788441c1196586c541c0c1c078080c80c0c0003002d031281d08080200512030344e15100e04c10303415400e05d28101c1d0300e0440441c0507 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 782486600 1250 782485350 782485373
    0x50c01120b18130209130c06081b0304030504030f030807390c0302181906050f10140d09060b04090822031a040605060a08030a110712080406020c0607 66
    0x510807491074074002000d80c1a10f24030401c0c0e15801411800e83c031715100800e2580360b07082c404211800503410b079012071940c1c0700e0148144128000900c00c90350f0a01041010341c140c200500440802c941004088002f9024102040905209488010003410122000ba256980640003c0b240704941c030b5900508054901003044582c082a5012118903860304085402d03800c0d9401c0070390002d41003c0044540c0420740d0805114404004040d00e0240d481c409140545040d8820103034405081140c124040c038103c400c414503032100d17091008103040d550381d0713952454001c04240d005565903440d8078020701115000d0f40850303a1085504201c030804903528a00c80d40111101e0410320701d91405a13407a90307280cd6104202543d04551a0210701c00400140d031980c01c1c04403021554641400e0119441c2d08141c0d00e804280c803001c101450070f2018880c01151400d2600001612034458644001103011034081590b00c202d0013104115511400c0c203202034901051a04c2d440e014500c00c01a1901003414072104 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 782487850 1250 782486600 782486629
    0x608100b1305130b273301020a0b07020304061404061b0515041103010c0f050d0c03020f070f051902010c0609082a011a0d080c0712050c01120b 63
    0x1c140405101003030708030051001d8a1a1030700300440b2651040503206a60f1040f03204414030003594603540e070b403160161010a03803402d203802120340220440307a01c0c1b0211a24464501041c8115494070300183c0394a21180c009440200250f00300142c01e000a50344041d09003c41000411143c1c980341c6013001c01400215510110203030f88480d041040b040000910509140e10400300c0080160b0400f8100740d00d189204a051034400d619140e00c1050041c01a07000e250081002c3d2036541c10901d240724024040e00f00a0300303010405601b0070841e62036061000141c4201800754070107103001002458902d240c030000740c488000740405161104c0c0141c0c2d0282c400e003c03240d8414004180d011140c43c000d9220b019902c0b000b80c0750120f103441c4007440c0c40155281d40c00d00c08408024885e410359108900d601a03203822059030007001115964000c0380c4010001c2801010080072591724950f07500c3384803810310141204a41c150044990303c20250782c0450320000c401d00c0b6140c100461a40d180c009091076243c2c091 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 782489100 1250 782487850 782487859
    0x117010207050c04051801091a130c0b090406091b0305010b13060e0111030a0c02030d0c050c0415030c150306090c0e0d290417070f030c08090a0608100b1305 69
    0x210309512504405650b8030b0100b0091204203d0f0b417520308200d035205910106007a44100002d18064182040b12b02003580091200154604025105034140d1186090781d4101e900c40c200054509141e22070508034500c1941c80206c007000d1903a008042e0b45040e072011a888205002c45400d483d841c80ea400d04641e11814680b4000c40c418006a90022080c0d40800c154000071030100007a5801001880d1030600c2101a40c0c145480e24400750f0f03e0340480c00010388541e20003074411101e03060a5100685c80140581e4807105181d4a90701c03214403a10710b4000d800c2001d075040003c1c01d1942c041c0140000740074504028000d00c0d0383c0c0c41340100941000060035219000750b2050100348107101000c0700360034440d5003070700c880071150217112107410b00c00b503801702c0b0003050010362002002c2012081c0d5000d0303175209191000a2002d0748046a00fa481c000b010394401804011131000c1d81d50f19035211005040a0311418600d00d4841c2c080d091281c841d80c0a100200b0302000503a541030206061141540e00c1142c = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 782490350 1250 782489100 782489111
    0xf0a0501091503090b0106020d091a250501111305010207060806040c121b0207050d17031b070b0a140412030e0708030706020403021302120705071104050a050117010207050c04 77
    0x4000714041d114012000d0071940b170b0f05002103811540400d0700d1072003200944130303611280d44e1544c8540002c8200c40d40010004018061341d0010003022030145005400203e8285501c1c90644540c1c1c21900d603a4941c14903c000007a0346e5449122044c0c2c030600805090010700003c0c6c0c5440c0001e131420b18000d107007a02c80d41d641c07401111400d0150100500d0b1003560117041101c0f00500c0c12000c040107000c000c8c003000d80b00d0000d000400345056244000e8070340d07000c40d1112605035403800d40140d07504040e10fa2804900f146c207221040c040400098007031130303001e03a060502500b00310341684101c414418002240c003011901b04000305104840c00c101440b05407500240665400c00c400d403c00e40150800d1405020000300003080c0145030f005802600e008803640300c15080c040d80d19030200c0c46443c1108251700241c50002d8620750292010f03090f02030081c2c42c02d0703803104031780300c002800c40b14111101042d07513903151300600281c0200001440c4440310724008600d80031031030b103e03242d6070028440e60900c10360b20341 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 782491600 1250 782490350 782490389
    0x1305060d0c0b1e160f08040902161109070c020918100c020f0d1205060a090e101a09060f19090c0e0109051008041106180f0a050109 58
    0x185600c090350381081c0340d5070450b92a00081e0030903a006403c00c0c50818450395031100691000781c11100341d00f840e2900c01c400660715030b5441c024645540d00990b00d1031070034000004d080354180000c2000d001850900f1200001600e00031100c071101c180e659010b80c1f1040304110300c15400100c402041d070340407101114250341d0540030042c42e01c2d03c2c00c01c1841c90f004032400d544250320641c00260150289400303807200e0b40a0709050340c0e61104090918000108028464451284103501880d0010000b400d1b0020b140e45034004507060b104042421807099204200300c9100d90300c144684482898410310f4001c46c40151000900c0b080c07005480c85200e540c465400180c150349814a0200c0300d540340d9825126580d980200d0720090100c040a000851802c4108061940c42260f01038103441006001c4c01c0801c5010404803400b140042c0b003203c5041245d501c60240f90380c0c0d000a03010f0102d40380c201d9003074401a9414085090703105e921a9000c1d080c2c41106000581e0005604419104400c1e0f180c3d010b0a0017 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 782492850 1250 782491600 782491609
    0xa2004051c0c05100819090c030605040501021207180803090f0609031005090708061e040303051f1418060d030804110d030309020102060601092103020c090702060f15130506 76
    0x4a5100540c131400800c0b181c03015a421800070b038810100030b50007421104031400c8080c00e83c0c00501c0e004081030000c4109000150b071a900441e0130900070303030005051500311100001d0b210700a51b50000810005a0314450050210f0004005806018090f50400c00c030300c40420030549800d4601d42c410700012410200603181009840c6201c4a0020300f80030a040001450b40c490f4004d0080b2040d900440d8001a401e40110003120304135100c0d241c03014255038a0ba20110b000b002c0181c42c1448109542c2e00520b00c0701e20b6490044040d00946814551111000d41046140e4102c21102c0350003401c2c03e010450700fa40c1c0c55003034420045e09424000d0250380d49245c410a1014402031280e4032034000792140c424140e15030701c00c02003140700381c08a806a8480d4401502e81650603c152a85e1012540f940c400c294250004656614030074011240050155800107400250466115006901c10000c02241800300d40906070081e88143c0e66015400c031800101c0e403690b04081442c80481c0d2160080323085c3d5200c = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 782494100 1250 782492850 782492873
    0xc0f010e0604031a070516060903110d080108010e01060b16050a150207021219061d0f0d260a020a2c01120c210e03030a2004051c 57
    0x741115a21900c9241c90351003811143c5041c0980ca00c0b01c00010780c2c0c0703400b804c1203618503d80d03040c0d06051350916946820152031994021000c0016140c01407800b03503020028981b210f0641d8488000070344c1486809400c45205032144161681054010070200c100306088581100c3d009684129018a904007249003025025000b007100c0300c0c01142c0480c014640e03000e007840510849200c60302c4820000401d81e181400c2081010340308010303280000080050307000d220700000594461400a05251f40e1904000c403448001000e0b400030401c1c044104d50002200c1600000250840490608524001c84200d0020f1a140c10a80c0c0002e84012482c0a11592640741000059001d24140d80c5a601649107080702080b0380822021007506500d030300503015640c800c500d560303901c01c1030240000303080840c000110640442155192282144003000b480250310594011801240414034000640c214011107030004d02001d00904c824081c690741c00210a05000d911070f0b1425450700c88e03041410300c3c0038 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 782495350 1250 782494100 782494127
    0x70f050702150919030507050d021806040e010c0c05060f010e01060e010306090615020721033903020d020319230a180b0f1209010e0d09080d09080c0f01 67
    0x4514800a0f8000e810301d40c600303045d01d100e60140c0340041d64076000e100100e2400e60000b580310441d0050043c058503d2502503a10107402000416810b400340142c6007122184004000021030b01d00b642d109015040020300d80007604c01c42c0ca04003540c905084004481d4060041c1d400700a6155600c000320781c42900a5005440389d007604104581d520324821040d2a074244904000d030058082c00540310324000c103012140312070454000c50480c11a0303011212060054041d000300040352050018aa0590b0301008480e04525280c6a803c006810702a207000b00d07028554003103500c10000324600003c150449030103454140ac140e5801d24031101c15074060300c0119408002004045050040c56030302080b28050801d40740d02c9500f1a60719030101c54440d1140304d005c9801204208982c520083c0f19520a40d8007000039000000c1402028001c0ca04140460160700000b54140e03000703100c40d200510113406078070720340d0038002c0d1000d18024100d9195418016290b00c900701050313201400381d0190748842c4032320 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 782496600 1250 782495350 782495359
    0x1b0d0f081b0d051503070803160c0911040303080c0307090501030e03121609050a0e040f1a04050a15021e0a020708070e0702330604060504090f0209070f0507021509 72
    0x2c218034001000203100071107000c0c4181050740d600801904002c964503007a680c1c00e1002e5440c00344d8034111441481d0140300c04441d116540700c00000c281c03105104104040054841040da554514200106401ca014200b690314100070003c1c0041603030440c01c06000c0703d0003070070007040d0f41c0e0318880d01b0780c1140540100c4100b4480c0881c1000718009491184c1524030b00213803038805225859000384902c101c16400340302c4076803a447c4045000300381c4024000d040d1303500c1078440b60f10a110b41a01c2c0f902c0341d401510225000d51041d0340e85400c0141e0000c4000c00390b0b014400071070400b080928444032004100001c0039031800d0000300a84402d01c2070213504040e001c07003011a1403982d03865601c43c082c641c00312140c0005008501d00c40352644009a040000303140c0c0c1e504508403005406405041d5a131018040310b80c8241e50380c0c400a090307100e41c0201c2420f903001d400c5440500c01940107020080f40c00900100c100010400a01c20f010703005800d482100d60180c46018245a220b090510759100d9000041d511 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 782497850 1250 782496600 782496607
    0xa1d0606040e04031812080f0f04080304030606030b06090606090d151d0708010e0303070f03140403020102070b0907050a03060b060c0609030705010e0c060307110a0c06051b0d0f081b 80
    0x1341904030200382c046160948400c5007441c1e55100d03c0c100d508100710001c01c4050f04100c07040e8003040d440c02902d2074a88001300d09117441d0b0750788223882c5140d009a00483d9440d0303d8100c10418094801d500540c0b00c0400c0c3d850004c203152402c0015414402c0840251050000302507140034402082619140c803060704e00c04128244036101c000d03000e05514108460b20303201d1180041081c42040c001c00802403600d0005500755161000156440d024901c00c0204150b9200200c110003050840d503140030394000c1d00010303560300042c1400205203000401c05036603984290b81c01c118641704c03400d91104507070b046080003a810151800040c003c3c418083e04007560b00c5250f00740007108101200600000d48100e0080000b0507040340758540b2601440b0440d40d1210303041c00094106030090714850b940410350415184500019542c112501e0901e8104000288020a1010503410340d0400f000d260b600310300081004008601005000301108040c00007080141c1d40131503035203044030020b01c2d04045a074400649 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 782499100 1250 782497850 782497853
    0x6200307021807030b210f0f0c100e04020d0c2c01030c0314010f05190e06060304032c030d03050f01030201110717060a050609041119320a1d0606040e04 67
    0x9010204a11941503801004c0f24121000c9001a000c09002d01da00040d0030703800c51420070440c110ad203d11901c4d050150441d4001d1660781e640c03004101400b4082000190b940301001e005000c0d40e020300c500341c0e02800e038403886012020310815041d016982440c3c04500d4070120344044002d4841a052f45000b50280e00000c103000c0524500700c8103842090318a5000c80799070700303609445500716220325407602c8000d034045521424110f000b181d20030701900304600c03060b20318274254104081003208401d410080c0390078046d040c6000c0c05040c032f581016207000e11041c01c004880392180704041c4002410b100031403031030245102060080d0401482a01c103110005e00031008426124103040380e0750303da12443c250000e0703018945011014060303a0010b0680c0740741014202400600ba00f880551945040b188000081c0c0900510380107614003c00401815009440a400e160911081403114031812a1400901c0148105040c1580c0707011a880350004586a0b800805d40c24403039a0003803c07429445804000 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 782500350 1250 782499100 782499139
    0x18070918030201140c19051b061801110301090c030603080c060106030605061207030c0e21060703140c0d02090d08181c030c02041506200307021807030b 67
    0x80c0c0c0c140c0a03400a00c04030308210b001550380c503800c50b146002c08000f4000c40c03240c000601c001007150030280c20910720302800c11a0b0a40903040e0700003442080d500c017104003c00f05030300c1a00c8403019200c900003030107010526120030b420740c041406a030302d01c20744c4c440001420502c40e410241c01140c210001d185d443e82c60064458641034240600030110341800d030006424203044048841c00c480707081c07000702140ca13840403c40250200d10303082d0041100c1c402c00c0c2072490f69280c000912002c2c00030a40d030910f0756118102420300400900e140d06040c6400381c01c1060302d0f480701c1c549070300070b1031328215541d40c50044107010b0087c012004a6500b2071124112001080f0301c9900902d218881c1840300840c10b40301504000d0000c01c40303110b91030300464041c05400001d0180d681500903d100800104000da04c0c103c110b52108603a920940000b90305a50114507516690480c00c60464a000910314140554002c540500030307030303501c107060902d1b48000902c000f0f200b5844103001d114028132501e00029000c4013803 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 782501600 1250 782500350 782500391
    0x9070b0a1205091906020d0e06010815090d170718330906050f070503070822060905011d03060403030b120c0904240903050406090506090108180709 65
    0xa01545408003058a201c0002600355016401c900b0403005907a04c2d40e07a05e006904540c841080071520741c00c0d1410382c04000c0c0241806000c0c1d503401091458601c1c034107000144006020030340a0707044140a00f59240e4417080b68083c80201e44002489a100c40c00304a80403c01c810080408401c6802c010514040d004403140c0030411120030345c7c0c0842120440991400300344085d95000c524403403400c02121b40140c028040c1d2001400a4900f030698135101c103421a8040c01c800c6070002c034001001800007000b5400381c2c5640c504600020455410104041c011000314000c6074188401c907a0200281088004820f88a08000d000e960305da04091030054041c10004442500c01d80701e040f05210045030000e000040303102d00504406407034549448810008002c40362203417032100725141c000c0c031003074180c090300e40414800c1e42e0b081d5455140c0100288903001940086108039001c01030242180c1c0e004a046401125916000d021086000201d6280c800c4c0b5501c5030400608100717010b1010107441400 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 782502850 1250 782501600 782501627
    0xc0a110a0302011a10020c01030f0b0307140109150207090504061d0a0c061d0f040905071e0506031306050a1805031201060302070c1202030705210c060306030a060509070b0a 76
    0x41c090001308081001d00c1c00c0841d0540d006922a680e901560361094208401122241d6130000b0f181c500200400c1c00c228280d0440e54804a85201408480d41d1002e903141c01400b00000c201500e268961000303403190094481c06c0122620388012400b4083d203544202c9401e001e80c1000c004101c060200140c403840241000d54407001850f0000850500035480040101c2200f40001400348060003006090f04911344160f07041135580c6070106c00a40e007084888054107141d0903040744040f1844075401c2035482a000703207000e44c0c070a1080c006200721142069000756440500455180e0301c11034000c00902e243c0369030491211280c0014003c0c4240800100011041310383d41189680e20741c00140c00b80e218106008190a000200400401d105000c0400103144003d040c0d400d416a100c000482c05d89269041103070206442000c2c2e0310091040020a40000d0152006401c3d458540002610741d150544080c2c05240c4800c002443c19005000d1a406081c00c61a1142c45442081c0000c0094222141 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 782504100 1250 782502850 782502881
    0x13170c0a11100e0105130308030108071701021603050304020f04180b09060c2b02031e0f0f1f0510030e0d02031608180d030e010e0a0b030c0a110a030201 67
    0xc2581402c168100090401c0107881d07500b01d9014041c011207043d8014602d40480c405591808000101042d00540c002c010b0320700101295400c01320880406980d04200703148582c07040011198880c0b454178005501900f40c04d010743c50340d6407030000c00c030740044106d681940140b51903038030b51071000c0d2a411140b2003409618020507946d95940c2c0c3c40d43c0c0c0c80b415544196625003d015400d0720241c8031803540e82840303420310b0a5250b0611040c1003810f9030401d403540715181c4c1c1c02078080d6684070203411170154014007514013402c4034180a0001903507214054415512030310000010721001170300000d00c40040901800100194030102401001014640e4080c10301c1c1c05001425644148000b05903845103003649164404e44159030340d004440d90000e000400c442c0c0e804600720302d60350344049807010312a0094480031010b1070081e0004000c200701300700c8548242d0180b202449084055415640d000880d00e045c3d5030b6500c4203410039503030207030a030001101c00d2207080e12500800d135043d00910b01c1d010700b800 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 782505350 1250 782504100 782504123
    0x17100e0c0f1b060136110d0504151a0a03060c030204180603020f0a03050d030504020406030b0415061505160503040e010807050108010e060325050301020f181813170c0a 74
    0x80803107022200c0070480c003000714107210030008621646d03444040c0b025400c08129141001008402e0251507046800391a0760034800380b4141d40c24132500940302181490f044528000d2841000105141010f0001410556556009c20b03808d5010342c0c100c802030410465070742c610500081d680c60207841c2c1d50100705e00500903801c005d40f41c0c0c2000c2c90030000b5a5031101c00b510071692034001c118003d180041c07050341d200351565000404103a80f040803d0040d4040c1605284c0540d81d206407000b40e4100d81c0c005100c003000ca02010701056845000c0c0c0d480307a085c44003651150796690508030300e10b000c1c5400c0820304007054000041c0481c070015000701152000e0700c8100541e0b994200904000c0b070704680064044c0c0040d907403843c040d091b200e02ca1300516003801f0741640003921100401e0884c3c002050800410900045901c44840200d40210100d0401c45020f10142e503110400442c98101400203000d400c0d410284a0800c10816014001072000034049500c81c800c0790b0180703a903000c83d61001d5910f0501513 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 782506600 1250 782505350 782505389
    0xf0b0702030114010f1e0312120b010f090b130801180501050f04030c0602030702010e030d1413330c0306090b19210204060617100e0c0f1b0601 63
    0x50340c1812a4101219445517500d440607080200c4510500c5001c241c03c004d9010002581d481252012040540e4406034080c00092082c411555013a03a558140100c124460088a50107201c000684005a0704541c44d40303040001802000503540040085508015040b00703501c0c0140c00f45445207010740000c0c802d0f6154900300e440d0604082c0c50141c0018004c0d210000031582507001960810b0f450f100004600905880c2c085c1107401000d1000c0803141c03540c201d070000f10900740e00290804207030700c0f007949504510741c1c5d40a11208100d10702c07250300d00c02d83e18480b030b20351001808842c0d002550f001480f0030b03040d852004004000302e004101e0b41514000e000714090401400051010114106990905080c440b211014003001007041090302150500640143c4480c00f4610060150740ca401e040d480e1902050280f4080041c060002107030210303010003d1403400116940c00030302c1c0b1442207a55031141c20200c1a24400d0141c40400102c0f26071944004400014616040b9000781107036604d4011503 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 782507850 1250 782506600 782506631
    0x2120303190614100c0b010609090c0306080309090714030c0406030c030219210f02070b07022a0a03020909070e0702070b0403062307170f012702040f0b07020301 71
    0x4030f004603440820f104400f81c1c070383d05041c00b0749214140d1500308403400e00011380c1c818420a109800100009084113410066000e0134000c1d4407114000d4141440b20508004841340c2c3c82c010000e01c0d52003003151700080f07482d13640a03030080d0301c05c1484000301ea9500e281891a0708299402841603100013850302c025007504ea44a8800c0e14030113100349100d40300088900c5002c40c0c4810f032000001001d0700526491408000c040d2141d5522086400303c09a00d500d84c1d070030050801c10000b07040d030007950003550700481c017140f03000149400b00211800301040405c41501141858840ea04000e40140600080c04481b01c07000aa1303208980d50754521003140c0d030b03c0030801ca84070701c51031081c0b0a04801c00d0000717000184568203c4480040340710381c0300c081800d140c192a4641203065801e64049040ca00c034410801c4010480c082c0d0200f403000b041d0791254500700e100080b107070501d41407000044807280c00b04411034140d0100c40050114801802d1543d441c0e0045002903401490704078825032a003299080103101 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 782509100 1250 782507850 782507861
    0xd03091b0605030f09030903071d0610050f0c0304030f0305030405010b010504060906051c020f070b07031b11010b032a0d0b0105150f030c0d0f0902030303060d0f0212030319 76
    0x11582e807402d0460f111400b04400300b00021300345540c1c1380024003c0098580301080518020030241226a0718610b04800e594080301c0041c0c029800381492151102019400c4800c4480d010b02400c000c3d56a40550510b0301c0c11409540c00040c8415000381c510401d050348a00070b14021f5014200800000e070303c00c40150340c40d01c0b45100b070001041321b0350020065230b1f02440223807120340f5003410020030400002a00b5012a401002d1a00207140c0208180d01881452005980c1c40070742c909007003052222400e20400c80241e81c1c40c43c1020000709044500f2440000c0d002042161000380403100300014449418215034030041143d0040740001d07588140c1841c0c040c000e00300036900850191010703401d080030310017580404407021000440400092264469400045221781c40401206407540722020f0032005071030754100034800741c5052101c1c9001685d8040b04581d0412411160750200458616040082c0c800300b21019510030303281d00d84402d0740100440207511601d0b903c500004c80b400030000080c210751 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 782510350 1250 782509100 782509109
    0xf0c02130f181722030f051c0c0b04050c0a03050609010e0a0b0703090305040b030a1b0c0309090506130e0d180e060d06110a02010b01110d0c0206030a0605030d03091b 73
    0x81e070f50180c40f0440382e000005240d1070542c5842d00c0510f804485100c4c0760503030194402c441220f10304c10720f00c042c00801c0c4106600190720f000426220840800010a40104500c01410340380350207011808001c0100100d81c1990809000b4602866803414003544825040ba454581c81d400c040000384452008210494040d600c1404517249440d010402c07401880394100480c284502000b011076500c00300341c00b0f14401c4401d04008140b03042c07039046030030328040da08a241c0c052201910401d00040d42200000094070190100090941e640e0000103582c05041040007007001c5c600103501000d1000031486940303694180e01c0e0810664022400c56441408500c1341050141400000c24001d1815060706015117004130008121003105440c600c5860740080110005030f90740790308615141d40c004d8850600b211514020f00012520340701c1c01348ca4002c5910300207205a1000000178022070f460790029002c3e01000d011182d854128a1000d00103080b01c0c1c5e070540328007210408010764010500180b40980d0b = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 782511600 1250 782510350 782510363
    0x1031505010c080304061d0102090f270712020403051c1e2f060603120a050a14071e0b0c0f0403020d02030a141608120a0f0c02130f18 59
    0x2c1194454a07003640018008440f00c82d11a41480e00c00030407000e89149064003800016a900304c404204031a8805444030540111000d0f940708006650074141d0100106043c2c400d400207650746401221101035108085000600c0420088240903000440212001c5041240c10068140d0b40c0e003624048091784200441401241d080c200c07451040f074102240b2070343d12034000c0c02d210342020181200944120b0f10300d5194449000c0103054602001507a1000c662515403d14000c4800c600600750311405400300c0074084032004003010100b403c006c031482e01e0703080783c41340100184490740541c000600c15000d56401c80030380046060170950108541e100407105003428a80351960b03081c0103000041d56000c0c2c2e40b500070841d150012030001001d0311003003203904000d0100304020100c10141c248103604924a268022a00c8004201e142012900b908019003040400121400d000301c1e02c0e41c0319100300035008681c030022890300c00f0702a08540b4030004511800c0c051028030f40032650040300942c8001c3c3c0314 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 782512850 1250 782511600 782511617
    0x120809010f02030412081c11160c0e07021507090e0106030513060603030509131a090c070c06030204060e1e1219080d05010509010806010e0a290103150501 68
    0x56004615281d4810110b005507400c0039a1840789000002c803402003030780d40d48000210b450314407404035405100181c081904100c1d0140b8040c013044240541f511603203408131302404032801d22201e01001c100a195103011701441c0d20386000002e498088000780383d4030a0505d180818050340c000c41340281036802d40c00d0300000d6603282510450181002038203126140444110a201040c29402404003550007901c0ba0303a40e0f140b03503900b84081032401200c0030500324030301404900c03000c80390254030261507000c540419a0342c4404051300114070504074000c042c020329080015007141c1507005481116581d4590a10021100c4288150000c82c0e034460780402e48001c022100a01e05001402503401c8504d044520b03a4034507400038501030120b034a040e44d4481d07001c078460300083e40d079000d079901405d81034600c0d0f409945003050041e5100e0040c05a00308a203004000648072481c02e51052400322404041414200740e1241008030b51008528402e0009041202d5202c042c810524004102c90b0181d40e202d01 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 782514100 1250 782512850 782512867
    0x1060f02150c09062d040806040828180e090303181204080a060f090c060f12060e1602010209010c060902040608031b0105070206010320010212040b0a091208 69
    0x2032000100b4407541070000340040002603d62002801c4d505461190b01a038000c20783c450030361140703565040315603a280200700c01d201101d004984180c2043d030090031162281041040403801c0b2405165240440005000d4412601d50003c4c41041d280108541074840d00c0e1141191110380718201c80d11303000c1d9881000840c0c1000c403071044204c1c0e0b42c2d0350711003a42c0d503401e1101105240766229070303c42e080d240c2c0568400700500005103e00c481c00d0398041d03402c0003183c240e6520449280c0082c4074007810302c020359451a002d14004d004204519039054000c001040d15465440740c0302d9015140250308200c059000c204050051088401d940016100e210030790545903a504040c00b2030000482e0081d48a240005641c0401c1005d002e0800340412003200340764203645640c0c2121001480d00045501000c01000460100c086102c07880c5103002c2d95010018040300140e02d008030b1141080b245034000680040c1d00c0410740054071440d0640d03510001003030342d1020349900c3c83c00203040107801d1080c100300030030 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 782515350 1250 782514100 782514133
    0x705070c140d060203090f073f08210f040201140f040902030901050915010f0e0a020c06010b0c0f06090613150216020103050717010315020409021c0501060f02 70
    0x1c1c00408010805040341029541d001e00340e800c00d0b82c440d8401d40c07103207500c0008880240604800b400480390040d0240c80840c131109400c04010032a07038017440400e45910342c100c02c0c584965078501c1c3c03c4082243d0b07540e035010b032100d025600f4031510081041010042425404d000401c00d020b01c0c2c0595415000418100ca90f10042e4084200820742420410000074610a903001035446140c4080000070607240600b04181489108844554070301403e000500c0144c0061000303106880074064190401d0703541440c0324000b40b1070141c1d501c40a1044100001d048600200100030f41003100040e21820003252540c1c0c6d0303a4a0060752a0382194011742c3c0001d4400300c181e40040344c1c450240311004950b5900758a1207040364850b120000051201a41002c15075825000c2d25400c8496460111031544e00100300d103a0032032041c0801071a054801841d01c0400300c068040c0d40103803c03200c004654800c4580f400c020000344440a0092242c20701d000050700034050401806c10034840c0c0c0142503117154040c2070f80c = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 782516600 1250 782515350 782515379
    0x24170105040f0e0f0105010305060c04030b010b03061c050d0e1017060315070905100801061b11180f1e0f101d1008011e0f060b120f0705070c 62
    0x7441c0050b55145140041e90081044d0304041409600015065046050041c20614000c01d50072411604210420024020740007050440340b40d900c4142e180c2e02c980b0005090b050003c46c004c0f141d000c040111009008020890310000b000c503407603800640300241c040c01080900c0c20840e1010807030f2901c41e014240301d650700c904c2e4001801401c4d05c0f014880702034800440c00051300c64400140d80311506210609111442441941f83c90034500c2c2c1962402c0401040641072017480381104445035108810002a00c0802c070b43c0d228010f107049819003c501a030744a00070101c900005840921002c40d11145501442c0c07910380700032500e0304155a40d00800f600d1406c034050024001101600d50000c0c0e15000388151a40000554a010045040800c00300c0b84140d0b998201c03001592404009440c4007a00c1000725407020020306001c02d0a06808a0703a400030403080d0b1108554410004100084100c40c90005100e03030340140c00101603448034003040303803980039081004080b694011301c02c0c071040d120f00301c10 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 782517850 1250 782516600 782516621
    0x15060f120f2111060a06121b0314010c090e060a030311070e01030303020a0f0806010f030c091205010903170408120402030c03100c0207080a170c070f2417010504 71
    0x11414006140480140c2c1c105510412000410701e080b9200d10000502805030800760b94003082c4981c608121103514400c001d61401460300504c54030131a41100c030031401c07000075030f08034021075440d03207140481c03d01800e01c12036218001440150041481100300300100e00900c0c02070407050207241140d07000e503680f6506800c04882d5110300f020000b500e596650215000e0351082c0e601503101e00005001034a2482c289030b00c6000d1004007420440c0ca40d910601c09a2242814900400e010208400940c0e10b001180c2111046807001c1d1503680510070150049500d1070700c00c3c0d03074a01c0040e141140100c4020001d4034001c0540500300200081510010303000307908107000038155480c6011880029280240c981e4014401c5078843ca10788141a405021250040020030080c00d071503001551038150003041d88070713101002a0003107540c8a05400030405078018000e90001521850b49401c0c011603480918038800e135480800207070124565100d144400c1d030f4042034a92904169003440200b102400d0100d80 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 782519100 1250 782517850 782517863
    0x5010809030f0a03060302040b040504020f040515030a05030309060c0a08150f061b0d020c06030a020706060e04060204182a1202040b0405102a110d15060f120f 70
    0x9100110b1968014400151540c0b80000d1079482c5105200c240c610000da210310882c40c0404100140e110b00306e400081150171070f000174155443d1440d0000d0740820050441d0940b052043d01e00401030004015401092110101ca40743d0f5114400c0302c000344111200400002c54030800703d4081c4800300d191500c3d8442c0144030446000f80000460007907004504011082c031780740b4000c595403841c00d0190189100061000e00b03a80c0c0c58010101d541888060080c0d0046540040c8050610145600c0380028041840b0407244500345800c204010350410300401d54256000c010702c50020b0894404d1035100d107420112519083c06001c2c2c2900700e1800641d4540a005480c50310310002c6000b48010400340c07000108a039281ca040c501030010b000d91491030102030020340000c64004130110804031001140441415121132498a06000d1805a0208954121f41010350030404c2203401014180700000c10541044000c0c0e03211080c1850201d00d1181d0541140c0d4a0007840201e9411150200d00500442 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 782520350 1250 782519100 782519107
    0x609120c100c0224010f1412060702030a0314010f0501030e161701060803040b12071e030501031101140a030b030c0a080706081b040e0901090507090608250501080903 73
    0x2241c0341078492010400c80181c11105015030301131000803000b00b00304030408440c4040d41c1440804245c01696005484440d0000925150710795208011003089051120030340781d050400d488069035030f4001491050110b0f040072000c641500d0361017000c904031010100c90130044d9103424010b500400f048824550140104035002000e5402c000c00540140809a084039841c40304038081421600b080d0000380903500304203c10403190070200c0a4031112101c008841c0090348a0070300954481c05000342000011080d00004680c2c280c2650000741240d000f0744d03082024414810044076141c585d403038180b052038814000c0b4448688258801c920050014007103404800312900011081030300c0e83d001c0007640d8007400d801d100d10b5030300c03444080d0410220030903620501d07100002030070140a0ba005400d075003920000003400a8409400111006801c00c041d100f20790f8846a0030000f414003402000c109100e8103050019900000071140c0300240c000c5040c1e901c580c1130800448501e0000780000c4034520051 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 782521600 1250 782520350 782520373
    0x307080307180f1a0309030f0c0709050a02030103061407020d0806010c0b0901061703030c0f0f040b03090d0f0224070c1a070806100f1202190309140609120c 69
    0x1d82c6202500c0d108140300385641c50320440c01e00d129000002401008000e00c18410700c0d03000001940d0884082000c0503494800030b0820f50320301800d075400700541a040a00340040f01080340c3c0114145c0740202c005100c00789140101e500300807800d86142c0c0043e401b40100200301889515856000101417406007002903890b25520000d00d0185c8400710207954a8408101914050406691480b151000b42d400c524110100d110703e4020300c1040c500300200094688451165102164044c0425802c810303100d0a01e0409259510090220b01c00403652080282c4070990000500306071801c228a803840d88500c1d1181007407000400a04a0070500c0507030f540d000000b98032040d0000301311010000010041c40d04c03800c003e1516201501442c004c586d6070280302b5a072035110242006080c00c0c3d0400c400701e03400020240c0001c0c4100e944203400300d1000313000c41d2051607140c3c0210f5025030103440495131003d00c99000c41d403166800e60f03084511744d0107001d024161040b8200586100c20a11050350341c9214207 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 782522850 1250 782521600 782521637
    0x316031211100c0305091b03121e040b0c1b0a090207050705042f1303030f09080f0312010e0c03010e044e09120807050703030c03080a0506030307080307 67
    0x4003a0041c01080c0c9940800c0f541507402c0088040341ca0001d065514440480300200749c980f840040150441c1c1c2d0700060130491104203240700001203038481da1465960fa500d10302d0b00303595000701450181d0307805030703240030085941e051009a80c2008000d05d18144603282ca40814020351040608851900800e580090f0f141d45034030440740b50782152079003048040d00c240a41c00c51004030a031010300840b800e10800c0c00e040e1483c1c0307811083c0c9625090a40c0c100c0000c050686083e103080d48030705078505c01c4d050003140d0450302001a150300703040484406151f03622404010003001040ba6400302e4140140010404001d0b007252943d001030042c103003910f40100c84081051080c074400b524040b00002007000108a0303c48101d140d48040d50803401010705040707444000c040c25400d108052000c40243c0004040c08811012541c882d0b84c000c1c11141c0c05ca650740340140c858000c040b410ba01240359a00040c1080328640140c17840b41400801440c1381420740d940b086610b82000c0c0c8210200240c602804907001070 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 782524100 1250 782522850 782522861
    0x909021305100f08030a02120a1701030606090608030721140d050601080108060f070f12020c060114030a031413031a041101020102041d092406031603121110 69
    0x18040710700c4402c0e003403010380741d0b404100b58009141d551041180ca05001d0380400c0e180e41655850344071590750206600b044503800b01118030190064a0100000100550ba5000300200c07200308000703201017071ba2180081d4032801a007101421400304410418040780e06003100400422081c20403c21102003100005101c1e0407105139050966512018044590380040f036640c01000010300900061800d11410003000390050192400e1002c0c0158040880e400f5541c0ca41071605013400c115110710114200990700c0c0e40c03e12960740c0d00b0302da035411030b0000c1c01c02240d5600c220b50541ca4807400c965241c41010201d0340500302061010040d03500102c0014458102d00a41d1549210340c200d03227080c54206600307940031502c00c490644e88108810080b010f00858031704541100c4243c000116a214411141094004550021444c9900419040281d85000f104d40184029030071540d404440142c1d82251000310f000180c00c1e4400c4803600004280708440290b0407106000548035010150031070042a20f5 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 782525350 1250 782524100 782524111
    0x1205030c0a0f02031b010e10090b070c0302090c0309030307050a0201091401020307020610050a0e06040905011803090b0f0405190302030139080f0a020c0d0c02040c0201050601020303010909021305 86
    0x407140e001c2c0340651500300008811100f04a2016a020300240000b0f0100d801b42100700d401042034100302d1030054003c0c8410802042c1c200c10306070b40c8683c0c178500110001c5550000b00c0c410003440001c94030460359070050700e100f055170400075899500d641c1c40646298010b001c5140441d9210404a40000c4410078000752081c444030025843c1e00b00250083d0808000814028a03441c000204001c260380c0d890140c001c48020014610b615264000407030058802c0103c05001507082114060101d0803c10b111034081e8040c0c0c1d54081510b4452094589601c03e0651720001c5000a01003400240381c034080c412082c500c994041c0800c907a036a40441c2c2034482400f441552248814003401e981c11200d246007091050040c0c1818000340d8a0f41d01500c107074400380035909001400d00029846850b15411030310495540d904070741d42d07140702d0100101000c0040404038007946c24900c40840c010b005000700b6000303010580140d4216800c00790a030000746041c0a0990f03100300140e04e01003180c140c44c402c2d50f0041 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 782526600 1250 782525350 782525363
    0x50118150b0102010b1003361e02130b0d05010c050c010b040b0a140a08150106030c0201090203120319020f1905072d08180307120b011205030c0a 64
    0x40c480003600048074800c6480a042d6410220715142e50b80e545419080090f10702e003030024070901d609401d1449075400c2460000c042002d2420000701004542c26400342174882d6503481c3c090702c0c0c01d001c40c81c071044081c0e2000750041c1c1d11a18115504042d030300011640380740500340382460303149a02d0b80c0d4203482d078286402010400000b1040340c01c003402e015070b1f00d100505840070302502c0c035000040b03102004180b0444603400901c20030640296920038200c0024282e07502214506079821201c900843c8081c880c1e44082403401d040c1d00d01090041c020030031150f40081c06421000d00303d10310784801d03600050445100c100481d00c2070b2404a05c46c0f01520008002051a6403120500c0380943d042c40c1c0000308000a11200740048000145e00c507040c8280356201003441c4e40e12084498520a17410f02c0c165000b4040300012800c041c05019200d026030b05030608404590b88540d545a0314003541004d04805060345c41c01320010301c0f24900c44022602802d208004403841c0801d8a00c660341032001c200022100e4 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 782527850 1250 782526600 782526623
    0x13080a0903031d1806150f040806060103060b0702010804060f020c06150109081906090b0106020c0a090204052b02040c0f1112090f1807121404030e0d050118 69
    0x24550300548030600f03502030820103541c0b035000b0740004010303100258001e4100c051a10002e0303803946484004c210521510f00010b521100d180442c1c00454010b802000c200d0b2241c4800100190303c0307402090122040500d080340b810034560011502f002c00180251a040c1d140d0401030142040d0f0301c000c06c5038000c1c13540030306001c1c1441040d0340d010722144041c00703042105410043c410604046007115080014102c4d140f5070541d1132510001074101d1200207050480d2381800000e4a6070081960041003004540240d030709511461203108034010340c090540c00122440300403180904c44402104e900e40484440c440003c69a07001401b0703510158460740001c2d40d141641c1e485103405c260020300c0c015280001e001c08450ba492407801d24011802e1881c80342d14000c400380c01c0da40b40c0c24034001081440880c10b00e0f55190402d009000386040c90080e00001e032520340d07120001c0071240c402e00d00840c1e00d07984070703180c0b0844202041041e000e0004162555541c406056500c103040b00c0d100c6000c0b62043c009242e0 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 782529100 1250 782527850 782527853
    0x507031401170f062e05042309070803031f12050309090c070f03050702040905120a0e0103020c1e0f010e011b08040507061d130911010f08040b13080a0903 68
    0xc0c8296180741c0b0746903502402c14460a484e65801c01016111700940e408010100380600b00d014040c03aa00103504140b500c41c0922601c41c079a040d50042c940a4440900786448a907a500e6642c90148941800c0760014030104408281b0f01d103004003403680c0c8002c1030405d00c3c3c9940440741d59484c004007c50304d96000240c04541414002949a44541c492800078101600754030791340c0c0c0070105940e00804011000820200b1550703141d000c9103225030000100e81050040044c541410383c824100d501c0460f0028880442941c404d0088176078910405000e8501144d503003c01070010215807000b1800d60040c03184a003010315003441102c0c240c0c0c00440003c50007000c185030b480340000e07002c09004c0400206508101c041040020402c0865556250401002005407000980b450000696560200b500c805010080381c0c3d5030402a0070318015200840300b0300c1880300660346504100105404941ca103000107010400015180d0351015100003100d041801c103540f018040e5000b0614007000c5442420b0510 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 782530350 1250 782529100 782529103
    0x302092805090f160804170304030e0307051207051917033412180308030f0a14040303090305040312180b03240a350d12050703140117 59
    0x41d04804a090031100f1820700d19151080c14a0a100320f5050001c1540807a082000f4644542d4102403c5070503184c03281810714004014000039444288a84280c000204151034105c00031004c00050b00c000f413500902e40381c00c0c0141d0026480d103020144a079030000080c507043c44540150050240409503540c2c0c41620724500514480c8a43c4c404144102000d1440c1d0201c82c282380c001041d017040e2201540c4a060400b1105200303002401082c50f1880b040000402c071040001e98054100c0c03c1c05480c09680b0004c4000c1201c44841c1c0701c00fa210f01d550085000701c1c0c040c4c0d00059140c0e00a1501514003a203075110400002d40c240c0b0030000050702c3c9100f40b0103001540101301c0261254201c81840c50400c4100a0704100c0710542054130552034009003140c560354110510001c2103690410b1b6000c085404909088503818a0600059003400b201f02d10f20710340c0441c02e14128000c135291040700c0e180703c1d0401401000014000018159074850780400d0700805a501d038000c00361403103000c80390800b22061a = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 782531600 1250 782530350 782530369
    0x80c19050a1d06030a3908310302070f0b07050d0206010605040614161109090a0203101e060306020d14010b0403020402090d12020102092803030302092805 68
    0x340990041103109080c50341d0f800c0704a9030413140100c0040b500107502014003261072100c0100d062040301401030704020105801072582c512403640c0b1420455030f07a0a42441014680c4061021115161100301480194619038011601e0007441101d01a50f00c0c1c52a131128400103802102512901080341e104000e0204000c0f0788540142c405000d19502d849400381040c043c0c4d014060500030120071007031300c01ca090400d5a8200d040391220180e294094280180030f4884100000d0169004000040480d00300003130f0320041550203801046806001002c00700288690441d541d11040310940504c0240454040c600255010b88801a594510601c2c00c3d0122500000d107818541092401009045503400945007141c1c0c0544000d030b83c2e4100f203000542d800e5034002000742803100d80d50003102680e9056000d802d01c1e48050f901e00c4d8004403550f8080c08025103110512035000462002070000070301c6500a40340c0c2c0c0002820403071100402c2015041d255281401041010113100401c1026150103010b0 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 782532850 1250 782531600 782531627
    0x1204020f010c0b061309050a15110319020a030f0507080708010f0602030306120c0303070c181802040b031f02120a020903210708031303140910080c19050a 68
    0x8220540c44558031843c8043c0e005061070300c1034074406042c001c14941c940055000313035803050a407102038201d031170154a03505409182d40c410314640145459154868411603000d40928001200301046910b0f00710082d5100d030011004050b11000c0c2d0141c2c14a0501855000da0040e85078800c940c68420740007400c26205a02610342e101da045010400c071078000c403ca036005581552800006600d00031858236108880740344503098400061103034240a8a54000c8082e115880798403c40d600003c20f04105680070311044048038a03103141e800c0010715055006c80540b041c0501590002d0018040182c0f0340710b240052142419000180550f01d80405100158018900303d030850030b22031218042aa00c2c0b004014510302d407980604d0415850216100395000c80f680482c50359524609040300322038000b003009080300440c0c08413a42481011070b40c2c0c2503401d81034010f412030715928443e140c11110860054803884045504209100c008804502225000c15007a00c82560b1001100340003044030220811 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 782534100 1250 782532850 782532857
    0x3031d09130b040c150207090f0516180f14190f170f0109060c0e0a050f0f010311030c030f01120c0306021c0f1e090b01051c06021204020f01 62
    0x10000c0148420385401d80031a00400b00c0641942e9030b280001c160600d54100206520300104801603450b40003d144050303c80000c01807192a107030b941458160f5200384c403003180d492600c0102500c458415200d4a01c400c0d1060710243c1941d0b80c942004100c200b1640108506d584240c100980310306228503c242000c00d89c581c2c21041a2501d451486c2c500c05c1c40c0036140360b80c20230344015465890300b0020001442c0081d0000c1211a540e807034144010010300b0b0b0610701048812942c00850301d0031240903412500040c0c245500f0003040d4041183d5805c00380d5030305041c1a640d5511800c0c0400200c044c5100b0048030426554030700b44a01a4040020140d00120b4100c500400e03400000701e45503880000c59a1040001d40ca0b1034004c2030b05070710086441c0940c480d03549420f88040030070f64942c2186124241d1803984c10300710707089108820203543c14001c001d0a60003618004201c2400d0204070024840c07003c181d800f00420b20344da10702e01646e2200c00c154a00c1358902c0140029031421801c410660b98003400e = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 782535350 1250 782534100 782534119
    0x1409071d010b09191e03150507020714041523120c090a060b070f030e010906020a02061e041712090904030f0e220b04020702090f07050f0403031d 64
    0x110710742c1c0d5610410003924040c210281e5850a0440342102d20b0010300b9107000c07040110025403003456400119840103550f50740400826091090807446a00c1c05001190701500110742030803405107859108002994110703550358002c0360031a03060310008014200211850392034002c003d04d40308800e000030048511515580c51180e502201c0083e007070900d01c0c0c00361503000c030781e64030400d000c8020280c9500800390710070000740c4002001006e240ca00c419a219460f0f00d001550640b00450f0484e410340a0000584e00c125842c0c000340c50044003030542c1c500003000030f1110724403d03401401c0940141d0320907000c00d041d84089442c814414402e4240c1074083e850b80c1801c1011090014000b1580508060b040c01155082d048040348030701410410030f04098405e203000b914215010484d840221311141070f56103032451291051074076008070b400540d001004030a86869170401000100c0002d0945007c1c0041000f01b95621034548003d00029030098032110350095250290040080711109464030609112 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 782536600 1250 782535350 782535359
    0x6030c0c0b060f0a0909030f09081504060e03040b0403150212011205251a161b0302151c0b060301090b01030905011407020d0f0e0d0302011409071d01 66
    0x800c4614035500488054a41d48400000c502c03505407641501d5001010100c000c40c2580b0290011030500d8880c0d96500c103802c05c11442190f00c440d10b8002c2c0c0c600d54000010f041c031503100b80d00d00141c20078001d04c0e002a03107681031244d00d40345622033f62160000980100302003042c171040700195055144600d90551a10441d00c003454645181405902508900540944140401040340521482d40400030204c918840108840d070412a441548404164098440c1d14004c0c540c003a2520099044400780e030001d001c1d500c5207008006c1303280c5008240610000000566a44420300100d41d0007480c440da503c15080780381480c1c050760074a5868030035040800c0924540c4804040780e044469121000559281000048001d03002500c006400740d0308002d04802c00d510450401c60146039140c0880c5c1458101000c1903511000c20960880800c0007445152120b042c105000c160b518800c2c8000558002510482044071205644611032136000b20010700c0950740031a0440350307490901c88903e503a036160 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 782537850 1250 782536600 782536607
    0xf150e1f050f041e0c03020301080706020304031203020c280b0c09240f04090b03061803070303051b1201051c050601030f02120604060b0f01090302011b0212100203060a06030c 77
    0x102e1618050766444c09501e180364840f40c40e40014a02041080c07006624a680c020041d410a010b406103a026088001070711a0001044404403540009000d00c0d04040c984190000c1d00300b9400d802031406000c601040401505074100c02c40e5014100081100c012420304000182c4001c00f0505c42c01c0b810840b21502d607442c1d40d80c044e0702c44191131346294004c4540c5004a09070240583ca40402940482c01003448003094103c8001c0200c00c1d03086948a83d00c1d0456080d0000b90b9986c03038121904200070b150007280c0300750801c507848003d0410264803c410203c07690010751000524401c05003009005000500e0000c00c041c1c030f0a0407030303486d00d40000c6907601c4854440c0030620006040c11503059008046451b04807004404c11134010542c2c1c0c1c0303482c00e4100305000d40b0b5201003240c80303002c0701624900e066004000c0c0070141c940694030503070b200500d6660100f0b11080440141d07030001250300112203e034410048845500c00a090140c0c890401a003800385480168001c10b050504150520f0803644e403 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 782539100 1250 782537850 782537869
    0x12030e1501080c0405092d010509150a112a0f0304150302090a030c150306090218100c050d110601090912082a04050108090c01120f150e1f05 62
    0x1001c85001800740c42d6526081e2410081f4000d000000c0701c03159861001006d22151200755640400c000d000d80d980740810684c443c401050003201003441a000305440321712650100c80380001c440c04262a05445140302c40c024030400244030034032240052001720380801032051941620491006606141c00c3c805024584820844104200340e408981164541e40f4811410001c60b005041603085a0710b410ba8000042d00410407900403908001001030414518400c0f907050b4041c1c2000b10b404041c03000100000321601500810400c40d1203080000441c100303121141d0781402907207a208552260051550811805a002c0c459051408403610041158101100854402803409207040e0355080546507201548881600084800311803480c0c07100d070007a0060082d14000d0302c610810741c0e0340511203561244128101400076a0041a2021100d0686c00030b2800d00c81c20b440100340d20081064680c000206540540000203626041c8840032a01407600c00350840d10303980044a060030300c004030344d4051 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 782540350 1250 782539100 782539123
    0x402130c0f270f0e0c0f1801122408010b1f140a080109180c2106050c120603240a1112040204060501020f06040f020a0312030e150108 59
    0x103240c0741d00086103900308000c010007000ca8001c41c80e5458595880c0503510f0f0351030207880c08503014200414020100b54044e1107000d001c00d00b010b85004080b0340e00c607003040c400e002c4150500c0300d026440a00e194150181c0325004400c0140328001d55180162045402c486520a404691505a1618150700d0f00c3c84060324421090080a00c070312105d007800c0b2410700301200d4a43c4901c0f004143d001e005584149114101c1e00300800c10f011b0411880903c111000155400a00d02540107030f04214103011042000c1c4000302060003030740045c046841e00b4040c0c4100300c50000301020700041010304082c00c186420742202c01a001081041c0c800d010101391800850900d14201168000040404943c0e41142050040f180d000681301c540325000c52000c1e4130300b510100d200300d04240f0041401d5200003184065868990000d044070f4440f80c0f9200c114422142d0240d811034404400440410004803050720801c0143d40c0001d00180280307007040c1404080740082d00040700550040103e00000a011340740c0341f = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 782541600 1250 782540350 782540357
    0x4032a0b1b0c030f03061e0916030f0603050601050310050c070825060c0824010302030a0609050903071403041410020a0b130506100605030403140d140402130c0f 71
    0x50441c000c1c0e4681c00d010340796000d0041d110006900190000e0341000c0d5004403001da49039040d0360003000024403500303541000c1503082290311002030b996141e15060403000040038280000c0340020000d641013a070f810350b001501d2070f61201c3c0041101c4c0c1001c02c403824259100038420499400c02c1640d24800c1e206240018245c0c540101d44141c5100c51032442240300f2840000c81c51001a29107070100290007604400000f241c140030002d0600201c058100540208103d14a4a01543c81c0010346c002e400c040c243c40070b0244d45410200d08204284500f038000c40c901e07170055850f444545010f070700a074500c040c85c0100350010302c010030070184280e0a2454002080702c0e100e1009600c075408a10b05049480040c050316502d07000c1c841400c6c1d8060f242c03000c250041c0240d40e0103039904101000c0080d41440754030000f800c20400140440e100345840500200d0101c0241d203049039005000c02600c1c54902580b1002c2ca4000c248011880c00c91003d104069000000340654506500054489021103d121062 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 782542850 1250 782541600 782541631
    0x7050f0c07050405010e150118051e060a020102090a09020f0712030f05040819030516050a1701060801051f0c11151b0705031c120f020304032a0b 64
    0x8030305101e010040c01c00580104425a03444101c00c40c41181034800c81b402c0e0300a02d0b03442d81c00354420280011401c21102060020034542414440303000c011080c0440c0038600e4a070501015a03c45004150301d036003581c00940c80304071540070002c03500559880200a10b10400c0060101e00c3c5450036030318501d8012030050b011415540d0140d02030081e060144980c00d1902041000b0060010301412015840c02c290501040404c00250100e81060301d502001500c880000400c0b14464802803481c0340c2c641c42c06201500f081c5507060b011800a0300040003207190b0100501040c1854031003011540c512420006506207502d0002e004402a000301078404650390480415980760405802d2034050301c403017020354411500d100a060b0740f50451201e0200d0003800e100050303600d00010b0718130481d4200c007007100d6030f0080e088042d00c03040101050203207001d4840c035210803849001e00c040d6106502035116207003180008040c02d81c20821701d16040e400ca481200403030004c1400800e0380e45d030001004820228 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 782544100 1250 782542850 782542867
    0x30506010602152701091a0612071503090b09011b05120f0a330e190c0e090408211005061b010903090e0114010c120e0604080a1a07050f 60
    0x2401403500c40c20030001d6007001811400c1104404080d20b64086402d211f000c2911070000700040c0030303056a40351001c1e500c5a84288084100c1100a9400e800a814005022036150b0340390505100d0440e425041a513444000c02c01100082c5500440381d07030309242c100d14205441800c041c4e40e81e006051102006042d10000f4004580b0307900c140e801544200c44c5204c0038660461810841030801088000c20604400021394940350522a070300171500340101c00d61a07007410b00020001c201401c2e00008100201103941c03055116400681c0c0075030302806215075140040d0540344184415040c3d14614030001004001d4116942001701c0292581210010740c2c0c0d001142c4500d080c1040c0841403501540b07098629010140c104043c5c0c01155a00d008003806d0f6a0380700f1510052801a03c501d03404220060306c52400101c0341606021042d00700e09100c414000c6820200d540741c0c0054005050a03032180c000740b810310003030310707020082074503e0310184070240381c000030040080c0034035002c1d56503180d0041103019 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 782545350 1250 782544100 782544151
    0xa09030615050a08030406110a240b0a060507020306150a12050307061a10020703030807030b210c0f0405010b0a0302031e07090608130b0103020918031303050601060215 74
    0x60003028010301e5a41d240751130703c200d41d4580d40320f4801e1401140c0040803c00c08600042140c007071181c2c21a000119076007086950b4513806880241844c005a901d0401005580d24410060040c015540d102e0b500d800c11441418030341038000e41169500750b045420038405a0710344e001c00c415a5a0407030049040d0301d00345002c41ca180038004005145906080072440000003c11110b07514080455402c0d111160720007042c2e0b01c604250001500083c0f0402c0041c990600a812941001034058070042e10b8400d646000e20300484030002c0074015811115003440e843c9440c3e4565084080111010869949000d8094046120700c541c0402410b0700800090a04454526200403c4050309035190040c601158024a518410300441004c6003440c00810350400351528140d501d607038014a4070b0b130103900719000c104583d04010200f44200310810340c0e41c4051003042c070240c16580c051f08202d9901c24114038005041c41c0d416080740d0708545c080080c090b0842c4680d100e69811a00d049481c1059030850086c1e507 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 782546600 1250 782545350 782545391
    0x6111f0209040501035c03060a06092004140402190203040e150d02040b04060b0d1b03020a02120a021606080f0f0903070605090312010e1b0a090306 65
    0x1107a00c20f2030400000140403600380310903d144001c0ca42d803108040050001650300518958621141c9503020f8070282d06102c0c0320303d4580c1c00c100030310071b41c110360b003a140040e1a14000f215042c44841d110300b01000501c403c4c3c09401c2c07003240301010f0a440030b41c21601c40e11a40c040d9101c1c2d8518120144003012080d181c9034107ea8601c094210325a80d0600c8515001c0e50701e0f0b1040c421501ea6140007000640b12807904400c07030041e52002001168800015000c00c0b000d00703003000840c0d5016070307112710006004490701c00400064840480200d01494421b440c1c501e0954403091950a240c0100049100c42c0d50208101c0d80d1203060510701c6454040c80e00d0304a14003903d5030408800a510804085101604840200d100b0724070380c90789105030390380c50ba264810100c1c1540c9140059009011704000035106e600030ba684011030500b1641002c1155851540e01da50a904c040320740e1000601344603e9030245001d009041421a01c0c036403034015201d000030500700c0c0c140301c05071009503038400c07110001d050300218 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 782547850 1250 782546600 782546617
    0xd020403140d1106010e06010806010201110c070306180203060f09010b09040b16090e1801110d0b0310050606071e0506090715080603031b0a1403030a050106111f02 72
    0x3a060806407900e055441000340403900205040620700daa003060002402e505036140d454210a00b51100720041d2000c2d000903140605554880280c034182403072a0014011904803800105891861420950201c5680138202540307180700315801400358400044641e0441703e8881c080c0595a5400029401840c0244c1341d80d90004031401400180202e98201d1802010403100000401c1e06610041d1405110b92041001c41d0392224000345002c1d03001c8407003071082d042e000000310302100701c0314516805600c20880d039041541d43d0000541c290804000800424102c81c004006a00308440007440320f01401a0081100710f4070780c000030a0151400c84aa00d9607030140442d607e50505403c030300e880c0e41407400358045070741b41c100105084c0d520075112715000320300240180d0318280040c070640d11340181200f0581154030800c04070a0006882c1c429860000c0c901c000039584a0520308054010342d101a806801006a00820b40050580101d414600300c0c000920901500c5400d0741154064000d9024 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 782549100 1250 782547850 782547863
    0x3040c12030507060e0a0213050618010b03010f1d0c0904090209181b0d08090f100309050c0907020d031a0a080f190305070b0c090402221403030a050d020403 69
    0x580c90401d60090064400e1500c82d9400380810420a040c650740e8000c44000654484044240e070026802c00782c0c081a00300101800d0040200ea1080ca600104142a8405d008130b000000c01044210b1186032502c029240011160000a51605901d582110080c205407100240080c110f03549955513071020313542c0369010740101850320380100030420f5445204c901c52140c1c0980100011101303014401d44405e408010700d6403a20152640f1400c0c030303d4000b0105550411404464081d003940c8031008100480c9842d03030049852409894082c0c1003036030003410300c2c0c0940c40707800c14003020703d401080304003d468035450006010640868000e0004150900c030940145807144007041c146000702c0d8001c45c0080f00780840340f442c0040d041080c0120403804024000074809c0c003420000070000c034403280d001034a00341c515040141000009040f41c3c881440900c407060001440050031204d0b0441e800200808689520385240d404042916032003107024402c200180002c1c0780c00302c01115416280078642109 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 782550350 1250 782549100 782549129
    0xd030c023a08060a090513030c05070317071118040f03120204080312013c03080d090218040210051c020c0f0709110708070326070e03030c0601050603040c 68
    0xc1d8003414801003034a0300740c0543da08600c0403414040c0c81c0943e41c000c1c91104030a5114510382c1d1070446040000075000c845601404500101142c860480b40040700b0348116220360718021894a10300c98100c1c1c0d003100340030341e6407000417041180a84040e59031007504010b961004a10354907007180c0d4103c0841c0211201d61000c1b41c04219a00004064100700001001d40f00c0141d80f0703001e4140d0b030001e01100c6140090405015043c01c02c64100c402072490403200040d0b920715449076a0205190080c2641003e030642c0c44074030030158135001244803441d00014086000b03d06080e004100502021062002030107000106084182e491003245010b80c00d8081c81192148450b121160b11030f020ba100802861280351000310744100584208038400c0300c00d0001d44d00e41100c030703130719425241c004078019410f200e030301040065030b00c1c02c0c1041c402c0d00105032141030b40c00345003401029000316107400c042d5000e6402480300d288001c400040485c10b640b01224040d84aa880d0b14117250302c0380007500070440003050017 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 782551600 1250 782550350 782550463
    0x1260106020c191404110f03010308070b060103141f0b040e0a1410050f01030b04020c072309040b04170703050a08070507081206011b0308090d030c02 66
    0x49106040544202d50503034840825211007400008140240180c4d012440c42071035092900b0790006100342100c00103941000707150f0f00c400c1a9604240c2c41524401c90000d014400c0011401d20164024003d0030300308035130a843d0b9a00c6821082c01440341d40c03800c020144403010b9952140a0100038000c079400b841e902c0f41c031205200702000c030603900440c400b814040c1d0700e0103603107450660512600741901806070203840c003410002103907070303480805060650b00c5198402c0c94070b41d070004050302c02940c0c1c0204141c62508070101d0a00b03880c0124032003011803240280019076119128240c0040e040748200301182c980341012840e05000f203150f0b24500c000002d25004064100c1c0141140740103903201c5840c03e0303580b10002e0769140704400700101040d4003008820175008009040540042c410314064008185001c228104000928002d90200d2036400c10842e0402082124040f04001071800344801b2201c1100603682e41e4a81d003200840240401e9441c003100c1000c1c46c0036072040e501c1c40e0b24107013040d02e4 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 782552850 1250 782551600 782551603
    0x8150a0506070501090b090c09190b0a0b1e0a09030b04150504120e0319080c430f1a07060204030b16020d09150e1306060815030304050126010602 64
    0x3c031101154401b14040000d142c440c4041402c0001d104050b144814544c0c4e4102d16510f00d448555584000075940e17543e902080d10350f008880c001c0d1141c055015622041c5100345141ca00d540d05c504450560108842c0c900c541e401900c0000301ca42c05508018184c55510b01819074003038100f02d80007841c1c509801c00003446460b046522030080b980d122500d00050305004c1c161149034517540c0c83e28511241e01e031039000540381070061400403409030665418005101d01a10481060142c080301d50301400424035030800f0100d0303003800c01c14030720206810107841c1249207030480c51107105003051101025050b001201490003141c0003180c0c48413045580b140c40346070803d5a444251070f2080c01c001c9400410101600009143c0e0303500c1515103408121900d4600c6c01c0c00801380d41d84d40c2100300501e01e2807845a0340c45421140030241c1401c0c00c0030031401d0400c000107042110080000c184120940b503040c2603610007108440540d0b10078602130f201410120108240203c00c000e07190301e5050b00000000d501c590 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 782553956 1106 782552850 782552861
    0x60228051b270c0d1503050304080106060203090315100306181509050714010e1809010510030c05010e15120919022b050f0a12050a08150a0506070501 66
    0x811460041002901b42d20466540d800498281300b4401c0a0007a10094a0360384000c508003000c000c006035881003510441c020324044200840d0044000c0303902d01e00695008401441140710b07019101c580618050030540c0c0d54180703140780c10300c0701209011b02000c0b650000000c0116a0038000c0c081005a2203501c2203042c0029075074900126250340c62603201c18407551060300f40c40d11301000348500b960f200520041c50410031540600001c0c031030006600a0341d01c2842c140c002400d03c400402c200e03600e1f082120240c00f901080004804610300382c9903203d113901905858040301c0e055001c90191a900e10029408070354011039070085940901035036500341c000151110381d03001030f464040c02c040009201000c40c0e00300100e1603040c003240d000b08140d080158a400d905e04528048000e00340704018040c40c0e0342d6144400940100e0752500c1959020307241c010540e6580358490300e4024003d00 = true := by decide +kernel

theorem cover : BRFrame.Cov 782374100 782553956 := by
  have h0 := BRFrame.cov_init 782374100
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782374100 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782374100 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782374100 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782374100 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782374100 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782374100 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782374100 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782374100 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782374100 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782374100 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782374100 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782374100 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782374100 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782374100 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782374100 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782374100 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782374100 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782374100 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782374100 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782374100 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782374100 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782374100 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782374100 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782374100 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782374100 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782374100 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782374100 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782374100 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782374100 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782374100 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782374100 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782374100 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782374100 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782374100 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782374100 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782374100 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782374100 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782374100 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782374100 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782374100 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782374100 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782374100 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782374100 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782374100 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782374100 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782374100 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782374100 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782374100 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782374100 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782374100 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782374100 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782374100 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782374100 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782374100 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782374100 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782374100 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782374100 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782374100 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782374100 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782374100 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782374100 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782374100 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782374100 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782374100 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782374100 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782374100 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782374100 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782374100 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782374100 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782374100 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782374100 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782374100 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782374100 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782374100 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782374100 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782374100 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782374100 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782374100 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782374100 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782374100 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782374100 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782374100 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782374100 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782374100 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782374100 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782374100 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782374100 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782374100 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782374100 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782374100 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782374100 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782374100 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782374100 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782374100 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782374100 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782374100 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782374100 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782374100 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782374100 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782374100 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782374100 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782374100 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782374100 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782374100 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782374100 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782374100 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782374100 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782374100 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782374100 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782374100 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782374100 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782374100 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782374100 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782374100 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782374100 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782374100 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782374100 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782374100 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782374100 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782374100 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782374100 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782374100 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782374100 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782374100 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782374100 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782374100 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782374100 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782374100 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782374100 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782374100 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782374100 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782374100 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782374100 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782374100 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782374100 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782374100 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782374100 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782374100 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782374100 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782374100 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782374100 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782374100 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782374100 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782374100 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 782374100 ≤ n) (h2 : n < 782553956) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
