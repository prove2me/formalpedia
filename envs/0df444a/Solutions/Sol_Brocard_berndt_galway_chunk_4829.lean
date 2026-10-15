-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4829
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T13:52:19.858678+00:00
-- url     : https://prove2.me/submissions/39dd9bfc-e4b6-4447-97a7-bf6d2b4cbf77

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 868345323 ≤ n < 868525179 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 868346573 1250 868345323 868345333
    0x3130210111b03030909090d030b1023040506040603090b130512032512110f04030204050c070b0f1f0f05060a09180c090f06080103080a09050301140103020f0d0302 72
    0x1003042640305031441d0800d0080c212410456503200080b00040212540c00498010b9402340001c2c5415000e000c2c8100012034100210042030303540242509400450001c100300d1040c0043c0c4810980c904950245c58050605559070740c9443c8083c0c0500811141152a107a1010000b0001164010401006030b07001d805042c000030038250300c440c1e540000e004c840002150b0300c82103010151a0610540c04121604d44d90107401c0491401000c03603c10148404005008018243e9030508400407102030340d0341281c0001e070390f454100500526004900005191108034030611038000680c4800714460a9060021501d4000c5407228008044862146403844880060b00344120b207003010241220041e689040410300755180a414859040c0c8100c00c00c0700d550f036089462102e42c8c001e05072800380400c118040551460aa80104003003014030018101e00c0c0082103c10040e0b00c15100c410040c04010024881c0f00d10415442c81066000e00c8124461340c030945480340b00d03041c00c648421506070590041c007 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 868347823 1250 868346573 868346593
    0x30304031401020f210708010305030a030e010b030a0302070302121b010305090a02090c0406030f0b0603010b070302030f13140d15020c0a0c0b0309010605031609020d0f020313021011 80
    0x30500c4190520344007155020310200001d101c450000c1c200b11841d040010801d0002810300c5080044058034a10401034120010b2011400010454400041d513180c00286158400030040c0107009401840341c0c94014900780c0c070141507000901c1c000b628021500b98240c8009444e0300c0340d03a03611480101c5100c410001c0c40995560082c1d0020782d228143c0c80075191040850b6000a1103084116102c070010b22011034140501075041c40b07059200d49000d10100110110130002481034081440313100e152100009001c0d0030540f0a00c1902c1010b2000c113005600d400d01040844815801c03400754482d0200381c49401c200c24a0a00c0d038074460b503030300090003152641c0c41b28070070006544802581601c0e0320072000d034200028940720002c80180384c40341d4000c0d164107020f070819003500c41300e50000e84280e102040700d0010440502c42e280480b5400540140c0c0c0c0d003001c9007654064020fa0b07181640551001c010043c0c2c810301c55507400e50300c5100300c45020034505500300036904010f40c0009400180d000041c01 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 868349073 1250 868347823 868347833
    0x11b030c0312140f0601390b09062409060d05071505030a060e09030d02031510050a14041409220c030b091f051b130e0a090203030403 59
    0x5800309020345440200d0b4401c040480c1d0669882c480c07903590050900c401c001c5001d8501460507001172007440d00380c8200c05402000d95042620f000c04102d40f5107895400c0e400c21060240780b481d000d03440184a940c078a00381682c0b50319140221003003c4103244554146007045086a1000400c040c0281181d0075505c40d10107000d03409014000450b6188a6540c1c0802c20304d085480b2840454195510a41d403481c02040520036604141e201014000c914800d2050030709000c0240c0342c18100d4228010386030703641d02001c414044070610241e41c1140c00342d4100d8400a80c00801407406800e00d40354150154155005201584600d1084481000f60011200214a00901764540004280100c0ca2291280010801c0c005c1d0000004440c642512042042040390000310f60b1b0388441d089024010707c500f0008003682040d00310100107021991840051946002200325006d03441c8205541c54941d00c05030103101c5208114051808000c00100c001a100400d234010900d240e907000c0e020f1410230303146a0720 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 868350323 1250 868349073 868349087
    0x5060310061d031213051e09070e040501030b070201051e01090b03071d10060507110d1a0702030a110307021507021518090606070228090f0b010e011b03 67
    0x1000c0d2640081840d12a0303035001c004d00d625000800e107050359152408140e4400604d51980318601800c000c000d5030441c00500360003503140e0342003580c01048130703070768900201c841e0704040b6102075001307140c10008000d10100c8032079548205699002000381c5d49903140301d0f101000d0540c40c07601c2c00e404da9100500020a07903400070b42c004080076048070ba0040d02c40184640e0059045406101c035a00c4004000041807c001c81130b0090070350342040c1d032900035607071651010400030515183c0035045402c02507080240b807a00450409003011a003061300d08015900940301d6001d040000300189080301e10107482e11022040b22640c5500900500c80340101c0d064254042e007200b8401e23a4131420030341c01e1020f840e00030310080032428100d44121803221545010841325050160840c0d00401061210500503251446089854640e40e80c0c04010b01540d00608508404203030032030980141012100b0303c80e10003e03042180c540c1800d895036154001d19400454150381e00c417149480c40080251080086802055 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 868351573 1250 868350323 868350347
    0x17030417090a1a0711220213150f030b0411090405252c1804020a080307050708010e0d02070e09070b2805030603100216050a03180506031006 62
    0xa14100c07103075103c2d00c0c3c0b07006400c0c0c0ea0020001c0480013601c0c034104241003441324054041210301d9454010070b5090207410100300000e48019a0b40000c90909425000c0807482c010480303003040141807040440700902080c1d0701c01022002c40d043c075800440070b182502a948103004403500403802c114030070040101501c000303041e5200c2c00303050f0310000b100503044480501a5800c0d980341c1035000030480a044100b081407030f07040708404032080c2340d0103819601c45080c0300d900d6074640b941026a4070f541c00011040403d6a200340080d220020f000070810001160581c22a01864004c01c505455008101d8461111101c400d0050b001100148480c84122800c140c101d050b1b0411501c0306a2103641c120510780c8400c044c10310f00ea20700c00200803120b1802c1c0e80421040001d1034000e00b5410b100020959814100244000d000d8000c80c4010380c3c240b605249124240d0042e08030741c13601040f400c0107410744129540010f10309400d030300007150500307103642240d000d40d171500280c0a51500e49007044803072808000c = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 868352823 1250 868351573 868351579
    0x4080c011b0f14070e2509090203100914060d14160605030910110901120b0402070803040c080a0c270c08011502010b0a060f0c0804080a1703041709 65
    0x1625520200e0403500c1400b400501c14403640d1150003000d1000d0303141c0403039540055007010307460081104038084880c02920b02251450b007440600301c244400c0d1241c107035541000304924800700030002c800d41301441c00b40c1114140001004142c0350300c0c054508290342120081d07002001e90010400240100b150841d050918030140c0300c1074081c00f907184a0010b096401000040d00c0070060103403440090043c80e0704a4001c81c0208050088200e960083d80a507601c0581440611000030b002d9500581105c141680003c004641c0d940d40c80c601280b032078100380c07000d5887c881340101c04110304100050505002d070300308402548941c60000321217041c065503e101d4940c2410041c1503c000c0010b40a100000c05049d150442c8940c10078403181c855201c280440000c6a0401d07a003284582c0f41d080d080b2064070782c03e2070812001d4000384006d8801d002440002804c4900c00540051103003070201e404401544120318040c94440d6803a00ca0b0460301054a0260210303007030004400f00c101c03c01d4014480c2a03009 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 868354073 1250 868352823 868352867
    0x1807020c180f0c130803040b03070f0219020907090b0403080c01051e0c0a03270209060d03200102040506070501090201180e0708091e010e06180712020d060615080a0204080c01 77
    0x2990174103066400650000c3d01300c05020061012054110041300c440742c80c0ca2005100031050844d8054800300c03c0302c806801200300b04042102c00d48038041c280060000d01072072076611a03407490414155070050342141459481d00000c80c24210640309020308950100802c803401c2d88400306038100035803141c584581810f560f111100c0c4060642c0c0c80c020911260800511414403090050150b0302200816552040c50301c0f0202c0400260003188466040300c525401c00320901e19811128020f105039004640e06c4480481c1940030000150001c940c3c0da4800c0c0c3e1154180c06250b41d1011000c00e030340c012441664410000949510311a24250340d006500c9422180070403188403521700168010344555619944444040a00100408c100d54100e1968142000c03451046000e240c0c4400060207040d52007003c01c04080c0955440b0186501c603103030400c2d420003e4698400002550110310200f00010030500c200103010f01290340300b910200d07031020014201c1e404215004507402c4800c1585450300b800c1c1 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 868355323 1250 868354073 868354079
    0x906020303420306070509060a03050901060f081c020601060c08160804090e19120809030c01020319230c1b06100302090a0e0a0f021807020c180f0c13 66
    0x200c55400c0b00c0d40e11000c0b520340b4040c1e0300000381802c0500c01082d0000303004003002440c4a0b51151412207442504a00d00001c1d82e464003a0283d02600441d80702070141c1440a070701090880d808144d40c280d0304510b41c18010540500d1605980380e0900348a00300204480644c600c011610101c0241161b01f40300d19038144464195590000790b80141c2c003e40f03001940c4034503250526800b00001c5141992055500340c507890240c4d101c0040e08007469208040140210104a40410800c10f07500300e501e03150025511380c6030440e08900f0418140768454045070078480d010190f1a008482000240d0811264400a9441c4251004286d10048119100980058254561a0040c8001402084001292106c1502e5401006070f1204064407040c40140382030540e501803540024901c1c865640030194078000e00003400003d8400e00c00f22600d40d29090349070200100590701041044450388201e8010362240300701003495200140031520300c00c401c0402c0000c903008034104e80c081c110305107007060b0039070301161 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 868356573 1250 868355323 868355401
    0x10b0f0d060b04052706121c081e040b0c0a0c0804080303010e10180f020702130605031002070305040b071103120723030910121404120906020303 64
    0x9500c0b46414040108043c0440d1030804a104460140c03c41d40c0c0d20804030f450703403000101034064860fa04c100181a09015040800d016524144188007840e964414841c0c401504502c800c440c6102e545170508200034020750825007a50040d50000345880c510b80d140c0601d406160300110005060180b031481d50f20010b002000100b010f0407007600910348a514041030185500030182600d0b401545094042c03158240075558080100003802d8042281c0c000b01144000900c5106806034201c0703a140c12402100500360800000c42d00160112804d040002c1c0b00b20302280105100107000500c1008208070b49102c40c000b810150b0b0180e9a400203c030304602c00079143c000b89907084103094102091903814805000c1e85550059001e203904040801201c40981d128403480c3d003e14814214506c04130003041c480c096820141c0c5521004101561010032040300c9001d089902f154144403080c40c018589100d509907404540081e0001d609503101c02900075014108410100c607051010410804001c0d = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 868357823 1250 868356573 868356581
    0x106050703230705161202010f0509041404060914010506010e0103110904020c06010f080a0f020105070f0219170309010c030c060e0706080a0b100203090d0c05130509060a060509010b0f0d 82
    0x283c13141000b080e1040420200e01d0900da610b5102028008000d500c100140c1d030880a030043d0350b00c062800ca41c1e18202040050f0007001005032903100754500a0401042001c0c9074800c840040c05400103107001c403801c07241c99081e41c0c021035801d03000070b00d5589159865400b0b82c0050f01c1f001d103034002650504080002090407a00312104034030450340450300411509603c0588440a00741c00400b800b0451800e44a01c5501d0106c020024100000095114244020100c040700c42c25401802c42d00c00c0481600c0e60203e6161030701500301c04200e039901d420380150000003200c12880d010703103585230b12383c03026181500c01c81d01403041a1445c2c1c1e00e4400400044400b4022040501a90703107500e0703140d042c001e005000301c5560105041c00b0350003202c032b4008043c2c0c0004c20742e60030103c200c6040f0b0384c580c118600440903050561005801034006040b510005030540c000611407002c1e03600b00d5009580e410040001d80f401d41c4a41d6030070100b24801400000a100000d0003080d031784070611494040128840f070215 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 868359073 1250 868357823 868357837
    0x90201110d270f180f0c02160605030609040204021606020d091202010c14130f0e010317030f070e210607091413180f030504081005010605070323 64
    0x70302044442c88a902e401c0c101401914a0180303400c60b442c00c0c03c40050304400d40e4000c1e441041c901908040c020742841c0c106100c500d0f200c18041c056285028400303580d540d440b560342d070039004405030080b41c0c41c1d20075004d0b01d11805000f4060f12a036116034080c0700003540604242a48030002c51108008140c1c140024003c2061202c0001401a154244440180820071240d011641003011125440f64032012005001c50005803e66846001c00e801008800459000c45030601c5c3d1460005865180e001c1968100c031b004001440e00840c03501c80c15056840100c0748481410350150100744224031882202d03250f05809854441c4408446550b01409003500b100c0008946c0001f04108180e680400b04a004140000b10308002c05610340001c2d40c07060346e40e080c04034807a94035400c1040008070884200140ca030090b200300f0703811a090400801560160080728858481c40c100c4102c401014441c01e0304803882e9690792402c00b44039a0f821646418013104030100c114855420b001040140c10007003480c = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 868360323 1250 868359073 868359077
    0x402010504170c010201140903070201081512010b0f06040609060e0109030c090b0f01090503070509090a0c2904050f0607050106030b07020c0a0806090c09040311010f020a120504080d090201110d 85
    0x1d00c00e20f00b00020b096404e9000c0d1104121110420310050343d1001003a01c1c0314550900307211441d640d80c588144c00c007040c03000449a200001c2803e60b02d0a040660012100100913110b413401d0051080c1440000c0c07041c0d10407100001c2c141641049824401c02000d045c2d0001403614540240c1c0c8c0791660841016507801545000d80e64480d00300381864501402d00030540c0a08100741c0c29840c0100103070304d03403045101c0e1a004070100000515500340034443c03524081da01c110200050b80d201c1108406003403140350050a8840ca036502c071007804000c0010f607011907500030040d03000d01080006200c816041048100c41c19901c4000c0031000038900e440641c4103d603158000c01c84000007034100500d940071a40144c407190018428440c42c047d001c02c4103603080d00e0a03689a4403035100d51400701d5041c8108a1404030551030000464000061900248480c42c52941c030343d00781242e541800012240245c9008058600070090300e00600c4481e00030307502c05801410a181441e40c1c1030041e81c01e0504142c1e440c00 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 868361573 1250 868360323 868360333
    0x26250f060f0305071806051e030f160203070b010918050a082d0d1d0601030b0a0e390d0b010509010f0b030705030402150a170601020a0f0803040201050417 68
    0x2007169051240030b501c0009403070424a1028281801515000039014050400800143c1c40d050b00385410031248085540030f800340e98a1030503061025100c18140c4918908819000100741e519200205540105800080e802d003564039202140c0e00500e882c041c420180142010040702245080c48a400d001d8003a690041e0744000741d03442450b141440300b002c6441c08440448a00400c6a02c2c002d8504d010728045000030203414111046510000d240e070800490b00c9190004410020b1031105207001d4807058005010288040f10016120311a0048040501200d03540445030040100b00c8120320b601e00c1d41c6243d00c6090ad50000c144040750707150040e1807150302c8600400c59400d010440b40e004210f92030045400c1410541c0303c41c034030700c009020a820060048081030955441c5e441200f1100d460000c0c040d03a500034400c000d80103041d500800420460080d00050f1194000704869080e15030001c1c100080310116610b011450700041c000b81d04000080c44040f4046041e0230361036040040e450014a = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 868362823 1250 868361573 868361597
    0x7080f040f02031b0114070c03080f250204140402091314010e0f0c04110d0b1314100e13060231150c1a040201030b091026250f06 57
    0x50300d01646c5101080c1d640c142000450702141104c0042c9040e41c1e80103012540d03441a40402024501070010a10181452814a4100f41040c050b0100a1520a850074040140038008108513804100d60180d00403190900041241320f03020b10402059109000b00d40702d002080540c1c600716050039264540b5a4000c5607003291511040040070304644003101d00f808428031b5140d281581d07026040d2510341050301e5952601c090b43e51031655461114101c0f10070031640c036000c0c15480810350161213008080c41c8036240454000c1280ca507240c4200c1c16881094100b01742c3d683c420000358810805860148000d100c0c06000245107040b41d11105481c015900002e4240514503064180c0c40445600784500382d9030920000b04401c02c001032030158818561495951400140c014141603c1004e50001d05802001030701c07601c4c881c241040d900d420031030300c24082030310504016803030344103038140c0e030b6603021100f0030710503a65070303081090341e0b114014019018030382c0c448910b104040a43c1101d80407505062000f = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 868364073 1250 868362823 868362827
    0xd020a0506090303250c020405041505130c05121c051b0f06060103022b0e1005090303040f03090e04030519050703090b2208030310060807080f040f02031b01 69
    0x2507410402c0c14010f540b844c1000001c00b00d41202e5103400009036049162500f50321401444010f11060300900140040e1410345801040310840c0142c150380e552801010411045a20101d0b02000ea400f40458040e03c2c10401007044a40048104850300c0c861010800300410300c0441e044200790300ca48507540ca8079901d0910190800f0302200420307031940303c40c8040d91617502c000b42594100c034003030034016981d01101001c00c01d5403221801d40f102c00c0941624094441c1c070a54032007440d60348401c0c141c0c0c44000f0307a00015010707a1302c283d5040c2142d500a1000c00c0214850440410106200b820560701903680c032040d404010b501240e05401003400031074001000000d481801c541d809507458800c1c900305095401410308109401521203184000c030308101030840c0111120807030404000e02000165903040400d40c0d0381d00c2119000041480e02030001251805030007200c0c041c01180d1151641940d07040800c0c103110000400c1685c020340107925120140c1c400740454010503500401c01a0108640000 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 868365323 1250 868364073 868364083
    0x1505180a0f05060603030310050d080f161518110d05061303031b0206190b0a170d020a0c030b070203040b1605060601020c01120e0a1407031104060b12180d020a05 71
    0x4c142d00036001002040302601055460a00780c3c2da045441c0e261a11050070311040d40e005d00188000117030340005032040d50407074240f80641ca443c441c0c191410100480c04004083e1404000c100d50140302c4915000c0001e80204c400b90180d54002d0481e141ca00410380b01c162603c0d0381078490b0140122081089402c1c194540681c4045100c44000101c044800300c5000796550310082c44d107034118001c110568403035200da40100c89540700c018681c0001e5a100c0040700c00010803e0450140381c0b05960b180425280003042c88844142c0058105452610710349a402462000800079021400100004030300940131102030004804060401c1980307002c00e2034007519100c405080507042d907108003041440d9a0f80402c80c1e41071351318400d02c00b00312121800c40d002e01d80459014010489001054a40452840025100b04880c061048000e14007400d80038002204d03210f01480c926403400b0803c211a0320300d0a50304982011980b013016544290a00d1554185071140e580500181c02114201c01032040401c1 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 868366573 1250 868365323 868365331
    0x3060c04060809030406140702191e0e010602071e0806070c110102210a0c02090f070807030506010e04050402061b030a0e011416020604030b0a020a08090a1505180a0f0506 75
    0xf00031840c1604002003c0c0c08038031140090110294009000c030b08648541c245540103008480400c20b05903162201100600e40081c41d0001c0c00102e01c0000880000360141641202c10a80241058900700b0700144030b0480e4081074540d49461240000414103000c03c07059105408555446010304c00c645070140d4248a00200e20f41150700410995907290006414030010308484200c03ea601e10503040d043c3d890300d4a80d94080d6001c0c01440800c000160032076145031143c9030590b41c4200c0d03075a4502090b402c5800682d0141c0c006203181d1003080683c00c00e0b50225030818001080f0310300700300d00c043c8440403c3d019249030301e00e2900080b503500d09036600140509070341802424900c103e0030322000382602600501e101455154030324040102903448183c111000303190046281c4000e032901d500000040c1d80080c6d2000d0018407100006041074801080101020b580300030b0b401c0e403800e18166484007500b8083c0000311510715070120301205080800c500503809110b0701c400781b0000c2042c10141e0074410014 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 868367823 1250 868366573 868366591
    0x1014120601031103100e1005030703060c08010609030503070b070504090911150412021e0d050a0506011d1504020d02070b0f10050904082b0506032a060f0903060c040608 74
    0x21091002d201c80802c200010303100b080300545410340d182d42c01d0b0381f40080281d20840c0c1500940c3c0c80401031160581020b0484013158942c0c00ca503990f1014212103642d483d100c0a000e68100744410320000e50441d54240e00104203140644c281900c40c0c3e00c01c000c0b2507650008451008004903103030a01d00b0b00c1000c0035042040c17104140e003020b140040030b0a21543c840340003440391a6828820854850b04036007840302c5034000c0c0c004840341603d0f00c1c1040d926000494280d80c1b81c8103450000900d8042c0c0d0b8003d03000114400240803183d104c0d452040702d0490710f400030a900c141c09100d06244860503101600c02c4501410b00f080b01d909244e070801c98004006450344485084403c2c0c0bd01140c0c88140d206074000713600080950b03883c060700c806191842c91000c16101080c001451440c2009960f421a9000301801c80503108003003141c01c0d00c900ca030b10000c1d111003801d04408480c00100c1c03400c00d000d44040046515400d00d85801c15000a040020441c1c0000e2030480100381800000d034003541c40e5500400da5 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 868369073 1250 868367823 868367827
    0x405090319050c070611030c031615090206190225030308011e1203260a0e0a0203100b0d020405010e011701020c0304141801030b01080f0c0f10141206010311 69
    0x510f4040381c072101980180e805010300c81c10003040481e000c10459840d0800a001e40c0d4540300c0081540c0d030507085100060f00c44c01f9103c481904110141e200e5a9500d83c2c0c010704092506e0490b043d00000814a900a00d040d8099403000901d04212444141c840807072b2030150068150841c50040d14603070040c0c0007000c50798280c5040c1c92510341848880303070988020358100d0b4100c22491508651010201c01042c0500001e0605039496070107d48019014031460141804400c0c5981d607050358030070302c10001a40c50361001c004403d44805661212018003070241012140b001d0135000320b02641d500781e002021449045004000074685400da1200c2400100005d511b8080303503a00060740c074011805841c20101c03115484a10079512181054030f2500a003030001c0d2150307924100034402030000d104881c020f00500c1c507410008240492503080499000b04602c0d00800c2c0b08044c065102c0300412000705002259a6072200100410060404244180d1440500d4035015000500341c030f4140d22940035040e02 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 868370323 1250 868369073 868369087
    0xb01060e0310090f02240c160915050933100c050a06110d1d12130e150a030b040210050a0e01230d02041d0702060106120605040509031905 61
    0x11402c0e003c0713115404480d001c4200c8041d20490300d29507070040503142107081c00104e0203803510010440c034202c55008003142000e00d80d03070340e606c100381c0d007000c41c07814622144440140150301c0c007402440d030004c1440000c084600c0e603402e0b07a030308030160024820550120382e0340340c0324180c070304007044002191092601011910f210740c0d032036a9490440300d00418850700d80c900403030f90355002010360301c03419617002e070034000240b4035045280c0c14222200c5a00303890080c0c202900270403514600f06c0390000542c02d00715403a10301c2c11407424008540900728041080d140f113024007081d80c44140c4400610301420b422802c40c20300d0300c104004407098041030401d00c1007c0c02040084d41d04581400c90400080c204210034014503100386030785c01455407228240160101e0145c070312803c00d502410a0700d1944860b80354040c0d00440103000340d1411070f81c0c1001680940300500805100d05040c03c0712034601c0d50040740305510ba800040c141c5d40129000b540560001c220748180c41c80c1e074440400c5e100f201d0305100d464480 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 868371573 1250 868370323 868370333
    0x30302060a0228110f06190b0d02150d0b04050f0720010c021005100e04080d1b1110060302011d0d0c090204050307090b031e0a0b01060e031009 63
    0x10000300a04111070380031984a66212083c40403105903407207012122060483c01c8006010302007030300c1e150300d200c1c89070310040d43d0010000256580601c404406050701141060840e00252003821405500072090300d0b02038005844205840046214813041d042d251540340c00c3c41021220401e156a21450070041806809140e031101c5640003009880c00c0300c4014024a0143d0091201e100000303465841c04e6960350b1819404155070603241c4001c881803086858220401550005500640420303114410106000407200002041d242500070b40102d100c442501c0c000700c2222010a503a0302043d02c09582d000100018011602c2007072f0b1114007000721900316000200412210b00744086034504103030364010707159612451040c98960010803800718584562051019411910500e4000c0c400e584010410282c540034518100901600911042080e80c003501c01000794150300040790301070b20130641c020400c00c410b000d01070701190b1150f4600d08101d1040c5481d16641c241e0b005030312443d2501e0807000038 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 868372823 1250 868371573 868371583
    0x3050106120e1c0807020d050c100c200a11011e080c09090406090b07050c12070624030b011e0311011707091d0106050d0908090307030813050a030302 66
    0x2071424000540e0140c0803900c03440c105102e140e140c80206000c0f200d40c003680c2e0282c0c2d5907100752855400d8440f0010421000d40707150250305543c0c1250f4200c801134855002c16a0312220320722030b203840d00729580c9190303010a041601c0c06d040c08459a030084038029080c080c070b1100c00c58209200303103440c501000110a150000c0c0140c41d444400700220000411800031815050b1000484020700c2000c1c0781c106490801c00030015480105c90990391440001c201078003c0d42962100303482000584141c1034850080001c95002d800200c84107075803010304441e495a1042d9840b003107191100380d044980e0031800d00c1003e04405920002c0206112401021500d00d01c880c1d030b40c2126480102e481e1101c400b0401aa80002c1c210301490b1000d10300010400940c1d4020340310011a001c00c10305a07008503e256840000103801d0040101242c0204408a007074038590307010307004490080045a048c489003900003400c0040c0740c0e0054810f01404101c41d5912894024150010310046940c3d03164186035517006900da03 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 868374073 1250 868372823 868372847
    0xe0a080d021e03100f1403030d0b040609020d060914040f0f0305130905060916170a09020d080a03050601020106120f032f070e090d080a141918112116031203050106 72
    0x410342b95001200c554035140c001c8805050450401c1d5110548224200b0080c1001d2241043d51410503922000e00c810050685000c0c0da002001a00000d045445854080c00402411810040f003005130910680b0a0307001c0d80d014201242c00820390341020820403401e9000a440340d420801382c1d0603030148c455000700f5039403d00095814408582c4e5540090b4000504200a01070340003100b0052a03c00c0000751001013a044c0f446440c01c014a4450000490888030300d40a01242342c8100c9010f100030400742c070310b08224140329180214004202c0c1c40c250000c1d040d0141d01d8240c0d5441d0507541c101401091042d80084c105080c4202c44070b00d88249601c4d942c51035020039009100140c008600015666003000f00320110309020300c9014180aa000050804071612594140740350441c203200c540e07900700c5101a10707500800c044404040faa410801c08841552440480c12001d4032300c14106141401801c2a41c1c18004c032990314a4079500781108074501c81000403003014a89001404456001000c094070 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 868375323 1250 868374073 868374097
    0xc08090304180e010c0e090c1908090f070e010f050d110d02011101020a020c0103050901020c0c01030c230403051606142104060f0e0a080d021e03100f140303 69
    0x210040b0341c0c0850340140005030000049500b049003800c401604000035030100c0c01c00f074808420707541c0d464900741e005020300842c001402141982c00d00085220f807820a4120004c00140c40045030400e61a510700b0380d45034445070805079543d00401c900c5a2802d46d1100409065910000300380d21075486140c0303c00c000d00e1061003910b40442d5070065921031400c6603504103050003315074840803030b00c0180d5500007044100340020b041900141403403d041c02504d01e00c0c00390034001c080103c0003400642c043d1800030b500108000c56421904414552944045052503140b16429955411820807908210801d00a25125402e0340c0c01080340942c07000d0600e10450200b0203850b191f4480001c1002e0024010407942c121004d00014401405400e500100143c07421800c10402565442c0c5071503100c11f84c010018050600c20b00081107080001c0d0010b1107d000604103142c030045a070801298150019920b0407522a0124000d000e00b450220308035019180b022010700080c0c2a40f00020383d03a101d69150810 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 868376573 1250 868375323 868375349
    0x16050d090501030b301501050f1509040b152106060a09060c060f0f0b0a2301050c1203070c05061f0314010605210c10050906180904030903060c08090304 67
    0x450701081c0c2e040000300f9140d0161b58558844a50403901207a00380240f5100740001c0b00c0c60000c61905030080c41408441038021410b0440b42030802000b02078440d4041c0d0000b0b48454a0b040f40c006040080030100c3d000d00d080382c2c0300200c890390061540c00042081e40035003020450780c4c440b550400da115084130660b1030088200c5406183c0300c1e01600c2c40503101034484d030500c80180403d080c0e6402c250520700c420b48088440c00c2d9aa502c04203940e4041d05a6104018901a0410154841c0d802010b88100c4c10f011038042d400100c0802b403c42d070049405200003044607200c0300801400f808655041a0300c030000784c0758030a030b209600c0c150104c00e00c401441c14a00c1c80ca80d4251010a4000380028100206100101110000b5a0250705900741c40c012440c0140c00100c4a0f9180140131010441059901c071414103400400b40001a80001444207414a4100b4600d801d40d40e4403420911640c03007030b40c40386403007403a51600c50299146d03040e002c0e0910034181d04008800c0c400000b5a070071214513a400d00 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 868377823 1250 868376573 868376629
    0xa03060b090a0e0c0c03040f0612060e0c1b060a02070b0a050f0109020901020f1507023c07120f0209060405070e0907031107060501030c1502100c030216050d090501030b 74
    0x3484c9214030520181e003800301207000148035480f045032204450f207540311407002c49844211142141c280d4003440d000d01d540b1901180c090409480506070254208035a006032812800c40c1c20b1500c101110710303000c4150001010400c02218103040c0e81c10082040781030000b81001701c0800c00001e014043c2d6071107240c0c0840d10304902d0f8801c12040700d81020800588581d142e11a016410202c4101c0701c80e0058420b218140700c8103801c0c5081c0c03c5a49a00c544203640708042c03000d40c0c116490040c0072011072071261042c04a110f507580c2c1c0c03500b040c0714812004810400070b140b05001c030520700281110b20807850501004a510740000d400c0c0500d0008880020325a60b640c24150000c200b005201350118801003440c10402c2016404241078a026003400442255214440702c940d01142c00401c00581000c0d440111f840c2c4180c020403100c00c0d6500740582401c070002c108004c4001080003c1d22694024019104c0303ca400040c0c0ca070182c9002e2800340002800f02c404a0410f00c00c0404505880b8a010040 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 868379073 1250 868377823 868377841
    0x2030703090b15030c0f1807110706050a02070e0f040609021c06150509160339030f020f071b0909050f060f070909020d0603170a03060b090a0e 63
    0x2039000550160381094103003403070f494280388004140c08041c0a880741e0fa5580805160501d80e46034180801409501102c81012400103150406401d2000340101140c50b01200c1000703100d00f2029206690b00d540d21032298100003403910107250704c8011920f290f8002d10000a041110840e80f0580250000c901000c851002c2490075010640c000403516850320751404214003034003c5075a410150811002070380c0ca42c070800c40ba007902620b01d400d03412181128100c0d00e40c0243c00400403e01140c40d030748841d09031500300300f90081d81c4a00c10751321150f1548000f80b038560180b041d401c10b0700c00e4002c21810702220b40940400d45c4155100a411510210b00c250013002001e044c04015100c440424014003220b1300d004c0c0e543c3d013401c5d12241464011180011424406029002d211380402c0d544d05031840e1034100800000c7d8811030085040a07102d170700106c003140650040c601c2c982d8446401550302c00b00c0c400300a04880315a007068103e21001c00c800a110340d1010394640650b900d00d1041078582c1c544c2102 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 868380323 1250 868379073 868379081
    0x80c0102270406180c18150801050303161407120803010312020c03031e04030606061106090c01021504230d02010606051e0c1e0109031409030a03030e0a020d30080a02030703 76
    0x3002c0c9070540104004141d1187e800c1280c0c0110540d501c40c2000b9076202e0042580341d00502402c0510034950303929003000305500c0d42120b00054116016039928940f6a00d554500082c1c0300c03420364040500100401c100205520000ea0140c0c04e4400780607002e40303a00c0080d4903031141003001c9505224580003099800908000c9800455010004001c86650340ea009440c0c884000c04210365800381d0400107698010201d1100410b2a05901420400c2003003103096000140c082c2c070550301c040191503604030a0065654000c44011004000c0c422201c18410080c2981c00503040300e82040014407640b944e526001618410429480e9452a00d0342c0f00c1035200e03440d1400f1960403040f00c149114003000e0000c41903100303548060280e0703242d10010000c0f10038440b60f4896045055050b0f444001d904011034829407104d1800a0050f0a507000f00c40700d40c001404a040c80c0c1801d0707400341505045100c40300ca40caa044209079a440119903940b042c01100034040c008024144000d940e00000015122803207644 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 868381573 1250 868380323 868380347
    0x512010608100914060a0b0a0e1c080703080411031603140c06030c0711041815021605070905070206040309030b2d16111207080c0102270406180c 64
    0x110800c012150704c0300d1049001e509494407805481c0781c000110b800c6091104560b00366409440c0d600110307400d581400104a510304100c0b00108580d400a000039144400030b045c020301950b074082e401d05050030200e0701c0b5440507039840c2c82548140300c075400248280340d400040ba60049a01d081e4000c05011550501c11441012507006000004220300000d140000d03040042c09454820241d48036101403104a51843c00c1500300300603800b058500064003642000c4504191b941c0150800700c40108501c50800180421606900012014040c0307040301c3c440c065104c1c1d9540b0081c25142029140540b02801c2808060030f42101074002540341c40e000c910844206a5020001d400c0e440c00c810f084400840c240d81510360290079035034200515210300010041d0000c0c1c1e00c041c11611140310091400c03a400b4400c07c440516090121460032031081c8080e00405540360106000031010200c500c642c0400103012520403031600301d090044034001024040c0440700058000f51000d2002c8080d140c04107440 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 868382823 1250 868381573 868381589
    0x130c0f180501020a1401090f0b07120203190e07091802041b0c140708030d0c020c0915120c0402040905100915060e060904111911030708090a0906090516051201060810 73
    0x698207404100103415143e01c90ad45503900c00d24226142e03032050043e4031007525003c0361803c030040c1d42d070a6014154003890b003100208085400e5940d8482d928012703600300800250500c102c0350702c10404c0d402e06000e031010128456024800e100c0021002602d402d105a801520810100b500200c0001003005008040d010030004c9a455102d07004c620005419208a000d0041c0280d00900d411030601100b21405040c0858845201e044e0700e006100358a42090000305061256003601070302c0b0b4840b480100040c0c607280c4004600303843c050907000c00304c2d9020750142d0b01035071414035070341c080440d505088030a40e06c891034462001105da80c0098100c1c000d45803460b51142c035110729103540903407640081050618034092911003440800003581d04150500c00c58030550030401c03410000034590340080800300c800030105004c550310b80300c001c07040b15419001141c2c0d06179558144101c40440607221282110b02d8030f0194070b42010748400e0441c0c0e0406100d41014000e180f00803030030070110401a4030140000d0 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 868384073 1250 868382823 868382843
    0x5040c1e0b030906181f0e070e2a04030b13080427200712021c09060306230d05010b100207032618130c0f180501020a140109 55
    0x181455140c000a03900a07860b1080c5c040300f81c00c04840407640b140244003521031104000005030584025052072030342c504d00c2d4082c50304c010034001c0d21401550300903020032480094400300340c040d00a40308078200440034900341c1400100006004111410340c45102c0070740e111340056240c03800d0007290040382c01040d00c05001c0600c42548542f0107400c55191003400360180180b141607829003070146265884000001010441e540c08150382c0000d0b0108180580b04030740c1d003d800e100000d03507072160502c204000035070b141404001c55980f601580010b8104041c0c1054200a1181550300c180b00320802c080c00344001d541400b05102c001c1d0b001568240d07014007000303105403210100a403206485d000c129030321002100c408400074124401c03172480e0030616000d54070f044103403240fa54821200188903a44040300d45414001c41045024010400026807a00905484c49000180002d440b484900380e004c0000c20041145070380c0020500301c1250808a0914100f499121190240001d000003804105403 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 868385323 1250 868384073 868384081
    0xf06040210172e120506061c06091a0403050a080c09101b0b16081303020601031b12060e010b1206130c0b0f0c1c1707021f0b040e0105040c1e0b03 64
    0x2126031404c180314809507641ca9892000700641070f07802c0503c3e507182800c2e64070700d0800103816a2244130480d005481c610805044203050040d07190003146d089001034008501034000540000784182c03c046484401c50800ca1440c000c00c001c441c00c8041007042000100801d4400500c041c0b5145130650085500350662a200ca40d460503138000614030030010740310500040d00d070005d819011031641c0e4984c3c040d0070a44d185444241c00040e040390010340c06500e0f42170015801500b01484c1d1070052041201185001d1400b1100e400c4800d9240c8180c022045c940b01000603540100e43d0725400b0046d8034002d08075901d1400c201400035050342103080b05440009801c060b080c00d110180401c10740480c119440e500081240760005a00c4c4114040420034a0448602c2c02c3c8401a043d41d100107148115918500300c05801e0400051a4040e5200c0700e54030300100d4103508150090780f030b845003402c1c002e002905090395040000120380c440c00b0f52281105141c0d03508521a10190030040003a83c032a95242c0c20 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 868386573 1250 868385323 868385339
    0x1104110c0703081804020906370306060818060a0c02070503030f03040c0b180d1712060a06090e1503030f04030c060305062704080c0f06040210172e 65
    0x40045540101d441001c1345241c82407506008036000c000d0b014201c07506100b80c044110300411880d0a002c007250a030104000312400d90b0351078185280125540c00714003949001c0d000303000036102422601c1c0c0c1074071082c104ca44102c800a07410f60080e19140002a401d02c0c40348089050440d030380c10641d81230100050903a0006105809980224046ca010040e82991040c1a160500c1000c6040300300101086802d440d9141000c5003042607406549881c40040441018120503445152000300708050301c807c2c408182804440c02001c0c145509101c03c00340d050400720a20004014100344071040040602015038900f401034640250100d26020b44968491400c0030b40015540160000240b40c0070004029141241d180d00c0311003007094404008100008a0b5a080341c8024400d0340c000508001c40340d5054802c00901d8070601c0c0f204040e00c004d0401f0303c10072100c07100c42000c035020412000c1c0000030f89000c040d28580c1041e11086442000461742e44862a00c807420200c451010070400700c0010052 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 868387823 1250 868386573 868386577
    0xa050105070804020307090903090306021c0b120712050f0f0f010e030a05030601080a0b090a0c1407030206011205010906111b010507050912010e0a030315060c1104110c070308 77
    0x510410092005a039144000c4440900c01c850103549a88032020801804038260b02c00c085490291804070a090b0720703501c0b0340041e0b0303100200000f0a40d03080400124000e0300d904c50403e19070403c03960078403022038130200180d40f80228040e041005249411b0042009403c018128803081030b4401d40301c032007000c20a515141c00c40010710004039400c101040542e6403022007210b800d031a02d5151a415600c594004403000324005140001c45603a64001000d199100c01d032032480b072a4180c1000c121844034400042074405000030002c0c1400c801d10004002030b4001c1039450549414130b0300145801e4041c1081409000396010282c022880c01d28640e00603c47d48004003650140c404101d00c41101904a2500703d442c01c95008002950521000300d0515182210703041c80b0311400300202e00103021061950030441d06540440200b42d5400d6003944142c1501c0c4444000c11060410101d28901602c5600c0f5001d10303031001510030b903542d07035131804a910128180c800000c980c9088440c501c1d00c1c1d1504003056 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 868389073 1250 868387823 868387843
    0x9032508070b030112030e030a0203010f05011d01080a0816080a030902010807050c06180307060f06030218150904290604110406021906020c0d030f150b091009120302 73
    0x41c0510000440c03240206401c480c129011000d00504900302a2001c640c0d6001c008880c03940350050400c2d110140c0d409004a402c00c01d0b2001c030004480d4584018500c2c3d81100c1e00801240903000f4004002c181380114021090940004000c1d80e00c0318040c0600346117410161000700b04101c08100051041e0381607120000142c0300f07890307056040d15046001d452500a08500001c5580907100003001c19140c4420b002c441c2409008403030806a281d680d510136540f4207680102d01540d14003040043d85000b10a10410301d18205d03d0384a1810b00250603202515503264003805040f8100116082200701d0b0740440180480c480c9140391703a24590703035100c900d00e401d0b00c20501c074a0070504035401481c021800c0758115026038004185035030fa490303418002e000340c0709000d4540d56400d10014400b241c040c070064600548079500001c2e507000001c148400ca552050340503003668003100c0c090001c0002c1104a4615410031103140705400d01a400454041c0c080303811000d5010300300e442c040c1c1019000180c0040d0 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 868390323 1250 868389073 868389089
    0x51305040320030702040c051603120c0e03030304170403020a0303020a06050c031513150e0907120c09020c0c0a060201020d052208070314180319080f090325 69
    0x11000c810301200401c88164034030340c00c140c0013046090b00529080d44142141e0605007455404c2140035400003110300382c0d03204107801044000650050010052096241428460510b10180c24180e00420381d00d020052004100120000c02661426060f40946004540c010291442182c4a20b0000c0d290f140484040300d902f0300300000704a40c100d4230b6040d0b911550b040d91070080c1011a00d07042010400448103014845c903565041c015120241900c1d01d4090f05150310080801e0400c40100303850010245c0c821107449000480e1180003d030a02c40792012101c0007440540c8a040e444456401c1100280c0030725480b8900303034400078120382c064000d0300078601c08401c204042e40e160380b14000410660100c20041d5581a6030400000e4164005001d200f806450110180258845421178541c0b18403d1040301009505500006d403404101d00f40f0b140011618250b2a0890740c2c0d81c450290140044103100c0b0800403404201946040003198600b0010250386c00420aa18071a09010a6030303024050b0 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 868391573 1250 868390323 868390337
    0x10f02040312080f010b0f090d0b1303021618050a0f0c03050a06121a07020727060801020a12020c01090821010605040e07030b0d020303030709090e07080709150513050403 75
    0x24980340b409650174101d0782c01e03003203491a143c8140505040c9610500c50654014a405205e2005c40c103251081e500c03581c25046600b00c80b82c0135047c041e01c1c0100e20341d040d500c001d08924041c800c00444d510030485030400440d0100d01a21401d80000192010b0390301600b18901e4030b410450110740c0358208501400007181c08028450715041206c01c03e01200f00003424005c1802d035850700301c07608041c1459101841d441580d140a072580d042154025101c00c9004c014600074441c40080c0b021403040d000203003000c1008600d0300b1903100014240e0010a0140c50240c1c2d800b16000c0d03d0000300f1340000c11141ea0141c2000e603202c000c409000c11603440c1e400400210744140c07001042a500030402c5600380d0b01d12144900c0680d807081800c8000d0105801c02c56041103c0025100068608102450045001d5107404a0b41420081c1d0541115500321302c1144c44d60002a0401030f614000c2410000c1c0e4841c44004146004408409070602c601503002d03d4014402e91050410a11154042401144a652a11 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 868392823 1250 868391573 868391581
    0xf01050a051003020a15030b0a0807091409151026011505150708090409060b03010c03061214120301030f0c050405010b040b0307020a02040e0123040804030b09010f0204031208 77
    0x148026806001c000d405c00000003007801401d504840c2544003040f0740c81c0c04a24542560041081c602556004100b5030344004014011301c07049001c1c0160201c484108030000b0b2810085440da140105500094034400c80804103a00400841285000e010380100ca850402c65000000c914098101d403400b07140d501e0a8110b080500890004600301d403402802c04a80900701da0f105065940704003000c03181203104008186858840c1c0c00352200070341c041e000c0000e03101c0811381494203581c00034040104140c45d120091013000051020b450039650440120030022403005952803411511308900740300c90700c0200001007000000d644080740c8511940001055941d20b00c20b01c0140c500a000f02079401009020510080d440480070350b50241461049a084144a80124081325841c1c507100500365121080e950303929616900740c0501c520010f803c3c0015280c0b40c1c40310a014001c5000060012201c0400300b104560250450038031400410700840d600c99136480d01461448822032401c1c041401c0f01700203 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 868394073 1250 868392823 868392841
    0x105030102030903190c050d0c1a091b0319080405011805010516020d020a030605101a03060105090d0b1003030905040903090506091909020901140a0905040b0609030f01050a05 77
    0xe20f02540c0f945005609000b030b0a20b5900030010080c1e0b22034100071106840c00c011403003c000d01080115643c860300c4000701c1c82d080119080e044c0f07080740894504044140a01c40c040011200007046000400310703100c07141040001c0c01c007200342101c0600381001c80b070308200344520307080107204480003600c60011140e07610051544200b031314403681e800318800748015000c40100c010a00c00e0148000c2c10400303910416400910303103625581056800301e40d030343d041202d151049079911014000011041b0f43c5030110b521a82540e110040a8030304028010130310b5030035521813251109250394808562401403401c0e0350800e846075100d00c02640040c1c28043c0016440c24144a402c10709500344d910b0648140c2003105000d095441030501640040c1a9400ba00c40c4004001c03102d0b000d03040740c2c180981c1d2030040c0300005107900580980581c450b07008010600f146da8100b40c5110444200b0307076000c66040d0401c000681c1c180140d2164642500a5080298041134190300c242e1003035111400810403a1161034071 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 868395323 1250 868394073 868394077
    0x2101081b091005010f0c060c1e05070b0c210408090405070e09040f1e0305040f14130f0609020304080705062d130501061512050c0405010c020f03030a02150105030102 73
    0x140100c0140c410801d03c455486680900544056400d00c04107080b07440d9620400c4440100040002a0f040c0c2e42c2c04401d40400700b826520b840c1c1c1c5107802030522408d9180c7e1450411f01502c03061008100040810000f100006031000180c0000c04070321282c03401d0700304507000307500c400314041c42141340500046da0035000f010600b00a84001d00b200801e90348590b260044410028004c3c0c503070042c2c0da8918405d151100002020300e911070380d65151260b01d80100c0400c1c2030307050b40041c402c08a01c1c180c816080c1e2a10442c40354030315441d00300411039035190824030000700500e0304180300300b0340004208000d00c4800001001103a220b141151300507900c000040d29543ca0b2090007408c1e9014074072a100c401840d14500b1a00f060030800505c00300d640d20790700c1c1d41c2141c4072544050304070764040c403503214442d0b040300b2070100d09907154409100c04c0c0360014007650103104034020b0740c1c180302d0369aa6402c15034688480e803041c800c034054101da40c1c5603000ba4008e5550b900b008000c0d0440004400007050354201802 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 868396573 1250 868395323 868395331
    0x60615080414160e092e2007330203160807020c06070203070519031a0702070501050f160b220807111503070815030f0d052101081b09 59
    0xe6040183c1402070040c1e1130380b8090058082c1e8440c0512101d90301800c038003512010800d00090403000d10401c5210030a0394160b0510074640700358030200c94281070404080345e507101e40c4580351200490029420042030803072451100c0c182500c0000113409140541e0045010700401411031003007000c00700301203490040071900301300140c11200300750070f290404101030542c00d440202038642c140c1e1500003040d003003150040800c1a1b0405550200280a004440b400c140f02d0b066000743c8840c030b04542c01950340d8000b40304141c100309000840724155410035050303902c1d400303500c840b01185c621203041c04803420071b080d0340500c2842d04204000c614008040480b06415901030300440c104001d40d2102c0009600e5203030301a81015284928038500c0000d407004600c186204c0d02c0d41011414460780d400180880b80c0004c9010390700203c0d51a40e01480000c0d042d200031001d19110750746410180c518260301c03051520b5247c19002141c0007180750388021030000301c181041c0280c400038207000420400400c00c2a5 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 868397823 1250 868396573 868396603
    0x3002030c041a03010e0604061506301803030506030c090103060f0b06030408040305070b0406051803030c0304090e0d03090f0b040303021c0507110f0c010507060615080414 75
    0x410490318508042c0c014180e680d010044010106031054080f07070075624801560030498000008000800c4200d01c201154001c014003010101c82c10050301400c1b444d0081002c24034241d102201c4502d000420002a042c087e00a00500681041005180c402410a481100420f003004002100d0f0304001941c106191401000d40c0420707440c1d07031100401481c0c64015214019107502c40154070b038951500135806035204141c09940c41c0d1440c10000d040c9411030300040500d80041104109075980a42034801030002d0a80c0345444a03413010000e40366200724404442c2d00d0102150000b4918050360108100503010401d41d000d03002d943c00c00301e0481d003001034020601c00f00c0c10307231610100305842d000c81d40c402c2c8242001890059011a01110840b4010303070040170940718410010345039403003103c2d88003050801d401001200900c00c802c0340c543c000903660a04004000c2624014044d86800c00030040c8881010241c22804100004000c040c049034241d8441400c82e0040607042400103003403003502a00 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 868399073 1250 868397823 868397833
    0xa0e10111215100c051c0801030c05100c06050a060f060201150b090109031209050402040e06031c08130305160506220b060126010608150303190503040219300203 71
    0x1c1d14240c4e05602c00407810384091081a00c0c2c191010364500e0000302c0c6d40c240391106c6201e989540741030400c00c00581c0102d030140744d00070300d4146d01ca5000080b25880947c44140880c443d0349005298000b0825030348480c50b00383c0640000903c690b0103500c006410711000d04486500350b205d069a00640c85851403450000308012410008907040e071814200710b00103490310000d100d60701c200103420303a001034100c03035103866001042c000c551400b080107040c1800c10702007a0500440c0c040c0050b00a41008220702d02c9076a503038154000b0140314004850090100703040440c0800d40c58180140c0c2e0300c00856407400c0001280359150482c0c06040c03c1c13010b81580c09820082c15603a540700450740c00c048a241c3d28030640200000300c2e8003131100c56405002c0d000759078412425140003004440d1021400031064002e0308200b1030400c0110200c0b20740c0e00c210501d420f28565035265031020403040070114030600410101e200011030581d00002130040c4a034540180506a00c40c42c024200300c201d40480000c0d031550007 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 868400323 1250 868399073 868399099
    0x80705060904020f190531180f0e0109021503010b0a0f0e100f02010b010507050a020409020d05070303030509060601050c0d0810050612011a120a0e10111215 69
    0x9a0004c280c1108802200380c10004010011400301601e64030301c0011031000f003122001d1960040b81c403024050031022000c0c10041111410b40d41c0f05281c0102800942e100720681410391058010ba2110610a5410407580b203620401c6070003000d800c04d003240304100f60281d058603401001c0a03a416942010743c501c2c60040c100318103803070000e9221000802d00584e8003418110781d98220000c031300381c4030070740b295900080d103d5002400c5403440072419050280a10941c0d0114000240110b52545c1c181e6001411070b55a0000492050201d44002c1403441a100e0110404d949a0410341c007500308141104c0c0e490b00e03180010f4407036024050b088074080d48942e0006801500c540d40d00c580124100800c800c00030303201d001144140d44130f4044d15806850070380040211041000251016841e08900181003940071910034045960142c0b10742e0b64151110b2100c407407490b003844207140760b00d040c100c10440e058034104400d000ba0040d804a101040101c80042c02c08105070b0040420000c00902510003084 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 868401573 1250 868400323 868400329
    0x10060c03080711160b07030f05030c0405061602150705060a090b071803080309070e0a090f02010f0e060712080702070e13050f0f0705130b0a030b1e0f060a0807050609 73
    0x3a00c0c1c03c00000d4404e01031950b0035951000e003980058411402c01c503a841c49181405400440b03031a1941040000800800c00785100c40406da42c207a03113003155800d940b60614030b0002d8290001c07102c081d502149000c00d0b400c6204140c002443c0107445a01912031a640b54440036046a210b4038024100080c1900020043d52041d80460b20039a504a0000355141c1c5a8403510a5a0000c03140c00203070b40c1c0400402d000f0901170380c0860381d0203121090180900e091980d11070030a1030804500a05001e08140100506401002c000301e01c110050b08164a481250528261002082d135400c0301040b552008240c103a4404961070055a000c480710640341e4496209002040180c014140e8090094483c0303404202401d12810f0350101002d0300811601e420001080100c503000b20700c1d000141d180031071650309a00c608041c03204894201d1b06c4d00714607944010801405210280c1140314414a110401400003142001e071401030000340c40c080095911455660381d1003485001e40c0340c3c4803400b8400070595207 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 868402823 1250 868401573 868401587
    0xa111515040f0f050106020c1c11010c0503070606050406060309050717031b010b01111b0d1403071b05030a08090d0807170c1b0603060d08090a030b10060c030807 71
    0x2890250000441000400c002c10458494407800203c96440d04c00410405504014a40702c102080f80c102058621030078800100c01d00036038005000c0302c0c0c8640d90100607801481c280005941100a4954503a003a103004d00081c0510b01541d8803803071400b0307004030f16144030344205800194400b00070002ca41c180001a1001c54981400d114644010041c42c040080c102c2004c03503078041e600e0004034210384904009840084241d50091040d0720001100c81907150312000000d9030310090b14050003815050400c60745c440c41015858030b89203c000342c10400c1101c0001288c6403000d249201c05030306501c59013019213030000d0800c0034026030030502c00fa4021749807900004009a00c1055041d01e068115074030710150440d441e1404000f04008100c14540f80030600005c3d60b28170140708280d810b04c009600240c0740c0c0c0030141c425070003001c1c181100c0301042901c0b011210b1084008040307003003c569a25259071203030f10485100c41d075a02c200c0700000d01c42d4041c5507040c081c940e25480ea40c18079034540da0125260 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 868404073 1250 868402823 868402861
    0xc0804030f1211220b030603100c140a020f0c190506030613180b13020919200706150602030702121504030e09070801061202210106050a1115 62
    0x1140c2c0d2043d80c1694406650b00808190007500c1522544002c10a841040040c0c554400d1101d080304104008041ea00407580251100e0303e07142c00200e140c510a01140c99418907a00b0862060300020329500c040e4000071a480d41421103400c41d460840b5405c203005900c400c0401120f002141c0c0c15061010b46800406964011000390100b100015045120350603034241240e03a0402d58241c655040c00c1c0201500019400401443c0020040c1c0c00303030340410a0203200400000c0c1c03102945035480f5600803140c00c11000d0441c0b80e0035500c0d5545404d200ea00c2c2a60081c03004560345464610312100391030308411074104842054001e141403040325000d00168442907101c05506001d030b6408602c40020b0811001e0065000c2e41d2100c030000b50701c4050080020010b40000140302082d001004102c2c1c0c041c107141003000f030b084405a2101007803408160400144122450130180b5400041006070380440a8140c00d20503a841003541ced88104c0c45680c50712611078038840c240010000280407541c14812414103 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 868405323 1250 868404073 868404107
    0xf09010c022b2f0d0c170d021303120e030f190312150306050c03060a090c02010b21071a07080a0e030613020a060f0c0b0709030f050a05010c0804030f 66
    0x70f1010922a00c0c0d403545040380c5190b002503101880000107001002040380c0d40a99040c4160100055200c940001850080010200000040030040718074142c058840fa2010740d9110b0143d2a10ba18003481d00c6c4505200c4600009c5029035107450502c0c0004851500f4150344003d410014440005a08101c5450200342c040c020100c903214600c541500c2910700c10304180140340601400c62511a003030b6400a00041d62a4030103100f030120700e0381c0f0f4070411f80403036500000c001984a142c1c04164094003a0798003060f4058503c10501c501c48001400d07601010780c07a40d00303407986c0e180c582808000c900030b21300d4010501441800794000180b0020010005104203041c08200c0203400d500182c83c1c858201c900d02601802584104118101182c4032809027209042a03030309240540d000600c64180c14034098083e03242e001c08035130b0080c050420007014582042079040d501405043c09a0303203e00b90701c8104c1d1a50702c0c200b0043d120911400341140a241c0c559076104101e4501141212407140803054110 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 868406573 1250 868405323 868405337
    0x120d080a090f080301140a06030b030d080619030b041b060c14162301110a03031a03030a02030a080717070810090f0f0609020a091a040503060f09010c022b 68
    0x800318034200051030090020040c0b0b241120f0b40f00e8240500c425588d4008824141007220ba082255800314a90401c8085481c1451041d03031450300040c200183c1e6400d090520b404808007009010340c08642905c524060104002c00c0304022070540d903040c04d13a114020025059000c20b0001801c0710b420420324034407038401c40b480c0d4074892400f00c1e8071410303035400100003642c40840c1c2c08259a005854020b03031242401c021b0f00404036845842d80314494000001c04042ea43e0685160300c0000070740308031400c20301030304407a00c4000d41c0354040c0d501c6d40440e16010128401c000000d5090b0720419070181100704845c2c4051040d06c48480a460b468006000a41c400f25440000308243c8814440c1d1690b0200c0b188010070683c55130b403422406c4900d80e801c60610140100142c084154200d0342d140121098080407601c0c140381041d840146020f02d801007981401008103200d40129044240e0b4002d4407800020425008604d034240c2e0b4404003521030120f02e1040320740b155a42030310075582a60502440c01c01c02 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 868407823 1250 868406573 868406603
    0x18090c0f0d111305030f010c081308070b0f24010507080a12091b0f05090723130f0b071a0a09081201060f0f0c0605130f050c120d080a09 60
    0x24880d43c02203240101d0032405071034200418a4100956556041804000c00a001d01d040c4024920f2000800580112072440086d10401c0101d00445030b4040d0044034030b03000c80c01e205a005040b02010f8a49010110603101000303841d001901400c450200140c451501d4440990354007215074114401071014044604400400000c10340103c1e07040034030603082003801101c5040c00f0b194800307041c1c1000000a00b482d50602c001e4407000c6500341c10441e0707824441f41d491100001c01c0c1e0116444402400e500c10701007a404151404604588151441c06840c01910b60701ea40400740b16000d071000c06030032042043d0b00c40411410340d050040d08910b020310b01003642c5841b92917401c0150306c00355820500c00031520040080c15401401d01072217403800d00d050b00c46120061030045c0070000048000d840140ea0344046a441c510641070402d41951003081002d6000c110f082c5183c68840f4082040d00401c4810008a82e5001c04600124000807513160800c054449244910042c81c2410049465040c2d0440384 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 868409073 1250 868407823 868407851
    0xb04080c0f15070c05041a030c120a050d050406030f112a24010509090a140c0919050a050c251e0309050105070c0e06031c0518090c0f0d 60
    0x1825940e004d41d0154001ca8508000c3c0000c03100010030700308050464400344205554081442e2486800c2129201030042c90042c410f82055030341240100076100318049080156000b0b805042120400c0c0c0701040120498039069003a507144606408030031200700304500c4103240c040621007000114040c2e0100101e11072003820318080a0020114100c0e0701030221049410741200002e0140c2026140c0501a080c1120704c65aa492a0740006044940302c3d518160424000c200d0421000c100810000080c107103001503405240003240c6481d016803c00c00050300000c3c05005083c0180f043c504a140780400c03440782c034010510001c1120b00c1c04941d0f5400d4802280003e0030240d902c1071685800f1115601601d405000101c50b54096414001d041c0305020204900c401c82d0b1040703c04000c00c03007066035541e40000e410032408008040c05005410341c1443c40d1039111003d400c05c10707000d286c6502c1e401000e0f001c10040601c00c4840300c84c0340100b000740c0c149401000340540445004e03c100400c2c480e410701c0b04 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 868410323 1250 868409073 868409077
    0xf090c090e1918020a06110309041a010201050912040b0d020c0109060203160806060702010503090a0b0405030d0c11030a051606050109050a0f09020a06080907030602040902090a0b04080c0f15 84
    0x1029558210000682c0e00348010311481440c00041c0e00011004541940403e0383c040840c4219420311000141d181100d41003441150b07503500740200308100756042402c00e0208403000a203903a0041d840c0000040c0041d400140300404418000c0710307107040501d00030f501101036001000c1c0c950001c1d000e100340100079000340580070307466205071409601d07854284900c21150007024103400800c0154028844661214011504d80a8080c0380c0b00e5900e03514100348905d80300030242d0041582c140901040705200d80480a01402c0c90a01c105001c1c440098004035030b2441c41e020001c002d9041003055949907809000145030080340906042100c010740c1e20350b002101d20981c024142d07944c5440800014005503c40c85080c81d44604082002d950107802042004000c0d02400f024880f400c4040742c10b95000300506402541e101905541d101d4881d4074490103500a103c1e128000c000c14280402c18584d06416902a03031030280003403100f01012002c00901040382d1301080d40240d42c0c1c151803d001441d03100 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 868411573 1250 868410323 868410331
    0xc0b1e0609090f0105100603111c0b040b0904031d030c13020a0314070c020a060503040f0b0a021911071403150601120608060907050915040e0c04020a09030c06090f090c090e 76
    0xd03c2c2e51b05525005000d000d56102c1c5414490078001000f81740203460110f0b1001444003030880000550410707010204004219055480d80d0200092003044105076011400707040e40000315031200003680f011000c0c103070b50342e1010f9803840d401804410126180c074041e501a00ca40c40c0289070105141c01504401380001c04140d0302840001c0314807400e101582050b580542c010150b070300d04286140380c280c81d6100c4844007500300505030582c1c000441c01c601c80039016243c4c401141c00210100703082003100903250881c07102003900a80540d68001070f041c0d400781c46228070032101501400c17602c020302c440b19560303035001090503062080045400074542d14034401ca00103451014014141400e11102c010318001c0c040d03120b41d120303204000c200004c1c0140e15100040050b015a0301103180f08185201c07509240d51040c4440c0c1041c40401c9038140c0075800f807260b50489004015a050840d100e0b081200d00b03690300d00a00d503507600401402c010000c400d900641d42105145020b83c0340b9a03c0703034420f2002e600300b5030b = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 868412823 1250 868411573 868411591
    0x625020907020d1e0503010504091b0b0717040302331308010506030601080d0309080906070c1a0310031e0b1008070618050405071e0c0b1e0609090f0105 67
    0x20410343c11242c01c00b60304008038201d030b020070f2001c810f5060f00424600c4140101805991580d0654003080010707a400da0f070444913004203a103603c2c3c807028810040c2c0c00089094500c0c03031701d25103d809024031510469082e41d40241400c07142002102e80c1c007029415080303540504200c1000700105400300100038001c003e20a8546c20344480c03800e00341c1400e640c3c0c042c2529220b0340102c8010820031030300040d58049601107041c04240c0d04200e00f1301c0e001e00d0180f2100030390040000900e0070200240650780c0b0080d280c210140000c1413001c0d8419000a020880712211041d484850520100f03811f414604407200c04a6207503802118203075079030501550180c5080c1554403c0d88018410000c0c24030001c400340543e40b60820060f41380304690301481c1000e200740f500481e5560041140c1b184505554200441902e14000700900c2e0588020040400030100f604c0c0415218041684400c0d0805010ba400c01c409030342a801d42c41c0d41c001c020b10344d0720160020819103e800703100b0304074917003c0c040d0340d02c1030000c5 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 868414073 1250 868412823 868412833
    0xd1404020a05040c08041b2c07021f0b0402270405060f131d1203040302070504110304061e060e0105030709110f030a140103060f0e0606062502090702 66
    0x2920522180903142d07002140b05505240000d4002d981c001c20706640103400c0541c1101c81c10b480900009038050641000402e0135501a2016407025030714402050021082042c90440e0340b40c8400b00d8030380c84884c0200e14000042d01c01c0300c02051068024810380710008000528050268800300100c41c1d00620040d00d03c2c614041c0c2c106070340f0b45481160707032080041d0b54000c1000948000140100500c1060031000c84d551b02c01104099040e41807010880510021129800d011840c00ba609400441d0118010b105900000c10f8900300349c06101d0004d00401c0340d0fa17003140ca8a94441000e85400010004115500d040d071403a036030182d0160b20014102004021943d50400702414102504e44e0004a0701c3c0e410700301d500407040500f004855035155028070030358aa4480e0004503025110070840001ea0901c0b000001c820321165902070402031200c2d000801c641c203a110310031511401d00700c440d40d52020007440b2105180082050400c8141d1400540e401040815400142409410b40e0594016441 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 868415323 1250 868414073 868414081
    0x50904140c0901052214190b06160b1b04140315040c12030909020d050114100207090213050d0303020405091302030721060f0209040605060702090109110d14 69
    0x105201d645010141a542540c0039810301e404140302500306080c48415191411001034024095400900d02c800000d0904180381448800c040011014219035012540b134001c00e405545404000c4440103151451041e0070141d086d03c0300e076000e10009004c01001c07a0100301c81004100900e0090000d041c40f035201c0407500c5064002d041c039245801c82180c50140440003030001050040d51124111810386100b50180062890115030034485544450fa1450020a5200b0010503541045050b00d10741440b10640030040d200f000a100003150081002d42c0058606214400194006000c85410410a2035105641d18042280351104107801c2d00000c0d8086020300440c80c007600500e804c5200e03104100d0003190305400080d00c4202900c60004403200c401d001042d07901c402c0c0c07141c40040340c01c0a010040e00c1c2e60106134002961000040a110720325090001c40d10b45003500650b0700254019200c00180c3c1e0a00445200030107000754121420f6130140706661551101d405001145c2010424543c01e60070 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 868416573 1250 868415323 868415363
    0x90703060801061a07110d14060402010e091b030c04050a0816050105120c030a0b032505030708120a0207030807061a10080a0c0e04060f080d1403070c030504050904 72
    0x120303000500002060502c07580c00c1000f00d415550302c06d40040e86010703041c24900000d81c069456031001814a007118820298071203000c0f030900e00c5a4001c0e00e4429541d11000304200d0484001c40300d400b0020800c561800c2aa080c19018690205048041d10303d090348030b00001d4180c0e03405501c01c000c16400701c01d46800080000302410b00030b010030300b001800d04400203070302c0481000c01400c1055030a8007000040841d00306403c0401d000c48098140e0304111407022050307000300c0c00c0c000310042e60780480ca0002802e040004030b04040b1000100070f4102101c40d440ba02641e94803001c00c400452045090200c0840c2e040b00045c56500d20408001480c0c40c111034001c003002002030102845240408103000b06950000c4034964048510140011100d0459009880c20780c500820583c019191200c0800c54001504061050f200d500040b501c400b09502402c80d80e00100f040398410703944040c0042a01c4500136840c4c11115442800c290b810180c851020170b203c1313441210107441d59120f1500e4060485 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 868417823 1250 868416573 868416581
    0x80409060b03012907021c05010b0111100908090a15030e01020906090d241a0301090c05090c0f0a05041d010e27010f1e0b10030911090703060801 64
    0x10441c0d2400d0956140100c041c0030070003503c04e00c03102d80503104103864841404404581143c2c5e8000d2084008203070038040d4494000d08034008035069032802c030401c107003503014a07081d03090066104010030281c00070820280c043c0180740300c11201c10f081409001241d40c0c86140d0b900240088400b494104860640000c041e00d03c10280140641d1040202c1d088545904040f103510b9103080e620840000071500e4500316540655044030b503003942c1c1c01b040303000c1150107420220343d000400342411a070a10b0b08007090308861707102000826a010740b01080040d030401d00d040d1a401034075880403605100b40e4031403100c103661043e40840001000020180260f05250540181001071382d80b13804902d42c140103460314144030103005c800c03050348016000451100c00807000b140b500c6000c0003d201005075120300b500a094520b01a443e0b07403c0b4107108040c03503812440f6614019400411180910617800c0c0c00342c0003800030301c40079111601d040060810720349a806d001401224a981d0010b00c0300e00e001c640718219 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 868419073 1250 868417823 868417829
    0xc03050702060708060901060f02211908060f0d080c0f011e1e0e010b0d060501090506061204121e0903020102060907050a05130605150306030d0f170402011b08040906 73
    0x442040c04c103010854a603110000d041d105035081500c102503001c030003a890022115400c40100117240e00001500110f00050070425825044903101010414425101410100c030055000951903401020f2880d04c01e00c0c520202d8042d1105515003000b42400344e00702a50188c2304010382e03441d021000e03007207010280180e246294080c0c0822a90b40566001924010a40e0003001d002c1c0e215454000c070a0020b52100c204080e0042818145560900d4000003420091069a9221b0316083c0043c40b030342820070803550000051400c030360060340d4640d82c081d00070344490000420003071007041002200e891040c0e4078000c075020741c480d03240140c81c6100080ca000c1b0028400c0015800840c4100401d40f41c900b00329040c1d400c201da01d6074842da181212500100880d5011a81c0301c50040d407284940d203014802540544070940030703140080e282000540d0340c03500050034000020094805454400c804448040d08280305140440700702805201c451051860070303c0507544448005420000d204040c0716850003 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 868420323 1250 868419073 868419077
    0x60103022e030b031603030e090c0c0304031e0b0708060f03011503150e010c0f02010c05090616050a05060115030e0a03020d050f090402280e1509010c05010c030507020607 75
    0x208030402411900705480104010040c1a2102840d40b41075070140241403001400c55911001e09580c0d080040031a9003410505000340001c0c40480d04905503c1d044860802400000714901461a95a0b0066500f02c08150604040d041e01302c000040000c8071640c0951420358540f812414000200b04a4403247c1c05510f02c682c0c58101c0080102c0401c451580403203070044001c4010412001e00388000c0e1418140484440d4a00305203180b01a411080e05000d140190b80200841030800b40150380d030b403142c0910103510030b0090050401c2c030b42480c019101070a20520603500000c640d542d640e841c103d07003a00a80c441000554003070702e0865040c410081410a5200203100c04070a544001e9110040b50019200300280001d1900080350500d08480380034802600c210f50380c401020804004405800160b403038200006655204607110b642c0000420074010480000000c1801c030126440d8050042141441401749a0402280082c404c03003c0503a4180c901250360701c0c0003d0020b0616000600c00d0302 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 868421573 1250 868420323 868420369
    0x9030c0d0c06050f12040b0709090908030f06030f010f05150301110f091f021509160501030b030a0803010905010f050102120702090a0905030c1e1902090408041706010302 75
    0x202240c00039940e01c044951a050140e5250b030202007a0849104d581649070000364500140020040308040c01d034800c2c0c20643d42d207140386071101074a009441c0200d40141040c00c040c0081403960340c0342005650040001411240c58481c051125030a40385241c0142d04581c0e03980e010016484607130300c180c150041d0110005c01205900555990342409407100500200b40c0100300001075840e41000d91070700550840413041807070b2080c08003c1d550590341d10300c8600d1013080c4002c0b88030120b0000d149500c503000c0b900c6501e01c441c1000011401004500110b641c90310038014824040b84a05005502a060740071000c134066041c814000054140c5034080d40c115032100036030500d0f40804c4001e40781c406904940f08483d503120b0759441c202400300280060a6030000062a07a014000051508101000d001031f4003542003580030b03156240c10a41480c42c8000c01c0c2c041d00c1900503c2c0400280d603010740b10300300850a0503120500d403034556100e0310b40140194451401401580740818500c0c01c203e02803004c03a8 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 868422823 1250 868421573 868421599
    0x1b080703080d0b060405181b2502040f1a030c0a080618070506040620071206020c011103040c030510050c0405130902030303130204063501060f0b09030c 67
    0x3449210b2940e00d10303051580c48004901d540d42d02c100300c50041c0401070044024031483e01040008010030346410714985d9128041c1c020315055041565907000365100c00d8406e04221880e14024082040c00803a07105680d0081c85811918500c01c007280d0310b503c1b0104040c1c52801d42d060614010000d020644144ea0124007000360140008581d9484001038481c14015000c0c0c000040c40c0c2005904025071000c801709000c950254080d111641807940718080428042c0da4144041d25800c05015640127020b0310110780010407540d40042605000d0700b00001403150420078035007500c1c1c00560341281e81000300b00b800c2050240801c0302501c5016105400c0000f0300381085100114400c0e403107a02d006407030f12101c144803041c01e54030100740203402030b041d241d5900c1c0c1060383c0466284003082c100d2065190440100e00590001403448020703140002c00b0075118062040c00d140c02150702e03100416036482e00001b01e80c0c000d103072610340020003860a01f1511550503100301420f01510401c0c035401600340440107 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 868424073 1250 868422823 868422833
    0x60603070e070c2904020f1905062215020d05090904022110230603060c160c03080a0905042003071407050c010e0d030c03180e041b080703 61
    0x100390401d04900f00010f90404510301040741c00c80400c0028011502c8940c0a088803000d464441d04c00c510888004415103000010400c24400644415802041a031020300990401000a000328a501d05052103400b00c41c1e04202a03c0400d81c0204905801d050b061642e515010000403081c40900d040c1181000c02c0b900125500c544003e00c046d2159026160100e4950011008412807205040c16101500c1001030060017a09613840e0b0b10f4201280e51100000f20071005040b5405040c0c003c000c2d03c400d4440000c01032032900031003c05520b260303100707151800042000d014040198410403281d070b02c2d400c0c008070180c0b03854015030006020300d0a040300707210340380d038228020a1029603142907282c40e03403202141221701c452600494180ca0100180403018440c0020380c20007611001da07191000300500c2000d20890842014008002c03d450104904c0024043c0302d0440401c8001644804000d07a00c0c000780ba801c50007a00c0551744242c91444a0b500c2c013501c074005a000d801b501c0000c0090350b18650322 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 868425323 1250 868424073 868424099
    0x509010c0b1617071b06020c060a0605120a02031515060a03090516050906010f11120403060606031503083f0603030c0709020903010603021503010906050a0b0706050714180306060307 80
    0x40b002c0c0140c10105c14204070729941034400003001c402c101d60251601000420083c0038030b018141c803807000000c540c0152103000074610400c41d4040e003d82000024020382c00039142014002c17449004441c1c0d500241a02d450014010103011a03801054292013801c1a5003040709841007041d14405241082c407076500c1c1e015003d40c00040038600700c0c02d1248940c0c000c5410507244c4909000600643c01c6411a06500e007006e00180d90049c03000b041584c2d43d4100a60486d00503400402e6125100f0000f000410004405409800584001e180900e0b64040088070300c003896070100d00000b100080000e440c8540100c505e039100b04150001c510709428214866034a94007031003002e0243e900001c5804180c0c030203400a50082d079002e0200500004240b50034078050704240618000349180110001b0359140c000803002c1102c180030244d52810400361529409880014140381c20720140341a441d0f807000301d400050840101e9070392070780d8a0580d01d4007014140800508024444c3d88480c10a029a540b0420b03 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 868426573 1250 868425323 868425347
    0x904020f0f03010e1f050c0a230712120e0105042406150504320108070e090117010f020f030a0e071806180e0c010509010c0b161707 58
    0x55103a02080307070040081d0151030f460440d0211402043d41c85055080ea0066a0000c04d400709000d104554824014480c40d000380301001d0001600341000c0181d28180d0b02000010802c5007000514124450720b9082c40d02e0701100106001a4050700e000c8001400c510404000c0c8230b40c00c000b8000f60916032204c1780c949450012000c030f580700fa011841209500303940454000d00c03400c80246960428120040c040750401e00c1540e0b01c05030302070401c612130b1000c0140c480c4465844425485041443c0e001107a203d50000c0c100000e002100c440040c2d01c0e0b64212000f030080c00d02c0020710440c00c0303448140c2c5081d20340420581130464018071110b40c0484c1207000b84c0e94001e40c007440c000307081c542c2d240489107024169130021486007949610028440a1a04000309072010740f108120140040410304080f60300018484002e50030403060000e2070761003034000b0028a0414035240410340c0d415250b042c00100141d41c0800740e042a0072550701c0050300412070068521003a20380c055180750040b0b000d13001803400300d = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 868427823 1250 868426573 868426579
    0x70507260a060504021008040305030106050a090806041518020109090b03070b1306031b020307141002210604020301030f060b2707110f210403080f12060904020f 71
    0x4110005200918151190100c0c101c40040c0900c0c00c0100060405880c181d0140c0740c110500da0f401805515640c0c0100c0e8956613803440c607880c040d003c540303a0700644074800402c201884002142081000a14007540c0200d5011071030a030120510801c8030318502c080c241500c0c58402c8503000d80e8016800340220382c208071020541c007140200003800d1090940015000c0301011405070105488800d03040282d50094030100070b04040200030340043c5044070580c41c0160300412a445c006082000700e5100000e115040b01d00d10020701a900c01660056002c0241805440d44100e0038002c0c506d00c2c060700103600341e0b01180385504645070048400c400c5e041c06028140c0354034001e040d82d154400c07600003a819026080c800010400c08810702c180c0306549440008100c1c140301c110f40100480c0d464000780f070380001401c3c0301100111400d00030025111318204c5131014000040410b045200511582c05c01043c05503a0301c00c409040c2d04640b0b4058601401076402c07004000040e15001903c035a0b00e40c1c12 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 868429073 1250 868427823 868427849
    0xb01063906180b0118060506071e02180c0a180302010c0b04050a1b03050f06160e03032226102a08010602010b0402180609030a0c080307110402070507 66
    0x140e1000400c0c80d070880c100400702c0f078000c000043c41480c0e2040560030320640500902c2000c0e601c208111060041e008050034003a070181c4118a200c010f001078440d800d07c0580a500030492400d0081e0401d04206e030008070b4100009904c010480d8440840c44a00b50840114030750346040d80c000034441a05d143c0700606450550f03003c04c040c01010032502c540b0613401110500c00b121100200c01e4140c200d0303c011202c621945115000d5244049002480741c94a04002d4101030104481203a40c08041d80c0941d07010f01040100c880030b031f4005801d02028100190690106924141000e0f6200315401c8030140b0240c003080d130b00080404041081035490507403c00c08039001d8008082c001074207861060184e10200000202500e041e0440710711412100140c008000c0c01e44400148410b078800c82e08400240480d06200e4a01d0340341200c0a400440d0024044818001542da5521b154048a03008107925610201d01c480130000d91803a0340c412014203079000e42c2443e51079078030240d54107013030f001e1a545400c203 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 868430323 1250 868429073 868429091
    0xe010e09010e0a05190207120e031915110c01090b0105030316120e03030a090608011409060409081b0715140a0305090c031f11090907050f070b01063906 67
    0x1174140e807481701c1c02c158800c5541e10010320380124130804c0b0100401c00b14443c4804151031f072801113150b0a601d8400d44414180b070506030740c0d071042c0446d540d51840b40c4640c0d0704ca2080900b00740e80064107015070403000000b00031149041a10751001e05900a034407a9104104105180c00c41045001e0802c1d4001c0c1a4801c1c1181c10000f41d600714919a25a0703050310000c02c1407903089901044120454402d51600031480e601ca0b02d20b01075074105113082d50703004401034010a0300b60501c2c1e400005d5050107684c0310350030005800d0300d500e80f21196211080350b07980704002c00d1003c0082d002581034500d01d6030070034100007442c40d10300304a2030060108800c03e04d5940d600290b03c02d00300b80b14038a1400c0005080d034001c00481d0b40100c0035003485048586149180c50b1525142141788011903e150b64020814030386981c2c2c1150456003640b0050b851100c0a00070310a2000280c4a202c81030301030030300d40d01c90111000d050300c00d400d11040c0a1fa50440250403242c0c2c58a202d4000007000952280c10120100302859 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 868431573 1250 868430323 868430341
    0x1406060112021e0d02190e0d0213060e04050609070602150612070305100e0601090204062307050a080a030c0804020906060706061d071b031b06090203010c0e010e09010e0a05 76
    0x1840c10304020f41000000342d440e8070030a00b80d0041080d0354625400d031000c1c62000904507640c00a5066040d04003050125510141c90601001c9900c03110001000c19603948404418203500c0f02070742c0413200c90340500c0038868411030902c83d65020b440c8510003010031940240f40400c13900d1002d004140a21a11864103011034024000e20028540107001c0350040d00300d2a1206e4010900180d5080f118051080046151900c5001702c4049075401d607a24903a8001616000e044003c011000000e00035080041000052045c4030344158240101b00850302c40e5094540076080d50f010310144420003001100b0400140e03642c0d210300d074000360103071103490b110745103480d00d00d0050182d60825041e07480d80b00d9005607074103139540c140c03441441c0d240c2d106000c06002c8560014003140124004020a0030300204600a04031541800e0b1105d01032180401c103a0610b802182c21509440c2144001502504c000d820f956002140d13440c8140c420742c0c0821880d80743c6052810603000203825036000e207840f0008140c1c050 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 868432823 1250 868431573 868431607
    0x203151017030702090403090f0b090306041407210201080604200a02010b040f051006020d020c01120f0e0d110304060e0904060603051203100609080a17041d04140606011202 76
    0xd40c003134081c05c032030305150401410380c0d0842e1081807540000b9900100f000c40260003561086000a4000c0c40d0a440d59610f85108c5044004040d0862154640003c1c071a0003003007240030340b449545508022501d61303000040c45a04010651030080707007850a20a000b141040d44505008260243d03503442d1440c00b44128007410362060701a60103420070300700c0d50100707086500c081d01440c819844080e60f07964454041e61102050000788002d604040400403955020710640d200031001b6400024034610508400d00840390b101c60203003401d600445540b81940c0e04205042020303010440218141468418002d00d1040c5400c041ea001740e061201080811895401c03030f1000e035034441e043c0d4540401c124010103503034000712101100c0c1180740800160f070300d000b80c005806444000000d070a82007010340b215035207081c00b40300c2c81e02004402c000002d03840c624960600307000507074151044010b003081d050059103030ba89200403c4c503640142042c40b2481e80c000001c4c403406104001d004d6102c0b94506444a284 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 868434073 1250 868432823 868432837
    0x91b03050c10180803090a050102010b010203040e100b040b1b0c0618060708031315090b060d0c091d0c0402040b121e07051c060f0504020d0e0703050a020315101703 72
    0x190f4040780e0100e1040030101c0506100c0c2030aa404d14000c6940302c004a007038607544801036005d42c004001c180300c0015034444407a8000f941d1a00340b4110340d52880d030301581e94400d5200d4051003501080080f0b104c8400c441e0b10003440281c5006000500d4168000b507020710810b107400390001411081c004050f260700007a01e0105403c039070015200e28002c402c96962009000048030044480d0031803001e0000a8450440c5c07154004442200959951052045100b0004021350b241d8801510010b40407007035000390480d020000b80c9010403410742d016a145400f00c1a68a00e03c900d00601042c8205040703c400e646e02107581c0000700307175207448240e8050403680d810302403900c042101000300204541c101c002031000d45540c90703030740480c0818903584000b200e216004542c0f80344581401000186810b8020f4031846031103840009883e04441000e80c03074040700e40d10444030781d04603842c0c20b0150710b400d1060324072600b0380442184d480d01c0c1040e180c44104d10640980b48502484690000d1040c5040040e1104 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 868435323 1250 868434073 868434107
    0x303011e09090b04020310050c16111201060f0906150e13020c03030114040506010801090b040b0a240912080f120403090e0a060305190317010603091b03050c10 70
    0x540720107080c809010348044134240c0c040d2158200071140e406445c824584100801d08405007080300d09880301c0d0410350000015680480c48240354021036075040340401c82c07103d8040000840c1880d21800f12550025940a080d840345403c170304001101109034140c440620031b01e000240b50403030000082c4c40904d07a01c10118007601c0481c0404030000004011810f03101c4000340e42071800c1b4000108030507901d08071801400601c0c007100411006040d90082014420010b0000c039110305c4a03000f03d00701001d00c0d4448413212100c3d02415400002d1a1a0780464071041c0c07030709103682d6003003160b4074136a07031021030004162a8000a01111801c0ba14007a164000d0482c200050346092600300201a401180242140c00201c1c07030204400d02c025100d880308a83c0d0080c0a042b401100000942c0c00387c03c83c400c01e40a203c0c400d15104540c80500002c14040d040c0354600081070446c608000e0305030310390080700c5150b0500b100e0051003c510002454842d412049410052030780001e02c0c00c480c959008049000 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 868436573 1250 868435323 868435331
    0x5061512040f05072c0c040819060b1c2d08090102101d0706080106140309030408010c0c05010b010f1e030e0d110f01050c040b1b0d03050702010b10020303011e09 71
    0x8081440c0b0508100c01d065601090203545402c222110148154460002690f0043d2416611000c040030480c0380d03107000c0d81340042c0380c52f02c00011400401c2018114410b584940004c46d003044150144603c0902d4500444280d0b002100f25098801d4812070003c6c0c40c0b4440410408101c3c1c0c4204104442e09108a1003481201c5000c5e10680441241c0c0d100f0465a014400e40410307054441c02c0750038100e400594901014dc070030300c10000b13690b91018040320044e000c10400411a03d8090041d1984040b40e991a0340700c841031803c01c0c42c216030303441d03a200381040540c0c1c41c0090015844031605202c0710f2000c00401262018100a800038810590038010a0103011521610a90000f2010130680b0480096601446100f0f00c80b60880b40c0484c0d105212490921051209010401c003402e40021001060b001c2c148031710168519144c1d0203d28500041d40312710800501e164280a41084030106030361040340c00038602400381d283e020500541c1c07013250000c8840c0c0403c00e003918041d070040c111050108 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 868437823 1250 868436573 868436609
    0x50108040f021f081b1c0f0203010803031009020703050a051b0a03121a060304030e01090806040615081b01050d06050a0f06080106020601060509040903120e0105061512040f0507 78
    0x41c0e00d1030160541d0101080c030203400150700841c101c00c1442421243e5a4046c40d01500042042d0f002d034020f03c4209540d995920a100d030383d02244010b5000c1c28404004588038a001407031400450078a0f04081140e6005102030b20000b90480e00b0769650007c981070594440b0301c008200701d903e0385420940c60081c07052454000605030840156900a0900b003000d0118000801013002c440d10001c00050f08101c0400009001c203208610921030278405261030f05066584900591509034240c2c0d090340c00503076840c01c0040c00030090106400900d40711001c1d100c08025403d014004201c4032441506010002074040d061071003592200001d02001000300460302c5e112501031000140c10301600022468120001c5480b60000480d18100c1d6010b59445240c0903200d8140809403400610407001e009994000d0101914280030358000075004000000d641d2030304008000c03d4280e00042144a014100105280303c40c4151200c4c6c1c0c03040d080790a000c99240c40b880c01500c1d00d20310781d0000d030040701101d20074 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 868439073 1250 868437823 868437859
    0x12042102102d0206061c0c081c030b03102c100c0c02130f060b0403030f0f03110f07172d0306010f110705060f091305060307050108040f02 61
    0x9010340d010102ca078094030103140710070381d0802000c0901007405a44014005000740c0b41054100c0c9100c2180c269030307081c00016545010215065400c4030206411445013200d001000340d118110300306c650300c0d09001d824048004070791111100c0001d801d020b40ca5502180c00701105011514950007444101d41002281a0404d07440b283e1403044e20010a040c103003408d407034511542002d5640740d00200300703155680d0841c42d0080100014152100c03103603100d040000d003c1c002c400141c07000f107000c1e031100c181040365104c005011045000300f0006151900f0340410700304080300251500c150b0003c2180350ba0302e09a0424060050441d0360f40a501e10002422407a800e0101569030109030441101e00f8014234024040364a034001251f60740e00150100c1880d00056100d504541a00d19500c401c4d68015900c601c04560303258090440102c101c2d00c00030300402c0030700b000c038121142c1cac040c501030800c802d00308075001035101c54440c0714107410400504080307014020030300080801d441e07000700000360140c040b10700 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 868440323 1250 868439073 868439087
    0xe09030403030e0a080d05030a0f180605070207081914061e01170c1c02030604030809100501080c091902030412090b0307090515070b04050f0f1204210210 68
    0xc800080519040e0038050502c2240131055800c48000f0b80741c3d503481200215610b0b08003c10841c10b2603283c020407400c1e060382d48607421984454024544000d21142040c209480000d4070520456125000820001d10041484442030030070f0440301c101e10b0070030300744104001404981c800e101c0c02884180714103024522a10b42c15040784055403e1640ea03540c0c04801103c0c1214008181c5401c0200c6a0750a483c04007030503e4a08400e0960729444140d40d000b00345004012a0b00702c0100b00100140681210700b040700100e0202410300511856040058062b00c3d0310042d03114074014024032012800d1160b500940d5840c003445c8a500319201c2c5002d0034000441c43c4000d2022020500d45040403400d4540442101c1c45165603449400e1003c2c6442d042c015188803400c0210610442070110b00001501c0e8140c80303015a0180006140050740e0200709400c0488440c2a0071107a404000b064158032009801d480071a07181f0006150038154100101c0d4007158103240080d80079017040150700c6041d400401e = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 868441573 1250 868440323 868440329
    0xf091e071509030b280c17061516061d030a0e0a0e18072111182a0712030c18182c0609060411010809070e090304 50
    0x203050354201034604096034080d0b454000541080c03004c80c00a980036961040a115290b09141340395407021401819008a039501e012420001c0c03807402c0b6409612800c082416041401111078048030345540003020424031591000606280204a0842c10322440b0b911655001c1d01015074080301e80c0e0045103003500c96000f01d071900301240d0400f441e41c0311401c0103011103040e41d10315000c0c4009520b5811400c138000b030306004106240d00c642c0c600030419004500c8071540580b00f9404080d1040100d19002c0400c1124042c1940100300300641c1c20032140c40c4140d0380f904102d6180b803881141582080042000c850004010081040027031000104521050140310010071a5001c05c030400620350f044401900c0f51140f140e00d00050380050000c40e01c02041c03001038006021000401c500c56450310390914029600c08014030000140c502c02032a03090002550004241c2e010b810549095510420401182840241048a20000038124803400c20990014080400004600b881d000140315a03a83c0280 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 868442823 1250 868441573 868441589
    0x60e240318011e0b0a0f0f0905011d070f090305060106050c010c080702030a050f070c03060203040b09030c1b0102101a010e03010b0a050402091801030f02100807080f091e07 76
    0x5584140080410300c12400f8030b030703411164611a03032400d118100290040c040e10303980c00381e018000084c0205603440c3c0c0000604d040c1e04081049803808030b0300320448205034000080d240120b03084540e90304540071019400303c654103010956502c0b40400321713488076154200910720f02c207010001c0348040d00706018110980041c8001d001d82404014101c072a01d2007510104096030051003c596400c0c080c50103066083d2881c006c3c0b41c248900c0d03071201e100491160b4030599900c1d03400030a020500c2150303102c05032b200c500f001c011481d050f004c111240d640c0310114900c10550081900c0d05405070300c04d00c00d18500e1001d865080c04400c080240403810030440050b2540400c1e050750114a5a04043c0100402c41d40d000744844100c920742030074000170394401c805c0b41e5408124030000c0701840c410001440c0c003940c061549851241501d01c1403115202009221006100d2450200a54240e1240b04280e00030301c03401b841501500c07612182c030710344180d40202c016145419a03500a003607a000074a071003203035070741 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 868444073 1250 868442823 868442851
    0x40e0c070c06110c091509100f05061c020a1b060b12070e162a0501060e04050d0c05030c01091b0b0301150804020a0504050a0507090f0807060e2403 65
    0x82c0300548040b400c541c0c0e82a00c0d60403e0400c1c9005142c112062035001c1241c0ea00e4214100d00b401c006a45060211402400096000800d0200c02130701c40050740a0542500c000740b41c0303081d01b4602c40d880003001e0800082142c0000b200f0b4484c7d403190f030700916280c455070181c007041425803900f01c015040107601a40240d001007080384034400001421802c849019400c40c4264891101c4100c007414400b191209001d40e9140c649416101c0040300c18640e695210a4100201c05142650a607291a48152076440746481400003254000c1102ea0201d0200d082c800d610b13031020b103841030560007500300381501540703408034000c04e0109070b9000042d44640c1c14200c02c00c0c0b580782c2034400c50b640070a00646078200e1001d545c4003c4a400b500242350818001001c040d09107039500006010796004440c600e02d43d980b83c509020400e5000212031002c0d29801c054107411600786a0b00f2691420075114a0007005100745080c406a03d0781d101c040102c8500b0280031072481d05d00402035225a0055030041204c00d00 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 868445323 1250 868444073 868444079
    0x6061e0807050901081807170d08010b1c0b060d0c030501090c02072102090a1a0301140a09061506051902030306090402150d0f0605011b0b06010c08040e0c070c 70
    0x4120360080c0714501580b2807505048410004460f80d802c01003030031004007404001c808403400b0030883c41c401441d2080400011501c02c5c5841c609240d002c0750114203012145006100c0900307a80203440384840d000700305e0040d002e44c8041d0395018000000e602a0000340015540c0d40710443c5800010118a00b40c5042c0201e981c3c130100c040c1280d9901c2012401600082c1042c0300b20303043c0741e070a4080c0000b5000183c15a094580000700e40400640e41c02c11000e40d58058000c3c41c035402c1c10100e80200080300200840c241078a1030b440c4004001b00b10720011a6200405003c102556200c03901c100e00385480460016196076010740554404540b04907604003004250003003500c00030850b4410351000c0c0100003c0d845503400e110003150034528201018505010b1404070540c0b038841c1d540041c02121001c1400c510700400500302948400c0740340c4404400d02040400306500150480d0040004c2c0b9101c174501406040c01d1840f40185d40000c5030b006809810300405140c1034018001d46400b03220180041a6 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 868446573 1250 868445323 868445327
    0x70614161b17010c05030f0a09140d0503060a0b07121b050708060714070f0201050f0919170d050315180412080c0a170903040801150e09070605040b07030203070606061e 74
    0x219030648000f441f0b0400550301c0355036500f00c1c214151141c000d01140c40f81d0140000e080c549001c1c2e03040300041011040200a00d000c881d202c0c002c1002c4454245400c1031503d030801d0015086041c0000e0200040080703040e5020b100030206020342000a6940181e01c41d41d01c16103c20060b504440000c100c0d01c00c0030405684002142c4029600c90f140486d04640c80d401911079410140b1054000f220602407520076481d80000342c0c9219540a0a69101c01d08212808200d0ba0358400001c44561281c0c8800b1442c542200880c0e802804007150305d44403444480000d880e14042c4140400002003038402c1c001000190b03041c4a00100980c1c4854540e581c514010b54203a0040381400720015200c180104c1540450010581d00584954142c0746400e0300c4e80401400c0d2100c3e038005a4942142c494108050a40c0a03441600b221040010701829490064002c000e4066405005110b24000401d0303003c00d4000c000f10750b429684a10140700c9140d607504042e0003940c1509200260600052481c1c3d040d80c = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 868447823 1250 868446573 868446577
    0x60f080c030d030b0301150e04140303070c030813051c030501050d0b0115031401080714030f0607080901090b070e1305240a032102070614161b17010c05 67
    0x600240882268004124090301c10610380d05d40655032041c07a401e001a00c04c1100d000b40000c0e0082080710304240c80c0c0411240b8800b22040f440790801d00600184c645c0c4203c005c220725805140c401210741796540303464802c18107000000c020f4440c006007811903040b4601c0780400c40300c06850420480c0ea880080c4480091690b000a0122142400501c2121441d141c600c0c01c0710441c0ca00002d42440003040c0420a21007078110440c55407000d00704225003ca00140d40c11100d00aa0241100107600e41a8540c1c4001c0a000c3c42c0912074640001100003d00354091f80903203402035103000c414100b41401400c01784442e0041d5001703200b00c00101e00544041c0c0100c501030305e00070862400d41001c41c3d149051100d498808154400c1000070000041888281b80020341020b514201c82c5900584202038505030641d40408240028010361098481c00c400030b881011040c03410b03074408156545014141d030b41086541d0310a0070343c00400441c16140100c3e150b110040c5231802044071038400f4009030b400d8 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 868449073 1250 868447823 868447843
    0x2d040308010b030a0b030106031b060905091512010207060c0906031505011206050604080114090f0c04050a020714070810060b091014032503060e040f021210060f08 72
    0xc2240100100300c008401c000450b0b010040c4e03040015038000c070000207400d5030f003150b006950b07032040703120030900c0300141c00c03c100c00804803410200700c85071405011565100009100c00d1844070003410f8440c1d152200c04403403910070380e028001c640d1401c4600d05400145105418080015580b40d004540503009201e144042c101c0605400350007450940115480c80d02040030881054550300000b800e920780b0b202800c041c002c224000320b20b041403c50118444600204444c01d0b59000009100c2a00e602055141592a055501045a58640d15000064440e80c04000d00c80c6021110741400c00c180885d100040d2103095058424888040e0203c03016214240500383d050b00041051001500d4a02c1c1a2140540b040c201140e40e8407098466200b50f07001152800700c0075105242103880d04d043d000d00d080503900340341000c12485081a2034210b00035070040c0010003519220030404290341d0384603440724441802804503a030440d644030140c0d020380494443d9004050358020089580b820100c1c2c20141 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 868450323 1250 868449073 868449077
    0x40b0309070b070213090c0503011112062b081c050a050a02031b130b0406050a0212031e04050f0f1b0307290d060b0703110c010806040b0102030f032d0403 68
    0x40303c5c1381008618000c100da07004c11144004890800600b54800703003d852041c0c0c5140d60b020b901c0da203428440d29070400300242034910486219440000c04045440c003010b108070684840e81088045142c1048240f00300d0aa80c00400a200200384200c1080c0d0041c1c1d200e9105814248401d442e400c0c3d9040980c001524017004080c480d4001d440d00c43c08800c0540b030300ca000d07010002e121640e50707807070075910303901035006500003070000504018000c2d0104001519928460740f40c42c0b852030141c00300800111410500d0b19103a100001060510800300564248000d5060554800241002c2225079910500c002000200c1c0c441da1018000d2401017584e074125450a15410b00c18520703441e017002203203e40c8000318442d5500384507444402c9030341d1080300040d107100504543d40b90a1418040c0075107407504400130709075010926250b0b599074800302e101d8205406541c04642506641c0050341540604040402642d9011080005801d1444512101e07008006401700381404049003070b0003c40000c0300e001d00 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 868451573 1250 868450323 868450339
    0x11d16050f0409050a0605010e010e0c072402070501060906060e030601080d1107030f0c03170c0706051e07080d06050a06080f060409120f0806030f1906020f040b0309070b0702 77
    0x1526081a03004000200e100c2d200396003000714a03551b040c00700c840a0304207031840840c0000610283c810002180d03001a2500361850802d5625962030580e00320030004030111031185a0703030181800303040d0141c40080da4007600901c0f06d15199048580141901d10480c000a8884030140005060205185060f00d03c104094440c1300c14000c3c01790382150100c05100f1a41c8580c00002010a4802c201c50ba5241d105410070100c042c614200b150484400101e0031032042406c00c030090703083e0303000103030101115038a060a23030b104c240c0b81c031071075140c9819880d41e6000d800c0300050f050100540d07400101030301d00a00104112007910380c0c00744000005540a10f0000c03507a20380200c1e40d003040007851301d50702030780003000401e09841ca545c5801403142c15001030004202e02520900106070000441944140254010f05451000ca5032803543c4a070306d54014444616440140b1051006039012035602645c8581c0c425911355a9102d505d115034022603821101d40114803022035040640f0044910054000700404 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 868452823 1250 868451573 868451599
    0x9020a120b060408071a0f0c010902090a06121416060201150f030b0f06061e0d06060f0507080705010f020a020a0303050708010b03221209090605101707030608011d1605 74
    0x35030104915405404040c1c400d01c20901c00d00748100080c410423910701c0c000f0480280074814410361030b1002d030008500a0074200c050100a4200c283c080c05c1c00d8011200800c00e01c0b0130000103040110141c1c445441d001c034030f000800c44580540000004003441e50800c0b4106a03105100d802030469808020704800c074480111b100d42140c812109c0d00030000425003490404448a20079880c51304200b150780466000ca44d0b65401c90711449048014045410b00150b04804648001c0c01885081c01c014142d480c045111410702c6002d600004583c0b036110411540c405031800301a540351810007045000a0802c0006403e0600c285010b81c100c030001c803441401c40c0c84902e0360811483c0c0c103d65040390219101d0f01c510200d1003c0e03e986101c201c094548041140c02c1c80310810070380e050380e001a80210110407000f410f07154013092203501b062034a040e40c0c2c000d844070581200603000a82c0f001034075600380105112540c04062420b05800b403903c0443d10204003d603000415100c0c2032040c1980007000801038 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 868454073 1250 868452823 868452839
    0xc120503090618030a060c0e100509100e280611120706090221010b0f09160c0c0306051503010507090b03071205040c03050c01020307050c1909020a120b06040807 71
    0xf030504482c5410f02a54048044004203240c00544441a544030381c9884061404a80006156009036000da420252050300d015020f04284101401c40340180c040394949512688a2000c0f00c00c640e000038a022400a1803c03c15205070061800c0300c0701c2c0c51900c0c1c0000440c0c6000f00b4240b070346d000741c10303000e0130b091400030320419100c0c3c02002064501076151100031005035540d94030013001c154601860320101181d5500c5608440b0311010b9035002d074400b00c06265040d91114002c81e44070f40504444515a00455012100200d866030024038004140754088108071a03908194800da15a1010215421190303081500303031942941c034200403c1c4400c10a0100941c00001036501174450300b030030044208540c0242089074000ca40c01d03102c1551040302401007080c14040000d0501d4244001c50508646413241d0392204110110a442136406c009030041d01c0c4002400307003006100a110443d26100c0648020f8001402280c0320040c05260010344c0700c17503144c180190b90555070414006c10380301d8109001 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 868455323 1250 868454073 868454077
    0xa080a050c0d32010e0a03140a02061807080a0623070e011103130f080c270a06050d030e03010c020601082d01111c110f03150306070c0c1205030906 65
    0x241404011108007120f02c00c1d03090003807810030607240b40180398030189410000c1131100761002c01803000c1c070104442040c1c55400101290001811010000c02070604440b16140c00950345c003c1c50349000d400344020501810b07600035400720b2201c00300300400302c12400c2503940d6480301322030303d00c040345c0700c0c21498140e544211401500e00030201d04907403030034150302003190209170349030311040821640003002d10003040e06202900d43c0002c25601044000c7c0e449800c400410b840e01d6080e0041e620000005030b0465880c1c200a0040c9009007001c40d9040c45410b00030711048490503468007960030040b00030700040c03000540a04a95041c0c014015514000e080c400b0044902c102c45080c214040d041490003078001c1c80fa040b1001c881200399696603464a4404100038082e990703022240345003a01d0490288111412502820f42e0400c1203035403503940c1c0e1266034042c0c1d40c005405816110f0358082292107078010410380320f014081d882c541e8125076105000e40c07003e01c0c2050010196041807040071658184240 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 868456573 1250 868455323 868455383
    0x303092c0c18120307060608071511070914040b0f25030b09070201090b0a0e0a17070f0813241b08030717070c0507050f0f0a080a050c0d 60
    0x1040c0c02c040000310b000a000b204918500d40c415000010f06804000c081d101d03c000506085014000b03803881e040400c081440c48a05200501528540484c050081401800c0c0600080302c8100300c0c40b80e00c03041004100c042118121111032100e00030030440e404c4081a5442000c00c090031070340500c211040c1c5150100e0b01d1454006258a0307041d000115514040114402d02460703000003000c14040c1401741c501d60001c2c15607082c0920300001c88004041c08200e07844039030b80000d610311303501080c2011058a8410940042c1084c0c420001070340405c030a8600070300b80600e05145807502181c0b00c0e0420702e10300411850203901c8001a19030130801c80e0185914108401c211040701d24102c80a44550b200c44d441221410005102c2c0548020464604002d09402081c0c41c941182c0290a603558980e0340c6119000c0c9500c103d400313081d048019610444414080d80d0b0103445280002d40d98101c4650320314042004460320300450100003068200034a10422994100c6181c400a06040101420740c0d0010b0b5 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 868457823 1250 868456573 868456597
    0x30306131805030c0f06070f050703140c1009030e060a09090b03011e0522020904060f15030609111f0c0809100c03081f1a070c0303092c0c 61
    0x800c281c40420801e00190205801041c003400291440301101030509030700501d00400c3c09031a0300d0550305154004280c46d40c590f4182040005001036000500c40c50050002a80c01c40c4221040090006100c0e0062007030144a5154200120700b080100560b070b00820a044001480c0003804000030a9680c01821103504042d00015800c11178601a00701c50b000082e49104441d02c440030320126540c40155080c0d84a0307090300382c41410a0590001d12144000ba0003d88031035103135402c0d46504a915404400c8505090524050300369603442c01ca00070380264041590011306a51000f00c0c1800c140760b010700c0c51300d0070400e000b403102100c0c3e40c1a01d08040c1c0c1c038010b540006041c09150880e03141c0c0307408210001c81c03c2d20303a001070640c18600100585401001070201101e00b00711050001d0700000c00c14180c03400e02ca060401403084005c501070a02410350080e207404082e41000060641000c0004140c0d940c4041c640010220680300c4c0075416100c800898462200a0025003010400c90240901c0b901d01 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 868459073 1250 868457823 868457861
    0x9060612021806070b011503050103170a02121c06080703080f0a02120f03010e090a0c06030b01120507080907090c020303070e010c0f030206010602281209150e011103030613 76
    0x80100f0180d42281c082220009140d40043c081100e0f9000300c01c0040215107000d004075130659035012144140709101500028011070006005402404440f5403010000c2c4159150300c071004002c0881c000c0c0d8542c04606518018006c18050342c0810342c2801c1d01c1d00451224a001d0500c105000e640d8000c03081002140079070a81d80403030501c00d074010804029100780c199200c2d414810400350705000603150340c06583c410410040025a1051000304880701c9080014052280d0030058990010040081c1041e0340b4190802c9481508101f1303a5000b51444002c8a940c0c0b51100416001c89016500c508003580c818400540340314802c0024a01700b00041c5440e0200540c142d8560b40c0c5024640d000701c3c0036802010062100c0b603030400040c2580f0700c9002c3c014075030081034200f070030060803c141c1c0a042c80070202141410f4174099903003400208040c80d04108451043d0070000c0420110880660001e2040900c41480c1d40f000401d5034020b070340040c600a07001e9140e01c1d40900030300361071020300b010660b1 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 868460323 1250 868459073 868459117
    0x1a0304150c0c02040b09040b06040f090f0501060f06050a020303010308031018330902030601110a03092912071806020717060709030f0c090e0d03060906061202 70
    0x1960007119a0240a9164150402c034948100002e42e00303180c2e13216020f9a20b160810020490524090781c00c000161000284c06d15042c4409014100f080c0c40580b62000c800b03002400c0147c1544440205c03040f0700d00c0d0810161302d900c030840e00361069540c01d50050740140010710104005000464008401c070034240e004565902d540441d07400d00486840079240d480d00f031134801407030340c1044101146c1c6800130200070701c11202c401000c070505d41c003901c03030501d07804400119180d0080300b0721462481002c3c11100002e02d41d290041c003982d464052040041689000d00034518480080520090f0010404c141011500740390fa00b8030300380c01032456041041680303c40c8500150352080c14040c0059a020b07050590503d8072792428041400c50741203440d40100100601b65500c8801c0c4000e603076000c00454002c00d03181c1008181e030910b603080507550600e404080c00301e8400c0001c5100310071f40d20381c0381030100e40e0f56601810219916032060001041c0c40c0d104140902003d0b03130041015a900900082520103 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 868461573 1250 868460323 868460363
    0xe120705060a030c1808030a02060603070f12050102070b0103140f0303040201320d0605010801080c010912080910050406030e0c0307060f110f2401060903060e030c0d020c0f0108011a0304 82
    0x950761b4884c5180d40c0000800761280c5505200d42e030307400380043e001002c0c058545040c031030000280d442034404000d40303c1c6801d0308000b000e404a400203508108600c0c80d40d6100d007003085041c8078003044a06a40300c0c1540d0150352070703008801d8900c520b805850700301c0007170b0060640c2250604040c038280e842130180381c401044035090002074403412000760700009943c0c5c00c010026104680680200a03513900c45007000005a80c440000c0b025245060040c46005c0014641130400b40144000c280d80300e2110540f00c050310303510a016108640312690240f04030890343c1110394450001d0720050341c160f08450304c14807645014021100d0803038828038150b40c80011900c0c660782800602042e44100b85c0224017032040544c2041103280780544604900790b12540740c042c014040c3c00f6188001008c1e5034580d220000381c904140103a50b101103194086e2861039420100007525405070108184c454580040c03110002c0d4814102107040c5c1d403401c64401c10007098240c000103150802082125018901c0001c01c1c08a1 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 868462823 1250 868461573 868461617
    0x6060304061d030912031201090c05040b0c03090a05010309020a061110090c0806013f0b192004090e0c18041208190b120d0e120705060a030c 62
    0x42c0e5000203552205850000c00c640e13400c40301082c03e15544144001c01e40d00d10203422441c1103d564240004200c200f0510a407044d01440e0f0018642c007401007020103202002000070070340030301c0403210085440d840310b00560807a1106d05019410002540701400802c0c0501e60202403002ca9074115440c28404500307800503544281030803240102c14240070469183e080040c2ea015240c200700780c4205c0d400554605802001c015000d4401c0d075080c3c50758504d08041c014454a41682200c0c16940f10318041c0040501e22605140722030ba5075207007054284080b02d0401450891603a81c44066241c6071030448841d000d0601103102c50307503500039040c030031f000c0395103070400c0c1c458102c0c00d442c6002d894580342c10440b052078001c0410340305100c600d108007d40005200720120110000640014500c0e58240104042003040d42e03040307005103c0c0141400a1316044503210720904021215410070741c21514645071180e90912400360012428419001d0701400398018140d07000007440c02d09254030144182c41409 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 868464073 1250 868462823 868462871
    0x405062209050105070f082e08011b020102090303040501050d0b062b02040530010527070e0105131401090506100f121d0604051507170606030406 64
    0xd81d54a0560341000028010107a01403101d04104c1c189000b6460060243d5000a040b0301042080da0483c90075008190804407070500c5400c0700d40429a145c40000303000b40f1081032000b40d82403d0030781402d0418414021110103010280145003014a00340c0191100d03000042e0b503600701512141c0183d41d5032a000081d100031042942000c007034501c00302d95014440300d40f080080340300e40104000d003e140ca4240244203480060040c4091201d80c000040c8000820b000c0104159400c01c000d1000c2d00c250700010210400040034040c0d00c8000e17140c03030696150110322611034900c81e1580104030900d0981c1d06c20301d64000000f00410744100b000d11034102d01e00240c128800403a945c9080c4103081c20100c251404098040c01c00c41c81421403180003424203170320089407051490b1641c3c0000003a240c80f210030b0940381c1c8080222900c1d41080c0c0740803030b11409903c01d10082c4409040020726001d04c10003200309001d10f0800050240c2d03c4071030078488540c0c4014010394103562110030600d17207038032003508039541 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 868465323 1250 868464073 868464139
    0x40f0c020d090b040b03040f0f140d09090e190203191505090f0721051204151d0d0311100e06071713030315090207051006060e040506 59
    0x824071489001411415050304615045141400103101c900290411241c00c1070304280350010f00e41051412050003600210010300304200710108001006001900400c8008141c40301586191100180400c50b0200a4401d500d9401084280e0000b4a102c140400e010700203010f964134111411103031000305800744c000702c410b0050026800c0d41c00001d84215a0030401850240c408200400d5185070340d0b81642c000c0c41907041662140300150400600400515507220050301d40b004030b0580c80c1d40c401d8006104202c106840c00c0701ca0098280b048001021101d00c0e0740705000c0e1840480309000c1d03940c103031a80842c18403088604001c4100420410410142405800030074400d400e800003d090403009000c810a002400500d4404190b10344801d980c40507038010154503240060604038080d0907880d83c03c01041001c02e40203e42329010ba0010b181d540d01580855140b1941d26900341e00701c0760325120b408001400c0c02e00c14041032400c0e4001640104004000100700030390f100407010800d20410104003 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 868466573 1250 868465323 868465333
    0x60b0303090303040314100212040b0a060503011d060906011d1323070f0f060c0c05090c0309010e0d0e0108150616032a08160501050c030a15180b040f0c02 68
    0x4103101b0411206410511060040d030411900c9220440341140240008086c44408000103e0610941c8d20840080800900078451007403885075400d400244d03c21420403d0081600046cac00d4100000e20074100c480c03095402c11a6814107800070004540601108440e00c01c1e00c040030f0210f091808252040310040c1044201028541340c0c03203181071180da0140c807c0d0004400100556203c1e10700c42e5044900d03078240326041079114644207103582c00503007042d40d001c0001c00512080450741805540314480040080100c0c030019107020303560b1100c5501004c006102d0302c0c03a4500329441080340c00c3e000303900405051028003100e00011480d420911650f030f41e80780e0443c055030605600c114000100c0c842e001c9030000b4a1207110022406080d411005403c44100090b801b42c5620883d04101820307801200800c411705003a01030101d41c1e48140e5540102a040c2402d410380408a0f034011401c41c1c010b400e503c003522548860f28000b5000851000707602c540d44003240c0a50714424051100e94203e1030b40604 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 868467823 1250 868466573 868466603
    0xb04080c090c1224030706120b030c03010903080117010204180b1c29090303010611120a03061517041b1e0e010f0b0403030804021c0b091207050a060b03030903030403 73
    0x840c1d004c011000b51440303136100c0d04003080300340d81010555020700381c5881c01007180c44140340800d2402c2c0804542030f40540c42c1c0040c001c00d00d039100261605072580b00018154920019503114242d0142c1d0142c5a000c401d4000d00000013403041c0c3c410b5610344006804c019401410410540000718803440980300d4085100f00b600d5101040320014000803911909146542400c01010303176a404140143e1003803007030300000f010855404101d2040703d14110310f001d60b5201019600100036003024402d00080c0010350b440106114041c400d041c032407103118091160140c0e00d64980745809694407039895030545a071040070900fa131032007001402c403c1003c2c0500c0c40041c80c001c18003c014005138052040711406540c1400661141d03000c030381c200c981600e8143c2030340e125400000c40c007880c102c0144040f50400a80c1c0820099415241485001c800b0140c603500801609248283d2040100041081c4c0001c010f220020751141d20003a10300402031704882c02d0a000c100800d203150301c82d4000792a4030070340c00c17800 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 868469073 1250 868467823 868467871
    0x180907080c0103020a0215040c03050d0201020a020721020d1103030703020313050f010c03030e031207020d020c040506060f030901020d1d010e0c010f03020901030f0f020409060b04080c090c12 84
    0x70500101003803030114944100d40c24000d4aaa4060442002c1d454000010409001403d9055005150007905a48a08031801e601038000c1d4450142e1070b0150089110000f01f0383e21504940c65051301500c51001ca0300140e500f004400d8200344c3c001c55a0f020075000c00d00c1e0310b4400300090281288650000e5903607108641c03107510040c0b001c0e802131f44038038000340c5500356690b80052041c09070b940c10b040200c1c441e1714080c1b1080c158092964605040000042044101e0740e000034148400c82e00c2d41c09448103026040d003400103881e01254440e4008104000700716126140c40011540f2842502c0014180400d280e49442518035130402480c5020144904821403282885020001c400110042000080840000e440c4601e00c811503003e06601240c0000365034083d4110004410111400300000707141194010b000f50003500501c40f400b842c3c14404500c2181600c1100c00741d41d1490002c203030b095498410031190300c200411407681c1000500c0303050030031101c03010511b014002c40487c4802b918150305078 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 868470323 1250 868469073 868469083
    0x3030603240506040903020d0c05030702090408090424052106180d170c1803070e0703140c0904020c070f14121c080c0403051209093318090708 63
    0xf03840e200e0307032800d005400026000500d03120810a60305201d0001d260350b040c0982035006a0781c01a410140702c004200403c55240018112640c0c2106c00304040c100030b03403801e1480002d0a00e18139008613214800e0215181c81d42c40200b00da40d5403101000101850500381d81441c03170941d122802401180000c648050341801074091982c0d80745031500503c06c00404040d003000d405030291441e45400601c0c0c0e0350f290f24649500010701800b4080343d42a035a100000d40f61045c0071114417002038907002c1d80202884203a0754050142c082c071250103060003170420401000354007101b4840c20a01ca08070340060102a85400a0024450100404810080c0209001042c080d0020000140c1c100d0340003d800d080740321030035019104a6103401c080d00e5440c54000c91003441550401380c002d01c80c6000030303005525140d008000b030385002e55020707800c0d45582903051100c01900a01085a90b25000b541d060400417501825104e08c00400800c032912079030642100306002900c9000480e00026010305c00c1c8041000 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 868471573 1250 868470323 868470331
    0x1401030c051305060d0e0102031801150608010314070f09060501020c100c1b050409200a0312030213030c031103060c090f040e0313062d1407030306032405 68
    0x100140340000d0440c0d0701c500c0400b0342c012148900d201143c210038001e4207520807075924101c3d0000719a2410003024255050540b20056100c0350301b4040c0701c1402040d0039043c80c04540054641341810390850380c486900281000d0307a00424810403500040901d07441c0709080013040100310000d0802e0600d8002803c02d680001001d005540202c0308580c0954403404030420340d601b00611881401c5550a1400308070a258032065109050054200c18002408240c6260101120460b00222285828495240f00520001c0c141c4604141854107980c0243c0080031a2a590101a84015180e40d28003000346c1c3c958200381e6420251105a001c41c0c14108551380e00310200c0802d2504200c0080005004ca240b02680325014a449009485601d00100700303650300303c0a040181c8540300c2e02c840000f00050500c41400309d00d21100d0020003041140b83c03201029144955a0b61400451070440c0b02005610500e0101c0030140c0c0c0302000404160681010314019020b640f05403c0c0c101d01c0c1c400b00054a6000d4 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 868472823 1250 868471573 868471577
    0x1e0c060810060801060318082a06040506040f06060302030d050d050a09230a0b01090b03072403090203031308012f03011a0d020726130e0603070b041401030c 69
    0x11509118181d000f0849504480140c80c02082c0e00800008241d0b22019110340202280340104850780c10480c1c00f41e194000c180c141100e01ca1602d003a901c89da69441050318042d12542140c008503010501021814415074001d142c0480c040756039602007403502080b080220005200403c804070f88820b2806100d0b00800d008c03505104454140c1c9540032600c00460040618004400760102030704428040806c1c51a04010a6400d56a580354400c0192103035800191082c0210000402c52a0f806401703c418200c1c00d2600b4000484483c2055000702008441617a1611040c0040a0806400e1100c0c5000e0054038001281c019003140c400e0440600d6100c0f01c68081074000c0b514450765500d1000c1e40e044409585680d6000b0021003083d06482c1720300c2c40c0140c1746c10b000058107002d10821030072091810080c00c6078035403400074022000c80c80740104860712000003590402081541210848070340c06c09001000d9840880c0c0c1e03000d00006644c06684103007a0002c030599000030a41e007510998801a07418 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 868474073 1250 868472823 868472851
    0x10213080604240605090a02041406030f01030609020103060504020c07060f140f0d0e0307081c060e1303050c2d120f0f25020a05040b06070308041e0c0608 68
    0x42c1e80ba00550115049030000340b550401401040c0390751500700e10020701700906105850305004403240040c1d84640500805129030040c402c1c02400c1c030004403441901c030708860442030b9086682d0318000c1c0c03020f400c00760304054880c0b0010409640d02d200404000c0d003800c00404110f80b801e18003914031060b4142e0201806064040041c0d02e4138480122991500a03c83d995981c29075041003c0c01029003110050552001150340c0b400c10480700000d000d800c260440c280340881c00924400141c030391078016961041d07503503400709411159005503a0b990521a050003801d11803100c152a20f8222400e0380104204c0c0196a03600440e0380303600d20445461940005040c41d195080d0014425100c1e03420b510139034480010341410051200e40c140d80e52040c04250b85055003504000000c00c5114000c0164070818012400044e1441c0a10502586140c0a41b0580c100070a60301c054403014001041600d907061583c0c403060081203410086415144120501100981030a20040c61464002d045840d080c40f5 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 868475323 1250 868474073 868474081
    0xc170a0e0a29070e1525030801030309080601230d060509070501030b04110318070801020708030702160e13021c030906080a05060109030206070f060f0501060e0609090a0e0715020102130806 83
    0x480d02d40410f00145c10750410703900e00081d8030241c55008040d048031074001151040030105540b06540030b0481c3c0c0a0f41c1d4030343c0004e46604130180c0301c200038407455404103c0b0100380c01c00050410f00d41d1341102c1000303200c41c1c004520354484200f81d82c811a2081c019810100c0140002d6805101e042d080c2c24040e502002506c80c805520341840c80080c0900e880015540c0c401d9040c1e00b0f0401804002d8211070000750348034221032521040c95042944c2d4074001d0b0080c0703103000c40314164035003164049901c4060900300f1500d44d031991000340308200905a8110000460780e0000c607000e2004034020510a0360b550307001618103c8010a00080601400800c0382020b007400700c03e1381d0108010b01030365012100d070751791040ca80c40d00070180405040b0042495050417041242c10586030300c00ea04a4a031901c807000d0700200602000f4180c07007401181c6502014960104052035010b070300a082c00c4c100c034002c42d028291a6886038084000c00590100181e4001800c00e810740340d0010389000505841c0b0003000c05082c = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 868476573 1250 868475323 868475329
    0x1020d2c0a0209180703080c030304060b01020a3513080706302c0c0105040b0412050102090d24020301060c0605060328060c170a0e0a29070e 62
    0x3c0c01138194042501d50100c4040d0608051100307000540d40005007560321854840c03890340300d4100719429180300d490300711400129400842c5501d0b1300356004010f0b03181c2120080c0c50201ca200c800c01c00742c0d140c540000b260b81d80904544010660108048048000d8074034082440d45405102c2d0000c404000440b41c01051280710b42e0500f0703001d080242d4040c1d06100000c0d400800a001409206d0911014510b0030b0034540a99604e280d1101111300a84074601f84e04001901c00b03200b140f1403d90002d02c02c010403c20f9110303070400e100e080e0703120314005444c0207501000581450041c80080d240c20b00b490f095400503450b05421411240080d5000b5815503141c8000a0200407001ca00074080589400010341c66903800c0c040360605003c83e040c01300813540415203225400744007600480ba41d500c0e0102d000741150180c00b010f507054a56914510460b582d40404502030b007001107407900c507842104030310000501c500901c408560244440aa8680710300030800da00c441d0050b0000007401440002c0341501e403 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 868477823 1250 868476573 868476589
    0x2d03010903091406131502061f1a0409090503032a04050d03030b040f0b090f101521020315010905030c06160605071e031e05070201020d2c0a02 63
    0x10b581001c01283d00205000880c0c01480303110b03401c110b10001c003180412881c074101c91301d5070001c200d03508035241d03980c2d00030213400c05c030002c12885031044009401c00c1208001070042c0321880030749200b003107091990750710040043d580d800c0401c0304ea0380c0000c0300b04884003103041c5160f00c0d0801c030620700000c8601002040308a41c45140030b40b40c001c907414020320007814004d4210058030781e00503000700020507030f1203401c0c002041d00b81e0016110380010004500f50030081e801150040301030306130072108907241c4000701404220000300345090190b4400301031039621000f503909520510701e45025940340391402c5171112004140e00e01506110413100140641c1c0c0b40059841c404550a0fa0156a181540c0d400e0304040303210380034002d00c0c05042400f0003140c03a40c0712183c070310001d140400d4041c1210681ca020740549120301751044c546201c040c00c91482d03034002d41089810a42c10f00005180c00013015150b41a50140c5914410148024a50702d0481800d84491000d081404001e0061201e0a6002031101 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 868479073 1250 868477823 868477829
    0x1b010804030f1e05040807050d050d030902130203130b01080a050c040e010b0604090213150e0f010e040c0f0809070806010b0a02070f0609030219120219052d0301090309 74
    0xc101d8070728061180c001d058805040e00c481c48100343c60116444004e200d9070245c014900f103406812000260703030402d1200310030041d9102000d4501005505411001080141410380e40052442d030b0700c01d0766040301e10045000d600b031581001c403c0340c99030400800703401041e0701848641d07208146e10404241c1c046010784c40440d00329000308040c24400d4500303015010320014981d21120000f0b001501c00b5460f4000c0c15400c2c1c070700f440c1c01e404035612112203a00c03010b80c0c144c0e800860302d24056901e543c90b01c120b1054081d0382c14140300c1d5081151401040885605551b0800464192005001d0349604102560342c03010486004003005410000344c1500d5603010b00c00d0010600d404140c192846009104000141180c0441040d10719074440004007400e001e484141c0c00354140e1030103204c2c42400309000906a6219051811120a06609005100040045440c2040008503010460740c0d690400c501507980f80d100c9064504032128a00c514544c00c030000c0358440e0703240c210100c0029402084e03090031 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 868480323 1250 868479073 868479077
    0x80d09030e3708032703010e19020a0b04031a0a052a0f0f1b030307090e090c042c06150108040501020f0301090f0c080615070c0b0a111b01080403 64
    0x1101108103080900602c9030382046115020128410b492161240c071401502c81e10340124040c0045508281401c98000004010350740d0848024160303070003148104250072506c041d00b8565440d83c0c1d903485544680280d00300b203807124036031406001c0740c04081d202c95400a614103000c0210b4280340f01c8413a68801d101d45110381c0000c4080c0c10015005560f000c1e1180710012520243d6103010140c1f1503020340c0c1c8540404000107151081600c0221400400e50344102c6813929850815070405d00b500d6200c03c80200b01009900c60b22051000c55201c80c040e000190403000801a80c480899940d405c0841210380150352540c8071404202d1102024480c02030100001e0070024525282c9052490183c840c0c840080c12003030000000280740350f040d5100002aa110f202d003017280d10340c000c80850f5450030540c0e200e648000700402401c21075440c03d0040c45500d01c00c00308150400c0c0d4450700d0400540200207040d0109011100040a807503041c8505412410000d10881d0200049070000c2c090b04405071001e02 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 868481573 1250 868480323 868480399
    0x1060c020301090c0305070f060c03050307030f020c0a03051b010b1005090307080604050304180b010801094a0a0b0412030b0913031b020d02040216080d09030e 70
    0x1040d51829804402c1c640d801c04101c06400380c4906280b5a2020148102c0381e0729062080001005882202100842c540c5950340500d96110b8440c110058001860240c030b91356420004009254010864260501e21079240e0545507281582c8407043d8450222510201c7e904000019190341d0750840101d2040702581404c0d91a02d40040100346440d1290708482d070a84150002c0c04103004000015108690008080c0c1440003241d40f0200147c48022941501140f854801800410a01d80110155910220303140c40980c900844200c10301d81c4001211041c0003416414016800e1070080603a08109070704001c0c2075040c113582d40c0034980f4100034009020007000403104844a440b0741c0009100b40001480d0b000d82e410b102c00c550104032000c3c00100d0100c3c0f51429a009a24006240c03500c00607001400500000c1d11a0280030283d400a0038011020120713030303900d10014002c40c3c06050482e14010300000c80307411a1030050410205c03015498413417060f00001400100076200128035000032440e81207 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 868482823 1250 868481573 868481597
    0x3100c030e06071218030e0f01050c010c030e1204030201090b030c1303081902160308030c12010b0a080606040f030f020f13020a03050c072f04182003060106 69
    0x20020614041c02280342c0c051402800302d49a4014004441000d00f1315081140c001c13080440e000c004041d0900401091250341044a40e19008100800c440018101203241c0500c030315405003180e1400c9c1641e004240d8400d0031840d040f0f0100a200318131801f0445245c9080e045800107841485141b1231078800e4040000003c030940802e0094070500d0400b008408840d0340c613844c005a1540110ba04d100414080380559100031b0720002d02140401002e48204403440d046d0b46481c0350691004110f4a13808104003c000074102842d18802e000b080c00308503032612048488e5008061300030117800039100300c00a102c1405000925a101c1c42165809012810800d40b40e202165040c0442000d50b644203100b41c070742d00340c0d4800035002002c3c11080c0d0f590804c019a951291401e243c00340c0c900c06030468401c980825491b86481858081903d041030340c102c0341d001940d0021b010745d598050303c1c0b90b01d10ba80c903002c0420041d800b102d01d001b130207050000f4070810b03503103170046907440350148120810050444020 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 868484073 1250 868482823 868482827
    0x6030a020403120306060e150415020102040e010f051206011406090d022d0a230a0305030c0d09050d240618020a02071d0126160608070e03100c 63
    0x8030019907000e18841c0251100040250082c86244109004180090604d03591840d023840c01e16400105109040d081c02c1c10041c0610310319071700600e1002950741c00c000c04560f462152641c14000c009207080303580c4503810102030200314454080300060307950118005110f542d030004550340f80240309840c0301c1d880300e10000c0020b0300d40f001c15030042d41000d81910b4030716040d94014000d0b0b04158200d501c1c07032035601015040c0700340900c041c8100c20801941c0b4007a1143c1c052075010500305800014003c02195031a81c4503141540d00540c04102175a2195200040840d045a070050050904860600d070496403510f82c480c0300324054649104c18969141c2d840c0c801d0969a00080250030146d074841c004250508220b0001d42c8410303403a41c09442020301c00204000150300c4258452408003644000d0707480c2401c681200c0c003540e1034511a09204541c0c00048550410000c21034804003012031008500c0c2040103010448068850310403c07041032348244603600c00092550301400c2134200081e2000e5002c0b02 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 868485323 1250 868484073 868484077
    0xb01051908071e02060405160b04030f1704091524030e010e0f03091906170903120c12060a0f1a0906070507090f1a060702011206090c02060603070803030606030a02 72
    0x1c0001105054220b0509a65001680c54490752281007102d420040d00900c411100d515031040b09d01c1c00600304404e10000704010301c02414103202c0d10300000c02140c4461581410f412541002c20440c0d42d59410340b01102d82c094444000300708100003040b211a00c1c0c610f9817100c00d1404d10100606840c0d03c014207648800b5449442c80d40c1e00c04041d50281d044101c58541c03243c0c0402c014901c0703000b030840c22500d09060f10010004580041c0c4a18501405c8401060a14100101040e84a001c10303c0b15401003681110728a10582603c0c8142d40c0c1c0f80b0361030b034034050104400350841c0d008543e640e134184442095603410030150341e982d058102c0188015241515548282014039801030070105265040000000e55181948c2c820b44082c40328280c1071140030225401402c07416121840540d0342030442c2030590080960303e006142c20712100f041485001d003554000e42c03210080550ba08c04141d8240c0e0b0500010340c010358202c0140c103100386092500c56507400301034840f600c900f6001001c504c5101103541 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 868486573 1250 868485323 868485347
    0x406090f050d02030c01061d19060b040e01050306180d050912070605040f080102030903041703130806061c0b0106030507051204421a06070b010503010b0105190807 72
    0x301c410700b81e80002c009403240c00290f2014600c0d800d0003008625100340c45240b40d000b03c88003450481d1603490220045a60711000072549030250381d400046000e000450060020700a601e19903121545030100b1301d440c0c200d0017030000e4030020301900429000080440e50005110b400d29056488250b9040021018003030300ca40e0900740d120b00400080c0c1b20b42c0003805801198490b554480056584802c014282c1c44115403420181d00104400c2c0500a81c000c0050f0201300080112030412a0118404882c40002e40000c0d50f40e6014004103c7c0504d4030210031a4a6090705100041c140380b80d40e1021101d09060141005044d03e8a001515162280c400d80700311542d140d10f60082c3e07041c1420a6042c40ca03c0040d10125030115140315052401150031941049000021100e411103a4a4011005040782e02c0e01d9001070a50610034074140d0f8458010b084414017418a5030701c01e52500081608481034444174606221062080c081d10001c120400134080241d420944226a01c0301c1e0100e907004900e070 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 868487823 1250 868486573 868486583
    0x161704051506130e0a0606050306090c0613150207180902090a020c0102120403080411010c05060a0e07050a0801020405040c030506030a1101020c120a0b0601092105070b030c0d150e0406090f 83
    0xc4d21480311303428001209600036004800c01c00105e61914141a1503e07812201400d140d0310241c0c01000e5800c007640241885142c2030107100b102c0351510800d880075000c4003625030040e84410814040e040300415245006800840300b000400300c030754003003080d10100038a0440415070218089040d1602901211141e64510344613002616003450040c14010b001d4070b043c1c4103c010b09091100075400750340c03241481508100205895600c0c514000e014007048000201d403401005800102c0d17889004c0000064401540096156410481488101c4040381c00760000c040c101000e0080d943c90102c0d2980e4000c1d00049542d610b06003102c0142d10781810381168a0f000900c0c03188001240001140d40e0781c0840c4940c4494010340c40c0c84004680749102030007140414005000d04565140035000c0c1c04011502c6038064030080baa0360040d40c681a0021200019a0000002c082041c19414480e6540c6d18150070080c8003401d00b0504a00356408000700001d042c141e4410340c4c0c0b014049186010003204d6888 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 868489073 1250 868487823 868487831
    0x201031509060b03161704062c0a05120405010f111510030209060d05030d0c091802030601092c0c0c0f0106090c080609040803100b0316170405150613 66
    0x80c400340307000d13138030440b45c0e400c81c0308400d400a01d045101d0724504030f0325640100414201c1c3c880713880700360041183c10000c2000292103850020071648908600c00d0b8400008090410b03004030f8108203080403000071481c0c0c0710840c10070041c4016a042080c0d8607440e5007501d00f481c5980140059103181103c140d1140100203000c000304101815000745000599200751016003d07a00c5d590280b00c1a20b02001c0000c1c1075820602101c039900300164814610f6000030b00c1c000300f44c2643e032034002841d040f00542144550741c00100b007100c256001000c2c20010003a000da1602c181c940040c49450b21005020124402c0c9044804208242d0340c1078280d58943c4188410f031560840e40201c400c2c020915417260f44081800c201c44960014000c13288580b1803100508200c190f80e541b03546070800d682c80103141500031032000341c000c1054494030001e11b1182c2400e140d0506c1e8861101c0340a030000b04044030603203854034040b0420000400101d206015083c40684903803247d2200310009041c0e02c249440480010301e0 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 868490323 1250 868489073 868489079
    0x5130c0912060903030c02010203060a090203130b0c040305060603060702071e080d090e060103020903100b04090f03080907121509020a1d010e15180403030f050708090609030412020103150906 84
    0x200d510125079180704e45c80c10000094142c1d01a400d0340000c590069224046050400c4100e52513002194040c00c00d09070949260341566421003901005d0361014064039010406004000040040300e40201085000b40201c3c0381004000303590714100d0284030a640c04001001340982c1d4071140c01c074042c11089054841c3c014810030002c2040381e4900c01c0380c0b2070008003400704100307501034821154a4000600600f100d1f211041c0110060300301c01c00420b4005555405007004a40d13801040e4050700c1c440e42d02c0545078140324201c0c074640072081d00183d000c2014080c140c00010703a000c0da0403400701c001001c003007920003090000070703043d00941d40900910304061070041034440d0302c1200103050701c07540411240c2c40d4444064032640800d6444035690440200e80a0f1990b03d030080131401d503c54828500441e24603500d5034004150703842a64640c0c0400c001406000e1524400c2c4000359110001c140190b00b0a80f518181218078441504040c1c10300d65607a0a95812107144a1280050a40f0340014020559 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 868491573 1250 868490323 868490333
    0x50c1b18180d0912080313060e0d03060605090d02040b0a03051209011e05030f040c0503150f0a1a010e0a091406120d0c020f0303070c080d0f02060105130c0912 70
    0x408452840090042d030854a50b00c0d8040c01c0b48205070b8440002c40b2a0b458a070f80d4800c04254409000340d41c05071030140e589800910b0074005c6500c2110808060401d540c020700024041e1403250f00300c2014000140310034001d030b840320400d08580d0b41e011280030441001c18030104400d190590405003190103946004044996614028024098203070b0310000319130302010348141480008000000001c004201060034a1082850250810f00604c80012020340c0c0d0700010380350188003240c4100030410003042240e4010404140e07540010360190500203501502c4080007088502d51100d4140b00c1081151070840c0c80c2c1ca100d41010300b02180c020003070015030120341501248101c506521130040c507000d6140729500071400c03100a001684038460b01c2c01141d800c000510501c183c0c1560184010b024590200d54000008402002640b01410f00c00c004100c0081400090441740744c1558400001000140c5440b20b103140d40e280602000201030131b120100f200e4000131a403168200000c01240700302809 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 868492823 1250 868491573 868491601
    0xc020f13051501020c0a0320120a0606030b010509040b01060f0e0a0f080c0312091c1a220305190903140c180c070f0501020409020d060f06050c1b18 65
    0x102c0242c084810280702642000310601860000410312011002000031121010241001e42003000303011800c2d500c918441c841c50114110710694401d6280c190030010b002d401401d180c090002a01e034030300a8a080d40717903412b1120301846408100301c0e80316950183c55109a181068904000703101e81c12503070f40c4041c0c0031908100d500882c80381d4026032501800600e000604c0315902d64031662041d0520000108004085041503096440071507800190f500249902c02c44241560344121198514201042c50041c030801c05286001905688060000829005030582d40c400c1c00c2c840c800f480d5a49000c904490000702c5500040084500840c03c41c187d00002c00c1c031014605046c1c0310054450300c00c1c81d0054198100b45e5814403141c80c10003038040411075401d0b991401034013074400580740c1070341d0303003c00001c03a03100c0307400d010865644003824000140f034100c00000a00c0249403090420740070454150700c0720301e20307c10307144256005c481e003928a840c0c210700a0411800360000d0f403035918001c0c5c200340b084 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 868494073 1250 868492823 868492861
    0x40216060f0216060905031603020d02060604150902090a0e280b150724090204061e23030a0b070e031b0d06020d020f090a0608070c020f1305 62
    0x80303082604107900519036100340c0d80021568050544084416110000101000c140c15109400200b000420300020308026881c80340c401c0d4018200b02056030f50007410410013410040c421400c14100d40030425016840c201660040c0d200160307500c000c940000c07103042c0580e0061920002086c10044418159250802007513070014403591000c1940240c0021103807000351035a03120742038100144140101e5000340444900c5101400080d01008078044000c00e00070850b0b048540e01e8508500071402c15006400080200400003e501101031841a20441c4c943c0211040201882c403458100c0c02403c000004514002d01586c80c160303081d0500d241c0040c0112020808181d500011046500340029190720b103008001c41030740003034901c0c420403004001100040d035030141c0920240d660030182d440109941019086030a50780d00c24102800305840755a4850130a100005080042450f00480b04590107a412580c44841d5445d120002d4200300c000034803400c06ea8504420080e81c24075412141c408 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 868495323 1250 868494073 868494083
    0xa03140616050408030706052d0712050108060c1303060c12061e0b0f12090a02032a0d030504030602070b0a0e010606021e0a051005010906240c11040216 67
    0x4418101c58040c0d42901c1180714805080e40200070712804204641d01c80d580141003c0180060411506000e02400002d141e13040761411142c0b050000080c0c01041001b207001c00014180301c1d56161149092b01d03400001c3c8851040c41002031100480e808501749807024560082040110000010004000303868402d10414243d04e80000854a080000c81e00030011030500e0f407464041c0d0070320003e8401604641041118034005010011081500d4002140701c1d00080f00100300d12442c0d40101441c1020b1411a0340602103400d80440c11480300364801088108141c4d8070324454551840c00321f40c1885a6800036003421b10200300c11081010300c01195000301e81003a0148681b038003510b201ca007240e01520404015a000303002c0519010041811003012001c40c209540c1c940c102d9449081c20002c60000c924034840d9910b0040c441d0b02d0541c071030000038041ca10700c0c2e440031680e0594050b40c01800c0042081c03c4c400404502c60030040e603007040200f10315018009549801204502c0803030401c5505044407 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 868496573 1250 868495323 868495351
    0x2120705030d0b1806040906200904050c0423190b070203010b0405010810151214010c0207030b040807060621170f1e041e0e060d02100e0a031406 64
    0x400d5107400100002d40300903d40f08501131361101c0e0b04000081c40700b010100d40c8a80c44e90741107400f03074500303c200c202100441012682d561203400e0070042201d000804c1000501c40600042c401130309100f0000903216161102d00d42003070f03400c0002801c503003c1d1a0b900c0c02c00d0440001c2c080345030f495620140980c0d910035002070013141d45490400003070724000d01602c9565804001d0700d441200c1d8903044031144401e060500121280c4034150032501c50b1440c402a12020351208002d01401401d208105076203050348040c100044c00c581e070b5140004400703030003c4c020700710100d01c100c103120b80c070b038401002400102107004462604c0121811140d0b40b190058410280c0c0c21105c141021601d412160340a5040b801c09103841488020460603011100c0801903074807080c400414074081c101901d1900143c0c2c0081e00c0c400c549020030898004400400c6240100310b550040030058a64090103c014a402d0500781d10440f12680800e42d10303103141d407018211803109204282c0d8840c6c0030811a0240c070840384416 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 868497823 1250 868496573 868496591
    0x5010807030515040207060209041b11060105030304030f1112060a0e01020f1909030c06350a02030601111509060f040302070b030c1c0e0607020a0c0e0702120705030d 73
    0x50100d440480b441c072030900c039051080105113800d90082050510501c0c00508161489010408031401c990f4a09512051001d06072141c5800110031a0402c24505c0200b08a40c101b1002c282c52f4052440002c202d06040d610b50f01c1001a12901a8600702000c3d0001c44550020100c580e956101503a02000080c0342008480301110b06000f19451442400170359890450b103004152101140540c8881c10844d01c00404000500d0300c2041070020500d83d40c4014001d45000704180141540000040078402075980e03041e41101c250400700e038007120700900181c60b030b942d00006171080285483d41ea5845c0c045e80c407030403507a00c04400c00399014426000c2265a207a80e40081c10314081010380b00580564400c0f00100056a4614001c660118020404505250041268058140ca21182c0006094550707444208801082008039844001d0f4801801c1604458441c011030441c40e00a10103400051400580c0e2113008000300d4041140e00e6410350760f40d10144c02c0c050740700d070441d41c0000e1015040024403 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 868499073 1250 868497823 868497827
    0x3080307020c10030b03121308190c0b090f09040c080a0305030f0106030b0a2d15030e0d2a0f1209050102031c1a03030a0504050328200604030c05010807 67
    0x5000d4031740c0080c0c000c0401909080c40c1c012243c10440c1640215000000041120340017440303880810600400010b20aa4052074500346070380c0c4a8010010b419000d000c81c0c2030381d0383c40c1201c19100f600140c41e200740c2d40c2c986003032003841b40312240c000700d81078800c0e241c00c08100366224008500c0303000c9060154400c4d0741c850340224241c0e00a88030131940304101050500c40700240090b0b580d1240e140b0010300401c1d400206204c038007003000e9403110840e02d020708410300e606034150113484940c2d1705400182108010400002e00548040c1e240e003401051540c2c2e145886100fa44500c5105540001ca03202100d019854001007403034490356281d0002d644410005041d50001007074440c40e6919201501040d40440b08000042148a88000068010303601080840e14184004c05504440d03603036907640d0364200001d0514049840115099030440070302c1c0486140706255080c808103a20550140414148402c1d0302e1500000ca09083d51161000900000b08040701c00c42104480082e210040165208001 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 868500323 1250 868499073 868499081
    0x909010b0a2d0f0914071202090102190b091c0c02010e030c0a08010f0b01180504051f0801050406050c09030d0819060e0708061207060302090a03080307020c1003 71
    0x803980240d260081449040d100003a1800c50308403140d40c11114003000071401c22660400e41c455810070010100900500740d44c1d0192070001034002c418403131a41022071004100808541c01300c4400c9a0100e41c2a016a1083c001e07030058421080c441030102d82141040705403010140c0d8840500d100d50300851038840712100c4010aa1a09070b01c4040c0000c950b078005550b810b000d9144c07180d050007070880e0300c4680da076110341c08405040328034000900c16441400c06c60448020b002001c0c14401c8641040079010341c5114083c0c20f0b41c4080d503000c900d030b403941c0115040301c140c5c2c45400c1540140c00203021886100561005118601502081c042500d8039280e1b050035224085100d41c0582000316208030701e901941046400400c030100d0039010b0043d40d85840100e55654000407a0441000244001c095009100c550000400c07682d08050b40c01c80d40359140d803560709100c0c0c507050603008624241c1584c3d90301120300046420003a81c99592030b05800c005d40312541464510f1003039140b90412074400c1e210f442 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 868501573 1250 868500323 868500341
    0x919150918030c0f06110d09060c2a05070512010906060501080601053c09310e07030c09020a0305010b04050a14030a0228080a0305030f07090f06050702090901 70
    0x2614207102200d03459900d001201c1910039100140c07108038000c51410f2074002002810b845c11000200401b4034600201612b030381004050030461b601c450340803104512440000607586508e07290322a501a0305c1c0441c100089548400e40c85035820400450b00481034104c40c51181c424981004456100d400541d108070042d60700c980025000e10001c5c022030b04070341c0050100ca00640344480b81010b0032065200190b40c00301d50801c100b0000c2040891414104400281501e00a5903d8160a940c41000300408091034000c1056502d07000440d0500310144080d202942d00701c9000b4075982e85501c4824040d500420010000a00d44000012551001805e0314255503008007289a940c2c90300800d541200381900322541c0c18000d503002000103030740b40c00305100a01e4190380018841003800c80b4103001c0301c9441e070141045030021401a00060f62240c1141d0340070000c54082903064640c580100c44500705600b00324145030750341101085c640e4100c8080c1c24082e100306c48109640c1e48005100b401e8524880c = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 868502823 1250 868501573 868501577
    0xd05120114040f06170705030a03080c0d182109081009060b180105030601080a0b010e04150606020c0415080a02150c030a0507120503040c05091915091803 68
    0x260061109040c0500c1c81c1c0640070000b00007080402d01e100c4003408031400b56000202145484040104004041c80407000502c021009404114416200500540d2004100c80d40348000001c01c180580c0e020b9004036821642e42089580180701c501c0c258503540c5038600044400c980d41c103108a0150721803103c102c1640c0804000d0114501e80500f007002405010400b1100e080c0c07112802c44454803144d401c030a105541407550141545080306041c20004180c0000342c0a0f0401369400c4c010496005003141116203100c1d9800b00c1e60380d50700380070072982c001040542c446410081e001848560024100c6541001100c2c104141040c02c1018182c1084034460720b40b003900000c030744c000076182604840c01c40c246615070305c1d85412005c2400d00e08650018003214040745000c00c000c81809010804c020a685040c2003040c41d608154581e0303460a5040d00c10306120765501000150b50b850700308440e141c1412651028020a000c481c0754140c8040a8024044440d00d4401171061100840041036110303038040e = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 868504073 1250 868502823 868502857
    0xb0109080109020d140304180c032403080706020c1603050105100302030a0b09010923011a0d140111130e06061c09020a0e09010f0f0203070e0105031e1006020d05 71
    0x2030740c0d60201018a01c41740f06080c002440002042c40001e800f412100d0048880021a50910100641203ca0424003a10001030760160507406164039900170701a030381c11441c0c09860700c0c060703c0c010002e403103020104011030050140e101c091151501c00c80c01130300c1c402c5e0002d1000303070307075079041d041e0540f1052101940c550b0010500e4000f1031902d0030100e421035044000894820301d04c1d154035a100c0c81c0e020110382600410040c020707001900f1706c80d100000d0410100d1040324001803002441003c244480074210300c81c0d40b0301c0180444025807241020400024281c0d4a40c2c0c80c004007244052214814800094214400112203182c28411100b6505000394055904501c0c461050014510301d90102d800804105000c50413440381c0354114483d482e03940c0040761010152000f0401d4078a0014155203850041c030a214405400030000c1001c9076003860700940341c0c2d0b18008000040d48003001070100449104040c00362007032104060303605951054003214200099860201c440c0c1c421500000d083e1120 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 868505323 1250 868504073 868504099
    0x24080f1905010e0a030c050c0109061706010c02120c1e030601260601270c020c040f0b060307051209030301350f0c0a090605030601120c0b030a0b010908010902 70
    0x494516024a074018400000e210058045452400c00084c5081d40840c03845a072020820404001080004600386000760400f13181420142040000210401d20000e541001901c540d21942030459415002800007a00b508040c4a07240c4510400342498028560b009000d050983c0d00c0c40300f001900e0002c0c1c002e00c080e81c0380200c0780c40b882d00d182200d007845001000207000480c17010047c181c080c4c02d8080c00d40f0f40380c2101c0d240c550303c40700c1103030000d030051814006d004445035004650051141d000355000b080000100790403000400a1310f01f0380381e010b500031003441151548480a3311032000b5401200c02584c40d04040241d40340400d22032206894a0f202201034803600804510700c102984050310190b0f03071091803c1506009442c01d500605900020b083c1c1c03810300d002e012100040c04034070700030018142402d01190b120381c4140120000c070030704070f0300a00c20885650066001025415403068032424503240240c00340c0350a403030745800502d1f080d2020038403400600c82d11903640e034002d05c40140030130 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 868506573 1250 868505323 868505353
    0xe070b160f06020a1e020c0d060c02160e01060813080d110c01020c061f06050f090303090a0e07080a0b09060d021306120b0a0e0304091107020424080f 66
    0x81034012105a441e0a941c0c400007030242c006845006400d45802469920078910090042507280942085612505c00c00348140c03141142c40030036540080011581d9421072509a2030044084c0c14460100717006080002d00c540341c20b8100d4103807169a80c40d207100d500d40d000505000741c0400e002030841001003100c0f42d801c1ea520f5101c00d0344150812101d03030400040030b0075603003282c0082c1c0860149030829000c001d41c015151943c680c0303020042003200405420644000e0050150188050210070002440c5400703680c200152560490010450ba0005864021141e01003000f80c13001c8011840941c041031320680c45000361003055101820b0410305540c0d2404200b1400c401d1041a6001481480c4001c6615020b000d908081c22040d8090f0302240c5062901070082003000b800352422902d01004c01101c0e40000c0304950445114480c04a0200411280f14a83d0b00c1801d50095025241003090188a151010090640a00078070310040359641e4100098035481c21070070a500c9908002c2c0d001164403 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 868507823 1250 868506573 868506607
    0x40b0703140705060f010e10030b091516120209150307031104080114160f0c03050d020a03050601110d09061b060f090b13030806010809150c04050102010e070b 70
    0x24003070300c0d2414140d09900100059035114040546594001404025030720401241d80e03801004119092201031904101380000c1d1442404000c2030084008007040b4811010403a50b00710704482040180d050410780c400941f9080d60b9004000031580c44403001c2e24488092080d5820050090017040c450542c68402100a80c4010418000d141c0e41d00d20520b690740e0a4030150001e4040c0e000009031245980c5031402034010300400c0e554180c0d858224203240c2c03aa000381090302c10549802c02100e0180781d40340a48d403601a404489201a101149800070154107801c82c0340907103001c5e01d07a00ba140d074001a200d5140c554a501000104590b104108060b41c8110000110b000c190450300c200d1030348568805c8191854940e02c004034a48558020b028444800d807210303001804070f8480032146906940190140b00020002ca05201c00200003401c03050040c4441d0740e5082e1f800480164500e1300302000e00d2107802c180150f60040d8a4500c00c040d517604002450f2043d00c08428003613007040d032410b107410700074 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 868509073 1250 868507823 868507837
    0x10e06010507050d020d120e1018061a09060105031501080a1e020a03110a090302060a090522060801181103010b1323040206031528091103010b040b 65
    0x1c410046140454410712140380c107003d059029180158004000401e4038441d1881e08101601d0041c1c60002c0d410009605170301440700e5039001c2003003101c03075040c0a07500004060150169080c00c09541a4040c43d011640003804120345010035603c0e940011207271400104c84015901c5d0702e540042e105580035118550b4440680003000c07a000d0100004103040c00245407240c481c0c03c0d00410461003464050151043c0c0071110324030242091070b45000244200c3c82c1e440f003c0d00889001440002c1103100345120805070602511700c8495443c202403000d00c0a0880c1c2c2c001000500d0400040380401d01800b44104d07803c3c0422080b42080c5040d240d51070000b9240404070341c103668860a000c2c03d5101c182c014500359005250008044000316086c2980d080c0000500400f03031000f030100001a6151029a030f00b000c1028107410b0b0001d1003d01040c80340606c4003413010a04000c2e80c0c0035403a5409684400e068910b607800c1840400d05011242046000c280120302c001c250501080c0000c8000b20050528 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 868510323 1250 868509073 868509077
    0x11d0f10050a1409070507030c2d080309061f0b0d0609140103031e090b1806040b070203100e060408030403180f060f020a02010504050f030114130b010605040608010e0601 75
    0x284540e01e8000400300c400c103a0100c1407075402203420000600e020591150700542a0a107030f450003000d66401084215903040c02000206041c0c0c1140040d01d81c620b0813240b5010181c50594a0042c0c0d05107000307240c1003218a00380d107108078400110402da5507040003820f40300d4110401d10071420f00826043da42c100428000c0382950310080020213250301e01403c03842c141918892b43c0300c2d50450600a102081660409024500000740d800010342c2c040191070484004100e0143c039501445404556001002c64050780400c01040100710010000020129580b00300c0403900503038848140700c801ea585d0b001a2590f0742c0c100c100044d0200794020b0040da8058460301c0c0904200c448600c20b0b2080000a4010a6500b540700d0310a03c075458101900c3c83c011101d90006090030b20451303000030010701c41c80c002c41d40a88120b0705902503e4400f500031a0901c1102c0245061914007905008a0708c1c0c0c0741c420507580d030a07410000242540c0180200e44c1075a40654070302903560308011040f000c412000d405141 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 868511573 1250 868510323 868510351
    0x7440c01030b18070c020102061b0d09050c09070f0e0904020307090b010c051f0c0305060f04020d0b15030901060f0320010c0f0b0f0603030a0509040509031303120206011d0f 76
    0x10f80d1100740d02c4062140c092512042500d94003800028a4500028200d0810f64104a0100b140c030540d44191442c19100803400320b181412454014140000311042c15045520f0710240b2a00503040252900c41a00300c0c3c2d1080d40c07241400d0300704841c0000a4401070f4040d0040003041c8820b0f600c41d00070001190040c10a4100c0070880e0b0b9490746840042d034036255407003d450502c02038000303090203600c1501c0810314083c400740c1030820000c1c0719100040d4806125540c001102c40007200ca0f84c0005002c0c0d000188442010301c591050003506500c00c589640c0103500e050750200b080c0c07120100f9102070740c0e0030a40f20075141c0e0038038009440494110300000d0511484803880400203001812525080d445848040b5090070011000c42040401500c00c5200c1c0c0c205000154040f9480000c0c0d0f80b60400480700800c554640c407207200e055100c0c01000e40c0c001d0140340b1021080c0107070b0007004007180c0380381d50848041d030307994400315034081c2c601c00d203015240002d0001191104021401c1c5036044415544150 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 868512823 1250 868511573 868511599
    0x102161d1e0a0b19080c210102300717040f14030c06090c03120d0f020309032d09271003170c0601031407440c01030b 52
    0x6015003180c06228083e1100511aa14108039410440d407200c2c0308800b0322007a007415100758a45154569840c0261105018041c12002d07412824013482201c1d4021542c4950b41c00c030f5030111182d071804240e100c2101d401150554031010300740c81d00c2490709070f4030a51800543d810740d00601c20094810b81b5002c0200f80e1410210f070f61010750340603188408000b1503644c1c0301705949504011000703010048640001e1a200703010388021400b4a0f109410744035040d03842c6c5040160400030250b0b811460b206070710101c00c000e840c110000c000e1410300094040d004e005207a00318800c068000384608050040d4061204a10750308007060b000045914440004031030410f4070b0011058000226441600081036140400030300c00c2c000c501d0f1380384004024516150941d07a50340c1558440c01880700920840d0b000e561512402003d0042d6005080701d0707100c5c15450b005c904641d1101c03c641c1e00440e810f8020b4104840c0703401c2030540300180e4680701c0b80c02030f01c8503180910056000385072109000e42c00c450300c0c0d1004 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 868514073 1250 868512823 868512871
    0xf05030c07050d030606110a03020c0402130e01080f060f06030c06160f0305090a0803281b0c030c0909030f030c1701030515280b0a0305010f05060102161d 68
    0x5100024030f9660000d042490f100c4010a4a002c07a040004150051030302000401c1d4045002680040142c4d005a900c114072660311045442c140e0144140d003e0180c004200340b100401d0104504a0b40411508140c5803080140000e00d810703502242c0c1544808001502d40c1401c402805111950707800c011030345102911010440c2c140c2001c11000a14000751003501442e0180303080c0e026222040c001e50410314200c40c0303400c00075104031030300c9644518403080c05c640d54418204841c002c42000baa150003000c040c50400d011200d98002108c401c4e131840030110385042c041c0710310105160582d4505403440c14405083e001003403031400200c100807040c44114911400080046e00071480b600040541e25004002400d800354094801c000286e0b000c05606001003448504030031460441c10000341e510382e05400141c042d0216800188507508240241e113400340c850b4402c0b440740c8070a03000d4581c91001483e501c0303c5003010340203100503207495100c02880428440c260036404041d01e03490f2003c503070400000c = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 868515323 1250 868514073 868514083
    0x1202040b12010f060228020a0512010b1008070c0b0702121b0606010e0108040b071205130b060907050d020d0b030715020c0d0b0a0506010c02060a090608010f03030f05030c0705 77
    0x900c805911400104601440c1c000f0202c0104042e01c060318101d6040c0c00904d84200e5400480514207400e100240255030710030044100400000340040501c0100c0086c072800b80c42d204003200c2c0300d003c003980c0d0034640d00d01401103a840f0303d0003513807244030241017650f900c011180b01500c0d041c1107119480320040c06100d8107000b00903445003003c0d80c1c0803600343c0c4d030920703840c00034014585810044010303662300042e6007041000c1c2e003040d40401c1150003503903070070011600620b00c038003214955428a000d0014501e0407a02c4e140b0502c0c001c55000c0040e039602c105000801c0c006990002c0043e40800402d110031201d5405003c0b4600410030125403004074500003440e041041d08000e003085c8070076002e61201038040002040c02074054030315886903411911a4113940c80e000349460419501c1e4800584d140c1c5c4501320280c0c40d1503000304000d40b114400800140282694000c0d0004520000d00100b01010100401d42c200d0358540e075a9001419800781c21101c58002614100400c007040c4040c0d0002102801 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 868516573 1250 868515323 868515337
    0x1030e0c040510090e0706020303040f0302010e030f09030606150d02070201090e0108030c0d0c150207051006152c0d0512041d13110f150412031713031202040b 70
    0x1080f2102c1c241414080400c584d4940d504013503d9100c030300d0130400903801205407940300b500705003501d80c0c031ba03c50b0a017a0702405142c941e030001400002442030003490400080d0240d0103090701118544e0351401c1c01d1000c1122640e582e204c118000b807040c880e900e42d243d0000c101c11481850000001d41d52604d000480d001c0c02e801409040d000414400358400c800c00a031400500245408009180681c41d2000100400c4042d1404190005080340c244541040400090405043c0802020340da850301040b03500d5917102d2200c002240c0c203002d21a51a4411403a0205841080300e010b0b94400b0a02003002810941100316014040d018140301e0310412070001e0f100904804103511080e00c094030100410000040644603106001d2450301c0c00b245215006540c290410f8070752420303034200034000925514003e000e0100c0840e00117004100c0d00c881c2c04000174540e20a4880c0c001c078491204100082c1a01100c0d1510310b51030b1442001c1c080b0b4402c0c0604d500c03d042c9103100500e07158803000c1ca8144c681c0500 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 868517823 1250 868516573 868516591
    0x13020706141308040b0d0b0607060906060b070b0a02250c08010c0c26090d08090f15030712090b07030923071e05100c06050a051501030e0c0405 63
    0x400d9105000620281554450900340780e10190209982da82603ca00540c094a50100804280ba200c40081075001102c01640180300644031205072405102815101d0012141c1c14100440001e400c4521415941c0c050b42c00b03200305050faa101c0e0050310007900181200c007021040c41903441c1041185e00842130481e4002c040042c00541045049400d461108501d002000903002d00c8801160041c8400302603008840c1ca1054005414011280e9030b00984003441c0d48802102c10840402040c1c00c02050000c81c169801d690364003003101000100c000c0d0283c0c03081400c10402c00071b03078024401c0d0314040301c00103000c80000c0c850b07141e45c40d50480e8944c00c40380b05000c80d90b190310303000510104103020102904c07280c455085400c2c550b12015126121403184050300900c040005588004000802c1c3c00742c64041c01c41d000401044200074500848018241c0780035142c00003080003d0400c1c02140c1c0b1030300b241018600074070b12400c0114000c151403258141c0c50b000b4820800784540c1c481c000c1030300400c148 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 868519073 1250 868517823 868517831
    0x24090b0406030e01140f0a110306090708070225060201050a02070206120a020412080c010f0b010504090b061c0b01080a020703020c09071106040c05181e061215071704110f13020706 79
    0x204520900703d4070380a16032307010000280200801c980c1d03908220755010040d03191810031900d4500301a0f1414680700c1102980c1c16081d206d03584440340d01c442d08412a0500e500901c155141c0c00c0a0710100d200310a0081c0d00420108081c81e503895401c2502e03500b00e0b100d00001071500c0c0e074a544610058426010031180300c43d000910100b0903809001c0c1c3c0840c0c0c100d840c0304204880c48000084c0061085124140c11951a840202029511402510038a000001d68020303040c6032140008010000d410207940440d6a680200e040b0310310f02d1084d83c85581e419001080e02407810020040f045200401003c2081000742002c4103100041c012503008a101c2e6107540e0549081500700040380071480540224507004104000320741401350300c002e800420700216030b0300646030380780400c0020401c0c2c07840c08264800d1000c2c000c005a025241c0b640304000303558503008400754111580c001e42c081030390003030519140c49900d07030307620f00e40f0f0340b40754003d0400100811041c0c00c01309040426a003081307100313480c0e2980d2 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 868520323 1250 868519073 868519081
    0x80405070e041b1d06040c0504090e030c01150b0a05030a0b040c030e07090e150604140405060103050c1e120102040503150a1d061602100624090b0406030e01140f 71
    0x1040d00d00402911300307603201a2030a00ea00102c1c0e0590000140707a10321441c0c461000c2c03400c0c84d01070422034001c1c241d114001d0010015010301541c0c0da512802807400190f19101c07904a02030160070f005026100000d100d14904248980225203540000d0003880005954804916541c1c0e6180f055a284981c50740740498444141c05003142002c04a510016845040038001f2540c0c50300419500b440010400514400e0f455200129004000923910403079103036055401c2c403052083c000b800c2d07030490303124030221140468070f007083c030601c0744440020140c503041d500c06c182040d181105c0182500c00000000604099850000a15001c003011150301054902c10034080c80c040f19000e4000300c040d400c00740030100910703d4a2541c3d00e050080c60065048050950782066510901c52054000c450b034034213008141d180c00f52a041d81c0000d032519821250b40b400ca803200c07540500c5445040701d540c900031900785880c00800707034050940d80e05c01040c42c0d540c500b4004010030b2200c07480f60041d40070481d8050325280c = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 868521573 1250 868520323 868520363
    0xe100e210a0c1e050d0807080301080a050c04090305030106081f06050a080603030f04270507090e0a0902011d031f02090a090905030a12090605090c010e0a05060307080405070e04 78
    0x2164108040c0c1e0007102d59030b09030240051501c5402c89800f03031280341d440c1e100b501b003140b603074000d515005140a0000000055031131001030803800c1c0301c0c0a0782c2510015940102000708403222043c000740821024401000000d0081e020164846e0034007ea02d801c500390740301c1d07008a01030150480c0011450210307080840591002809a10803402c2d0011442c2420003e91000d0600585c032580004640482e10714001d07000c401003501d0014040503040c4600c0c2451075005d004410280903000c4142c2c041000501c11203201e000340c040d0f040c3c040c2c44d900407440c203100d49222000c140020751034141c0703c1c8060320340b190300030b9109802540540050060310380c0c0095040041c109255400b0481150601041c080441c2c004022071340300d6420703420604079200c1e080001c90060311520501809052400d001c1004800740800c6000266000b641e880001c203010208204801d0814003485400c44000d20009003083d001d040e40e150828060300445460310394070428042105c0301110f04448602421031041d01d03d40d = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 868522823 1250 868521573 868521593
    0x90f0a140f0a111e0a020703050708061905040b04020f03010207020303070b010618030b0c1624060b0a17100503060709062a03030c030b0406060302030907060e100e210a 74
    0x40c4034424142c5000c0004207410404c445110807040c40c03100000d183e1806a008011900045038401c0656075800d5235088110f4440400300c640350303a40941d00d802c01d9400b0416125461040c0d9101380400c402c0d0701e0301e40a00ca2000c01da500c0c0355400d59801c02028002d0390b01040130700321540c81480e0080081d810404001d00f102140141024400d03088078003070001031404440b0560014407003040e15195015240842d650307041c1cdc070710040c1c440070610007042046050341e100700e05100c0c038400c42403041303590324600203c2034401c4044500c00a0085030f4090281e044004803250007041030160401042d884000017801e040003a103110b008503030b0b818020005160003c200c40c0b842c540e4031030000244500c507105c3c14800d20303034a90b0080c105940e40900000c0c02380258094050a10003900402003035880f0701c8058001d60080e00d020351644035004000465510810500f0a0814054a5448111aa440e0a80e402c400042a90303901004e00c0100c032a03100c9081c0d0f40c2d000208486802482d40300d0305414405d080c8 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 868524073 1250 868522823 868522841
    0x2090a090902060a1b0b0106080603251a0903030406020601150201050402010906051309020406120e01020315130e030a080406150506090d060e030c0715030209090f0a140f0a 76
    0x1074101280040507a603450180c81d034000711810464082d0340310301c800e1a40c4070003055001741650305110011801503801f40340d4521494042c0e0803190550304a51403034074280070b400318100318124004000d1240154428481031003043d500600d80c00c000d0000c0c002402c542050b0800001030340000700400c041c00000c00d50000c1d148003400200410b0034a900001c04104050082809205000031040760900c62486100001c0c008030000b19110354032903400070000e200c031458030410f00303081c003114080ba03c9042c801c990041048404072908030818070144110384401c4d010003c180d039929030816000c8001807009003155007013540c2e015058605450324108540030050410500d14240405100315110b2908407040704070210b03990300f07401c1014030f4881c0251003180600a241c0c00003103031030b40c82c01200203598815500402c1d60340001803000d490840c100c0c02042c41855212405101042200003446030007a084103810f6030100c1c0305011505a01035501d401c1e244483e407481010100600d0080d50303c42d640c04 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 868525179 1106 868524073 868524089
    0x20c0904050d1115060d02060c070e0609010b030f06040b0a0f18240909030c020306073b130b0d0506090601060915032c0102090a 57
    0x11400200c41600102e41c00d1a030300c3d0281d06000c00d0700c2d41960900700201843d695400304200481805070b40a0744c00440c10002c64060303141c01d12141007d400725181c90301543c20700c002402555071059004a022440500a001c1150f40f480300c07142e0804411100031640c1d482030f03000030359035100e954000d005035100140006040e421081d11050040c042138000c00c801c100c1964a06080c6801501c483c4040150301b03414082540141e0200c6091406898554a0342e415907004ca858201e081c0c1d9a100883c0c102c0c0d500f0382450643d035401d00c2502e44032100202d4120088144c079050400c4684410344141c0f2001c00600403035020768088070040c24010101f9050324030505000d506e0796000c1d01c000b07505008070307000450254015421042280c11203402a9407900d503441c5e084004181141c0301d420420700e400d09568483c400400807004400c2c800c0d00044c2c0e610100d8007040302007002c035844158 = true := by decide +kernel

theorem cover : BRFrame.Cov 868345323 868525179 := by
  have h0 := BRFrame.cov_init 868345323
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868345323 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868345323 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868345323 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868345323 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868345323 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868345323 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868345323 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868345323 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868345323 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868345323 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868345323 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868345323 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868345323 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868345323 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868345323 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868345323 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868345323 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868345323 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868345323 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868345323 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868345323 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868345323 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868345323 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868345323 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868345323 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868345323 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868345323 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868345323 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868345323 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868345323 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868345323 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868345323 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868345323 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868345323 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868345323 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868345323 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868345323 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868345323 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868345323 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868345323 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868345323 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868345323 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868345323 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868345323 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868345323 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868345323 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868345323 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868345323 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868345323 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868345323 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868345323 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868345323 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868345323 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868345323 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868345323 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868345323 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868345323 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868345323 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868345323 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868345323 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868345323 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868345323 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868345323 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868345323 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868345323 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868345323 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868345323 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868345323 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868345323 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868345323 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868345323 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868345323 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868345323 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868345323 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868345323 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868345323 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868345323 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868345323 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868345323 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868345323 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868345323 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868345323 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868345323 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868345323 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868345323 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868345323 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868345323 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868345323 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868345323 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868345323 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868345323 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868345323 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868345323 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868345323 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868345323 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868345323 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868345323 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868345323 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868345323 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868345323 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868345323 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868345323 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868345323 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868345323 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868345323 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868345323 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868345323 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868345323 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868345323 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868345323 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868345323 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868345323 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868345323 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868345323 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868345323 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868345323 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868345323 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868345323 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868345323 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868345323 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868345323 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868345323 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868345323 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868345323 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868345323 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868345323 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868345323 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868345323 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868345323 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868345323 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868345323 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868345323 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868345323 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868345323 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868345323 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868345323 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868345323 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868345323 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868345323 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868345323 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868345323 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868345323 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868345323 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868345323 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 868345323 ≤ n) (h2 : n < 868525179) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
