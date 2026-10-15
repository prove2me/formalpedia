-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4627
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T13:13:18.095107+00:00
-- url     : https://prove2.me/submissions/9a8e6428-170f-4217-82f9-889ced4812cc

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 832014388 ≤ n < 832194244 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 832015638 1250 832014388 832014419
    0x60a0e0309031006061d060d090c0905070c03080618010b1b0717010e1b010e0a0302040218010807020a0503091207120804090c0c020d0b070e10020601091a0904060f06 73
    0x100079565849081c00314a911000194090186e02801641980325030300282040c41414081400c0d56568080c3e40204941c0d40c030544002c04001c8070800042c036014902400103940008100e0000e51f9020000310185000821202582c003031800c106556030038400b03800d0850703001c050270300071801400d0f41c41046c82e8130800c548800b901c9040030b180419298611010309580c1c400f00054020f402020b80d510000c0c3c9003003a0301584641c00d103021101c10b045017010640505090304040d401c10700010f195001400440c031a030641402c00e81e287c0c15141d503021422070f1544100e04004080e41c004005c9080d05160009100b080805008182d031100769034cc400d0f01d100102540c408031b0f1002c0300480c0c2042040c1c0e9034802c820306a10141000c03000d241481d40004c500075142d102c020078403903d00b40480c4600744651035000005e074001d000c1180c0342c0900140070313660f10402d01c204509103040c4030842c0c0c59500140c2110010000150000b5030300d44640e981e50028110804568040c141e4841000400480d00000034 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 832016888 1250 832015638 832015663
    0x30c02011d1f0c0f0e0418030c0c050418020f04020909010305060405160506031f0905010f0e0105040603080a1d1314060a0308090103110f0d140711060a0e030903 71
    0x24819071803552001654140c28405458030b062600c01d6400714682c0000c8149480100303883e29030303a0140f161002400a11a414414207170245007a110703420113400c03011203c81503002d01182c65500d80e8a100300401e490100d003407440318030302c141880e01c01414481404034803000000c0c800b41c1410f01c010302041030100261700035a0140e1000f000e020601c10f007441148038005800c0a02c43e44103003000c0100d8482c1c40040c3c40c0b0343d0240c1042d55501140c03882120604068002c501c400c1c4802d50356000d521282511034041c12441c1484203000103030518251107448126903202e200305040030085c640c141c070700e101c9000585545098402030322140741d42d41d800c42c10aa030f00b00500001c8004440d128012103920042c4954050400301e4018404502d03488142d40600500346408a14007034490400a054041c01c2c2c404001d541020991145000080c0c0240081520000350344a0540c0c03031090469403940041c0119509070025004200100000e4000e58026100700f130881b490700e01e0900100e46072141c0542c00 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 832018138 1250 832016888 832016893
    0x60a11010e061f06090510051908010807060207030b010909080c060720010e073804030228030809041b0207170c061206010c02030d030906050a0e0607030c02011d 71
    0x400281c00d0014221451805615141124182c01d011014110203034031b001e541d1086d40290201d0b4411440703442282d08200802280030b0031002d1000014002d00028010704889000c0c5950101e8640d1000800004aa800000001c2c16910b414828002000c502c0c0060b514820b082044d210301810070842e03507004960940d5646002e01c1032030b400d210440c0b80d80c45400256418000291406400021712900b5204c0400c041801d118081c0c411099000020a640e00d00880c0f01851000d000000f50140040368000d503542584181c0c004a0b000800c130580102e42410400c1c10414000324402902070304528601078800180b400300400c4103800449101c100c140140d110000502200000d400b200c040380c0d0100000f410b4001500000813800d000d04d0300280586000d440003d4504d80c0300e1071081c40d0320780d005000e03941c0c03015030404001c2c0640020174007512858185404140011924800c0007010946200501180d4450070700407809090000601030031903403107601345082001c00b900581c641c030609800 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 832019388 1250 832018138 832018141
    0x120601090609020a0503150a12050a120813030f05040e131a0106050a05030901060302060412050f0327030c090a1d0606030703120207090c05030105011d030705060a11010e06 76
    0x5045041d500d80380c00040d107090060041c408041d801a0039a0340146003c840a1803007406000850b02141a690000d140c504602008078203102000c9a1211014010100c401400e4000c0c04140c0c1c803802c5c15140d429000b1040105040482c1c4030b21462441030100340b4100c6e160a036114801c102250003500d1055041164031f1000c01007210680c4010720000c0c940c81411010b40c9000f401502e2401180141c0d0244000000002c803106400c2d40900051980142029201c5848012001e94001c104500311031a20074040c00056000000044c3c1d850f00c0340c5115400c8250032a141d0201d20b80d1121625190544102c55400301a541d0781c41006114081c641000a950340000404414050305441c0d0001c06810030f0090000c035807800716450080d00d800423841d030340791f080d820412440c00940e54080810940707880c1b644501a90722000071030403a0802d90740d620000c1502e00700c82907080c0200008a078194801101000755040100103005022480c0c100300c12100c00e00d01c4010f09603a51100090740d01d401010 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 832020638 1250 832019388 832019399
    0x1020408151603050f0601050c010b0a03050d0f0c0209060d110a030602090109050d080706090206070b0c1801050a09061202041d0a140103050a080304020d05010f06031203110f090f120601 82
    0x80300c04114207550f140620035030400074141c40a4110142a250411000090031045c8210941100c0c82c02a40a0709148650f552400c1140d1109007001400c0300084840714200c030014071031100c19010580040002e0256143c0710300b0400e01e0003402c42c1c2100c1440e140030242c1d2466880744203800c01140514001741c0d03503200f114001806480c0f076400091243d1904180d44011502000c00d8a601f03070790140000550003800d00011b400c2d809240c400a0055803c80200305050a5080c090540741c101e410f004500742c0c840310700650300c9004603038041d800980300000030845944980b100d420f410001280051034144c6a104071030085107141c02040003004240e080c03041004440c85292007169a0300045206941142d43e0f1035211035000301c0c050302900300400403505541c0c03000c0900d003d00b0342c0039008104d810250460340300500303c10320042d20304210301c2d450781003124081c1c006d481d0040308a1181c145040c8180c903945102d6040056825000482c0480443c0c1545440300a00d117083c9540c00106465850311 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 832021888 1250 832020638 832020661
    0x2a020d0203040807050f030a12090905060d120804320705040203190c1b0b06040506060f04060c170c0609060c04030309031e1509020102100b0f01050c0102040815 71
    0x1644040031944100701c01c11000e00b01080c0308090303540844140c0100710070f500000b81b0b03003a041c1d0030182162080c4c2206070800d0350060050320449411810600041e03995030200010444880806001301d40c0c2c10351824002d40c0308102d000d03800f611403101d5082c030401c2002c2031009110340daa5201d00031840b41e0301c10140381c00100308500040000300ca042d4914038010003a55052040345a0190030991100400c2038464002d01c07120f00e280311420440700c2c035090a800e050103100b4042d00e0f114040c501e13080105040742000b804841019140a00461429180150446800c1c00074041a280e105e2800b026102004854000b802c8035220300004200d42e0801c07402080c281000078001081e569006c010410000c0d400c000e400301220b40065007803480a040d0008400301081e825001002c03905248400000c0e10040e03400086018000c0e8215450340e102d00801800711501c440c80c50741c4c0f10b040194040415841440100700e1110b01d0340001d0704041d40c502d800303441d165010410034528503101b4108214403051 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 832023138 1250 832021888 832021903
    0xf150f0b0f0a060f030b031c0f0801031e0311030a030501080f070315020904020d0905100606030b060415020a080c150a0207170a051e030601140c030405040b042a02 72
    0x1100c107a04440e915a000490071107242c81800c0500ca40580d0a1508902a6108804140c030143c140d0f0451080c0d003100544820100100301c0200c0c401c0c200c0d59080611410030b0906899000f9030810100d40403200c0c0300c20523800e41d10300b2001c00044604c0810209010700c003400f0580c006460118a039410011450300741030052b030010883c0c1d0300a40007007002c07460b42c0b2003013a5842d031000d100680d1400e818010401030311402488080040c2001c940f0300c20040001400c400c60145880304000310b48e103610707045003540d0060003034a030b100405200601c1401814090411200e100e401120b81c600884e41d84c42000f60041082e2018a4001803400300d81ca129031542c056128184d40400c40c61300d039031a5107850903040c1824044808040208810030120700030b0b4119600702c0b0511440b041c0003a40c81e402400d982e4004c44107070380020716a00034202c40e880c01100340c4862421120155040c90300303000c180030003000c0051a261340551103d808007040394201c0441d02e403048613640022400c2c018400040e241103207 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 832024388 1250 832023138 832023161
    0xd0f05060306160c0303051509040c03060c14071523010905010b070515181203090d0512010b0a140408030702033705010906110406030609090f030c0f150f 68
    0x400e180c0d8100341c3e948864203061407941400c001405490b45000d85c02e0b451680b0441d43d800c19a184140001d114900c1c01c6281168400c000c10300c181d000c0c410040303400c40051000d08400391030900070f0f280012541050041c144402c0400003c070070014005035070350485031040250140025000500c00b1050600034107026124201c54103141107400c3d51200c1d502d60520a4800101081a021400040c0f681001c0c1540802020884040300c21401301c104443e4425031300c400c910310516006000e4580944180c0e000684060a642d0b4036070310b0183d00c41680d912100604080120540d038410038160094090400307000702500640c0c441000b44103240ca408052101c2d405440580c0a06140841c5005102d4180a0003c00b8049181b441841d0860143c0304000004114504084160340850804c40c050000c40319159801d00075140c1c2d5171280300846840708400703401e09540f07140800c04a030040750011b98840c840c128042145009444000f214601c5080c15000c40c0c1d10742c42145a150241d0190310401807 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 832025638 1250 832024388 832024411
    0xc0307030c14010c05121902360121020904060303080402030120030a0f02090307030302010e15040b011202060d110417030408100b18010803030f1510140d0f05060306 73
    0x190850010704113025070740c010b10117014a07200080c00c0c0400c0c1d9100d19400c200146003552213121052001142c581d240c0c82c141e8100181c081c181c15627038039580d1820b490b803030180c5a1a00b0181200403903e0385900007100040300c1c580030003203400151600c2c451a13000703600a03581d043d11b87c01c1a10405081da5001c55a1861003011100b801c00c40c414800c007202d0300004145800551160200d540c80c0c00781c05805815685409070920010070b068040d0060b14981c10341c0011340c1c20302d040310200000060700554010380000c02c003000600148072a05200240389000818243c1044078021801007522180740a00900c8a0007280800100f220028202e044c01c0da035101030750030035007060f08040e60707140d07102e403030320700c0c854803109210810707103d0b800707007401d406120610220f1750741e11030200c0c595a6009854001c102e0035200700103101921000304010400c80000e04207a816800c00308112030321014221082010582040102e4400302c1510503401d000100e40004074030342c075002c4101424080024a08071900c0c = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 832026888 1250 832025638 832025651
    0x703080a14060f010503070903080310030605062b08040305010e010e0d0e0f040b180c071211060412021c1e020d091a0417060a0609180201030e030c0307030c1401 71
    0xa50f1850954549200c003840d1043e207c0da2400401c5503190499480a0700030703c0000288a039441ca0410410150b0740580810702468580c1c205002a6000700349645100d40320401100402c5400516a011410b00501c40c0b01d05007512522040e08540ca00f031040c66543c0e565010700200305505000700250700e0320307600b010355603051903501040041c01c1015640e0711450b914075400e48540c0e2070201c09480350115050b5103510385410300075a03440d98000071003943c55a20100c03605441501c0340d580c0c2041078030301e00c2c05800300b91500d55a88010078a9403001c40c09500511003421f0407118203200041080040355249202880300645070600102c14910705400c40d00319086948003950811074050446011490350a800d010f2480c402c2e09030701071500601c2d01000c50b45100401c00034006070550080070f843e64200a0a540c4540507002c950568901d00100b150030b243c52030156009600141c181100c0c003041e2854441a5492141154000d08040340071a0b25010b040b418084110f000700c42d0041e80c04000c001c10b = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 832028138 1250 832026888 832026901
    0x1804050606091003050a0207051203220c0e0901110315130912050c0c0303040e07080a050103050c0d02010c06091202061e040210050c06010611010c02011a010f0c080703080a14 77
    0xe00b40742415620515444601040300c1b0926581100c034017640003420394050222010200c805e40c1d00694041e000604120350011410700c40c80404520300b80d0040c101300c681c500d0404141c0c485040100301441035541c3d400000a0002124020b43c400e0000070051001c0480a901b04010281d104190f0208546001e4110f0002008414402840c1f403640c103199455072442c9040c10b241c0503d4241d01078041c003002c5030009003104003007043d40c0100344544031003401c1ea54844090084503000d100c05401948100c82d2807220f403c00c1c400714602c0d43e0043c0742c0061083d206484a10070303104050b80840300091401c0c10080515418044640c00c2900030301d922822039410a0078584410014102074440c00b200c400b076401160107034048502031500102a03d44544e0740c0c1402030200181089000c50b01d508011050095610601ca0791114524040220b100d039041d09004440d030680000c1c0725404e1246000c118400b1441c01c2001e8001c6500c0303691040610300e041c5411a080d12142c1103101d4400c0f40c09002e0164 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 832029388 1250 832028138 832028149
    0xc17090607030627150909110111010213031203020c0303040b0714040e151201050f061207050105030a1116290c120403181d09191e08180405060609 65
    0x80c80d8007400710f015001c00c1007039005c600b030075441807840318502103040c0100030b0000310641362124240c85401c078480959902909034400c1c04204444038400e4030003800000c40e82c0d20709030b004a600c2d14005040404d8003a0340c030b00d150b00547d03003690440b606108100e07810341c1c4034102080d0341402001050031309103003ca003210300080140040f00c01c00c40d00174001b00541c45095114404180d1100207000038249800c48003022a01610f0841c09030755500d01d00d81d0f2a2500181050846006941d000d00c0d560324031688000806141128841c205020000c6e00401040c01661514860080303010800d80b140f4000d090210110f0003007603101d0340c0d08070010445031001440039a00080b810160100003540e032403504480030003413420500c2c0854810040480c280d02c202a0150242c1c21107982030802e515030000e459a40c1c240450494090a602070701c2c040040c2064404403440040d600000320031000b5580c80400f140c04c403c3c2012090103403140488014601130061980040e010358010349440400c501194 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 832030638 1250 832029388 832029449
    0x903110a0305030d18020a061e052b06030204020c0d090f03020a120510060f0341100f0e06180c01030207050a050604061e020c030a030c170906070306 66
    0x28150381d1011403103082c176840c900302e85502d40c3c0188440381117a150300024007031000c20003082421036852480d4404041c0160110762240c0c01c0002c04000c051f0a00c42d03030940d000e64101d0008001916840004016110350028008003070341c2c80c001c2c1c450041241d9009142c42860741c80050703411140202000940c07903030707003108085e1507131620904440e60b814200245030203a12040341000c18a407010001c4c107095802c28910580e44a21810f4580c4001100f4203150206811820120103107586181000c6142d150255841450400107079000400e0102d168804c440084074402d1045880d490300a0481c0414001c00e507000c0c0c0520301c00c0d200e41906102855131380703030221a8281810342c0040d00703109120003084a401c0c10f55000007241d41034540352410701d01500c182e041031045901c1800c002034070014540240d41c0d41b6804940103506001d6074400442c05480382c0c000d24800d0080d5407811500d1001a4008184204003400c0103100a04083d0f1780101240c0656005c10a0640d1508035002103000c10320090 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 832031888 1250 832030638 832030657
    0x140304150c03080a09061418160f05010e010c0b07050a1b24090602031e060a080607120e060a06050901090209011d030712060923060a150801020a0903110a030503 71
    0x12641080e107000d00c0241401e041001401d100102000234580e2102400e680c0c0c0141c2c0000c1d512011140082c250f1220690b000b194400c9400301c0003030025511a0038800c1c1a898149051480781c0c0c1d5949039150003007020f6402900145002030183d01c6642c110201564103807141850011003c1c49466a1202d44000c07503a0421031049000d0084942c0c1541e0066031400e600b01400b103581e4200a60000d0380c80d203428043c1840b1081410001d400c0d4900b0701d60f0281240c0101c00544075a980c1c002c011100742c2110383d5580032490ba00e0404010f070600801100317120703441a031070005e04241010100701420358142e100c1403d040c01000312140c141d0340440c030b91607441d2101440108420580c0c0c0040d0401e00b45030062441060000031a1042c00351030741202000e2800382d480002500103400a407a80c030061141d0015903544404041201e14496034080040e02401c00580d819560700c5d00d058609990061001d0700004200c50340500c1400000901403862210895005c00101e203550754641e120301905054 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 832033138 1250 832031888 832031891
    0x601050325031b020a060e0a050709050c210402010305090106050f010e03030405181509011505031302090705040e010902070309060c0807060207080d0c02010504030206060d0807140304150c03080a 86
    0x11035a050b402500a482a1003800301d08580546165000a40d1446030b80d0f4103690307003400c1c0402c1d0260710001140c582c1c80c45400001500d4854103158056000e0300c000b40160380c0d40007040100107046001e0403074403001318480a80a9106052034000101a00d101809850040e45458004c0143e50340d035100404440e48203007019042100388400087c250300035540f1503a080700681130001501c2800d0044a03200e2140001c08482602802003484010082401606409400910f020309418010405075a0100355086032859924503540401c02851080c0c400201080c00814107002080b6443c0c291405086c4003801103080861a1710002c0c0007240511901003401003c10426040c840700c00111648e007900214255510242d900e06280594000320110350700600e072442c0440c0852046c001c1c07602481d0558003c141c00d807507400c10094030101c40d42c0e00f02d420f05010414180058402110400c0c030401c0c0001031500e551401c1d2000c0c0d0500050f0002104010605030000002131b0001c2e401900440301500 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 832034388 1250 832033138 832033201
    0x9040b150301061422021801021203040302060604050c070c0e061003140606070302030c161404140a020901050c01180c0f0305030d0507110a0b040c29070503160c0e06010503 76
    0x41d2500170808643c40418094000140041040c01440c0d507544148002e9081f5012520412101c408502060700e0060043c0c0218020a07490b28140d0400b98111140400039807030f0441954581c140800e40e0350220310b8500c00c4d142080000d2030a41c0c1c0b0782482d011a4141404540274000c8421005540100703450710407140410804203051003002600d80b400e41c0901202d1000594042084002c1d090780b1890210040003050388941c2d051034000d00440d084480010003803900c5042c44c076000703500001401c80c1004428048140312000901507044046016051007000b8041800c2c42c24001840c0d4210700c00705003108108000183d0008200c440358036440c00c00080725144c1241c212404407105a021405104090b03d005c00d012140e0243c0d4022886034001c1034080350f40f2102100544599201210700c050071101040c1542c0c1400c0040c00d6062141058920b0720030052101c881e440e0513003a082e0b4402200c0b104c188584421a030f1000d41010007401e01a04524100790709d145d50b04105411104074610500 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 832035638 1250 832034388 832034419
    0x61b0e0f0d081b03130f0305060a1109220c030203010302040617030f0a09030c0801021206011b080f0d05040c1811030106030b0316090c030513022b0209040b1503010614 74
    0x1610040c000c4405e18001055030346088510720b1000b8001a40d85004050100c2d030181c80750301c5214403014202069500b400502c2c410018200e0440540003606990141c40d4203a034940e500c115008400e45440058482d4110700512088410542080d10200f0000c2c01d0940e01140000030341d030281c6c0705034000c10f94541d48818103e80b441117551000309a00f45403d00490744003019005000180b440b1a0170346001c1e6691001100c0403c075600d425501b01314204044030110f00b410000740000301c691005c180c0b030f0104058119044950032601602c2c03c003107000e01403000c0706201c40c41e08031804c1c00840500001c502d070f0844136010300c010f03ca008181075481c1d00c480103a03141808120005103d600c2d2000e60107546208500141c005080040f000a1810303000900c41404e0503081005580c001e802020000800140c0803c8150100b000c0070455020726544401640c8802809100707030310074032209010341440400c00040d40c070402001442641041020702c2403500911288441403012600a9480340301c01 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 832036888 1250 832035638 832035643
    0x20306040f170f0c06091f1a0d050a050d022109040b040f0209010f11030f0f040b0409020405090f042d0c080717031213061b0e0f0d081b 60
    0x1c030700700b0904120200e11000844104006400003d1035a81030310440e80d240480b0584420f843e2048001000107000301522040087c0c0c00301c4c6440d98450016001e0045078000034039040031032041260741ea40146291400c1000a00500c07071041300a000520924178030107816038969040c1c8050420700d900200d010741d41680c40b41c100c5642c1c0c0c007000d0010460448203c1c5204081c0d070065814501092509444c0e0014900c1850102001c0c0b03001c1d0080c60a1540c210107080b440d901544601c101d1040520000c20046040c0c8000c10040001d2000140d80e0340c9000184004424003c00c104c14060710081002b011610f0207403940f11041c5c00380000c0001c0c0c0c80c031194040303c4c03405030300000d08907940f10704021a404c0000140c0900b0f5601e0b01400b80881e40c41000c5c2d41d6507a21413001705440f902c07001c1e00855500c3c0c10f845844850944600e40102d88003a454141c00302c0100f0640020b0f0001c0d200b288405e00e241020143e036410304206803000e07030302441a0742703404070710b4440c4268040056030082c10704003014505 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 832038138 1250 832036888 832036913
    0x2070608101413050f04020301060b090d0213060302131a06040501021c090f030c0801060b090120070504020c1005092802040f06060815010201020a09060e120f010905150103020306040f 81
    0x2400400107410010010340e1703031480884080b8003035860100301140c08100311050b01c00c640b20040002d00224240da080c0800b210084030b0034854540c450310301000581c2c80c81c1115103101602c09001411180240011031090b280c0d86055020b80c40411080c0600c0e68082484904a034074041c0780314104121107001c54244100380c1c405c0019211149000c0300f00100c0c4020f46007185c0a490007884604c0d2107004444d800d10500550a010900d100c268a404ac030000356281244101c003011b66000d107030f03110f003c64141da020700140c1004d46c01c5080106049007051095076009080035004041c05240070034107505111465806408400c0c810b80401d00710b544681001d039a441c885d180a221843d034410000d406e54109507504c0703580c0c040310550344031305504c144203803171411900f41d4a8000440c500b510542c0e065405217080368008041441c030303c00700c1104101e0551980b58007400024102c1150402e40c0c1000d20307600c41310200311400b400400150340e0004041e42c01c41d80140e0010a40c08543c84c0c20f0082b4541e = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 832039388 1250 832038138 832038169
    0x1a070503070f0905100c02010206060307060504052e0c050d18290a091a090d060509100501170706020708030a030509030d090503070c0b090d150608060f07020706081014 74
    0xa1466100b280c4c5d580c090322102d2007900c04e8007104d2007525074004064a58142d801080c0000d241807104014a16001d16402c0384000b4100d4046880c1603080c020250a8032140f1074000441d03184005c12003044400c120303c03802c00c0c08918208861350740c45c51056040c005c06225030300c0200304910300c1c40b9896a00c2040c0200340c0784040d4210f0758401d00c06802a00c0c40505102da800a0383c00050103844000d010812221062001014034a03a0300080c0c0c2c0f07000051101030070b0010103105942c003500300200380c2c0c45000c2c040c210314070108040c14442c68915140403000d4000c41e04542107004200b109940020585040c0901400c0c0071540340d4890000030b10354000e141034002c146050422180134894040028449140141182c0441030b4480320196414855030081c0e54020703d00f0140007002c641c20750210221806100404601d281e580c151481c0f5150007600c0c15201241c40105010803150100071510003001c1d80d0802100e645002618038003501c1d070a02c5903000c140245848110103903142480202c0703010 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 832040638 1250 832039388 832039399
    0xc0b07051f180501090605070519030f0605091003050705033f04060e04050105040207031b0602090303040303031d010e0d0f0212030a09230a0807060e0d0c1a070503070f0905 76
    0x41060a00602900300c02d071064417014a01f0000c501203a1080c01220f049081d0700c0c042581c8050070050840040c1029402c0c09800e950724600451281d85060040b8081e1420b0140f010394981542051420954103a1040340300f0341c40a450f410440480d00c840d400402001c0b110400818540301c0070741c5421600320000e03e1142e000003404945603801c00c0d9004900b0006072170030861030f81c9034070501080348542c04020300400c80b008401c449115904030750650080c480c01d00942850703c9980401c0c655042500101d0111380c403101101c82601d400c80540b540740607820024010343e14003406650b220100f0481c454200000c0300107000c042ea008003d20201c000d414041c062fa44d00d440c0d0420801800c0c141d8007291983c0c0c68442c2c10815043c1c585504054850440241c07407501619901d440c41540042c404039149070f251489100904004e2041c1d11040d502612140c3e221184e600e800418141640a40706d4210300c04028010010313407010a4070b5002030182008138032620311100a48882c48141e003c25441f0 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 832041888 1250 832040638 832040681
    0xf090b030c07050d05120c03040b0103080306030f0d030f180b0c1605100c020c10050301060f0e03070b03072c06073f02070b2a010213030c0b07051f 65
    0xe50080003002c0c6502040303503403420340d115413100050f68402909c0c040c09240c002c00052011524420007142c1100005040391040d0b101469628200080c07440c0711008a991241c1d00000e0249038080c00c1c074144241011050301d8440b968640000490142480c54500404900c0b442c1c0341c9141c156400f002600b100813a6000c510100c1c484c8054014245000300500900c14204028101446864a199100e407070740c0c1d00356801c3c8441290740203407081c407040030012000b8088200391000d2008001030145114190313038034075000d90041c00e0f65108840c182c690303100500813180c81e03031021044982007950885850395902098101320307a0780c00303140281e880020000c19010a401101d025501c84443d9050000c0042d110b4520050780c03922290b00c100340b4003081c1049554089040d04040d040f070302c1d10b0104404030841584001608a0700700d10818461045c20b50307020f10910508040c52401060300b8001d40389010900e80d41c0d01c2c1c440502812150501c003035207480210a4800b5008070041c4101c24a100c00c03807 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 832043138 1250 832041888 832041913
    0xf0602040f0e1003020118121202060718090504020d1a01081c0819060b030115030b10020a111201020a0503190501030f0b091002030106021b010f090b030c0705 70
    0x254030600c01c49503014680140010351004240031244180e20402003000d12615540043d2074803060011070030f01c5840f2001c004225010000d600301500c0d4040e50912152080411004c2c5c501840030301070009005102010b101d040340d40000b4101998031079840450746131a02d1010030013040f80e407c00184118244417a20103950064540103040b40c00d040c003115110010103112003d202f008540c004009041d0800150f440c280e40c0219441c810401c40000422940c7d40c00302c1e00c415042078110184080c1001062085c0c1985802082c0c4e43c200201c94120007103a24503006561180301c00300041c05029005107008059454107100145009010025556400d525400421a6200f11141d036040721304048056504a03c510555058a512603803c1456445c0342d00c4400c4d00d0300000f4125100380c03140340710421945d1420b00155009045640040c00403d01c0c0f400481d5100171038104140c10800c0700e903580c0391700c0f5512404520854229038001caa498584204c0f210040c032030741070301900520401c1d024111 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 832044388 1250 832043138 832043141
    0xc070b0a030903090906050d020d020f06210c030c09040c0225031401020903121b070609080d080f070c020406091a0a090912080601021c03061a03040f0b040305070f06 73
    0x82a41c07007a51000180364986015600312107003800380350b070003107848c0103001e0042c00c21101800009000402d2074010014500004250780c0c42038004c0880012407641034109680c0304841c05400c40710000c010350842c68602000425400b9540c41e40b03100d261207641c6041c26a000f809151086015200d038951700c1081d01300015029072040c401202d02607000c04400ca086a410b00c2503c2c858140200507000e810110660468241c0051407602d450b10820211240100d104011000091041e900d804404d54034042400e420329010a0720f0406108000c810850303c004c004c1c40c000e6000e415400c180004524500208000700071580140705541c0c544400c00d8209000103c01c2094110b08607007a1134113548450041050303d00f50070300100040314880407400d0490007502260391010381881144c030144421294030512a48080052020907510003050114503440c2c4980400b041c801582c082c51810a940d490071140480c0d8005032a5058039404201003620560841da1400e0708180c0b000c4c5409240e080040 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 832045638 1250 832044388 832044401
    0x40b0613050124030b060a03020a110616030e010c0c0305210109050603011d0307080918150103060f05092d0c0d0501050a05011b08160f0209060d080f0c070b0a03 71
    0x703501543e200c440805036031182c05411810440030b8a203504000c00c540d000d80207504030070043c2042c400c0d1138000c1d1041c518104802d503c100b03500304d4a01f0b4806d411040142c2140c1b680f0303140b042d559040c80b40790440e440e08500c40d844044d60600e00195108440303035205045070b04002060200e00b0001d400020b003078400381c0055024200840003081080d0b02080084100300030000c1c0840540c00034400d00012600903000f5154402001d000790403000c980c044454040b4100715040742900084c03a0034007500f0b5a240c4680000780c0700c58414040b5040c14080007513101140109031880c645100010303480c007041c010314030000c1b07a02c0e592072845460801449121554024600c02414503240000004103443c284207030b0310403202c040cac40709540040040903802c003101c0481c06c00ea0b0202401c005514282a003119142081805a504813000079158810008140405080c00307110300e0103221208045460b50302220a2003824ac0d050558582c0d62040c000e0030601c0d144e0185e02c1e0980003081002e0803d42640000 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 832046888 1250 832045638 832045679
    0x12100905010603120f0807080c070204020406030f140c04090e01061e0305121314010e131a0a0506030c0d060e2701110f090d061a030d03050f040b06130501 68
    0x1000e0806101300c221040c0320081c001700002045100810019070098460540004480202900c1d006181d0041020b9a200d640031400080d07460081c00f00b0010b443c80b0f800c210200e0608034213000d0919400c4814140942d004000c42e0654a858400d000d140035840100281074030703c01e28a12401202810407910f06a1005035181e00421b0301c4404101c00c400e04032012074000c42032201d01581040310442c0b50446490415060240c1c079890007c081d82c2d4450f8090007030308400c002060030700d0658210301b00ca1511007640c07801080841401d000b595118001d0b650701030340894006840d29400d240080280526a001c0f13109015004140121600705881c502000000210083e03800c2107000319070303404c0b20781d0403134100714000090082c0480c801b0243c000f880070b41c000901c05c50081c0c04a4a4900c211038680c0741290059800c6001038040782010b0010220107007843c01c017001145000703054400f202a004000808420405000858990700c00d00510400d03115404104425a110002da8400d0714549100 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 832048138 1250 832046888 832046903
    0xb04030212030c073c0f0906050d03080408071403030a0b030a050a032f0102093a2420070f11030a050a0b06040c051812100905010603 59
    0x141c0424400002c2169280140d41d401404507a01d01644500c003d29488240442ca03a0000ea442003481001018a01802c05440303103800068640300c0c0c900600150355018400003820540c04005036500d4034150035540b6014100030100b6074072890101070600c00c0b80001001c1500301c1060714400c610010203984203001601040046020060400d5070750011031400a00c203500c6000760b98002441045040241001d1101c1c500c00d500385070504205418464416079503d030740c0412155114a015004000d8011040c070241001e8607880c031401000301c561002540f011940700d00840100545918003e0b01e40c180d444201c4100d01d45001d82d032000e0204107415034022000d10b001c10840600c00000ca802c000e81c4600354424030a1540d540400181004002d10341c035009640c042e1001c18410b0044a401c40d110b003540490741d1070b00c541088125007031a0303000b200300501403200180d08580780c40a0700c43c0032000c480100e07000b0301844080d1301e0030140300c1450300100c0c1454425810001c05401c034600b541d104044 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 832049388 1250 832048138 832048159
    0x15090f0615130b131e0e060f0f0702070306150902070305121005010507110d05031b070b0f0d0207111f020c0f21070801020a0e090a09390b040302 64
    0xb00c00a444882c0c0d401a4015401104540e80000c9a8441c200d1828080c080c030001c000308194403c100c5a0b64403410320660084410000b49843c400445684500180b030600d40038140390100a60340c0b001804020020f640d5500542c021651880002004102d031440075542c8034a139190042880d04800303640700002e000314001c240180c402c200704006885040c3e48050800c005500c0b00c0205540703110720b45401c0052410340c40c001c940184018800744203070b5a006038400e18140c0c10740e443d01d0403d074000320300920240b04c0622040000d100320754802903441e601507280d4401c0d0a16002e50404051400e9201000190f01c841c882c4964038018030401803602921f1001c24040d090049000d212880c09600401000701412480c80300b200300010f00c46110100c4a603940c50300e8459089921040e00400400e03100b04681c40f02c2d14105010680c00500d081043c400c4110b40d9898405030089190000c5006140c220021f2118070ba9001000110703049100d0328100c070369101a5901c2d980e0283c08244c1c0500341051 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 832050638 1250 832049388 832049419
    0x9031718030a030e0411091e210715030b030a050f0106050603190510080114250228020a0306020a032904091e110a120515090f0615 58
    0x50228281030f05034840c00181020802080014540c00805c44c420950500c42070b0000d86070460080d10800c502c608101c0341a003001e04014400a112001468201520000350104100820002c0464011904080c48261144000d8014094101c10f03184c00d840349071b210f0001e01c600011021414200100200004c5840c0e40c20701005210844420459015500300b100444040b680402c1d4040400c07820301175456110380079507080da000e05440c0e00702c801408040c420746135900b080d2481c41c5021985100816181c801c03002c0d407a01050428040a100c5114000c3c010320302c0100843d00c899802040e4110043d1030b842c082c0f009400043c25140000d203442030640c00048020048203c0e00b011140400340307101c1c03c174200005809882011911036502402c013008000100c140503003807500c158407403550704220030284240107940f40c0c452824032450010600106030003017158110100111900c0489555000080d807810405080101e281e01c00d043c204035201c80091240c0d58040000c80e00aa8172a5026 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 832051888 1250 832050638 832050643
    0x306190c03060506031602150c0403020406050405130212010e030d0203090f07050612041104050a020306090a15050f0303041e1806060909020d0605060c07030213090c05100903171803 80
    0xb406843c4d00102d0400205000008218464003014410b104844507404d20042c2c1c0b43d20010141c0300040154008a018400c6280500416001c1c16042d00c0400c0180b510320032109100d80f01d14070181c0500368214010b00d1004003034018408a589250072a036641900c010164000c0d132041355141e14a02038170010103480c031408200c00c170481b41c0c000e00c054105034154405a440700d8026008440c0300008118082032a01c6074000c141c810b41040000686030b10348041807150f00c00000300180c510b10700d064041c0c000c440d00360744580140d4205a075503888400200300482c3c0b0314421504880e8250074800c1d1001c08580714980920191070354080c961400000300c0f8800b0b415240240910b1001c13400c409018800165254041c0c024002210b0000c100c0c55030b00d40c08030b0b04030740c8480100100c54111580a005506010340080002201d4170f00802400b9583d45900c0180c0000380141e40c407606c0c2d05c40820029502c42c070f80b00c0d000340da04101540c00724201c19245c6660781c1e00c0300158070142400b010002c8070a1030701 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 832053138 1250 832051888 832051901
    0x1005130504110f030c12041406070207030b160201091a06030d110d050c190302010203071b120c0f12030506010e120c09130501020c0304060e12030409090f020306190c03 74
    0x5010241444070f1100403031a55000140341c44149581808065a040c10820110703000d0750181440316071013031a000d9401d0070007000a1201055606ca42000c10004072110026507004207484c20700061750348104022030141c46c40000107040d0742c080c0041901c0403210300341c14500660f4110304039002511007100607600c1c900003800c40481a0010000034526034050801031401e000c0d110300350b41d40c00c41c030804000341c21182c2060980060b0f40c00b00c2002105600010000124602c1e000103c1e000c180c1c550300d9540da038104084ca001000f142c5540f610800070038803265048141d01003074140481030303140ca00600601013101c00f18002480c84001080034280098440308042024016000d641c0d24242404030902c009440940f041c26048116004148203101400a040980700a155118585040103006c40c42c1c40380b00502c030340c0c0c101c0c0100164840020072101240c5440101154000c0a424030681000840b14041d4160003100100310b10625882e09070718101050381400c0000001c05101102120700 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 832054388 1250 832053138 832053161
    0x80d061d07272103081f03060b040213080f0c0607020108061513030c14031614040b06071a1807030311070f0e0106031a0d020f030c1005130504 63
    0x1d03149902032690a071100c0d15452103010b5080c1c59100740ea070316101c074000d000310610307a191036501d40a41c108150f8821405600310100716801c4258200e00c180002d01304c161840001c110030b0b0307208206461901d49030140d6500f80006010102c41c6903850012580310860105c01000300d00030f900c041d10300d40c6044802d030313034649806941d1500c0941c2d0b410709100c0489105002021a00018070801d442c00004035240c0d03024510480005100615003000240d00114001d04e41c0c1c032075009102c4586c40300ba05142060708441002100e0399000200c100410700514400d20005e421400005200c070034060b03481c13101322400c2424040501950713101d124080d500100402c1582041e00036881c1080801d06c91180800b80000c0b0b54161450725980e100c454000140607405460b01184940040040366007600c214207640704035000c55900c544005000843d40542030304000d03c5105402c14108480e10704001300910b1020144c1101042d5070030396405840c50304041001c0d01d00200c0349001107101c1c205801096200c00 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 832055638 1250 832054388 832054397
    0x17031809010e0f0a060e15010801120b041b0f120b070c110607060e01050108150708090309220c021011090303040b1b192a090f0603080d061d07 63
    0x12030300e90f1840c02407940a400c2d920032a8440030080703480e060000380f0901404108074013650080000700098064001640b04400c0d01c00c0a4060101180b4049099517005500101500529119068681200d94290001d546a8201039800b00707400d42040141c40c5031070700900400d115aa00c9902c1115040c0c90704c0c030020003038182c03200700b005c050825001922040c0e208210120710780c3c081080203401c50301d0076440001242d1010b00001120130780317821544e0304103440d46021202443e10b210815940d1160324103083c098208280d01000744618401007100141110101340100031100c0c1000350341d0100d03240091501c4e4606000740148952034011548000806009982414942040e441032a0400700c00f20002e02001c0d02c1d00c40c5504d44c280041d00850130390320844d0401d00342c0e44c00d203d034000141c10794510040c1c0d0200f0200d070507803960610480072102c3c182c1003c80c81001d200c500300302414441e80024142203002c281d460070701205401803810740b41a031114082c00100d8040018220070182c072a0000324 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 832056888 1250 832055638 832055641
    0x4150e07021e01151418090102040317070b0621060a050f0a0b0a1202010c0b04050a05060604020301030b0f040203070f1818030504171e0c19080c09040c17031809010e 73
    0x440d100f403036008070040d0003050001100b40001050001e1b060851b50350250707035400142401048403c1d0544148048402c0d183c0d0300f40311003680c46084c100d40180030544100d0345030042c43c1116003003080450f400c10340319064503d00d0030106461409440c00760790029080b10f81c50700082c4059214031944101080040c40b5403005850010b0701d612a04841c50107074100b040c0d10350f105021a00110000c0d0003170384558000e20400c58542000ca05000e005007072644101d004200400204040d812180d030440c0e15801d40201c0ea840c0c61000901d003084540c0410450200e410740081c03204402d00b0510850300d1036580a215000b004c080c2d04040c00652100100130400910007800609412013008a514503c40304440c0c21140750041008139003040b1250003030303d500c5140c2e00d00b01802c000f41001d0408502c21381c886402424064902d4440c94804204d07802400c030030300080c050080b0076103500010a014428460724820000c942034a03503000e00c522007002da100301060011404c0914600b8100c905002c003e100c1c5 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 832058138 1250 832056888 832056899
    0x90605010e0915060d05070f0f0b0306060f0a02010f0f0c0806040203011d0a0b0301050f04020415030224160305030702070f0501050d0b041b030617190204150e07021e0115 75
    0xf00c000584a241c00c60703407070319850b8000f5008101c000050002003580c1104549840c0381000e42c1201c60300000c0c0c49142c18400d0110039207440d0282c40410100c0c12085071940d4020004900400e0301c000c00e80300441c02e1406010400840750300c80d04c0c210302980d451648a030340e09000d10091b0b20003071142c0034411101e90740da50000c801006110340c100c0e80414011032030204400000b425103000351480303110040d100060000710300c2c0610a04540060110100000d00c0ca141c0004281000718019440200b89030030010f02010603c0080345c002000c1804203c0703e1000504004107250411110207000d0f00c41d0b5600440e0018003140300b103003141c0d0169101450072a144d64884090a4015035441e0001d44680d902510b0b4020214410358424041c2e500254907440c0c81000d41c801502140c10f40040d401900f0a185a410640d4a01c888031b50190b0703010501540c1490300035095070017a030021021080c800c003030101c460703404950098984252070b148401000440d0a403401c0380c6031b280c107046880d8581c4004005 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 832059388 1250 832058138 832058173
    0x10f0506060d0b1c030810061e050a050c2a120a11060d021216051204020d05120409050f100819080f18040e070b030109020313080d090605010e09 64
    0xd0740b81004e0075a07a078020106807428819110f0490403404248150b040250241d01065400002c008500d41103e4413003100c01d9030700744566094043c504020001844010086c050740032107800e100b82604071003044511036100d000c50426840c008204449030800100d441c540207003660702e8240f003540500800741d503555880440044c841c1c120358100358240047c0142004c5403000c1c05080200720b036070303005074500030004608040d90111280d003808030910100d00c181ca2521585031b4402e60517120b4528407407007810828901302000c0280c4d1765a540c0020003040d0680d41e038200d28040d112a20f60280d443c0c0320044030b0340601c1414000c0c1182548400080000b142d140121400c409000c0c44400340307444141d00c60400c00d03030700980100c10000b0205229035400d0a00344a03009011002401400886050a00c480707110b110600c5100081500807011860b41e503e006d24a010041d88100404c0c0e459030022440c102400c0c00007425030b6914070b090000504080303485041d07440780d4201030282ca100480c1314071461 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 832060638 1250 832059388 832059401
    0x6100e0708070e0d030e090a0203160c080d15030c09021e091801060f0215220501020c06040f06050a06060e24040816080c06041203020c090117010f0506060d 69
    0x904118420400d4140364580f00b013480d80c03241c000da96010380000c000003071003010701015000c02c119a2041041000603501b001c01c121900303c06240066040381203040c0382e03626000340c006c15008103141541340f1101d1094900d02c101200d1003803000400d180d580d0040801203020301441c802c0c10b04400140150228030f0180100103011000b030440c03402610903002e40d4240103090304800c0c00f040190410910b29a010426403000c18901c042d200c0017440c00003100000c8171141c007903036030911204202c010201300c0290160760020076240101d42ca81e213402d003800c038014a0852411754519240401140d25502980034000546100380c8456229031000350a000b0144c440320b840c42201c80051154030030721300c4072000900081a070100204004105502d14206171340055007c0a242c0d80013100010740c0d52108800c6d10101c91410b1860203090766070b804d007070303090504540b002070b1320403101c2c0004100e404a09209101c0c01007194020048100045444d00840300305880440d032041c0c050000340340b10551500882c = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 832061888 1250 832060638 832060651
    0x903030306041d1606111c080601140a09031502190e030c03030714011d120d270309120317060f0d0501051f0302060a0305090c130b0306100e0708 64
    0x2003104401e01071550030000d0603800710100f503110038000c0245c10341c0865074021204001c005002c20010480009000000d004070280c14026483c1c0094881d0380a4a1111074001622200b559149811000103011710500d000440700c0140c860320782d2080e181c1074030a86159615240c0d01124403080b074003069500f03110790414242d040c442c03a00003100c152030034000b414813644580b24440c9106c2512a00310300352800c601114041c1c1140f0b510070711400900040161000800614880c0d80307001541120000c2d0404007128540510341c054903d620722000d10100c0c1d0510b000c0e40d9003086003511500c00c00c43d1504035420240002d2a107595640c500c0b080c0482082c2c100d08000d00d18004503035408003044420813600c100303461fa0f0b5595420003401801000701c1d440c0b014228030310303554100c2c1140d00003090b5000c0c8041400801d580c0d070380000e01d416001c10085985140040140900074203042084011b0203803410701d86d00900401c400301d403160340100c840381c0540d0384a03d1241550340c0c07851401ca82462004005 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 832063138 1250 832061888 832061921
    0x5130b04230f1305300d0203040b130c0e0c0d05040308061005132d030f05010c0507020d080a0c021504090b090702030913060e0a0e0c09190b1807020304080607020102090303030604 79
    0x441425190000007010701806c405805a00c80c41c0c281010741c1c0000c0018004612041d440740c600707000400c0c2528000070340b10500da034100e8603141c02c800c088003802540304882069141c1010301c4107140d00304490740d00c100300c1240c08003111003881c28101c480d8042c4440404a14502c14014019107480011403120300306414100e041800e21482d0842c2c0d114569402076a00d026111851014061f081c0a107030322000d03250810504c0e241c050b0f4003141000c3c89104002d04225404100303000700600c070b43c001c54007043c5c004011706081941078520b2840743d031040c07244c02c809614007542443c01d41412a052803081c2283c2d00950b050201070b100340460340030802c810034a031540c0c400b80480c0445542c5c00643c0100c8140200141d65070140321854a40041da070b80d03e0340305028100820281c8950320303012008220402030081025074206000c600c00030107240c0503450f03040040c003c100400b90b0001c00740003200c1e0300c40c04582840c0c40301d00e0240e0803440384101181e0036030400c00000f0a80c1c00d0541180065203c030303402 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 832064388 1250 832063138 832063213
    0x2181e1c051203040201170106020a02010305040f0b0a0e0f01050f0a051f0b0414010e30032106090c040b0901050c010c121505130b04230f1305 63
    0x3a080d040c08052484080d0b03009010040c0419540d021540480603c407503031002204d54100080650b0395400303228001d040540380c0000038100a40185822740b100c0d8082108100e07401c0031801c405c041d01c1101e90324503442c450500300c84210501401914043d4581c40040e4115485640341880902801404410080d401140d21f03070242c0c1c010b50446000f030401551207503c4604140fa9010f040041300540d604118480b2840310503540c80c640510071240c1040e02c000d100080c1c614011983c800c07044090b007910301020400307070046402c00d03c4100a001aa4400001c96603c1c08200705104c48281c90035403078003c0034007050101004400013015500f8050402a00b0700103c003a1040c2075031201c01c3c071600010080d00d008180028140070b20080e195040702000080c0e418000400c07241c0544100260096440e003440714819111a8000102e9000c40d4005001c00c003280401d00103001c1d000e4841e0f00f210151500000c04202c83d824010481980c407a0283c9807216450400700c0c101c46000110b07084e032041020 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 832065638 1250 832064388 832064393
    0x601020304120c1505090603160207090c0507050709050c03130c051309050d0e0d03080402180c070506010e0402060403030807120608010e0106050a0602060601051b0a0602181e1c 78
    0x194040420380c400c0400c00f40050510088022001e41e0841d101e0501030144040354003669480c082c2ca9018205e00000380844140760403ca00e0030000707034060460280780c1000118079581c03040041442c43e00034004c036400329030349007040d00441d80104d881c0c4030084024800309036512030b00b58110682d0b5005200209041d40c80340c000800b45c014802c400c4090550313803420710081082c1407003512200110740c2464a540843c14010500850b80c80c040102040940d0000404664030101401c00141c42030b1303015100340c80c01c03201c00c1e01a0390121905581900c5030200004003881c02d003c140d0f1041c0c1d0701511050400c5e203503603000c0d00c031000003034400014805062240440d188482c07242000800c90700c800410306c04200d1240b14211415a04600d0003050140303400c0c8002a000143c0c5a0480300a29290341d4422400307003154030206e10360914400750f00805881e030003440840d030041d12540803407107002a03044d1540700c01c224120401c00d601c0316049d08842c40000a0f0301d40007441284240c1201003031303500794000d030307 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 832066888 1250 832065638 832065659
    0x15040f080c070e0a0b01021c05092407030314090303070c020906010507060e061b0408031b10020a0207050f01030b03060c0f13150e0306010f1203050c150106110703020d06050601020304 81
    0x1312562084035030346001003403166a0421440c2d105080c03540b4035003440800ca82c402000c07441070400540c05980104548140184500000522010514211506c07400c2c20315000300504241d010000240c031039039004c1964280701008482c0500303442c1d00ca1103043d040c25802e0142c40e910041a4905110080c0b12440200320a4002d8074144032000300501a41d107450001d141d078282c4540d000041240091100380301c0008000f080300c4207900340b180703412900300e120b481c014a01400011021007550020a5209d107850b0005000815250700b140c031010503400701d50045013240c1c009000a41d242d40b180340454980003510008050300d42913070381c000e4a8201c1041c41050610107036030000c0710092900580d590441c3d8040d25401a015089001c0c0c60326514103102040301807664014412410081a01c1c00d0400d40514120b40c42c0303100c42c80076107100b011034040d1000040c50911801000c521038440110a40c000840d2501c25294010144c0405042984900c8000e160081406040d031100300404030300e10030407 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 832068138 1250 832066888 832066891
    0x9030303070c1718040e0f030a080403030606321b060f0708060d031803140c031b030a080d06092a08010e04030c1b09060815040f080c070e 61
    0x200d80310492010550319001280070410400f4070400382044c0910003a90740704096414150908480c08075040f850500000d05210b60f07907042051034440010401103058106805610440c007036241000448d42e180c40c2580d841015071004c40109001081c10034090060201e98003011940c100c2c99400c010400100380722030000031541d00104e80c80b03c010403c0d001022003d403607110b0324071700e8029803500741003011950792680e43c00c00400344103103901250203991403040900700858004a81c0c9414603a0040ca00380c440105014582c002c0c090140d4108200614042d0300035403400250003403a20000c20740390340d0280d07080010380c00001500e480c00083c610525000d802c02818200c030003038054a210b800c01d16030751205800100144400350004000240321400c1181e8420303014104244081c2071868001c0100100c07240c1c0c504142051000410384c3d000e01d90003a000d640d4008222030031500a509842881e090031200200340c8800c0c40d441b440040e01e500041d210503112002100d0030039868050909000c83d0 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 832069388 1250 832068138 832068151
    0x50c0f07091410050918010219050a081b030c18060f1c1b0509010507140105090c01172220040b100905040506011b080415300209030303 60
    0x120340607402d200740d0070804502d40010403030300030040961418000c00c0813140e0081005540e151402c10040141d0001e4040316416010500c03400000242200c000d404d41d0042c0c50041d0002d1301c0c60000456860005c084050301020301106213055036214807040785981d0000114070f21500d0390707841e1903980da15844041d203103190031001c10700e4540742941d18a031040300b8140d010b444d6039803c1c1080180c06801c03c4c070282e400080146440b6031b44584034001643c29204121740101445191304490071304807810342c4902c0c0103a039034400b170703406495036140112944100c404542004100d40307008288000744481c140c503403960f040302c20b07401c03802c145840301001e21510a81c3c0c181c01e410402d122024034a0307d0b2040c02000da404030342824030721007442402003c1c2040c0e0701401c0d01440d41c8501050160303000c3d040c4544800704540c2494044c592a20784040c0c903030024803038012040212050015a9030290750540b071021201c4806c6c02541115821030040e01c21020408411258200200c00003520140000c5102c0e04 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 832070638 1250 832069388 832069391
    0x23090319062004030305040b210f01053a03020a08030c030601020606180a1d19060c1115071e051806041d04111807030501060f0807050c0f0709 63
    0x4210254014000108544619060702d007004203100082c2c220b41910b050345c1c0a40c03045500c0c2c6003c803402910308603103d1107812608040c90100b205034541e031400a07059031015074288480c640c020b207203100e41c400303c0e03002ca41c00c800c00300a4202c0c402d60030201450b000c5000c4d01c104e035a40c6482d034861041c45c0d80142c40400110f24000100b2501c2c2d60104001d5800c1001503800000015000c03a103001200009000c00316005d031686008941c0d044000c031030070401c0141c04241c51080e80c0034507590104890400d000c60301c02e400d080400b500039026220081001400710042d06036500d07891441501200024003110911840b01c0c106508aa104001080d0301071107912441e945d2002e054000b040c410807e14161321422003088240803601900413070141d29080f0000f003c10300d445624042020440780031045800821944103102c801d41c0d0385003110b0040b042a10308001d540d0701c48030216554050003801c107001c1070756180072440c564030540081044005400903100794200e004c00c903608080d0345902042c10039 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 832071888 1250 832070638 832070651
    0x60f070b0417120103080a0c12020106210b01060804060905030a0f0e0907050f1315020a0b0f0c03060d15061e080c0f01031104080624012309031906 65
    0x4a51600c10196071090001403c0407a010020300380c0b2101400020040500418103107000c0b8040c0c0d00c0c143c05242d00080b100200150110000d0082c4800d100e9a02550482c0e01c43d071840ca000d20022018064201c00c034040240c3c24030100740c1d104400a401203508540d6164401c01061040c400345c00e0380724440c2e907460044914030600800112000c066181f04841850a021580390854219440d202054641c2c5840c0e20a075690501e0b0081c05a01404000e007003100204440d96021660205203840b40044014584890700900c070001e808075440203180100700049a903514000c02500101071140d1240004030001d90048001e4454584c00034400c8408180c2102050214500b0340c800b41c0170be08020100c000c00711000584054800c20400e0505640e0843c00c0d02407018a000c51f8007038041e9104403401c030705007a9100c10804611030365130050001d10a41d407181942c850814203c9159482e0000300301c0d04054996200c25500030b84040b9414802e100b02445544141e140c51001c07070380580d0001804 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 832073138 1250 832071888 832071893
    0xa0611130e01090c0201140402040b0a080f010c031514010309080906070f06051f05190e07020a031d0d14190f140a0305040b0309010f0f020915030c0414060f070b04 72
    0xd90b4101c03904c1c1015079040402a11800e900350481036442901205c01265545000002c2800b1304481c1e005030800d4011814001409801504442c6410101d650108800f100c0c495041201040358020034000820707180c5001407961190704501c4445004c0d080301c9142902e2080024000d500c030000c100d13403500650740c2403810b2090a100e50340d88001000600782440c0090307035650724158082c2c01103d224a07040007d1081840444050f540030b008648214907031420301030030180d602d04890004400090400307121048805213052003104562014240051000c210354071554406140f24000619205065030b050300c0a14108034142d2190080d40303c1d10000d05e950801884002c0110707244021a440313901e00000003640f201c1100e08440c0001151078403915a0050113015148604d45c02c110103041a030400c401a00302e50041850030380444550301000441c1c85030740c0c000e002c1114a000e000405000030880000246100c3d11450b80033801585095402c2d21a58419040104c2c141c4102040d032040008 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 832074388 1250 832073138 832073141
    0x1e0403240b06040506031308070b0f01150f030b360f010609030b070207050a170f0c090118090c26010908161b0b130f03050a0611130e0109 61
    0x40c111016102030149403400d40108034144210f12801e4001e01000000508803500c0a0f0412039840d03100c20015901c8c49281405444107505442c1b091026502c1400081c0c10300201145400c81b030110345864010070b6029609400078400240e082d904050f01c1c2103e6a0124011455900a60302499402c480c401d110f4601280a8100a28048440018500600c03e15411540101c01c90307500451038621591022000ca0030000345502050304900c0125000c82d440c0001c074100441c8192010480c0e03401c1c1805410550b41d0840c00f0303121038100f00c0510042c420324200b25841c103080701081e8004140100a9512130208805e03642c4003032401c1c2c59081031401e00d061502031a4021004810080c031060180d6220020b1602c225075015404500216040d000c0104650780c804089108003424030703030969145000310680c0c2c003103804282125002e42e804603035003180032482c00a07241c0140091030074481550f103070002000c40c101048903610061000302c4040304c0d1000407902030300320f842c0c044002d945045d09000 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 832075638 1250 832074388 832074443
    0x3150e010b0d06090309080d0507140a11010e0301091a0103170a051210030f050a02120d090519050904050106090f0b180406020906070305180f0a0303051e0403 70
    0x81199060003400d0165580700728030540300315048000060340207038618054599070101e03800020140241030900c54180c2c0c01c040a00074040c080c102400400c0800c115190300e5500c54175004106080d1241034504951080c000c400206e04090000580040b06032641c1551148070041001c0d8081d0900040c820040e01522040041c081d11840c1e031b0610315004005032a40c052150380700c6a403030007080050340c24800c10890000440c0c1080400500150608086403a5154004180c0c00b482208100300017855001810318025181a614146010700380010002c105003012000c90740b000c3d40b5030011030640e0301d031980c450040707121300000520586020412000d40d2102c8440c083c41307520384520400584c540c07882c401c0741d10610209556070f42c0d885203419802030044510043e00302c00c022a10320205a00400142410343c102d24281901d00c041d10708000ca4026846030140d0048180726003040000d014801804100c1041181c0003c84801041072060030340040d44242c2d4103045400e0700000c00c285c0c4104c0007 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 832076888 1250 832075638 832075661
    0x1502030405030318010b040609050402190506090409050f12130902040e011217030a140c03010b090d0f0506160305060a0636080601030b07030b010906030e0c03070315 73
    0x15411850251601601d83c0801400c603e494132011a8004104e50300790f2140c45c55000c014401c0195980b15040340c401000c00b201c00b00e018100e42e0032070203a00300708402602c0c1100c00007001507103418409010700005d494003403400c541c40c0c030584440d2003a40601340425500d01c4d00441d12035440d000300ba00001c015640a900c03180c402c1d841080f05000b0058507180c23450540e945203002c408c00800c140350002e00710310100c02c82041c141d008014010f40b180d158018168921101a1240030398440c0e000c0d50389184020b01c203080741d03504104940c200300d05004118803006400385041000e2000039840b49410324500700c3c0e160100c51480508070320115014807406400000c1a05c94034611400c2c500c0180111840e40300b010519070001401ea070111400f20450b070b064041e81c0c151449881d03038a50714203a81e6403080c0021036008803804c0020303003c0d9110f03200d5506d0806050303480c040307454504135040d0000c12050210042034000e40c3c0306a29151820800400118820aa561004480f280c00c0c04103c0358004002c = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 832078138 1250 832076888 832076891
    0xf07030204081209060705070b0306010e03070509151f050d2913060b2208030304082a030a02061512033108060601090b0c030d050c220315 61
    0x1e000a110028510b0031003031074440e00c0d6a84280150006045001b4914010038030300c0b913100c002ca40703600074801031400f07540d080c6c80300c95011000704100341c1c49030407a0140603000280040054000404074403055454000034088920a400900000040c041c800b45040c01160000906c1030048180784a411841407008043c1c41c00c95000d04020704080c400042c00b18810301c03007400c40c81620010703a4000030003031034004c201a640f9072240e1102708500c80c8200d00b80c1540a41c0c880000340c90760703002c01140c0c8601d51210480340741805003078004664030a24825030414140c045040c920000c010401414101e4054004103014508124000707110802644600d00803e03082115001100c2c0000030b03244400c0c0207504d000240c0c0032000803900691080202541202698400011910700104882d8028642039854592040d11003002040c14401d040c900c2c58141d0080205100f800f07021380c41560010380890702a0f25001c0340c070b0401c111801050b05003120101c039040301082000500840c0364010000c1030750 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 832079388 1250 832078138 832078147
    0x130201050304030309020102010b04150509010609061b1b18060501021903030203060d0519060e0607140903100f15150c030c0f060504080a0f140a030207020a0306140f070302 76
    0xd00318000034000800b03050311882071700210781c003c0d0082001c18001400c10010100443e141c3d100c051650300c99136010b411004000f0510510410188040d05c415444a4001001d100080510070721498030541d041d403a038100750414040994a290003d00c3c80c61f440011010b501c101c110102d510644c446419988401840710745861a60100c02d00160941030050300c80d51020b0105000b5103036520b00038240e0044020004410440e00e140e0031100380240c0040209900e000c1b109503031038000380c802402007408582086d0a103105100100031580b40981511414800f000c03801c800d0750a18802e48803c5a11415100c0300544406080d1000307205c0c21681100c1c0c1c00300c0f9a0b01401c1c003000814041c08008484000c1000d2181d10140190a1135004130704212600d402c0c02e2450f440e42125080e400028a031020131100588901d54008031072501502061400d0302151041e002940520812a08568036040010202d0020b100e1581420b6440462011618088030340c00b00403500284810300f4588180b1 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 832080638 1250 832079388 832079393
    0x318180c0c0b070c060b030105040b040302070801060506070b0a0f11040519030b04080c070e09030d2d1802060c03030f0705040b0703030906021614160810020906040503060a09030813 80
    0x8041e000030350344c18098a54542030404001400c440100c2a800d5824441440204124240080c6c8561300980c20341c5c4501d0340b240c000a0a036091071240f9540814140821408a03030501c2d1050342045013040c0003e4198002c203894070548032a88000d400800c008202000340703050041012800300c1103107a008074164103544d01e04015003030243c4003401c3c50300045244a00d11504000e8000604030214001180d490007924541d900d900604c41d1255480c1001480078580a011140003481c100f4648183c000f00407264040d0002c0041031006680e0442241802d0301503203540c401080500b403084042d503640d180282240c00c0e400c0001d4030207000c12100304402c1100c401d440d819030f296030b07501d46000b064a11107802c1c43c201078001c030310b0301841014802c180b000800001400200c00c0c1c0228500b07480010280c48200c4441c1000d510603546c064100181044254400380c0c020612032500800081c06d1a4442001c0b82c80d000701160003021180c2c3c0d07403164a060582103802581d000c40d00318050540788060b039 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 832081888 1250 832080638 832080653
    0x90106080a080904020f0d0501080d1704020906011b0327060c03031a15030405010605041a0f03030d020301060504230607150617010b040e010605030c0d0318180c0c 72
    0xc801400c0e000003c2075001c15595250101e0b421070a0340100191541b5886aa44008140a2103004030704e10850046650241c0a444080b0021159200042c01c13640c894003440300b801802406681044105038000e950700380c207603100c3c20110340240d030b850200c4140008a2030b0080c03100524030201c0d184001c020410540c1c08808880c4260341032030042a101078289500300f100c8201c0740322944c8000030216521023010160041d42c0701e01d000e83c0c000c1c412107540d081400100d0751080081041403203181100340403401c0009031101c2c80d084c040d0171207160044001f58901260000c0c0c1000c000180c0018081049180c0c01d407a2940100f032000380d407007640d501ca00009040f403091110082510746003040e4002811510703030066004081d01e8011500070f0010415440c0203241e4200c2c2140300d0f902c2c2007d280742c1004144980710a070348001d8003c0103000742d48400c12800341c0103403000f01e040000462100304149141100e490041c010744c201581d401c49181441802d40b005054450f003085512036400003ca07205 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 832083138 1250 832081888 832081903
    0x91809071205010605090414190305040504020c0f0102030703091719030f0e010905070801060b040510080c0705070608060f091009020901030f020f0d140702031e0408011401030b09010608 82
    0x301d00c58085500240780ca0360140407030340e0000754800044c008000a00c0440003542c4071040d54403061b9000b00d14444403140e8511804400540020811300c03091283e03007041d500802d640300500045074060102910b210742a6841203450b9000030340c4442c05c81080001c0c0d549250313640d00e0601d002e142450230b40050030040c0e4460804850806444005501103501c060b448445089041802404090614240180d403100c0d148108481c5601e000f100082c50114901994261480142007030303005000c0348011240d40c1c0c3c0c0940070700c0150707004000031000244d04103d0107000700100d403a080d40c1c030714240c000c00c16a09205201203004100321ba00b000040c0d0b10042b440002d80398080b1700145c0b5400074074012070090504040c4048914800a87d03200c02c181d4820103400c1d51190781106000090085210f50340b030074030959030301000d644140241c00139448003100a01390302c45c2c2c20200e2805c080d03907600b859003503441c016480d4021402841c014010b02520302c0d1040c6d40000307900c00900c045842e10038000d603200613 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 832084388 1250 832083138 832083149
    0x10b06180616150501060f02211e0310060905061204030f02030c0a0c090e011b03020f21071107120f0611131701110324090c09180907 59
    0x20700080001d890512050395944050300000004045180c0d00f0070000107100030b0043c0d0010400015205030070510001c0d080300070f0941040f120a401c0d03401b0f03094420743d4000649800d94440e41080b5045c040e841c020280d44505225000381c00c004c0d142c500040c03c181c0c07a582226001c2c0c00c040048003a182c040e2000c483d00958940b505094011501a04034218000e0510a610034010309000400f44540c01c440502600c402c20810010b07580f49451035802c86050303044008800300d41d140600c0b80180aa400f4100003e102002e003407a02d0300711711100d24000190075180f107901000c81c081c4000a40e0109040d1038030110980101804c40c1403c1c0c0316540c103080c019000348000801c00c1c900c010003586400407001505a08403241d140c0d02841c002c126200440d015501c04043c2140075460401c03414010600b9000c40303001114519100c1640000100e580e514000318440c03440400c180311354842041c4944212620020300d9100c081e840c3c10010101e0740c5844c6000300e8902c0b1014003c0e2801c02103503a104440 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 832085638 1250 832084388 832084399
    0x50d0938010f060806090601023c0a052e090303090308060d0203030d0c021501080a050d0c17070f020909030913020309030306040905072d090c1d0f1e03010b0618 71
    0x80c0c0710b90042b89040385880c01180074044140d44030140107900542000c25166148506104102e0302084581d541d280130409403499009a080405149185040d80c42c0100e22140c20b11681407031700382c40c0060b1568000110b0021b0b5842500f0310905920803c15500b100c01120511010356954000a41c1d90240c2e140311a8501c0e40c42144c079030f0640c000c02004418034004c000a098540c0c0d140e1006440d00400c2ca81a038030380c02600c4000301298883e02407011103540c40003849506000507648518503400030182100c131401d044001d4005607445505040c400e81e900d400450340c90707003020b0038020171078502e00034102510700500c00e203d0b80d00004015203510a1040d140010b0380c50882c10003624103c81e541c0004440600402c00364641c0a00d40d00195410000d986044800f50703941140e4400c85421001c1c0300b00056100d0441c0c3c0e01d900c40300003c031034002070041012046100141c001107070307020140740513482d1100c0c054003590a41420300610b0703040740080f51200d007050003000080600d074069001007031103034 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 832086888 1250 832085638 832085641
    0xf06190e06041505061c0c060e010503070203160c050d060e07080307030203030109022b090516060e10021c030504060c050412112e0816050d0938010f06080609 70
    0x640352046c3c0321010200d800503c0c181d40d2564280000030030340301d014400000318186031144095025000300ca004201f50350045150a22900044503522855501140c0e01c0c0c10341c1d400028980d0315034070803203c6140110300001d52001c260803950714014143e4040100b07504144401c50209401006490440d0b400600250f07550900000c642141c3e04c135082070340c803480010a004100d001040c5d01c0103500b54031403807ca60094684801c983c0c2505e0262081d03500140729500c9080b0b9a061014503207100183c1401242c07d030f90032145540c031b8000348a889a000195881c6c0c10001030050314040e899003003520f8104149010b08019806050f6000c46c40098144072031403a522165032110341c00c0802c40c0c500d43c014032129805542050081c5030080d078058001689142c0481d00b080c0460b02d01560450140c0ca03001e1030442d41100c40d40c05414000c4090b1400c0042c41e0101e43d14010303030701203041000c41d440e13400308900713165111a0f083d50700181c000e26000c80e03400710148403450300f0154058104400f1100d9400d40e = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 832088138 1250 832086888 832086901
    0x305031803040303021b0d0206180f04020301060c0201170717040f050d0c151e0e0114011e080106050913050c15030a060504020f18030f06190e06041505 67
    0x50400da4421001240700c009000400d142c1d011030001442d008800d480c00c3d482e09800304001c041c6010308000303580200100b0003190712109030b003035003ca085805000c403001480390340001012600f0982c0440081000d106a100c11981e00c080042c490031032040313024603a810301000003025210500b50b03203e0b502c100768000c28107110350b800402580680c49800c40e8500c000c6000001c020000ca050102d0306d9055242e40c101c0d0b00c0e000e601a10220720011561900b1884841d10054060031610000c02440e55071101c1d110054503404840b1400707400c0d8050480d07407280c602c800600020704960b00849050f490907405001540d140340341e00b034010a03050b640c41c605d40c031382d400c046041c40f100040703041c0d0000324a105048501381e40d401942c410801c0c0c21080000c0c07551035050100380d106882c0e40325503000381001448020149082d40741482c00001d0120b078119000e0759600d901e03094040d41e001c5481900000410340240042c010140721024100240440c0d0529558584104007810220b44682da200d2000809 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 832089388 1250 832088138 832088161
    0x30c0302032205012c061b070e070f081506072405222604030f050f101a0405040323070203010c0e13020903070e0a2301060c030503 58
    0x20810b40382920150101c044891040d405000c0c402c0038040b5259015200100e1006100039000881d04507a41c10100048400c0003019400b81c0141152440314107940315001c1800c01c0044003074289100881e545080415020344440201c8101c0020041180108040c00010002e0719840c480180e81e0640c40e9151480c0c26444103c5844103002c031900c0c4981114031098203500018001e1503008000b0440740c0c07101c44007190701f4034600805400410582a07045450030f80f01c10514010b07841070107460030581c495941d5001d08030072040a8407540d2008440c1152140c0078491101d90801194007041000d100050b50100d190540440d036100d40d07074510021b01894040c0240c0070031401411481c0d83c01070020007100550307401c4414164003035031a0141b580b402500038400401e6240004280c00000d510441c8250701940c85401050b4043c003405038009190710104110501403410030201184c1c5402d00d406100e04d0b0303402590070a500e02809001003010039002410341d150b4940600e031040d0f5942e1104071742d08 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 832090638 1250 832089388 832089397
    0x308070b042103090311031e180a18060506090109030305030402010c1b1a030c0f130308030f16030b150903070512030406091410050702010e0d0c0f0503031204030c030203 75
    0x14400d41d070449070303034040d030f15601c0080718070b20945452020b001c488201958a00a00d612401501524030207058000786150141104040143c0c068460a107031a01007400d600d5980d00076000c603030802411070310400f400d010b818054030090350010700b04520080003c000d82610321000e4140300c400400701c1c080d640320b00e1341d24030b00703542101918080059a107840068075540b84200b00060540d4414480c8142c42c446c02c0b05e00807148010003a0500d03404000c2e1548982c409641d42c604103000020000024001a015500c610101c025034031741881c08041102e01441d0310400081098034041c194881c0781d0301c0b0100e0040c42c0304202e0709540c0701c242403000709180003180c0d000b0075807207003803240c404e648010000014416240d0568880100c16500c008100e4400755211741c1e590300240c1414100340c42d03445840686030041c014940201c88a05100119014442542c420340d4140c000401c2801030826030840d40d00241400e6004500c0c00c001f1040c1e000034044003801c002e08001203942c203113060520802c01d55 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 832091888 1250 832090638 832090673
    0x90604020c0a0b07110303150108280507030e0102090307090b040b03010e0c03010e1209040c20100507090e13050705151908040f030e031f050108060f010308070b04 72
    0x180c04442d95400c220010740c10850749800090145a010b891011001c4190707030013020300411110078000f492005413181c810062103200b2003a9042e00788015071104000034038020100040010f01030400c203100609980041c00c102c82103070700401001500d51030004a49080368a00c1400003003901074040018040c094181c441e035890360074203203d4003090350085200842c20b10105c0c020010210000d40b0a500d07038100101800c4038540030f000e11449820160020000c200f198a0008941c540c150400d1900381c6803035200f08916440001c00c1d075010a80e510070580c002d0003a051240c0704526281c0d00d071545043c000d180c01034000002500d48100482004010040c20b002800c000320520142e404100c0b680000c44031001c10100b0641c003442e60390040f00480e000b950001e40c030410742d17a0aa1010b0342c1406c1c075010801d8162180020038620700e051b540490314030100074480811203524188542d440c0560142c20700900c110400010030016544070210f40c040ca61040a805a070f0b981c0f800d040b2121203e600f01c4 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 832093138 1250 832091888 832091893
    0x9030e06040b040e2503150306060b0d0c05040b040506090a08060f0411010c1205130f090f061505070318120b062d01030e070510320405090604020c 65
    0x4101894554050070540b042ca070344504440c2c2d1010104104490000018a68017542881d80c0c40d04502c40c0d0000d80540c00c244141e05c040740d41d03940e224400c0f20801da110780c00e0080c0226640106d80c243c1c0c050714881c9000c91600c10f09241c10003650032020310551144600c03907040090301425545504000d800180740c00d01c02d80f1114a090308608850f0310007180c0480d04008a40b0f01c84003d0b40c080e00c0c0c0c1901d107503000244d0040180c48030074140c37000c1d40490340082e846040c010b40020406400d814003c0942112030303003c5501c3c4540788850b41582e4082e0005c1c8442d0441554440e9256402000c0c2c0b0703c40d5405141000624180c02c40103071600d5000d03081040010000c20b4034405000007402454021032040d02e0390384044075020304071011402201d51151443c4441c0c040c001066100341c202c1c207610001d0304140d034062503454000581c5040f404407280041081040301082c802036000e449a070004503c210f011903200d20004c032280c00e01ca61b0041c54864869000401e000b07445540c190744856505604 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 832094388 1250 832093138 832093147
    0xe010510030906050106020d0f03020301120f050a0609032c0f090c0408010501080c090f060a301b121a0c0403060207060b0301050606070804090b0328050606180a09030e06 75
    0x1c0080d01c90a8882320100492000004042e80c50710a200300ca0480d00b2452503402c40801c1599226541d9071444801c1d6514800c90400c1c102044052003a5965141709454845040c04440950b401c116110449540c01c20035140c80d43d04591039031000c0c80c001d15822100d142e555984d01480103028000c07500104059840c1000108526500107041c0010220440d11a0401d980b40c0e6503800300382000300c41580e0801140030f020020b0110400f002201c100502c1c100c1d80c800e003c40b80e105a815030300507000396001c0c2c1129024648040c111036800025000485c4c0c03401c0a5035480d00c44400c0c0c2c0b4051140e4114100c0c42100280204404c0e0096402442c1c0c001c10070341d9100b145040090141040b4090f151203075180c02c0100b0094030b415011103009039880a15103050234901391340600180b0101c0000e036014041ea612000e034641c551003490b280800c120ba440c06240031345050561030508003c120314004e80015419801600701080085e40c00003240c0d1010440b8025440c00711240e490802d00603400420205 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 832095638 1250 832094388 832094399
    0x71b08070305070812040b0a0e0310021305040e0a0f08070c03022809051e0c070803010e160507032a081c0b1f2003040e0a05060a0e0105100309060501 66
    0x115001100e1814080b0344a1941c484185c90061003144a0711a00719002c00000200902448181800c52001420b0390a21004e89102805076440380e24000306140302c541040c841440c02d44a20302513103c3d24030050110204580e1140070300b050008003c0c00c1c0b83c8010440c08100721900140d2005198098103021a402c5080900d070904861000c0400a4869001c0b020035400f205114071840b0340ca11229203011941c070a000c203d5804405400c10b81e0a080410041d000326080342e00441c000c2c181c03868070600700d1400b00013501d054980300800c402040030800c440740100b40d00c0b0100b4110040c0c500151003c0c55a000d0018044c0c00380b43d00d0060070040045100480c0c040280c60a8000c4184507409101c0c2880c1c00d4200300c140e020700b0291000d15900a01a0806e180c42424441c1c0f00f0000d8101c0c0e15052401000300c285140c1181d4008060032950104210100155011781e13904010150741802c1001e060141301c0c1016841400388500442240102440c01c5104e900a5400690400410055075844a = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 832096888 1250 832095638 832095643
    0x9021e07240b04050f06030709020a030b060f040f0803071a060619030203060a050105040f031101180f0612050405060103060b0d02060c010e0606011d240a080709080109030203071b08070305 83
    0xb51040c81285420002582c4079150b07480c40d8411100103002c1c0101908281440000750000705003c01019920032079800240c81d15002001c0b110110703401191a20304d4003419100c0c204440d00402c01540052019100050100130800350008050280d2400d507a41d48001c911980604c01c2c0100f010b010408001003080c0e016801107014a1050360098512900c0d200107442d00d1140b4460402000c000c01c0080010410301c401d000c090040515103c4000c0c482c1c2440e5401800081e0413500503014286010010301c2d4009001c00a01c1c1840c00e001c0c0706900d81074541c80e0700c6820520010340300a482d007040d48901c1e07a441c005c440e842640141860f03241c2c00d50043e0305e8001c245400380120584148000700b212580a08240c808002c2c0030b040c4404050310040c04d109000f101000f12910203000c1f50000280441e030400070b4200d0074070540da041902c1c131700703d9001030092081d03a0080041da407404850074007080e400300403140c040d500807104111203400ba603800789510446a00882d4103001e600e9000c002c01401 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 832098138 1250 832096888 832096901
    0x2030a3006051302040302060f0705152e05030c0d02061e0c010f05040507030f0302030d02210a020f0f070c05090108150f060d0f0213050a090c09021e0724 68
    0xd40d030b8207580b0201403c0b448100e03c160301020f580084180600c510b0003070a84020080740348624181c4512207071140240d20f01000a982007107610201e001090030020843c1039500807800b140000f29416450000130944a0a6240e5242e00500303604c20b02c0f000750b49690084900b0705090103102030101c8525541550940c03c00f01c00f800865090041e4903400308024000c007405160458082c02e1b51524666401ca0704c1c420040d01101980002e04c0794420525192003e05a2465400c1c68001c0c400e00510304171604000050103050120701c1404803c0c031a007440010385414600101d5041c2d6601000c0c10705c140c040c0c00680c841039100360f40d140041780410021070703c0340428a51064003101500c0304816152161402c840050300045445c54046c04540c400d192071815500280c210240f8030000305058050710030440319000301035191560042081420090340c00281040e880841c1400b0000c480d0340d071504200d412000c02c000c004034080043c88546056903401c407415407115060296100c4400e000b8000 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 832099388 1250 832098138 832098149
    0x1e010f03050f1b061305060d0207050606181614040b09090106230d0b0d060c0e06031504021b0303040b15060304050d0809012007051c02030a3006 64
    0x62100300b0000e4420005003110820022100022500070b44028480190031030f0f13048060078400076900146a440d00030003454140c0c4a46009070741e40d025418101d2400c02c015040d04d014404803c1401c0c10b142c1103410042d00245001030140d0402410481158441021281c101c480103000900250451542005042d502000d0320600240d070780e1940c06071584003200074000000d541c2d4151402007002e00c0c00040018888542d00001c17410400e00200302821000c0004540d00d5946200c145a200d03000a0440000801100c4452542c0b40c4051844107580c0c00c3c4405501480d004030f002c4026140c84590f00d80c66050400c21a902c034a401d003860100c244040e14402508000101c00440c903081c00d400f2070f03219a03080001040040e4030004100d851070002406001e1035540c810940d07030032200000b4500081503d40d0106512100a400c10302d0a01c10310310000b0560402900000e600140c0201c1610078901c054207001003681111183d1450f007001100d0101d84000540040b01101c00c900e61144003a40c2 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 832100638 1250 832099388 832099393
    0xd08030a0903031b02100b04140f07080903091f232502180408040902160b06040510140d1208150a0501021f02070c0303050c010507020106031106031e010f0305 70
    0x4c40b105003000e41c02d01c04c07400250040e00541c03d100e03545650b41d00030707800f0040090000a94240034000798901d44006076000c958400000c0d0610074100d41c80140c07070ba000f92600010751f10b012040400103c00301e110410303400c01c000b142c83d080c25816000d50400640e010015100440d40094010b080603107034403410019044c00c6a11882005000016140016071680a801030310f5004c10b500801c030400c000127004444240c01000003103030300740781d0380080c2c007070303c001c0405d0300700c001c0180d16119000d0a0010407260056243c0410071000707114003410407040310051a002d0f00308451070030116100710799180e00580b0a00082e11008140d81d880010395108401e40c0440c0a581954803082040070992846070380d005a014014440c95082c034558864200d0034071b0000189024000d03642d0709241c1e001680243c0c040b5202141c440031426080c00b8069111100f840204450341c21965252040c900c80d805880c020000400020341002c0c04600c0c9020300c1c0583d00c102040356945075050328105c6201d00040300e5a0 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 832101888 1250 832100638 832100651
    0x1509040c1203020a352a0c0a050607020f060d0209100804150e0706030e070305190b010b040803070f03030e250b13060311070b07030609060605091503060d08030a090303 74
    0xc4105d0500035040100d0883d2500044040f2200001d500601ca4102c220705581c0700621784c22010740130305d0901b0345144000e400c0d800e50903020000c2c0700d9411780c800c0d4000c020030402d400040c2e480308180d102c1038008541d8680c56000b00d004400082c0200f02940340c0014812401c030142e01e40103d2203070300c95485100d4881a005030304180c00140d41c110714410010380d011440038081c4500a40200f11260446021900302e01c0ea40d4403140d1500c40f0245c400c5001c80304003031484080c8140d00c01d400780036022244009151520702352480c0d40da4400c800024100c5044450541c041501c40c0d0000320403184e003d0201c7d0a122009100c41e6605200c494051111141c072050001d8040f448034151078128501041a83c013042c940207055010f414402d0b60003403c5c0000b04003003400a0f40105c00d15004030140d640020301681032410000860f01a900110b052003000c0c0220103140e9200818081403c0c2a00c1c2e90300c0c2c40751280008100003100c04070b8024013080010003000000040c50348440f0580340030341e600744040c = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 832103138 1250 832101888 832101923
    0x109090b0a291503011403061b1804480207030f050114070302030109060e01050306070c1407030503031015050f070c050d030e040609051509040c1203020a 68
    0x444108011205003000958481810100c00340300385440e04802030407100f40c00345030182c01d442a41c0260025011444900c0088003c0e040400c040350f4403c1c46502480d03000c00c480380c131132a8203000d05603820b008800000c904201549030398114000e0080380d40a074007000d100c01e004a80320701c007a00071016049103029019903e03280c01c128003880694841d80243c407585045880b240920350b00888156025921050a11100c800d00081c0f18401c45003aa80180c495061190320f4080e00c0301c5c3e51018400009181c018451541c020074480d41103149820620160500d03851300c074071040c0300b800c1d2400280c010304800000780100400218821754041803400c03c01903c4540f000c0203103c03002001e4001031024095110444215001401c00038026801002600c4d43d81c070000d0801c0c0c41e00d81d8110300084000072094801c0c00c081c001e01000e001c0e20b141c01d00071403420151040743d460902920742d200e0790200002c2003e02502c01500d801a00030b800c41060808068100039660b003412840480f944118074010402 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 832104388 1250 832103138 832103141
    0x12010c12020319050402120d0f0f0c080d0b04110c0a0201091d13150603232b0e1011190803040305090315010e07030b03060c121308030109090b0a 64
    0x1264002c0c080c22080c2c5160302ca0b049008050042c4100e0300007643d018587c0a600040155002030680366603401c00c0c40d02e41000003008800c82040074000e02194810110000e03132000190303480808003110025802da407590000300034100c02105111040f2b000614000c2829021500c0c00185000703803910713500300359581184402602c5d24030401005201c8940450070400d424660703078002d03d00980c5181004680412004200e4966601c200c80401d940d008003a4135612a10720303107441d011000b001c6c2902042c8040304500c01c9050118501504075000a1144140d01545e029007092070080e201030a81d1600c010060704100d4243c4c0c919649215403551305041d941501c180044040c2d2148070303641103454540d000e442507088284070365030502031680034800c3c5144900c2864001d2a0441680b80d0034104420040c3c12551181010303406500808200001003040c1000c80e80f20083d0035031405020b98440c101e09000b10800013000b006040d00000014084000e9041084054055944d40340240c541000550 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 832105638 1250 832104388 832104391
    0x30b280510050a080c040203070504091a041107020d140f330702120d06082505010e090f0a020c0604030903030201060b042d09090c14030327010203070212010c120203 73
    0x900716807002178002190708068025540200740360812904098036000d0020030369614040b141d110400c044111344c03091400340035543d03c03060318041551800b0901d401042103210203400281c01220580702000c05c0386401c10010b205080d6400c1603d00c5036900300c059581d54028201c018044a440d800c004002400d903040482c010b0b8031540040412180c0c203d4101d0858020006083c3c0842d0303620070018184e80240a0701c00c1554034824044030040d000140c004404c0050b030091410081d40c500034403800d4498028040e04005000c0000352696200700341c13903002e8441d4901500c803034020f41003400101600306180c402528403a4000b40700b05a2074218018040c0940e01c14015a00c400c089007081910340112600000030041e8903480000c1e0b10f5000c0d03141a0755620500b21070501418030b081083c00d1160040606440c0210013961a050303a881080013086004a200000c07041c030b40310b40d10f280b030307000300111541c05074041c2c00c0301c41c030401c46000e880c0240700c031512110201d0341014850003c09050f00c2100d = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 832106888 1250 832105638 832105649
    0x30f050d11030d18020607060b011101020405130f0e01090c03050d02060705030415151206150506090108150d03050c100615050c070e0f1e10030b280510050a 69
    0x42d401c0818102080c070150090202c01c90f61000d80f0304031800517071618001420b0080c041d10000c15180c1040000400070300300c43c01e4074641a44148424042a550032001031044100c455002c10860350300d140301d00040c070b1725003003a40b10b540ca40303010a01041f4180c064078003100d024100f910117214640c0003e80e00d40780103d6220300019001c00c0010b00123002c9241c9140c2454a030035000405014003070801c0400c0c1d07090780101da06100000d01c1c034800c001a80c000c100c0c3d8001402c0a1441300703460840882c2850040b0046c19040c0b00c40080055601c8202c180d40b5814500c0c0208602d0100800d801c02038103c1d0700c0035070100b8842c041d080c401104291580561412103c543e10700741c040c0a00c00d0301c03c58042d003010305141881d00403140006020109418014000e103040c0400c0c10150138403107030582060310351205007094801108100284030300c4051503c03044a400c40c002d5015541d03124090459049040001180512242c524281880085d400144100031002040c03500a40360410406d100c402c0d403048 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 832108138 1250 832106888 832106893
    0xe100e0d0813050d1809020c0c090603030f040603051504090302070303120204121406011d19090812010305060112172203080304050613121d0a030f050d11 68
    0x11003080d41c4035148181d40803507601840308070320b070450762820b0500103020351400001e0030801410410038840b034841001000038803000c514080d1400300e025110000c40103228462801100040c0c0251030501c00c031541006074140071b9075106c1d00e620303001e8000c107005d54480880c0101415048c400c0d0034280319440485402d074008090261131070742d0440c2c6014484102c10b6420781c00748800105000d2950461600340c0c440d40c2562050020181454a040d2059200d585103229020782c030256030010500a6030001242d030316801c0341100c82c10f144070117000811002000040001000342d110b01c456840a8141e901c1101034a80c0c69984808003440c1c0e81c00014007400f64010307500301c10000d01c2c4440003088400c3d141041250000da6112101000c0ca2081d4425104800004100420440d00344100b0fa8886048101010480700316112040748004072001482404000b80b03800c8141c48143c40042101c0c00000c3c112520540c89103040c0500c003000140c2140c2502c54102c03500c0440380110743e6000c0500e2004d00 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 832109388 1250 832108138 832108153
    0x3010608040b04113001060e0c0705070e0c09040c050306010f031a0d12030608010c0c031107090f060e0c0f0306011b0506390d02180904060e100e 64
    0x200d03a05072000182003210311300c1d1407440d141c0858444074004910040e1907541004644589907001480300c5624095450a9240100500844045145140d04601c1c100001e0b03032598000e107412880c0c10050b0304100d141c83c01a0b8100003100d070000d0300401540348152400c0c0300c07a4084820683e818007040c2c4510b03001c904050800f1880500c240d01c008401c144020071140c0d03041109010501014840c5800e81d480447c0c600540c602c641c00d800b8040c02070401400800020408000042c6103000e0910000c0402c0050309944c0c0d00e000b001c2006030054484401d0401c0581e82d41c840000082200b0701c01c4150740412000000e00380302813a000e039003a040d886103c1d60f1560f540c1500440c0d83c80b4440b0036012074424502004004900200041c80c0b185010b070420190031031042841580400081c207409034052001d001c03032030b0514141c40580740c4908400720050703141c8502002201e400420328031b001c0d8011500100f0482070100940140000f81e020b2410340360f05044000f07425094030081c1840300200e5100d0007 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 832110638 1250 832109388 832109393
    0x203a08040b0c0c1e0d0f0903110108190606211107060c020f06040b31081c090f12180e0c21180318100c08030f0403140301060804 57
    0x2e0081100b4800b00040e5056422440004405000d0300380d0248030682c8012103030b0340e1054100543d02440740d01d42c100303520b8052a655420705c1503034441e15603604110021340071415146400c0740041c8080d5141005014141d1180c0000304205c2c50050b04843c414a0b080d41c440c0c0c81c81d400d20a1410000132900418078041940c0c4900c80a01180040c00046200300225041544801d102103801207200711004065410410041610503044543e6090380380e04000000d840c0502000c0e0062017141e000c0d043c2901d03001c1e8001050581c1001c50380000d5aa4141f000781e00800a10100c81c1c003025101d50610701d4216481201299003175803074170000314030307440556050000300105c48909a100706103000d100e1030500f04281401065012070b001c00304040321101840030b54060000d8460400207d44001c60500c1a0740040410351111440b1090103000341c4941d06840302d1080103204001c40d0800c150f01e030f590610024000090100312001e40001d9251030000c0d651800c81d108590480340705684041d060344858 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 832111888 1250 832110638 832110661
    0x1f0f061202040e03070206131e050303030708090c1c0605090c0a06050913020f0a080627150a1503060609060905060306011709030711090106203a08040b 67
    0x403c805003103848141702c0c0700f00582d19135008103200d805c1c030391516403e14607004d41d12040d03030300310504035910500010302841552800800d49512080902d448050f90725000c12160611591010050304050f802c0c00c900404c08507444070040350340c4182c404000e41e503169401c864036111a08201940444c00c13080400581e031082c00504408100103281040e184600a5940102e0b44410040032524002141540b6040c4d0860281540040f05807500151705400030b200c8200b0700060496000c007070803000080b076001540c1c91a040803001002d000c07915103a8903101041c0b00e192803511200002030a1110204006108500d800704075040c64894032501b5040100700002604010040c41c100709040e28000000540c03098120301500303066024558070303100c50810040b101c400c084254041da40030801080080e6000e5004d42d20810381d10505804c50000340b440c141008c6a80030320102d80794801242c108540072540040b051440c104e01d030307510901c7d20504240c90301c000454000e00403840300c0001900000c0702 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 832113138 1250 832111888 832111901
    0x3060d030905030106121e020604150e040f020405120706120e0109050703111302040503030a0804081204050c090708101503090803010f060801120f03140c1f0f06120204 74
    0x207810700341030316521400440e0031030300304d5032212510b007003044c0000040c4000525200c0c6001c0c051480c6040f001c00ca500410698441d07481500840340c2c02900e60000304e40318152500b442000140141710951854a8140281d00103010701ca204c1c1c6059014880c3c256000105101190140e4440300e00403150a40d250740204000300808586548803080100012010f01001c0301440c032659103269103c1025050000c0b1003040d855082080740b042000b4070040d40c4c00026202c0240940c64240c1143c1d54134613090105010301d031225030003e0092010301c010808082514100f10000741c0703e50076150380e88841291a0201900e070180050700c22a070a01401ca910341034044103411500b40865009800c0c0d4504440e03a10036404144030414501082c02040c0e88400607500500403000d040200c00303860b46804d040041208002401d200f0144030f045012400b5a098078030780f0b81041d0544003401e85400c103030202412404000d40206107480901452510396106200c01d842031601c0d03004101a4030341c24003000340030 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 832114388 1250 832113138 832113143
    0x30c300a0c140a030615050a020a020d0c030b09030d110703080601181716060f17070c0c03080306210c1201021e040f0f1a1e0c030912010b030303060d 66
    0x2907841c0009030400c0c1000105050b43c02030f503001500528111407800c140c4c600441c91010864204684400300303500182a25829404460032044803041d403034400d1500c0202d610061200f00080100442803101101602c0030102e15681807050140400b5022058480ea28009011826a402103900c65215032004e036031707203810301c0021541c0c42d88072490300035081820700001409030306c9100070142180f00c0500340d070002d000c1401c084580089040000c2e044101c0c001580200807074090004000d284141881a04c5940210b00244110b0310790070040b09a50007251120b01501805240703004a510307945030b80003104030240140c400172211000700422060041c04c150300030b64080c05204050394070f001c4192410061000c2981c1d48601d81109108500500d80c002c001d04c0543e00000c00a108058075144841488017a4150383c4cc10743e10419694241d030f040f000c3d19212004036070007560020010003401c010104076601131403060002841400d03201c00d41d8203650960003c1c400300b03405007040700e082c01490380b = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 832115638 1250 832114388 832114397
    0xb0306010903150603080d0b0301180506070809010b0a092408031b03090907030501030201090b0c06010e07050d050a0b1302090307030b0c04080f0a021e092a030c300a0c 74
    0x5540c0d07150400c0347d401c03181108103e29501d4808900d5442e00340718030701031050340584202c844200c80d25070036222140180340009000303003c6c0000d01e0518082d8003105010b2001015640e202d922804850003d004840301904403940f0714200300420140c2c7d07290384089a02000085250030741342885c00c1d250b1000d007a102d81d007030302c4240160302e102e94948010300e1080b02140d0740000c1c2c039899400010455040b6070b002c80750110003000b1200a0301404a50b4906458080b19900925120544200c9851042030f43c009906c520b01410b011103000d69812195660f00120340400000c0c0103004208100d1041881260b41903200003410070018880c175105541c452081120340e42030a40c2c44901600700300c10882c0400c102d42204140000310702d887d04106031000080389842801d004840003282040c0300281c14074100084142d016002481ca003041096000030303500180da1a4100903c401905402c000b0543d8603a9948103424080741001d10441582401d1000440d4900d4a42218140080c90780110520421 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 832116888 1250 832115638 832115651
    0x1802130b090f060301031103070e040f021c0501240b0a05180105040807090b03160e0f0a0e07080f070b0304080a050702130204080a0c0f08030a11010b150409060b030601090315 77
    0x25a5444007640c004c41c001c6d241c621914041f041018148001500814040e140d404280070200b40c0511004200540c15107070310190810130741600c078101201810041c850741c01d1031001c0c13242e003200b0424050842d401d8203600c25050b40721083c5846902800034003500140d400e00201022007008504000d075060306040581c581902d5054443c11f0807840d0300240001904e031609440da5090402c1301402220035411283c144e41d040004852103010b024018085200100001c100030032500c0c0d103c000718031440780803610b806540320103558444c06201211a201d0185550000d05159440202c2c1d2040794803080d0281340000049041d0f4140e04480010b036003100103441c1101c2e07030148620081000e0241c00000b0302141d1601d04d0403400d204143c5d040000e10540c1c41000b004000c0c000130554044001906202d181c41d01a0003240c1d0060000c0740e03009910141e10302c103d1203415800c2c80100b00f601c04000c1c091007110340b110b000c4501da1001341d54490000b8180c400800c08a20b60000c8042c11051242021512 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 832118138 1250 832116888 832116919
    0x80a0e0d051206191413021306020c12121c0f0209040f0b01020d030f020d05010e0f01172d0706050903070f080a030c02011e05041802130b09 62
    0x3490140c00030030000c18070000380381c004407184401c07807030340300808030792041841c0c207001131010380740d803007481081c06000c052659a000381e03480d20305009070003515410440d100c0f000140c01c25440c05282c030544d0302602445801c1c07001807d1515414150010303080080c0114a070300b64070800e449c1c0c071585003040045115000f001100341c0500415804581c090360247c2c90f480070008000c1111304d2201e641440300d1910b001e5004c1640c000c84c2120151001e8100011821003421400010b031140d540f11039070703141ca0000081828080c113184075025150000c401074646c1e8841241549039030311f55460110562018548007824644001d140c102500010b000407589000d54a4851410b14942c000802264011a400d051801c040000300004d00400080104c858a0310700b84c03584511041d14054200801c1028440942e4082d02c58009001c4810420700221154010000d0054000303000d00392800728020a0064101858000d680c5a078402c01b4808010300d1900602109540c07194000f940c0000c84100d02c03800 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 832119388 1250 832118138 832118143
    0x9031e0319020d0806010c030c120509150315090f04080307111911060a1d0d0c0602060406052d0a060b04060302070b09030f040b07020102150405100b0f10080a0e 71
    0x41e0a41039400800021003205405801804000c041904102005407020082588010100242900440c000700a1000c1c0d80040310203116a40303845030010940d00c0710148803840c0d100210700c990b00342c1c0c1c02d0302041c014000810000f90f00a89031005240a03d00104021407000f1000355048407440c10003400c001e45180900341488552140c0e40100c2520400b1201132141c1c079403280410100440e8040c0c90500f40c0d45025040381d02d6800b02140d51216200384103100c2d1503101a5070b6059400442c400c1c071075561150020b5560000b200d0454010781440089800e00e28100380110319820005801000c04151895207204640c004290a40301900d41d440007901c8541c420040001c2c00041d580540e40318450304200d246408043c1003030b0045d42c02040b00c0920082000d09440c1501c0c0501200d039a50f182c5400101c0c40d00418200a8200c0c9a8010502042000000d41c03039600103e90f020902c807442c00441003000c18001e2094207034018140c20303100d140c1e003441403c03419070100741c501000428400700701400c3c1c03 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 832120638 1250 832119388 832119427
    0xa0c0609050a020f15040e040c030507320a050111010f0507050901020f030a0903330603021305070e10031401060819110909070203070209270309031e03 67
    0x15001d4004030031903410350078440525444c041054130f1030024400c1420400b081885280f154200462420020500b0400b110310104011500103044072506502c80c036800060940b842d040444808021220032168081c18001840600340140651003051800e8019034284901c0c01c6c03201929541c0f48401c2c007500b9250b20a403801b4041c0c541c3c031141c4402149c1c001924050034164060324a620612074045420b511150000a680c0e024500c80c5810b4a40a049592024051040a05031078080301c03c2c000150181c0c03002040f280200c03205542c10b021440e4420486d68150341c56400255510400b9003141803140f100d002e0011249400240c802c00843c02500300b08084e0003040010b03105c00c0a001e80d079281ca503114242c85403000820040038070b080c90001e21501c0769800d980d000b080700b40001071351680240281e0307030540c2c1c001d030882003d4580307a03030382e0103c0c8401716104a43c0b5019540c4580211078000040e281000d00c0035000f8244a040707018080c41030301080b000380a003031104001180700c0750503040490307 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 832121888 1250 832120638 832120643
    0x91104140603101104030237140109030c210503180f0f0a051219060506030705090c120c0c0d0c140a0206072607030201020721050304110a15020c0a0f18020a0c0609 72
    0x21446142071001145c6512040e1027614104118503206002050900c69050129000c904141c602c1401920810000900405010f8260300003c10041070801c0e000d005159003520840d501c1d26881103007000c11490500c082c900319008a070009042c003140c01e11403c0c4440901100c000c03a1045083d04e075240040704a41d4070100c031481d40700d00a2106900b0108482c2010b00803c41e007014030740c030703111401030000d025a069504151401c180414420700941003140d0420079140c3c2640c900c54200c035805004030075500403c131106804801d043c1c3c2d00c504085441400658014a4103141410700e441e4900080e5500e4982d48120ba080700420301500d01182c01852054440c0d000540c0342c08840c1400c0085040c85268044960442c414091440e83c2c46011694090351000800646680803804100d82c0180381d00855071102c101c80701113125580002d42e814524070f044484071000340e21620031400300249440390f51314541c2120f03001c0c00c0c003500e0b03500a000822954078006058404036100c030829944c50003003d = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 832123138 1250 832121888 832121989
    0x506030705040e01020d0e0f060408090604030c06170a022b02040909150e030424090f0b070b1005010c030804030c0804030b16140306040911041406031011040302 71
    0x2001e0000c2402c0c010a180318087d040a0058550150742580c0c40b20002000101a00000038075515a03980340d5090b60f0103550001e010041064951401500848110100e5003000c042880011000450f0b4003c03114140c2040c218015010741c00307100722004211010b0062503880d004e200c0840c5480152140340003542c010b25031020201800c2c0e0380002143c600c140c1100c80c60f041048240080c0540c0121262004082c52011180a440c40ca0841e1a11030b6500400745410b000310000910040c49030240a40500641c4200c900d80c54498503031040c80c03124424140410b05d503000744404a4010144503030306c1406428013a43e4010181c2da4002c00307600c581c004131072050300b54040c04940d042c00c201c042100e645500701510001e040c2c0345560418040240000d204540b980040010040ca90600200244000d4000c0c45140c82104144540a034110b0b0054003a129030b00c0c420040340b485011703082c04150340344940c070314090544d0240701020342c80e019a000351a40321600e1701c500d08521200c0c0c0b1400701d12b1211 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 832124388 1250 832123138 832123147
    0x1401050a11251409240d030302090a060801030515100e09010c03060603020a0806120c030f01230c0316050405031e01060f0509340206010f0e040b07030506030705040e0102 75
    0x500c001002003c0e00702c0e0021501c4000c1e0246151940c1910710313040b13031020401c0c082070b0f80581d103c1402403612185054000003005402420140c058000e00140e09003180c05150440d00c50004440959003480040c190307034005009480d203010003003601500150006900b254842c0c0710803948905000956802b855695204d403403107507840d81840b4100140c200c0b031070250b1600c0d4154000615203074028005502c1100d40390500614140104181e504c08000a02a91110034038809514001c0050741c0041e1351000030314100f0200750203544480b62041d00707145541410350300d40414000d9032940f0b4010382c0050000c00c20010450b6a0104134006a504040311940850300c0581c6846007914525030005000e29507003641071110340e03035030362409034005041c0700c8100d207140b042642030b405600c034010101000b0340d640300340c248901da000c0350a5069420040600c08105d542d64000c074401c034021140a41419404004103101c18403d8004681083c40182192603094950700010100d550802480141da9400075 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 832125638 1250 832124388 832124443
    0x412030908060708070c150204050d0807061104080a060504021c050609100203100b0c21120106050a08280e010e100b011b06090f0b0702161401050a11 66
    0x580c0c3c0d8800c800d1315008800381401032000e040f04c1c0310361200510040030040045080380b425410b07100240401060700c803103c1d86600786026682d1242c0001d907402ca017010b0300144080310404c1107030122070081c0020600d8074201d807100401014060002c0781e000388200304800c0715800d1841d140c106203000b0740250440d42000b465040c6007892a04075010054010b00030064610000d4407084200d07020b0500c001c1c2d0b540c403103103003860030401c2107654070040c42400101c22910109842c00341500c0c007400c0b103001c401070f41c841400355004d01a15030f0b0300000492200c00240c6822909102e072045598821100c0e1991005d0702418055030180401054182c0d5541030004100f00100400801908485000c019516103000001c3c103000c240c145240c05c011300d04610104111660b4058980c030341c0c01401900007551185040c40d404602520580014401d00301c09100c20001c002d203c40446007428465504081040015603140d046050294180301d1108806d9004c130400f44661440541e4407001014100b4868 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 832126888 1250 832125638 832125643
    0x9140f0907030210030218060d1d0106050d1104021c1b09080a23010e03030106030b042a0309050a050c0a0f0807120f141b0d08031b0412030908 63
    0x300303a504581d21100301000035071595450100000618507000d643c5460614010500119540740a80c020070b0001d23107007038905502c0d4000a91003211300068000c0b10501030100d801d843d880e000e80c0754040d031070b83c82d90000500302c021903459078140940094100294001d00b4562a41c0c4402d100c1040d039111254101c03002d402c0079803440c071008a400c00916040c2480344c0c0f9640d50410f9a0300401a116280c0d5205d4940300c60050985d022006a00134040010f44002c00383e1030307410038801c410202c2d040011014040c44e10307009898185282e094208505020340d41000c0c0d184151103414014143d40e040401d0206209000c880311803030241c002440542c100c20180101c0f040b860348002da040911040034030039048003180c0001160b4072038101d41c82c5502c503401c01141714000e03800024041100d60301d070102c19030400300d0076000441d01d076025005404007160521407095400c0d40c00070701125081000550342104015162108405580054202a100e1a50101d0700303008a1042e00402c900c0003081010a804 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 832128138 1250 832126888 832126891
    0x609090b0a1809052a0603090f0d0906090501030c210f180b07110618031207030e280807060e01020301080609060709031106030a200d0f0509070e09010609140f 70
    0x10501e007000706a041d055485d2500300d0101620321500000010548154003048580000803d10090395100d0740444c0303001c2c1880207503100b50800724414840000e540e6009100e500b0307100b0107a03200c5000100c10f8501100340d0003444076100405550fa010b440600030a948103801c6090007038145903080201c241003520b4030700c9009106c50100a0000201c1038559000305529801445021810450241d5021101c0c2540a1410740e0264a80a0010031801551680040703085003064001d07620292400c80c940039400d65603c3d80c0211403044100b485002454000c001c1410381e0050b5400600c05965521150a83c0c4c0300780d018040a5100e0402d1101c003580a00004d80c120300d0303c1c00d00703d00b402c0ca035668866440c10071007640c604c109004400a48140055000040584800184580c0d983d07812070058030190442102402c0345071409a02950a00c1d60b44101409006080020184246000a40303800482c004180900654840d07100284d806a6030041a107034906000c0800e1181c544194200100d610 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 832129388 1250 832128138 832128163
    0x3030e0114070f140a09170c0405040303061d07300c080601200a02090a1401030c0617152b0803010302010e101715030a0f02010807020303010609090b0a180905 70
    0x4c00c1010324582a00482c510341140c6444020000b1074444640490600014285043d08642094204000c00d541030340710034255181640f02126480c100445078080c101c1c11203004010034404004c40f1032030440b040b02840c1310300041c0c0c1c044580700d204800a0080d036110300300c0364012880e00800d004083da000100e001010400c020700b002c1c00045000e8030f55030307840e410101a004440050124616086907080302262811f80c40c5600d40d9035a42e498580c41d0b40b0352034859400011401d00c4440d03040901000e04070301030143d0540d00c07041150030b20b00700543d22900000300700d2031621040b04035004080b000007419000e4050010719840e5032440c000504449550020240310744810140d07480050341101c0610201c00f80039031000025030307407085d030983c0c0042007403c540d80c144a465084000c011a00a40141ba00d100b070740d41c1134041d2a004001c1c0c3c3d480c042800b4140100c3d041c00400c1c003000400b41c0c041d042d4088000c00030000265109200b440c1542c0d8544400c840075219800001445000c009283d0a5407 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 832130638 1250 832129388 832129427
    0x609010c1d0607032604050609150406150503070803040501030b0103020f0723160305190209070e03030409020f0d06050306190f090212100e0601050d03030e0114070f 73
    0xc0340c0031041c1c25210712200d0561003034001040a00a2500c112415030700070345001820341c02c2081d9584441c8121000311021603181c410720f00090041c420101e40301e140c1030008200c00c800b135103841c0e50b1180603200d50400c1e100a88500300c8e00049641d000c011110040840c0d002465031036040500041c103842c0504600d50506004120752107a0261000480303100c1034110740d110a141c203001c0100c0183c21244103030901c6920851041c00c003501c00c1c8085420841e44184200d617404070081c06641d0203022244806507000d8040e00014266502464024800c80030040c196840c0c03c0d120a55602242c002548003e0100804610307848550011300c620030181404900070074062030140d02c0351009004401028a0540e280c83c85030014010b03e8202325141d640c000d02c0e05916114118249a403681361540051441d0704050001c160300d100812182d060320001780004807000c00300d880c00e802074003111810020319036171a80508201480e509585009003241d540d40c1030038140800e001441a50b4001451000c00c = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 832131888 1250 832130638 832130657
    0x301154202120f12250306090501050f150f0c0a0f031b120e0111060a02210c090f06090901030c18060e060f011103030403030f050c180415030c080609010c 68
    0x8091520a0701c040864074292010b141c0d40304040070624107900c4150105c2840d0f1050b601c4203031a01500041c043c0c82040b0300402007aaa25403c00070507400900981e60012024003501d4448040358000b8089036141d40050f80c90100024071782890242c1400301620948501c2001604141d48501d000c04503441030080300800c140f541d1105160180d0b00c084000030300542001c007102907401500d451a4010301c200942d000351409410b890080d5110501e61481000d0801071880d84042c6190401c2c0141d02c81c40c101d506003107240f0180f208150348041020ba0062050080c1d190aa07140d03803120780614811244101200d240000b2084845005c8413840b500718106131040c05141070320f580c00b5a200e403040350b207242500b100c0c00040c4d80c1c4c64000b07903249185000000070070083c0750b0181c11450340c00c2d80300e02c1c00b008583c1c0c4800102ca0326000304400b1600915824440003402c0c545908103508441d942c601010030035036a40c1d42e00e82c0a181c181d01485c8581c00003020000405800c0c41003003807103600e5040007a4207 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 832133138 1250 832131888 832131907
    0x11202090f0f011511071410050703020c06030402060418140c07020d15060f090606020706111005040203030c0d020109051902060f03040512071b05030115420212 71
    0x1155414000c112008100c0416803244c00d10800d000603070080e648040d1150151201d1120300c0300f20318205514020743d40700407140c7c2e0840c41141200c4500d0742541c050300302443d0300c8042041d10340c4054810380c0d01c01402d02c4081850140e260a25034141c0414100140382c0140c41c102802000d0001c0c8800b80c1e07064107001c00c20153b1074402e416400d29a101170f1030f80301022890341c041d00a02c6940c201d0100d00201c60800b00745000d8a074031410a0355510b40840340025603503002103074004110b00011005400126028040c014540c02940e0000d10040550342405040c0c90f030386203040703980c40b5844d0061703440381c1d500c1301845010b001100014104121880041106801240d080d21500103000c0005200000003800c0c0f00090051381003540000810680d42c3c8843e06049940000428508c110200400300c0081d143c5014411070840c2c0705200e102040c02c0e49003040885c0c510b14000081e100c0c0c00784140385901c0e0141e107040034040001c007130010b01740800b03449072000f460301c15440407100d1042003c0100a54 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 832134388 1250 832133138 832133161
    0x110d0804090f0c0815130213030516080d0f18090c09060311040506070b0717150414071209080c151602071404050601110d050301090b0312040909031403011202090f 72
    0x2d02d45c10980f10480121a6900054024814407054411000a48038003104001b80410710000040300003402c02041030b00c1e460a2611826050107a5001c58524406031900c140a00f120104001c3c0c9500c10240040d980e4002e0f01c00e490010014500207090b0f0030050100641500c2082c9100504c042e24504040c184000b1404078466070360f01034414030400b000620400e00c01c4114010a0100d04140412407c043c1c4035000e00f0428060458415420300510640c000d41200809100d0701d071507030700d0038540a8104c854800901501e130064640b0300c1c0800080c510400100404628281c0c0c03041030790351a1406040d00a00c1d4404101c110086420450007006200161050f02801000440d030001c3d064584000503a00c280740c100071040356000302c0590f50310036a00107001d14100d5411550500c0006100c03400c140d1110b200c80c19005d0322400511080c07003403000b00e0b408a29040e11074148404c4110382d9448400c0160001d900c2990400710300c0c0c2c2c184003141060707442c45405c15248171342e24100e403d10211100 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 832135638 1250 832134388 832134421
    0x60620070317040f03050a1709031b03120c07060e18060f1f030e0601061b0f061103090c04180f02120c0409060b0306130f110d0804090f0c08 62
    0x20310345040d5110b59680182c040007154010120946120f035015541c0c07503d29242c0c0030307650007038941c110130101401a2004040884031041740c0100605031204001c1940c0301d4014000b403403681c0510942641c401a1a0588004d000307603110840180f8189150400003000c0b41030180c01103028078214105c0c420b4141903003000d103400000858482e25001070007800f0421410380540134248041c01161a04001d0740c069000303280701001d003030070303144241c2c0c0f521000d131446040703004618000072288040002098101c01d803036403024850000400e04604031807806040c0c3d01300303880c274400540080d0182d552034178080c8101030900100d5180160300c0f090a0311034038105070750070700064003d20184555400f0700c60107104100415100601c2000f05440340d00701600100345030a1800c0c000d00c90742010481e1058151140040e0943c04100d03214280b1071640c07180c1031002c1c0121003d8100701e407020002d0000c0c1040340500054010150700082100b8550505000c1d14410141d01080c0030841d002e00c0120004000300d003 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 832136888 1250 832135638 832135643
    0x24070201140c07020607060f020a08090309060d05061804050d0f0e0108070f09030c0b09040501050306042301180f030e0f031e0c1903051b0907210608010606200703 72
    0x95859410134004504d051017054401404586000420002011640d01038100a6410b80c0c0d5600c0a981d440c2c0455038030b1286a11203a1b0024050100e00c61000031038010650000002d40103a107248410052010301c000184e80417544c81c5c2010401d1041d4070390240d40e1001d948250b16102011466440010f002d0039001381181040010007915003078000d004400c0318000715800390070101402c0e61810501b80ca50002c07204c90b0312035400c00c0000a501d10740001c4160190341c0000442c2030100c0000b4000200e40c05401003055255240c00c2e0402d62040150780403034801d03004044c0c074844140340b85002411f0015120341c4074400d002c142c00c0d800762a103000907031607800d039040180c0300900d051010310f1910706270700d03500c850380d0008511301074280b15034041c0300f0602164818400c607940c0c6030302c0b1007405d081c050030391900701c2e00f010760030000892591042e040c805000c1180707c0300203224200c242d540c0c0281e6200350455210703a911001c0070000a039000b00d9042d01d000101101420310390038245a65190351140c80701 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 832138138 1250 832136888 832136911
    0xe310507052e0e01170702161e051903050d020d0e100816030608030c030a0206090a0b060d03090902070605060f0102030405030703080f041503090c0e060d150e2407020114 75
    0x1600344d034014854240c0000d042107501242e031900e0000203580f000300c281a245a44400700c40090600043c0003080080d01d02c60120b41062410602801003600010410300180c000d011000004180c040c005402e80700e59030390140c1810000b86070090184164150068002d00d0600c080c0168181c1c42120160001c0344280407803614524800d0890207481c0c2d03a04016964000000c1020a0740c02c000b000304040c8501c1d40946500c1c0d44e5914401c0e80f104c00890000d407214400e031002510501c0d10405408007580319040c82240a6120f0403100101d070001d40c000c0321300c103503180c0c2030141a14100203880c3d810002480110326060504001c01c0e12503500d48401000382c5408502a040700c03280130180d802401400c41420980031200d0001405065803520540340f10b040f241004c100141e20304119803203084041c101a074804001e0fa03482d50404d82c507012103442d0640e513032124480b000042c441000b40e000201e80542c48494800c421040031880a891441560301d000b00c0c0950f40104804403039400b50940702d0 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 832139388 1250 832138138 832138157
    0x1504050601030b04060602101506050d0c02150a0f0f02040803090906150a02030d0f180803070c0b09010e1e25080a0c140a0e310507052e 60
    0x50b000f400d900003056070f11078184140406c1c01075000401143c0d0450380041807096590030100310b1114000c900818000550820032000904a15004080350490610445145c0b200d4002014500c00c82901c2513600a91200390584090340c06010358400d01c0d201110852600e80b80020b1140e5174850000301a000310103003400282d007030b59049801c0d900700c035800741003a688032a01c0c40004e4807a40020000e0922602d8090b086001c404584034074001c40b43c0c03031031b203000062075103445404c51904000c150204002d2103010000004101400860240210800119009010391082d0f402d064080d28542a085410061201c1c030340c00c0021032150750900c034058603d0406002a03402d0070780b041500290300502c6150b038481c00300800c8684000460300c07420380c9805511080020050b006502c1e00c02c080c04205d801c0301040703c0440f0701c01a402807194130480d08040980410718400340b0800303070301309480d55004000300700400e050503a000e5040f11101e44500c1c840d0000701019075040c09503240d00c1401c0011109 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 832140638 1250 832139388 832139401
    0xb060307030f0e01020d0b090a14010e04050f070305010219080c03040f02210c010905010206070206040308060310060b0a0f080405100507030b120a020a0b340c0605040f0e150405 78
    0x42c0902c1c203d6071108000d540c0c070071000614001401c00790141c0c0e0301031200c000004600103080d1064109074404d101074408245d19001d40c0c554003220142087e01d55004100c07400d95802820424a402144540009a1107090001854450004d640e007103505002da80740811070381694040c00c50742d0199100840e0290070605001155141c0070f00c5101000100515520305801c0314001389801190f5000d0380c0b000390303042d161001241c03640425505000982e004e4004980000c0c0500200390340030074007030100e4118000081008017030380d243e580800c1200200086200c1100e610580c0550391030498200100181015555203a07543c02c03443c0c50700c5642da5102c000c1485035220fa040340022040c02003010200210004a150315101c102002304c0c4140381d82c6000003240301e450070030f4dc1c0b1640d500004140115250031031025910400e298440705100c40c00c0344e404002045600c030798015044a176141511581041c0d41d003654000c580d003000400c13400900070024848002020310540c100c00b901d010404d40c40d1034 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 832141888 1250 832140638 832140641
    0x40b0703020a0503040308040807060509031c0e03030a110c010e0a09050604140a050a0f0c0207061b020402031807050612070c02010e09090c040b061216050408010204270b060307030f 80
    0x10b8500400303034080007800106009101002c0d1080c0c0e0603e03406c2c0e07450586d0700c0d041945e071885081c1c40c541d00f40d0031030041450420800c40d1000030071185810807107070074400c4c003001078115842540c0d004085040c0ca039031601c1c410000c2058001c1010b00b82071440b90f5401e0039002410105c1184100202151102d00040340c41d111608221000c0308031409260702428030301009030103030404071021100249010710100c4e030045c090241c00414101b03500540480760030300e00216000c0c1c22940c40d68100c8000310600d41e0068645200440c459690014080f40c55000d558a02c1c3c1800e019901c04c912030507061090900d220030000300d1b0313078115000d428942c80501c0c5610058654042d401c04040d0b01004044c20000b4100e0081070a590000088a0030880350ba400700400c02a801000c400c101481031200025246c1441062110350030b000c9804c0040c1000c3e0b844840500b664042d801021710310400151001c5806003100d0803000b89030100701d0500c00742d1a0500070900c0d50000410711402c15031907441c1da428a6550307 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 832143138 1250 832141888 832141903
    0x61602031218010b030111031305030f0c0c030616020d0503090a0f0b0105010314010806040b0c070c03211707030b0a030507140a05100503010902070227190b06040b070302 75
    0x25607030360009502d880000300c4440030005903000304a508103968002d2a16041c803070403021500c80e20f240c500390344441040c0c4103480d55510b000c4440c2c2c4030400100201c80d030110058590004442c0040014516a000389410400003a00501403170b07046030000811682c0224a43d281140c1d00d19000b5140e9449001e001d1404e030414602400180e0f0203010760052029140c02c4505850b03003a201032007850072881720040130300070034460340000e0b41000340410700050f01e1200140e007006010242a0404400e501c90450b1060700e5402140c54540071601705007040c1a5180340c401c482e0107410401d5000d82c21502c1503102203070041243e0b04040d0703500451640b035540c130042500915008000c440c80305403601c000e10745030340ca506100b601c94048603000050600e0142d00c2000b02186a030355007411a40790074500c00103508910300881c2d000b4011603a06915840c100c0e503040401816180d04101400c115000d90f900742c0114046031502e608002803503c4035200e9a080314100c40706203040c580e94000505003241414036 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 832144388 1250 832143138 832143157
    0x44b030309022e0c200f12151305030912120a03060f24030f2703030c020c0d0f1403040e150102010203011809110a060309030e030604030206160203 65
    0x720258900410300d9640c120f480aa800840c100900f00c01000300b41d0f201e848940d8001c08124501c0b00526124510a10a262102014042c030040001880010320f004000c2c41d064507140e0301014840703c680c0c80400c03105421410704601001c821031552076407502c0f441581442d0b4001c1c084640e080300082003c100325203412801e0041162224100c80c001000341010303201e01418101103d070040b076624442042001d511038822030910000050035010b902902105c2c4519002c20760b41c1c00820700118940010f1014200784004100c60b0901c945000740403240c003080900c0842d4032041c0020403d41321500541d2403990044c0b000e8aa00e4003d280000844a9944c058101408003040000703a480003290302d1405102494241226034101100482c204c0c04248101d0341030320300076441809001c3c0311f50f008030006809408140c004c120210081a40c60304a40c1c045800256a007200c0c0302410b91002800d110254101c000e0704007420a03450003959010090072036015480360001c1c59070200d000304202c2c1c42c44c0a = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 832145638 1250 832144388 832144399
    0x3080304170a0e09010509060a0312140f04080d0306030803130212070e25020c062a102d02280806090c0901021b030102070b044b03030902 61
    0x5902c00c60051203004401c2c1614041c0107803100108141c50000640b41c4151005008502d050385161180f0b5043c0520410440c00d0001c901c5250503062070841c010080c0051701e46c82181e84a1500030311a1810309042040001c2600e810411701c00250608100d0f508603204544200c1c0101c10390000540d444900401400390303109078900055080c5ea05c61446110702058017507500c003114020084104500341030810300058000e014200309900d8410040c045521080e01c1050001c000c80040340b04050400003000d20f59030001c100d020081400e40907000b80f42403d043c031140400080f620746100009040e074400802900840c070714140c0c00c0c402d6007806001800f5109460745807903480010704560420768416002d40b41800014140307080380e0003100c1400c14180d0007041101001040b280112810301c81e210380c155000c119a50218103101d4095010700d000d40e80f1024920030691114030081c4007902651055100f400e40c0c01e4010161078002d00fa0111120304100380440f10b40750031001081001802035105 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 832146888 1250 832145638 832145647
    0x11010309051b191202030706021b090c2a01180b01090f110403081801050a0f080c0c0d020105090f0624041b080403020d0e03120c01150303020322060503010308030417 73
    0x9600e8044c8a402c80c000da081c1d4203516100c0c0822038880740038141140c02032210b885000b03403a0425405a6501c4121510100e041c00e840c907071158003008503070810000c0464001000e10101d0313800e00c250b04481940c1e001d00581341c142990b603280c0e8000c052280e0740b80d2503929420190580c085030424064401c031040035640e41ca0312490b0086460700300c090740041e020b0f0918004002540907504844040d60551580c2c6c0e8620f500c0b4000f01c600c3d100c020410b920489041c04143e4028000300400ba42c4c0142c907800220b428941140f07031520302034900d802c0580a500404c10b10651710851010700716040f888002201060a0305404200070345490301004c0d6555045200d04e154141d0b026400d18001c511035806d84403207100d07820048a0907000c800e85654540c02041c60070b03000e20346400042094450307603800882d51040c0072800102001c41c2d68019005a00300140340302d00920000d5034151802c030b1100e041c0f1159420008024803078001404010300b6000000081401c0c413010f18015400e8200b040d82e000c0c0d84 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 832148138 1250 832146888 832146899
    0x304170304060f050909010302060d0b03190b0f0717040602090d08030105040f050f1f031e0302060703051006030e0a021306080d020c06030f040222020711010309051b19 74
    0x201da1041c816100010b451442c0d4246451040e000ca40d4901402840400c0b10390842e020401145d20000c110703140c0d1036270b6200c0e09001d40c6003400583c1054464500c44a10080e150400d041240002408010410744040c1005200d40e0000201c1e021403080c502c0c134400d40d6986142c101c0003031060074a0305a01804040501042005200086040c0d0348203840622a141c80d01c0e003800243c5030140c40444440c0124400078400d48851aaa001d1104000480b0031070540c4d00c5d00c0e035110105600c41c80ca1441030388015080241034042040fa5045038035440c0c100203902d0052102d0190003850300403981055120404284185000c20003400d0881c1c0082c21484450700821413000246960b120300501d071700601c1012240e150012500c20b07560400984800c0c40d40d6240342803088042c81c0100100c1c0e2101d40411016030011240d00b4100d040c0428490040e5501c9030350030010348850480c0c44580c10075044c10f441c41d000800c0481d0380c050114080c0c0714851140c0401c4001101c042402521400400c008070740000d0 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 832149388 1250 832148138 832148143
    0x60f1305011406130620060f150f13050606040306020c0a05120309061512010c08070f020c060702091f03050606010206010906050d060c051c090210030902150310150c141c0e03030417 80
    0x1000069043c2480a2783c8909008400e0444050694041320700010035000800036004141c1c0038500a041c5031502e502ca54602d030483c2c002821100c0258041140b44c01041020007000842c000082030b69821480c2c1750300716903500c03031004040d050f0700745415403c0315668840b96001001c004800009021a070540c040017030010100300e40303e0000400d500310341c001c802e00100b86c8030070ba002c000e000c0520b071000c65002d2118404c1d005e00b018200d401511110b83c80c0d500c01c1c500304005144950082e040c1414001c000910782030040c5c2140328400e01c0c1010030403541e0b90f45888081c0d5142d014801242400035084291140d0145901c45001400c1c00300380040042e00c540e110350000c9100700e942003100104284201d0440340030750030017500807000001c00c06030350094402441c0e001486040c40d0a40d00d03103550b0141d4144011802030390201d9803d13040101040034540ca500810000e0303400a001107105c14908500351100700480c0c2080c49502e8000b016945c0307050044170003409130741d1022400404419020340c1d = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 832150638 1250 832149388 832149391
    0x31803030715091205040f05040203090c030304060807030501051c14160f030c0803090d020d0f1203020705190b070507031701080f060a0c0c0605060f1305011406130620060f 76
    0x913002001e500c901101140100305540c00e54400092050500d820902480025840a082000c0500c1000da800d03178075030760401c020405803100c0d540f115440c0c10a160064295001070b0095072064060408280c07030100d000c0c1ca0207000c1600140c140c01d605800c540194240400340a040d070705c0c080004004688400806800402c90344283c000c0c01c1401c0e5180c0c0881d07140e004540c81503510101d0003034084094900f403c41803150074060b19415504400075503c1000d0740f108410306c1e401094010400703209125003404550f80080304007040500000165640301e08070f840040000d010700501080c0c4105051061210202c095409a002c4100e944c40b04011955515041c4050840340314a000142c00c00070300340070f03414100303500703031a0449507881695074080a0607000b072103140c20440300c0d082408160340340440c1103114040d524000a4950500c0f806140a040d0300040e24014807007040024002440c0a0414048400902c0e00790088020000c448498841e4210382c1403540c4210018809144100303503401d03 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 832151888 1250 832150638 832150643
    0x504030215220609051203070506070c03021f06060e01080601020604081b0618060117060402010c11100c1101020a020915060906030702030d1b080403080a0b030313050406051203180303071509 84
    0x4c441d01c06c1e94a45581c0ea80c441c60100402a0300004040ba4405001e207100c007011511a0040d2035261600c0800304585502140c12020100e0701da54040218039080490001030320320078642142a858541d001035a11180640014011500040c02c9031a55980b0040582d820507400b050781c0060078100b00650001140d005071944901460300000b030a080e214504550300d032146000380949946d9600155094410214203885591000c100d010b640c0ea208110780200800607290000142400c1c14207500301c0c05902e61f0300741558861960304015a403020707441c55000d440003400e4014684c540e0046040d40c00307210501500444040148441e4a401001810001100c3c6030100481c00741843c40b5182d000182404501041984001c00d0110b8403608250340e11070609440271032213002480101e465948203500c035902d4810100020300041ca004c0c06440004d080803241e10045c600410045501d030300c14040b9120340081c42d44890010354a050040d1900a500911420258a0948070f40c2c00a0400b01004 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 832153138 1250 832151888 832151899
    0xd180c09020c0a15021b030304050d020d0c0f140102040b03090d0314070e010314010b0a030e0a0302070e0712090f120f05090d02010c0210110d050403021522060905 72
    0x10400c040c2510a54000480c071100411203040203440f459442401c1100300b050042d020084019019000308440e41c004e074800004540e00d03c1d00d41444d03405c21050110200840d00003400400b0300c0d0390701001c100400d81d0055118540c2c0280c40c0b07011680c000741d14400701200d50001c035001880a41d00c1c0040c0d8810320401c6e06840380c0808107001102100c031089680310030f240300300000c61080341c07050fa5410429a018140007500d00c0f80a19550020007090780100750711a0f0000310800e001ea0b06004000c00c05940c0401002403d141e80c0d0049c1d101c00250140302c41081010b0005100c1d80d11135401e5041d03030700660500700040c3c401e034209501f0301c2090700303c140c440ca151408103144061082d8440300c030843c0f07142d46a500302001c400820a0441041100380d041107505500c08016030341c2c075610040c0c10b002c0c585070740341e07078020a501403403c01140e91401d000f448000d0108201588401c10351030059140056190341e10848450215043c14441700f0038175206050aa0200d0841d81140c9090183c5c0c404584 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 832154388 1250 832153138 832153163
    0xc010633050a050315040b18061e030c062107031a010804170d0e01020309070e0c07030c06020a14190201050a0e0c15370302040e1b0d18 60
    0x4280e4241c440d0071003a02c00140f0400004100d81442540028100401080840e00c4c122420005e407116841d8140c0c1d021030280141030203501e18002d49480c40100d008040303440d009828030002502d40c158101e07103034000c500000b10741c888000000b5003024042c00d1503030810000c2c18946c0c001001028280f1080714110181c1c0342e4651258010612548510f0b40418000b22080800c502c068031500704007848816170362a1041c0c459040c0080c0081d51244807c90f00511a080c6000c4401c6c080040c00381044035401c10410104010a5010b008003403403540121000da5a42c10b032020464038408110016000f0010220f2583e10300050b0072050710480009078020301282d00d0340000c1c48102c8043d2240a1031a500400e0005110f00342460210b0741086a084807509009940c07031445070900c0141171110211040382003c241064004044800700000c516086040c5400c1c0341a04031020405000c04d01c11043c085241c0804001c00801ca4002c02800d800030302101c10800301082c00400388907802c4811009005 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 832155638 1250 832154388 832154489
    0x80d0b040e1c142a030c070b03150f1f1809090b090c0609040e01060308031602101526010213080f010b03210408030a09091d120c0106 59
    0x801da5502c5840342c42d130b01c0100c007248400c6480f2a0004400c044083c0018041c00d4164207040c0008402440f01e0340e1016924501000b02c08251061480464031030302d6410340c900000d49565a010b114000030301c1149004109000003a90450f004c090b00c002440b00380c2001003100e855581001d05020711414040304180c07115004d80307482d40000c800c00c0ea0404011710911001c0e01c0c25410004003882013800010722551607403105201c1d0b90044a0410003900c01c240e204040580c104000e598464204404200581c05c00c01b0303059545080303101c1c1c1d04c941c291103080030f00c02403404500d10005501d21002103540c3c100e00131f40c060409031a8802d81155004e032a901c0e1054203010700407030300c1045009001e48905441c4d0038008500142d0820780140702e98003800b0214500000704014a4840f260703440d90102c807480c0500200540e5501c0440b4142740c4410b2a0b098503681c0000317541d020000340000e40e182c0740c0034921401d0303004040a0340500c0e1040d181d4010400000915041d040c561415241a582200c1520 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 832156888 1250 832155638 832155677
    0x106030f1815020d0212070c0512120610031d0d02071a041505040312020a06061d0103140f010f061a030403270e04031812080d0b040e1c 60
    0x1640207000480060700d50041c02c52140c1c0108030241c41c40c840107050481d1001050300650080b44c2510120724001092021302c0001c01140c00f5510031003140c07038a000040680034204036400341c40380c0e003c2c0524420039984070b4020b8010b07050b1351108400c0303942c407440712040c031aa98403650b40004d405030080040100324480210018020700c3c003440040c92501e0700d4041040c18000c0300741c000d030040110521002c80080d2011001c240381451503402024040c03e01d042100890f001380d4011860403c26802c0e072020038140c2038089045981001111711120258020300d420068144403421281d440c1078824010b410250b4841429102a242141c11510043d048070215210a68010300451003054541c05182d100c12079401003400703150251140169680c4502540714401c0d9401c501081020200d50000f490850b400801001035407a014a944000e880f02c0c02c00384945041a090907844201001c91522650480c40b810464842218a042c80034010180f00c0b41c0307076035050000901c60b111710182100c090b = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 832158138 1250 832156888 832156931
    0x207061b081b07020f011b20270901140f0f06040203070c0204050405160f080601050405130b0402062b05070e0f090c070519380601180801020a020120030106260106030f 74
    0xd14510040900606100c4041c0c001d00414401c1cac20f6403111140041105180e08003070083c505000c2c4081c00d803c4c9000302c01d0b000c0c3c0000f82000e01a52041c03081200300c030b80c0075601660790b40c2c044d00c0010340c1e80c44600b4020304000b201c0c0c003115041030000800299000000c1e0700081100c1c4500150340072030f40c0b900c1c20171041e54416035005540803000c008100c08298202801c0c2d40240c0300030102d030301e481b0071080d6800c903510144e0164944007401d00c40c074030000042e41c00383e6648220117152403485800f03d9030000303820f042a10f80540c006d00c00040050116140502100c0780590400d049a40c005c00f19000b5548000c080305084500d0108105031295450b17000c05000294a25000000c1e44240407041441910b14000c2540e81000740c05480907582d441e0035100c090203071107020005640c0744000792000e07003510390301c00f00040c60452048040244501d444181d9041d903c0306d00d050000d513081214031743d4031120303510f0060440c820b0000000070400e415500201c10505040c1003840000c440c540302c0002c0743c14 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 832159388 1250 832158138 832158169
    0xf0322030809101e0804061515030e24010f122402070605101502030418240f06030b03160312030207061b081b07020f011b20 55
    0x1070041040c6881d0078041c102c2c1c1c20035189004001d0081d03107009450807610140c13141010038404000d01091001c40d01490b945030000c50030700f4100c903207088264001204e00000d01820143d642c6e04402c40558140300041411781e640c690740e81c0c5d540440c150414044003c0c89801c0b038404071650001228010302c3c0c401d500c156004100d416003052001590000e404200a482e05420346c2000301d01d0015001d445401d01940407501c0890b20350b07083c0300804000b400b0b0703c0200700955006006c04c00c414540131000c502107001c00800403c00601c0d1110201c0d90b20300910100d54140700204021032101c02d282100411031713605507002c0c005040100c06064a520700c0707551302c103104034000c8014004162220703004408000145001880c0001507114401203030703c4001442024000310742c0c00032205a00c500481e4024042c45000032410f03410302701c16040c5228039000240a00002203c2002d107a004500b4007110f883d0902402543c1d8189241c2485040e48180390300070ba125040d40d6000e401d08140021820608 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 832160638 1250 832159388 832159403
    0xa0305010f030f020126040606091805060105120705100201020901030b100804060c20070e09070621110318010c030e030706050c13150914060301051207080f032203 72
    0x290f0703e4004681c030004a0842e02c55004031080b0041c031800340003a905100d030707020350000070300f060520021a0590f07035881c030920100d03481c4024030004a2000304507541101c200311082d140c0f40e51344c155941d04103003e9920440c0c1c401d1a84070f458240e56010340007420740170402d036000c00c21103e00504100c804400124403e000822042c005400540e0380d0340071042100080c10003055a011110ba00001c07010201645202c5400040041149030001e922240e00030168401610440e800c0990080000700d1010840d00d007542e030201c4023800c000107640162500c21038480680e90303900e0128a00202c007444c003842d4881561800c2800c20603580b2074481c0c8142e881c1410080d501d00070180e11214054040601309400c084000c100c200300c1c0d0b1090341c1c0c0c144003d04070b00c409a0b05200b641480602000c91982c0100d2080711a46c3d09103101e0b5852400f12819202d007241c007103251300182d0748240d140c03030f2141e08442c0d458460710340940c40407080000a07081e117104e031035001c00f80000c00010156407024144002052013 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 832161888 1250 832160638 832160663
    0x11b020c060f0a050903070f0f09060b250f02270a090c0b070c0b030708010303170601091203020c1e1203090a06050901050d0f05010504051303210902060706020a0305010f03 76
    0x41340300e203000f014034090040c11260816202c0c804059030440c1036000c208044030b02c142c1004056854010300c00145000205c060070509141304001c600a02400145c40600c00b6644000400004200e00c540b1a90050200e450140036840301c0003001d022861010881128000082d84803142070042e00c5402da4800f103000301d01807404081120541099a0131105040100400b007800b0140700091840383c0c0c4240d0b21441e142d4035504000d0201c4042003071200c60005804200301e851b0360004005000c560040e007000d090380c0e07001d0504900f00300401081c6944140f2040e5401860030456211041040c2c08464030b01925185941942d504c0c441c2c4070046810010304201000024000c00c0645603000701030620341d04e440c004520180403a82c03c1c04a0002c1603035540c3c0140040d00701882210381c0a003103c1e0100e00041c5441d10094594414400849500c8840315000800c1e8034440c0c021841c11366014024988455080c503110029401160000c00028074110001a426510440150450342c0003900030945 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 832163138 1250 832161888 832161907
    0x7170601171512010f0c021506060306010c051501090e07030302070b0f040b03010f03060c0521090709020f030a0b0d0206071203200d0b0402180f0a08011b020c060f 72
    0x80000074540725076034007600c10302c03501d60b111040303010b03000302600000041009801c81c5910840741c1c40440f0380c003190b02481c8882e03504804401400c1d0008000c441e0a5240d0742c40400490300e40171318802c003d041f4020b4119104e441084c4880e414142c0305101c8040c0601c0d04001e4810f55258403521020303006901100d030802881ca01000201041c400c0c0048042c40c0640b5001600000e5000381e000d2139010a100d002081440194410b5821540c11032404510b08520b50130502e4400c0c000d9001020391500c0240491780d0b000003006280c004005912013991220240140390b80e02e904116a28131070141800410b5500b450b0440741c07081d02c598000c01950800381c054940035801c06032004500d041c15030760301005a0081d48011800385494120195550b204542c07440c020640c4d21030580f81d80100d0040c03001d4681811040c60072811000c0c142d81000c200c01a282c0020384440d0f0550045050b0b51070070303001a031029014000a404540b0b0740d0211140080c010040c42a0341c03144408480304c001c002d00511a1 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 832164388 1250 832163138 832163177
    0xb090a060318050a1214030f0601030518010e150603010606080c0c210a02161413090b040f200627090124050f07020d260307170601 58
    0x85418030b005101c038400b10303501c1c207180c080102c0041e240f101c8a421100e07042c940c0003085220b00b013501d10f03c0d5415414800422100c14401500060500d601c610002d11990540042c240585241400900415000840c0b550702c03212180d444085a980d9040007404070704050140c4412145280c1c0d480c801d13a41c41c1740c1d162040b9000b6210740405401407804100c040800302c074040d102d484845001d20390b1a50f9050012f032510f42d0f40c0c440c0401d1702d80039944c204130a1800e000d4009039420203030780501103603119a2640000f80074141c1d000304a85486405c1c0020700240440c0710303101d280b1a5284c0614507104820310b890300701c40740c4441ca038058010410841d40903100c083c9541d00400b03440058000e9580440000c50408092300503018a400d44103440c8050404140c0f515509106810410728012406185480a00c200040070317000300b80d18000c136020000b021000c43ca1a903c035032003400e0340c007000e00740c03140665000380c0341c2c040000c1522800c1030002d8500c80c0f140d03004080584079078102031103044d420319 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 832165638 1250 832164388 832164401
    0xf06050711100c060f0b010f0813021003270c0e0c07031805090403020604050c0414010308071e0602070201032d0f0e030d0518060f0a0509160806060405010b090a0603 73
    0x4014100f0b441a0018015004500c58598064004101500300c0000105080c602c0744c3d00900300b1504074217100c03102c01c5488001c00d560350144d941c50420490554250042e20107060400c0910142c0708030160586800c050101d4118421030281e41026503445034905e6003082610f4218100c030040041c035000030700400074104411644402d444c0e13983c1e038603000282c041d50201c50660250700003004201c01c00c00b041c042c039043c0d03071400c98003006406e04008074003540300e03814000184000c4000501ea4103219441010510f81c2074400c1690010320f00a02c0c02c040070390803e5404a021a08124400190500c2d0000507000384003000f9401010306000c50a02c00034001131140700401316600c9040c00c8078080144001c2c281e10354000710103d8542400009a40c0b0b25002c0403108110390495024010030580e031280c0140c00c241241408201615844003207424280e02126a40c000c00040000207024007000c10f00620449048804001c6603036244906121031150041c11355024110100c24003503940294000d4 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 832166888 1250 832165638 832165669
    0xb12040302070e0c0d0e0d0509090604060306051603050c03151003140705072303220803040e2403101505060f28050d0c05070b0c040f06050711 63
    0x80c0c0d1680e541c1e40c00803800403c240c600010010001411004086141c0581e110100d84280181203150703800b032000b030113401284a554800d041c10383c0071a1650780d498005034040c5070032030f40c108064104814482003040c00840041c0109040200180102524400f90385c4039544410030018059100c10401a800040c007080c001410340ccc0303401004501d40810f10451041400d0b4642c15668282806c180c03400d031000e01c140800d50011b81c0c900710702e201d90110a840b4000381d508000640c500c09221058020300307203134000d4034040c8004100010480c6214160b07030700031b503c9400780742c0020514005510003918015800c90700340e8000c5284040c003440b60791244003076202003e42111036a48078000100315502a034507440e2400c10214800c81c26071701c05000e980e4201b100315149c0440c007620260241407405850203152055503a101006451406101120b00b0a42d12502008483c036118042d61a56005402043c40d0907001400100e0f2840c081c10844085c00e8012807401d40d03812002040141d41d00300320030382 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 832168138 1250 832166888 832166893
    0x1514120303061c02180c130807030c033e0a17060601212c03032e0b0a0f180e0a0b040617010207030e1e010807051308010603020f0a0b12040302 63
    0x14406489000a04d850160743d518640596600c1049a42105440c7c40d8111428540014030f04000041c2121444002c89610130135500300f422004039441c58500c10044e1404440c2180c0b035011840030f01d004400212100c2c00c844015605468003c0c0d40b90780744607140007609661003140400d001d036005a00d03004428662180c220101c01000311010166410805d80709403a41d40181e0307003c405404521040b0030b20b00090004e43c1186403a0240c5589241c0c0c01c141e18881d4102c105a07081d1410520068401500100f442959079012001000701040c564a103c0b00000300d191020b1103c600d01013054034100d4004004080c803070b4440e07951903802171032425610741d4070680d5200d0000748420004491600345010300700060b15034015090160041000c0b441c2c3c0d9100d80d051f180202d00788494007500048001c401e281c54803055a9668090310309100d41c6092650b2007030080381c0004e081074150070410a60780b00b51500c45a0b10144001c0c000803000ca4010a40303a03000a010202c1d915512040c401d038001d019104 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 832169388 1250 832168138 832168159
    0x2060601180f0f0e0108010227010909050f1e01230a080a03020307060609050c070605060a031506030c0905250504050904150b0a271514120303061c02 66
    0x2c0382d841028607075011440b21540781c02c04018000c1c90303252207801812154001e41c82d0515510158034610061504800d140314000c00004079644598100005407554020400190400001d40c1401e003600700d40c00101030404488440703071078030b0205c0030a040b20100784140c0c21a100c458040950122001d0096811060700c0030006000d83c800c101d01449540641c0285690710943d040c400c09844158014001c035a041400b4030161a4030f4100316404950019000038180d03c0300d1000910741948c1d0361000c1d2050030403d080c508185c081e40c0c003a0044034480c41c000c940d403954032401d41007500d40c2102c02440112210b408a508000c4450700c0c2d9200d0141f40c90306916003902c0702c0c001104a40196410b0359101068081004030001e64070481d5005039084078802c2ca41c0746407184510000e80c200380b15050f02580e8480b0b40900a480ba04000c801401e41d241440049850311811520300000025039441601000100e241c403601c04002c59000b80c4e400b520792440390b03030b158482214500130200101d0f0090980700 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 832170638 1250 832169388 832169399
    0x70b1605010606031e0e0309040903030e0a0302010608010c0c1707050a140313080312010b09131109032509091406040515010503010c020316050c0d1a160206060118 72
    0x100380c40191150342c50005d0a48807034409075040800d0341c00700f807081d10300c5d00c4207240198000105940b28904201c1b030100300c0400743d2070114007a010400c01c9041c42e01c0b078a00d5240825806400c91015184500001c0040d194000e904888490454501804201c8200201450481c540000b442000c0c060700072148116826580d44044140d00d02a9903915000030461506100001d1100c000800c4c4203401103007014203080400458003818460011583e1002820001d541c581000644031000c024104009000b0085040155680094100da20a0040110b18851501646100c20441d58008499070102e03080ca0201001003c0310352081d034076800b64110100394000c08000c01c40c0310f2072007000642451f15410280c04000071068100c1440b83c0d041808280780258008251840e41103181c810300340d850f40700c1c140036090032185103a03550010182103641041c04071036451f8007402024201810b5060f9102c80101070643e25450407840160018000309890f50710400806000a441c00c0e440f001155a44 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 832171888 1250 832170638 832170641
    0xc0f1e230f0721050405010f0e19030b01090f05010b0d05040807020a031a0903031608060d020316140a060c03080a27290f1e0705180f03070b160501 65
    0xd0300c2c1100c200012403c1105400703050701600740302c0c86050070190b081c1420000040d00200081640c031041025000c82c4108550b2002c03114404403094600c0c0840050702c900302540c0c0624240100180b2508040c50b403c07640307000d0310449040750b0041c043d85043c1024845400040c3c48081e1058914403400d001c000f0250341c84c040908010b512600c0341042485181c1008071140c84014000f03d16600140104001b40750304252444088040f46000b40481e41d699000030300c07080c034500020f5050310400f400f0010700313483c442005046d01d03940ca1034803140c1040403040003a045014000c1400141c0ea0080d50f03400a401500e55a411445809000c00c008042c00985000b01221070002200c2c00142d20405043c007903903500d1a0351940e0010441318468a660b03040e2000050701030004850050717000002070440982c0d01240094030400c4240a12500b42a00c0080c0140c000301c40c00a041064002883e0142c41d0541065500300009030250100c0c51a010301c4015039007200c41d01c0c0d4501c0d01c01084080000c3e500707 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 832173138 1250 832171888 832171897
    0x10923270a02010f0c11040203010b041d010302011e021e01090b090a030c0605180a0507060f03050919020d0503040801140a0c022d19031707080402040b01050d0c0f1e230f 75
    0xd4bd60000d840e01e14150800105020b01c00b0302c0003e1038261401400541d900c007404000400c41c0e024900c000b0412501c040745400c40444c1c0380a522481c40c4280031040d0f00640100c603500d40200c005081039241d40102d0390300c618070504003c010610200c04800001c40c6a00142c0d8840b14004036540702e12103440b642400c00d0507002c001c90740b0350051081840740540000c11040c4100d03451904008524003031440725542d4105016030901030700c400a5180c11565100e4140b034070268008250381d01c0c1e954038401c6a000c1c00c3c1d111200146030308594001a02c00c0164890301c13a018015078000c0064882c154034640703000d200303080442503900324007401070107900040044030100c014004031204044000d040c01008482407048091410740c1502c14401d085500c115043e803c130360119000902c0300304000042c0c4a5100d09038500d0407a605048106590f99085041c5508031070203a1030b240b10310b880c4401c8a90307040403419840d401080390180240140d00c10080800512006404018a04043da01c0d130a0f64a801 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 832174388 1250 832173138 832173149
    0xb0306210a030801061812021c1e021017180f0f0708061303440402040c08131b03080f0c1002040608010923270a02010f0c1104020301 59
    0x3c0300104080b590000300c4d162010800081d2074035050800f898040103440c0860017920075403a2802d00300c4454a08604044004c1c0d11202400702a13009c03020320780301c05075400c0c0240d11032031986504101041c007410b1441030290503002c10090a41c0e9142c20040c4400e9a0920f0019038450416003130a840c00800044116040c1c800c000d002c490300c0c1c2913075545041e000400500180c80e02c50840400640c1040e10042c02c075903003440b0081c071102d10003500103c8454400100c13200019030b040850042e41e42507079030360256000b51400d102d29129104140c502c682d050341c040e0130b1070380302c241e58501048816100102ca0307908812000c00d0780342c2d030351280100741d04520035410030304200040680d00b01404004c800804001d07a035080d420245090005080c03000140304240c0c145484d2602245980c0240c5804200d604c259a111240d5060281eaa40d0841640303410a0701c01c640300c90300380c40001d18006500704c03403568141c2d00c503654500056805c85081c00164021105408032250000141d561400914003910 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 832175638 1250 832174388 832174397
    0xc06051f120804060f1806090914010e07050c03090a080718050f060d060f09030518060c06011401020304090e100f0b030706180f030c03110a0b0306210a03 68
    0x4a00031440c0c0c411021650148603600c1e100c0700024006001c1405460484016050041c1a101900701c103445070305421102501c07910068030085035064000000b41c1c1580c00e4a50208440340c40809007001d0342c113083c0511040d040d440400510801c2c1300e58001c01440c1020003d481c01d000c81c04010860302140c030f40000c0016080b8000600568240090200c64a11809001c1c00307079040050300070300d8190014240c213018000b070319820014403d10703404c03106607001400c00800001165003802811038004810400043e22540c24107540c41c174004c0141d0f510414903d0141c403481e4a060a02c031020401c02200da4190b00007484002032403000303445210741a8000001400c2044044450a41250004079160707920780e15080d9040c000c0c5c2c8000411205070351060920308200100014000c1c40300099500c03203c9600c080c10781c040f0401218980810440f0300c104244014480801700b003281480c00342c06024000070003403000408a1503d2618043c050300402c118111001d0489202d03410080680425170128 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 832176888 1250 832175638 832175671
    0x70510021e030f16020d1e0e06210702030405030606060702180c1806120615041a090a0605030c1c020904020c0a0318050120120307170114060403120c0605 68
    0x484c083c00042c00c2c001c03103510140034074101210000d0150051025000d6441c00d40c40380d0340e001140541542400303180014405929001002240000409422458410403081d02c02103a031650000050f034040c2e480003409042c840e070340c160600010307400008080c0c1e841209a58400040b41440385034078082c403e07103e162581d818104200d112034900381c018190054104204d07203401c0000d132111083d000507040720799096001082e5030b0080e40d40a5504010034a0b03807104000c0ca4441d501c0b074001d1034404020303606031000c20744c3c0c0d1340b068401d4042100c0d24038041104100301815050041140c02c14444410801410240c0003004101282c0000082940c15031110440c81c00381500042c04c040543c80b0510383d480210704000000307000c080021070031000c101440804180c114418440c1c5501079000499082d22031074260030040c1000001a05091340700c81c0100041414101250304c6000440045d14442c071b0146140c0d100c5907030304001209442000a04090000020308030301032035002e0817004020700c03e039 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 832178138 1250 832176888 832176901
    0x30b0903041d04030e01170604021b100e100903021f090501020a0806090a05060609100c0f050601060f0923030f0a03030e070605250f0503040906170102070510021e030f 74
    0x701911000171810701c45950400112281e2003c00680e0082041e540541c5883c5078992180c05180c081d0f5546446000b4690341c0e0100d000e16070300000194800710100d401d242000b05c0c0000c11921000805030058020300c4c0c00100c0390280d4010210a1707220702c1c200060a00b115210b8600b240c1040100500080b80e40e02400f03642c0c600701c881e054005145d13180400071400c1c10b0300000e946104a90701d0358069900981ca0035049030084910308181504000c86040e10038462404949984090048101140310309040103041c512403082e020603100101d4a08121011440d60054204914440590325200e10954082e0003131040c0503016042c1d100791804107048030a0345540d81400e485400607001c0101c207200705512007240c1e11042ca10003070f200b1801c40050715181082c00c0b1030030402001410912000034000740016032a84400101c4090381c494a42c0c0510102e8058243d1290b00000340556000300307a000b000750070960040c06a00c0c8a00040008000c0060b41d271f00c84e9030012640c3d5190310310b00c942003040 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 832179388 1250 832178138 832178147
    0x20c040b01020c1e0f090f010608070206012102041116061d070b03090a0b19050604050402060a080a06080109030306150c150209010504090905030703180f030b0903041d0403 76
    0x14220801d0001c0c1190546940121301c1051071489030742c0c08030301d81c2036030300c80c003030320381c0c2e4801c01001304060035182c02c5140c5010001c244030000c0c440c1c9030000e003203580051102440400e20780c1c16540031001004070380c01101d4074180e40030030184013640c1c4150380300988030020301b201005204c5036200d0342c1000307204402410540c0464041c075200704226000c1c2c4e000d552a980c8082000d070181c0d000c03024003d031a6241c2c100680d01c0d1142c030601c01131a00d40c60b2003c0c48807a1428a804c94003d0020384801d10603955544144000d0384d0050314000e4000105001100c04d16000301e000316404a01d240c0b0025a40f07a440015500756200b2407002c0c2c0104e41d0350340040c005440200c4200c1c01c450000d00300183e01e040140e8030343c0020902000108a041d03400304240078268411800c5400400c40c005040c0f1024095061039501c03a400b5000460100701d00b1040e03a0100106180c0d1030003100c46800c501600e180ca19150012074100041200740e403030000304404525a49065825201c0d8a0010010755940ca0145000781 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 832180638 1250 832179388 832179401
    0xd090311010e030a080c040509010f14060a0806010e0d0c14040f06060c02100201060b0a0503090607020114060d1103030a0302070c0614091309150b0411030c1b120307020c04 76
    0x2680d42d05090001008000c00000c0301c244000d94500a400c03540c41005180e401d0041c2c1d004558404090300001411601b8100500240d40f60315074400202d0182404114162103101c3ca000041004200003440660242e0400c0001310805064000c1922207036483c2003004001d600451001c29492401d6949418203224032041c02c0c0e4044c20802c461420120040e0a03861403030750003803140c82e210300350445551017904590024a9966805502c0d200c0401001e41550404c44848503035102d1000050040d40c414082d00103860b107000c2c0310302e9086e1a903405111401ba001041038805401e004c108a42681301000103101c2984143e0340181c8840e004d02d00160200e100303610140401c8000c404c404210429a070071102000d00c12a080104450800f08010151804c5000584901801c51450000c0300454100b04a880e40031141042101d8036452480a5170200f0388281c00c807a0b80c20702605100c2403100b1030000500c0b04038021541d1005012a880200303900c100d03070540058100704400c0020341820b00802 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 832181888 1250 832180638 832180667
    0x602010f0b030727050c03010501030e0c090c0d0204081c20101508010c0306080c180c09060418150e0f1501030b060705010506090f04020a0b0901140d0903 68
    0x7805407121003000aa61212140034074901c0e4071822010490000807070840c1003015042d1402031041d0300e0180034800e0326801c24030502c0d010904111084848080116001c40010801001540a134680c1d1a40482e95000b0600070001d0035403c0201144450b001c00201c1030846aa00d21600c0000c00440c0061400c060a04102540803020340c0000c4a14400301e5000f40220885c3c20004043c9003080491403060216804200103500e0020340e5400c480e070680200b425a181c600488891704080414041001e40040c900e0856114050110704c0c140e8070381004003414000280320600b81038554480001c5242c4803036003218a00e40d40e080007170400d400410000d0040c0310103242e4908902e44960341c02c0c2020070092184a240310400340340f10883e8029032000c40c0e41c01010302429180c0d2014603214ac000c00c4146c64441c45000400c2c0040e0310328038080d210b1031155a019002e51846c0e41f03890102052500400f4103241400300e006290081c0ca414000645016005e001010400740043d040151081c030382200b0b00c = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 832183138 1250 832181888 832181891
    0x120f022a010608210415180b031005150910090f0e07350109090b1807050904060917070623181c08010f080d080a02250c0602010f 57
    0x4200d115408074414000b4100c0003c400035a003503013680420035104a400c141e400300e528a146003011640144614240345000d0741281d1020b496500106c1c02d4003080305c0022501e180140184210b0800301c0319070050b610130801c0b6034117100b00040083c4035440581e44c10f80001da1500000c0040c20400058180100501d501400312800d0100700106035103019000c11504e4841c280400d2041124507905614260300c0c105603010710b50315001203102804c6141c005031101e4500070301245030080510640820b00c031503a80100080380c82c0400303010f0f034841c0007401590340c6a40d0745041c10101702c0724610024024034100c81d8981e0740d056407800d441102c1d070300440303681c042c5a43c0000508640c0c12054007500011081c40c0c1410a10903402060302d001102c1030b0a400741100d0ba95140d826a81020416040e0f039448110011555108c01040d59100a5980040005040c409c0440d511940303503070007080081001118404005420141120004170318101164051082c3d80c0030000c599082c401c952200c01c19010 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 832184388 1250 832183138 832183151
    0x9021306030510110c0604050606040c03050f0a09080408190309090b0d060509010204080f01020a170708160e031c0e0402040b070b0c07210924120f022a01 68
    0x544035030b0f503040b10703a00b0011241d8034107404000c0e214040580300c18807400c004803445450f06180003916030a09941081c011814612036045481c003d009003489a0000310f017184031a03450580074405003104e20401c0c0c0d11001c00704000307e800f603000d1004209000c401c0403903030fa400003103203001014480e4590044054030301d819100c036401e95a080c000e2048a4114901003101c5c0c507000b942c01e009120f16401a542da00c10090590101c601c103401808a010140c0ca0300f05404401980624041d50308946810015000d000015403460400007609500784072450492046054800400e241c01118100d21218406c0400c01e840343d039520850070300002d00e094030705500303251508404141901402200904440708400003500e4460043c0640d04140c1e00300c21600405006100056804202c2991f600300145241da008039014004948400d8010180b0303400381c0301e4600e0540e00329006081d250003042d1154403250b4ac061004540e001924600e4a180b0304140801d001040ca20050140f00444110301c1c0d06081 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 832185638 1250 832184388 832184393
    0x5162406080a0f080927060f03120d0b101707090f170a0b101701090b01030609110a0f090501120b0105130f0c11190b01051002011e0902130603 63
    0x29607a03003043e446035400810070180c0c03808800350301540b03040e0b40c1c200d2410190140290030b00d036441001245404055152a01c1d15070502c0780012440c444103816a0106440c9220400450002e00351008168000181c0e1481701d03000800b405100340003000090310500c41007104524940c41150400c4040c102150340c10300e0074810407040c0328184101c1010003000d5600e0004c2410920038101c24641c03060148020345002c41c402d52500d03c050090280918421581d24a200c405210700420160049100000c982c80c0d662040058002908101e40050002c3e86100c07007a161441c1c00c42c05400104000c410719400c102caa0821500140d01c0501d040003002c10301e00110b0017605480b0306458081c2c40d91812080745261031000307822008001e5448078502420298070316400b1107203122404040003614800c0342140301c10206000e9101c009001000c1100c0104040e00d0541100078101400b070002044004807550491856125000001c0700a0340b00c2d081401149000a0b0319214011844c004004607425074 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 832186888 1250 832185638 832185643
    0x9060a0e0112080f0d09122f010e0d120c0804150b0a03050304180612020a061214090105040c0815010506160f060b1306031e02010516240608 62
    0x61007106110101d003424101802480001c0713900c46110300c1007180c1d541200b40c0c084002401d4100c01920380000200200d03250034441c42a03400e5a040d1000c0c5000313000c000e400c503205000351160440b02c00f590307640c2c1e010283c10018484c1141d26601615920701102191036820181c95aa2015074204881c5c40f04210000b204462440660800e40c1c9002070311200d00e2010805501d066000a00f49201c0800d0000e0303580c0c42c03401070440181c1481c1c02441083d5031025072202c3c41d040d210009602183e500004c0c0040c1e07118034000111089908004103280a07804050340b007034002a14406401c0c0d4450b400c02003030096941d046001000c1c81001801c41c0c81d00a0f5188075171201c18054240320388000281181c4003c550b240d094161500030442d0b0b05e1140f0145030120040c41103804640c003a0030045c3c40c140c1c2c5001c01c1c1c483c50040b01e40180011a8003003024003100c40d990701004080381400703000c0c00407400248003001490031b410310440380042d004505454410102070542d0700b140c805805d00c4000d110200c0301 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 832188138 1250 832186888 832186891
    0x30706090e040b060f12030a09050603061804060605120a14060c0a031e060b0901120605060708130305070807170703020a030f0201031b02030409061401050901121806050609060a0e 79
    0x4403881c000740d1242400902c45d03011042c942c03a445204080b85801281011004041041d8076454141045541d1814000c081c00110b4401f5400403142440e0401a0310b14502198414070410740010403a45803030000d5510380500820780c402d907000e40070700c0c000c00103a18000c00040010314018a4035113071158603002240306441d4007208050300c2d8aa01c1d0ba002d1b0b45d14a590406910010b01070100c0342d1a00c500c0405900905142400902030740c0207210800c01c6403003048103554002d42480d160011949a1110f903a0001c2e0744955400d03207066001012071410300081d4003800b5040c0252811520740b01211880c418400307a00c198680013008108016503403118070f0300440364820004c2ca100a01c6000580c01072000019500302465840c40a5075a150f0100041055841d01042042540c1e240c01c4c032481c0810600710f807540032840400081c015903000304030481030b80218000100300384d41d00442c12420340002071400c036030307041c1c44005001c400e10700100385581c865800d4807101e4a00d490204002400d400 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 832189388 1250 832188138 832188143
    0x2010b04020f090a0f120f081c09020405100e07030e190f0201080f0f0402040e0309100f1b0b0c030612070303020303010302092401050a020309030613050640020915030706090e04 78
    0x1c001802003102d51010b480001c01c9c00b83c4440106c070300c1f0148081c0070b0b02488a080b840345142100180c140c0c401100f400301a20304038000840c260b03031500404d0300209030050702c50b10340d48100049112050b02002030141c14610848106480900394800500a00c201600050380c41e60039004020f512002049660b501640450300171449401045aa80c2180304001d61190444400f0891040c402c1d04000c1c2e00c0c2c4d0020b8a82e0380c0c009240107070750304810004402000201207603000008541c560004401444d085000148410401d40d01003420510784030155000300c0c05a00080010015454044000d070360003001c03048060050742c020011500803200100c80380341840b0700400c40800c010710800655501d240080c044403010300303100c00c1990034007640c24130484d2240b003030f03038009148408000d000350020029400710107061219042d43d0200300c044002c0d49080c516400f4501c00c056542c1c10305903030040302d400e03450720607070400e00c003d15060401c650064824400c540b00200410007aa8141a03030181c0c = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 832190638 1250 832189388 832189403
    0xf0d050a030c0302070f0506010311041401140117041a06010f0f0c0c15030624080408160b15211002030c0408120c010c0e0a030b0702010b04020f090a0f12 68
    0x20741c14183c009008802016103210460f00950f000c0080000305a81a02d0054440c5180049044100300990310810800700c03c000208004111009601e90400c440303140506045010032000400b039806413200b242c0030381d10014082c045248030074100d120f8a801083c280307860f0025018000024040905845201c0100824444000700340090400700c80d01401e0704103a00c1600124611004003d4501801b4590707207924200c40b00c260750341042c0350803041c0304a1920380c242d40e95520344802e8002d4010400d914441c00901503804000340c4030366100342c41351403106000302e4584222002e018080c0880700d0600c24001c1d04900c5070804400015000c01c40d032055a801581d20741c0e0f41d030003600c0c241c0900d5000f01058862552103e0740f0f4a0b010700540014010300c2c000300a142d00c41c040442e4000f002450440d08513403040b506002152020840780d07803044540c0004103140c0001c0d000305049a010035406401c015007c1000c800625043c090320700240544204149150304008043e140848418001040070 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 832191888 1250 832190638 832190651
    0xb0f0f0d09060f0227210c030106060c0b0907180f0e0a080927160c050607180602071a07290117010c0807050a030e030d0e0f0d050a03 59
    0x1060903070008800207034440014018043c0000b4070b14040c4d0060000743d4116200b400711000e450030f42d50034904416500410000119101da095207001400718521080c50380144d143c441d0140c0c8090042c40010011036807000c6019140e400d00c000e003a00c000e008070344640c104400400c0074003d44841d0790101000b0f03c1e00021601c1c15610710400a000300f203507460079800345202d58000e000100c8098100c619081c1d80c1011803c0900b070b40f0000ac5152580000c140b0354510780800c00000c0140c140f542e05091500300755501100301e4450720301c0c0c41401c64a0100061070300c05841d2500c41605c0b901c0300104011700003000c40038146954150100304410005440f24404114030003400400d54802c03800d105c40c075840c3c0000144c03000385c843c401402402103411071445603480d42c18a5505201c2d204d1103010941d91591141c13a603003c2141d06a005024000805840daa8080d002c0c04041c0001c00402851420000b0142c20035a03e56041046141c2540c0c000e40280b03004d64030f1980c0203070803286003080c5850f001078076 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 832193138 1250 832191888 832191907
    0x50c091e2103160506070809070f060e1315050102100240060e150406020a0201030e010213090203040b011401020d030c05130303020a030221040905041403030708010f0b0f0f 76
    0x218003c07201e032040d40400e4100044240b0130003042c5a40140020340c4c0f040026a243c0c0001aa01c40152107644c0c078140c284c00d8100405445110304400b80300380100b110307100964403502c80c4c0030398660261091031040e903048101714668041054101000a00c41c09605158400b030210300380c00b8808806c0d0035401b280d80000d80342e42c0d4649031311700d80320a842c8030301148094039040010281c84580740c905002c0c01c4c0b0518072074241307481c55064900f03c4010354001c10301d54030241c4c011400303003951964040282d9001e0105004802070240240c000e00302c2d280f030050f01e0707240604010200d107206134002808504040032046041e6401300b036a80015016007000301c0c0d00810107404544134440c0011005c840850880301204060f03000c14617040032030007079003160300004100001d02361201c0500360783d40d8890700801c420814514150017042d8428061035445a02000c030415203030450348100c80003000114888014440f0858a515510140034035102e501d0800d20345080114a620450040105628000c1600313103d = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 832194244 1106 832193138 832193143
    0x614120601030b030c060c030a18050a170f0d0906020d0306050a060c0611030708060901080a02090a020d0b0d0819050c0c0108040c09050c091e21 64
    0x685600c00150002d04a0b449415058010080d52541c06d82d44c41014103415901c20f405183d07110303c0490024284280d002c0804100807401c001409a07032a5140c0e00819150311003104480300c200030003824031745140d42460503803d00c41c1e10100c100c03c0398060416822144603408581240520728001c3d820366006001d0140c1042c84c41d00308001c1c5910074950550018058000021800303003402c9424031a41c821a444404509013805100c81d60501d07a9885006161540280805039825400504900c20203001048041e4000c24042e4496a00b588580600100200340310850090352070500559080150800420300c0501600790646024000b11045484202d01501410350141e00640c0c49940c081c0068920403100000402c110320140b01d03c50041c40301c0c980c0b0036200c041090800011012034122500f0300200800103000a450b00c1c007440d064611280700880103100869107445c0b = true := by decide +kernel

theorem cover : BRFrame.Cov 832014388 832194244 := by
  have h0 := BRFrame.cov_init 832014388
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832014388 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832014388 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832014388 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832014388 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832014388 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832014388 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832014388 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832014388 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832014388 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832014388 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832014388 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832014388 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832014388 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832014388 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832014388 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832014388 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832014388 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832014388 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832014388 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832014388 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832014388 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832014388 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832014388 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832014388 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832014388 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832014388 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832014388 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832014388 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832014388 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832014388 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832014388 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832014388 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832014388 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832014388 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832014388 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832014388 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832014388 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832014388 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832014388 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832014388 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832014388 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832014388 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832014388 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832014388 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832014388 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832014388 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832014388 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832014388 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832014388 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832014388 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832014388 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832014388 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832014388 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832014388 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832014388 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832014388 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832014388 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832014388 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832014388 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832014388 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832014388 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832014388 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832014388 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832014388 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832014388 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832014388 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832014388 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832014388 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832014388 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832014388 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832014388 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832014388 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832014388 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832014388 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832014388 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832014388 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832014388 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832014388 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832014388 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832014388 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832014388 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832014388 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832014388 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832014388 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832014388 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832014388 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832014388 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832014388 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832014388 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832014388 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832014388 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832014388 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832014388 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832014388 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832014388 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832014388 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832014388 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832014388 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832014388 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832014388 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832014388 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832014388 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832014388 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832014388 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832014388 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832014388 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832014388 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832014388 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832014388 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832014388 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832014388 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832014388 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832014388 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832014388 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832014388 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832014388 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832014388 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832014388 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832014388 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832014388 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832014388 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832014388 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832014388 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832014388 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832014388 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832014388 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832014388 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832014388 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832014388 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832014388 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832014388 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832014388 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832014388 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832014388 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832014388 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832014388 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832014388 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832014388 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832014388 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832014388 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832014388 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832014388 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832014388 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832014388 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 832014388 ≤ n) (h2 : n < 832194244) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
