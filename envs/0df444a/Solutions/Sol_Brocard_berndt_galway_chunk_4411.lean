-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4411
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T12:32:07.641996+00:00
-- url     : https://prove2.me/submissions/010dee4c-5b3b-4155-9ad1-ba8fe74a7983

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 793165467 ≤ n < 793345323 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 793166717 1250 793165467 793165519
    0x4021e0406170a02010e0906030d082806031221110f1810021b0d0602190f1b0c050d08070b040305070b0c030601140c01020c1207060605060a0806 64
    0xb118040c0d0052804100002003000c4030014001ea03904000a160402405581802910460340550184d0868401d0030300c50114030350011400d60750a55410040d191029207000c404042d01c030241d070f442d6410800c1140b807070b01c0950300054900740340903105210441701171900301100c0c885400f16101c2600e410301c0d43d8280111010f003035007000155100d00415803090b8441c0c2c1001e030024050a00c0c0c001c9034204500001c0d100c241c00039003032900600501c61005110382c08031200070899556409000050b010340c0c9120048506200d00c4c0c0d00ca0078a1801140e0003082c0e076585041055042d4840c80d04440031401c07410b100c4082d240c054400314208442cad0316148449101c0d014003d00929001c406000425601a000b0700c00e4900545501c05c050319801d0784040d8a01c02503441c103002c50f001c14690000500000d001e011600b04141c001424112490b0001d820a03900c54035110140c1d0f400a0b01400700b01052150070068641501c2c00d80c100501280058603051001d004540b240c440d03651103c030041128a00a1 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 793167967 1250 793166717 793166729
    0x816051c020d05070225290d0b0114040317070804030807030f02061008061308040803040b040f0603090b04060b040906140412020c030a060e070503030a022404021e0406 74
    0x540c2c1c2c5902d006040000c2009a440a0050040755079510001203c0c2c0f10041a20680d280d0402101e40b4000071480070101542c0c0c4802401411004481c1c2c0610303106c0505442080e000b00170031242c4e443d00006291345080c6c9160104940240024008261398a180102c20000c1e00314a5680c0c400340d082440060207507605c000c24030b160024114080561140c0c213001c0301c800c40d408480b040c2e100d1170b064240c249030600400107590702c2440000c94019030f098100d00e0b081e0045428a04d0329854184460943d48503400050448100240c10070003805440a40001020185001c0081200070340d04d00298400180c4050300050b1a40000304007555154040c80c000d50313010740c040014512000c01c9015803482100c0c10388a801498404518590021410b0030307528200801400c03424009941c0c01d0b004102603912044144500103000c20643c800f00028030002a464000f040f50a80d90398507000c2d0311100743c1d1f80300058441d4106003c01600da440249003540300380504910441c00303450200d40189287d40c808 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 793169217 1250 793167967 793167971
    0x2d0c0a0b070303050a090f0201030507110d020109110411220906091a181b0706050f060a060e0307030201140904060e0610170c0a3006060816051c 64
    0x91065900c030010711480c1d10030744080c00340d562200000c02c01ca4241c42400380ca9042140014001503110340c1c001035118400e41803c800440c0c90748040c40c5445440b22a410140c1e5440c40321800b88016160446566107007145c0a004000d540c0d201c2c1d1a4500075441c8441c4825100c0441e44220390a0340c1c10320001d45501a001c00415984141c4c420281c000a04050315084460f00301520a0400140c003c00e1405038450348201c039180e82ca115009007816984480540300248048800151a4040d0901404c5401030190031401d02c2c00c1003002c200c100e0791100d401c0c0030420070041d409880204011085036024208500920760344040c160140c841c1001e0030361b000746800c8000c1501d1154400c00e9000704420340703601110220381c29090fa15009440d41c2260404203520015852000020003440ca03007c03103241201e40441a404a000d40b1100035100c03000c40c403010040180c0c070803030520a88004100929010040d0704005103000c0082194a101100b0002d00040701c0c80746900b81000402c4983c258142 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 793170467 1250 793169217 793169219
    0x9071a19090902030f0a050a091205090105070f1406060111070e0402010c150e010c021b13180303022214150408030409060509060603010617060d08030a0c08092d0c0a 73
    0x802c48a174400329122501c2d9407420000c102d54182511a4049a039440380403060f0001405c001550181c001c07092050401108001c0003001648644c46071808620030b6012a0310a183ca410301400c0813030080c00710303041162582c2c005001c140005030701c10440b0b0741c604000d02c15448500040f9085a041c0501521171040d07421641d81c0040b0640c024900201104c0080003c0d0034007003022071f00d4910107a408461001d10a204031a64900498114a0a11443d00000b1410951140b0140341800007009401090b408107071805580980c1003031000f07580c7e000741008000c5080c124420140842c05003041c1c010b11612031409150141081280d006d056000201c0f61116a80c0140c000640103900130302e1f0040071b440020414500342501981d040e1a8607807210600184900044070402000500565000e03000c0c0d4900d0300800c0340f020045000e244403110100d030100030306a01821070384d0058003c2c640b55000c01d1a81042c0c00c0d02c3c046070300c09020912042842e41000c0c0e0001440c021044440da5070205000d04 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 793171717 1250 793170467 793170481
    0x1050310060507050c1f0f0816050c100e1006080c0108010b030a2a110705101412070503041b081b010c0503030108012702010507032609010509071a1909090203 70
    0x80601b4000403070f5076034003010f101c2103801122203e5040d55002c10107079415079040103a900600140c80c03520241c0c411202540c15002076841600c07401c40700f42c103041e0010700c01070f40355400c240615005440d8000041c202a28040002080d25505104158003080b010022031241101ca030400c1d400300e1980700103600e0040c06100c6550103080c081e5411004100c4502e1202000d00340030452401700c2c0c00c0108a0031084d82201020f0340c840f00745031150041680f0800140110480501c1900e0142c00c06a5440340c403883c09103882400c1c084100d02d50007101c0103400081085240c00503580c6200060b5030f088d182a1201400142c03481d89403103100a05500000c4004aa040f030150311102ea141003041d056468001130f010100c140d0444080c0c0030740029000c1000d400840c3c0183c000074489038460580e03036810344042034840c0c0d21100071303030b4008407076516501403041002007000342d071740a4050008541c50090040c05842c00911a005005091100300031900354642e008800440040071416429940d03860011 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 793172967 1250 793171717 793171759
    0x1503240e07020c090411060a1e02010902040e0f0601170712050303150907141e030901061a04050906090720070602071502100f06090608010204030c0501050310060507050c 75
    0x81e403035001840741a484078014600742e2940d9010b10341001d1204110703c046801c1c020644d001040325420301104a442c1d2090490340b40d0310381c0c4c1c00929540001809411441008261039120390040603550060040f02200c4201280301c50444140b060421807946160b42404c0c1404038035404801c00c1c851a041c1c949c04d00c240800214481d03825007005001500095040003140c007001e49603a00011000018040643c1c04900108034001c0400718004800d0b4080100c007a80c3d40c402c0b00c0540c0a07944504003046041000c417240300740f9105ca0300c58517007040c1c2801301081140780000c042d0b0703110707139111030110700c0380c9010307006440680b030b6001d44801444641c940c24582c0c1e05100d20410780188545040000c902c0701c1004144e0301c00000e81c2c0600b102d001c00518001c051301c204441c240f801580c2c0c0c140065540203621841e0002c200540c00035880304e1560802441040c3c06500090512408108102c40e080030303000d43c2c0003038440c83e0810907141c47c51802c045142440914445400c601e00b0301101d0f4004402c4 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 793174217 1250 793172967 793172971
    0x70c060f020f0d0f021c15120f02030d080114011b0c0b07050c010306060507061a0316030302010608060705090d0f0602030a06090b0316090c1b11090903041503240e 72
    0x82103040c046604c00101c003500f04d1140b1503400c0c0d034200d00d90103500441b10040d003100008204001c5031043c540d032660181d8150048402d011501d40880ca51100114141440740741901c21043c205030078258500180d01550b48030030643d0710304124504481d40c07407507200ea148a119044c0c0080021489644900640c0c03200c1e8041030050f45d10348200000c4400540c464054402034441c1d6948483c00c0c0300150b913405c809050fa812502c401c451003c0e01760789480c1c8040220000c85840c11902501d207030308d10f06001e400c40d00c95420542983d00400c04200e00307a0742090480b6911300090b200a145001507051690180360714107802011640008180312400f480c07908000f090761500f440410404844108140c1e0305c19401940c14900010403004000ca100643d200540070041410201c1140502000586042e41514007c81e6a0348049001c120941008840c0c1e0354014203000c01145000c4c2000071031418000c080010804150f2110b405001c0d07400c0e1400348601c0300d03034131040b500e50403a11000c1c140c0540701d00b = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 793175467 1250 793174217 793174237
    0x513060c0215040311091510050a03060e041208040c0b030408120115090e10051f110604030210020d1824110708070807020319031b03020303070c060f020f 68
    0x180c070b0b58001c05852000c0845003200d500c0004103000c1d080703100500c2030b0003100030070240041c00c0d8030344294010b8a6a0f000380070090015542c40399201c0c0340d241e0245c1110403035007042c101001e800c020030001845010085c20302c0900c0303041580301fa968070301e03001c054040c3c5900103480b000008414801000795072230190244417942c0000403840da8a07030400795100814155003600042c80f40e50700b0085101078251181e000404048034143c00ca0301c940c04119446c9802c0f400e0000d580303184c480e4500c002c3d840508c1d021001640009070040741483c1d00c0080d99242503988060755207038001030a50700c0d05200d030b000c1180c04400d56a245094032590034020300410341c60401c00ca486d900c12001b0b840d465194810a09d11f8842e00d103030b01d41848081d850342440e5403c4480c045400c060108040c01c0560703010080000da2030205802c402d800303520351400404402c0c80001c9040c01c802400510000640c002c8192a032180c0c0c0c5140050020b115030400502900448102c807060610025040c108a45404000c084d6560 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 793176717 1250 793175467 793175479
    0xc0d0b060103110307080612030c0d050c0c06040b1c2c060a0c02070905090705181e0412081506040b18060a0e270f160c1e02010513060c02 61
    0x4940b8540c00c3c02c51004035003550006038030384002206464404012812003c01e8021241440307418905103241400352070254020072004161440f281c0310412640d500b00b001a141d45080a1802007500c03001e00460125910035146940000b00c0403801d54007848640303850030b9428100300d00c101102d44001c12010005e4249004000c005001c200c01406491a10821603004014072450035400c18010b080c00f420003042402000f50018281e0784003541d006078640121044002c0342400c0890300039200c00c1181811005001d1000c000200b0b04098546030545818200b00e07215548d0300b07640c0400c0e40c500c07044040d030281b004030f00460384003204405030200031507514603001d0203840441080603d0098500b488005004030b0004403c0d803d10302c42d080e01180980c9070606800004181d041200e0070111040340080580c08200180c103140607420320904610740c00c1c00b5004210030349a4201100584110148650f0003154650031a40718a0442d400b007070b01240055803107910340200030606694940306a11a117 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 793177967 1250 793176717 793176731
    0x5010311130501031115040b040f1e0f030b0402040b150c0c0906102307050d030c080906040b091f0c02061b04050f01050d05160801080a0f0807050c0d0b060103 70
    0x1d000740c803486040c0c80d0442070724403500c402441040000c1c04505405aa840b90a1000240070407020011704054074034030404000450414065012030440306800c02d000000d5100f040145140030701001e810380790801d00b000e490ba5114004503019000003500507030003c0311050040441e920000190080108100c240c50904403e6410040f81003401c1e5891039100c01c0c980d0b481803e060040100700440c140d24512402010f207a42001d12040c0c02c460010b48968004c09070301e00031550325224003201a071841c180303100c2e1b40c184900302e82d030f031908010f00c0103001030404008101c41e1141000080d214408100c01d62907456031410140003c1c0c800a48400702500c101c0002c20040c17840942a114020110103490341454501800c01100f8402e00740068144801080081c6c02240b01c0e000b96841020841d1a801042c0182080200040e005074000324840c0c1001d2031420001d064103000e40265a0080c0943c0d0301ca44890034610b0030403448031866940701c1c0d43c0c1c41030b0b0710400c02c00c4000240b082d0300980b0304021203 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 793179217 1250 793177967 793177999
    0x80d0e0310060e1302010201060f030309080c060c030d0b031002071a010909080a2a0b1501020309030a0b040c05040c26041a0702010920031908032805010311 69
    0x10718114003c107001080d000d400200180a0740115000003401403001003500c3c0d6554080f020b45142603007041d000103040510a00001d2010000341141c80d00c156000b40c507141a1103091920380c05400b107940320140d103a2180340c00d580d40c100f2104c104108036400071941c59110740341280c0701c2d50589202081c40f291300000044d0f0700d42d442c407406d80e140d50000d0115290480038a02103401201c04607184a491074103000c100c40010080340c003c0a09441119000d80e2410700c80c021121002404003800d0441d80300300000c8450340c6000c650003902692086603400c0e543c9440c500050750320050342045030820300e4904131000c1103a011807162030845a05043e9040c0301680f402038451041c0480e800b40600f81903481e03036055180070761041a8030900c18030000074451159921141c101c1c0d1f490750301c0381100030800c0c5002d80d6031070107104410b900d83e001440d010089aa641d101d56140c08010031035100b0005920307402108039070080703651050304c04006c8100a150385a24004400e90540040c15014203900c0b40b241030b607 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 793180467 1250 793179217 793179221
    0xc0901030834030c03110a0210120e030a02060f0f2215061e080304080d0503062701031a0702070905060d061a03060c0a2106080d0e0310 60
    0x16030360884605498640b0552010100c40680d014601c0712503001540c100e20110140401042c003403090f55400d4061246080003000d00ea810907403040d098002c1e080c00703030041e641c1042d18101007120f0b05105078900a0641418020302d0030100c1c65110340400100c010303c040d80441c4440c07058000000401c0c103521080c10030003801702c003240e450380c10f00391100801420101100789410300902c10740d09a550701503001038102c1601c3e0598059a1303022000c1d070700042c104000482000203040c2c414000d60a20749000d010070b50300c0100325031003400c1c0000000403c44544801c001e0b0f80c20a0710124030641e81d625080c0802000c10800d1006035080341d0600c141381142c04c81d072800d29008041c00c0e401032421900f030035404030041c50081d080f00c0c0d00c2500502d02c4800501d0500428542b05402516449070100a1047c142001e00003412084244810001c0d007114917080f410389403060800c58030464440582ea618100288019000701c08180306070240704030000d41c002d41d0015041c0b011f800b5031b51070300142c0600c1c0d82 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 793181717 1250 793180467 793180469
    0x609030417030c0a0201030b0d060906150602030f092709031837050d030c060f0203060a030f081c0b030c0909030a0c051513050114041218090609060302030c0901 71
    0x41d801104c9600050742c0700e030300709001ca654000d0803000000b116a036814115264106d04660890300d82203050710f103c814840302ca0090400f070025520b4070b03000828058151140c0304840b4443d0012845005d800c034400b1001e03a005e442511040002ea00b800b000e155525040000c0c0180e110241082151241c100010010020100001f603410040689071088000010581e081911580c158100203601e0765007064506009001e030b1540e89000d02581890320540c0c120480090b86c40e030040003444110b44591101d001203a03006450000480224030303110300b40b44690812800001a1101101c5813401c1980c0300041090b41282103036003c025032424440c2c0700c0400c0b56601681c0e0400c1c04194101c500814141d14071502c03034000c1e2610903030407440607401c1328000c5d2410100881300d40e241c4030800009109003461160003d40c3c030041071034265290524107140408000805c0270003010414807041001210020344142e003020300a0544600c0c0c1a40141030a22050b44a8403410359000d100f070501c0c1890034 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 793182967 1250 793181717 793181737
    0x13020105070303180503040902040609090b0a05010c0302030d0f0501140108040302060703021828080303060f1c0b0906160908060c070201050c070b1803150a0e01060305060903041703 80
    0x40d08140142d20190300900005801a402c1245076688100140051008102400417580c0c0142c44504100005005c0b47c0705400010030586010805285a520b01501c00215003003460444455107052900300d085000d00343c2810903c5080499010303880c0095080b9505845501d6094134007450308000460381050151406409600440046502c90b482900102004480802c00c00a06980c110111b882480f0800900003030100c108102e00424003081ca14400900a0b50700550079420100d0020b4003403660440b00303600c0744050f00842e160b100c81c0642c4081c03065802003910043c07498001015a194a0304484c50b003191150403000400c41d5001e80896015101c0c0344008049903903495031001910361003c10140c1c184007081c080401401d00402089000d071001c040403685820119036600102c5800418240c8690000394821480700000c000f480da1020004c10017041d800c0201803c00d004003010740020b0031700d010340000c1001d01d00e4004000d008403111400000e0b6000d200100058490050070303080 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 793184217 1250 793182967 793182977
    0xc050414132303030f010602060106020318060a17070f030c0914060915030901150906120b0c0c2505030613140c040c030e10020315041a15070b130201 66
    0x144012071818581c441c002c0000001d0030715a0350302025440e186420845013002043c1c0050014041264140199401426140025401c0030345003079155454041000249005640200c0c2c1d1960b014401d06401c01484599500d80c80702d401d08030801854141d1021042c40401d060852521035584149094003c45000f03605c10b0b03d200300000c0030441c140d48005c1000d903104043d000100c22014000c00250300500040000044070703929049a05110000b40c0d20803050315180a8040000744144180c118049512817194125961140700901e00b9018456000c00707540300d0001c0142d4141e021651a51042121640d0312280c0d40d650020175030b0701e00044400071804000c180164000401010224119035211030503560f14990210110381228507078108200026194400c20b07280500600c5145400400c41005600d9032401108138134090006540050040c1d0340c4000e40301a03417103a2a49a40305100040030944000d6a8101d062000d4003c04d1007602d103c0314210101d032141e00280b506102e8a5410303140c1c = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 793185467 1250 793184217 793184251
    0x20d0b1e150c01020a0f080604143d060e0303040f03021c1b032009060f0409021314090102120403260408040906050406240c0b040c050414 61
    0x140202030450341c404400c0100140203a107141c600a0020b000e4242c096030341d58401000120000b00002005031125003d1ba20780400c01104071100c0c030f0200e5014812015404051a4021004244903c0350a81c5c0c440e120240020840b44441072900e24100c1d01e0990312111002074942c01c05440c3e2182d8498000c0c2c0ba0340344001080117007000b4448243c05c0340f81c0c40325042c052540703881d82ca4411030301002c03c82840221603401d00401c03640040300e20651803002e040407185020352000c14110003020300300c00c0c414214450801143d070f0b034640244000ba1390107860410700069607e070500c0a0a040c80c0d43c0d4010a0303e5200081c0c4031a8140700741d0f9010455214121f550b91034644080e40c0400d24411800c0382d52607070007014042c02c00c2d001815070090b0300c50603415544600d0540e0b0b28084403c0ea41145104034200001000080d4100d20010216440404074008881d01044290703041740300200002c0c0b0300d03405801080103001c11640102d0845506484c10b00a0b5010411000040c800495001c0321209841031 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 793186717 1250 793185467 793185469
    0x6040e0f06041113020a03050f07020309091f0f0f2603040909060603020603180d0e060f0d0608060103110306070923010905060f0c1203090604080f0f0d020d0b1e 71
    0x507483e00e04041c0500010303140c0850381c43e00360681c0d21114090380429101e4090041c0d5203000c44440d944040e076480958144400100022100c4102408503071440300104c007100c0842440d80c1d1004000c0c801000c01e400c01c5660341d1070080f4445000d101d041e40c4890580d0700616401017144031002e051610402540c07415080040500092003600c40540b48940d9038000400181c69080082d4003814060130340e03d2042c403001704564603140d0780843d443d0800c0b0480e50704505c15140ea81c01d8400b0804016041511413405650a00c000d1010307030710141036442428000410302085002c02e03c1000d0084c0c0c1a030300c0c0d5650f6130300c0644841c9071610030300d19809207581c04821460351005400b9070240c014900850526664800692140c01815903c07130340d2480000e0a0540c10401c1044001c45040400d40600750305d495441c180c0c13500380007030024012050025480a508007401c0455070030080c0040350741d840d031102e41307414802504a48074108200349800c840080e9440e15110031440603102c00c11141403005203030 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 793187967 1250 793186717 793186733
    0x6120c03040302070f08011509020c030703050715090f0b0109060b04050d020a090c05040815091f090203070306050108010e0109120c050705041b120c02060f07050702100806040e0f0604 81
    0x8000b0341c1107020b100400308494226000c5900104840400440d035442000561301c0403060f0390f4051340806104000034011200c021055510864050503c69120001ea0600b01241b0710002c0c103119480d0f01d4039180760100140e103001a0441d034001e01d00f0040603070700c07210114110f4107140102c041510052108205c50314010840007091031010b0850841e203540d6990f00c2050303030040d040703040c0400c0002c00c0c01e001020f42004a08003a00213a4203005607410041c146036255105440880711100c1c008e032500300400d4040d0403950704540c2c080c00b00d41c031082e0389051a0b030040c4800c1c01526829404c1c80e00d5010400c1c0c0c14046c120000c0d03009082040881403c040503a60400c1156048500c0e02486030005a150380b20701c100c50030381800303021540384040c035584020806c0800004c3c413a6042d152180038520f1b80d90000c0c0c80e540c0030b040d1a05400140c0c13910041621140a01e8030300075440158900e000810070341c4103840d81d0050a099406000c1408205010f5894528440d009401c1c4d500140c005030120340c1036 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 793189217 1250 793187967 793187971
    0x509040b1e010f050f0f0a0b160c0e100909020102100221100504061d0c0702120f0a0606050f03030d05180d030606020c06030903090f03030904240506120c03 69
    0xa4401c4105008071801c0711900d01c40c007684001c449500071081005141002d0220351103040f8211503092a110156000036040a254094105c2d121030114480b8448003040c0c0b00c0e404c146410407020070b82959142041c0a01d10022103a2410b6108560300000e540c801c82d00940428507070517000b0f440d030f005420100d03d00a4024207c40307030700d4120702d00005500503c01d00c1840e0054414040c03407444a400e10043c00196032803588252a250503411810501e1540c0c01c40803a0000302c0e0001d03d5030f030b400d040c0c0000f030720414800000300000d0280a2480c6450180001d0b110a41e520401040c04080e955804018102d042d050f4419019041000b100e40071044544c8036a07444108540105056030903945003528100d8070380d44180107c1da032441c06009454040000e219000011103e40e850361030214615900c9010b0b1460080c0504040c210300340542e45c5c01c2c0b081e60305000001e00100410851a0302c0090f2418540240d0b040c80600b01c0700202d00c0d42030602c01c54450b25600e054502d0700f500c40c0c03040c03119035500c0 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 793190467 1250 793189217 793189231
    0x41a01030525080105030f0f0304091a0414061905030c06030a09050712110d080a050d240e0a0506010e01180308040609060f020c011e120509030a14040509040b 70
    0x1210641e07180b03060124420702d42c034825030b0f81d02c61040d81040d061600d0060035417108111a8010310707941c10707440d000000b118180d590f4071402184c4219410800d240e0851001a0a540181005802041c4509002c1102c0c854502156404035902148003800700d80c21440c01850780540200d5800c441c01c0c02d0100085401904440300015803003842e4441c1d1742072030001e0300a44800e091001c0e41c10140b0006085d410b120090480301c1240005a694a1204612071400d282090103030100302c2c1c040c015015800f00082c800300315901c48400b24120b00d400414821409042c2e000301d00200401c05102c414403d45100300750603110441044941001234402c0d40f8440b1181404801080001c00015400c0016000900301e90302c83c0741d40f0074200580600000c0840300c2000840d0b02038241d145090707911102078038100c448080e9180624803501c1d0b044401c106504c1504100505110901a9400d0300000030007400b08282e80e5089092003040c180011072045106881c2e0003048500170402040b0440166030301320300 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 793191717 1250 793190467 793190491
    0xd0f020d2c0a030204020a05070203071d0103141c0908070e0c090d022806141c020f131d010e042001050c0f0a020108060303042105030c1c030b041a010305 68
    0x2541c0d600160a07030b03001f0003204000460118440b001c5080c03c000e0f21010b0003d214240c0d000b164408581064580144070240902d4981c1107006840307030f424030141d051068003205130b151301c81c120140585014070a1003103100380d01c9846000150840e010200c540591006100326190480d000304000b040e488041050745d0146810260848544061081000c41241d1300740c0901c0355464030901800051119050f44d00c94042045110b03590380c0c00708403448440c0c0303407090016200c03500503034208094000d15100d0b48126441d0340340420340342c1d00c00c2507480c10211001e00307140d446e80e01e540300805031300c030140da00400001044c000c0c0e0300b02c9100c1e1011000340c10010300d0818100203200e07902d1480c0410390910610990400700c00e071801d40d40e01046060b03100c04103400440c80c00303141030309250035465482075100140c92140500000c02209200321186c0d220000116001405400401c00c000540150000003291420b00200c885080c80d0240502c6000c002c2180c10b680180c00c0015005840700510206100d0 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 793192967 1250 793191717 793191719
    0x1002070503030333180a11070b0412031506110a081804050601020303130311030d140a0c020705100e040e1e24040f0f050d0f020d2c0a 59
    0x24074204041e43c8114100d042072500340386102d41d4001e040480080c1400d800c0401c562003480340e00c55009502c8804800b0a2561007503031440c0800009000c07542c4400300b11040020414107009040f00341d41d020300d001d1404000108802e180a400702e880301e149071411140510810048a8003881d19045000d410b801910b2081d80151b5501e000da512100142c001c01c2c51a81c00c820041c10300740f1807107510074000e00003180b4500b080285030b043e200782400010100003a4100d540141803041c425241d201e20b45040c03e2020048070504030040040403524200e00701e01d032810713000c1d1040c030000f000c03001c0300c1c0c0292080310400030150045480d8011003d1607608241c5a0403003c24041040001040c602d8041140040310542d001141d0f0514940310030b0501e803140025205a00d0700e040c0807069030407030b60041a90002c02ca0354078128031034180c07201000d080c45c00354003100719500f13412a26200950115501741c0350640104e041c15038001c0825509820120300c5a0024076400907070800c19a030100d40207118603059 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 793194217 1250 793192967 793192969
    0xe1314010b04020706240f05101101050c0901110607080103060203060f120d0e15030705030910061401090608070e012102070f021c050a0308131a06031011040510020705 74
    0x82d1380710710380403152140c0d2032018200d9254900d51558002990340c805900345464229017032110800c030300525104e62046a10341242c0c034040d1404545810005009002c646450818617032181c0000d20050f0201e40385081e0551103034408101ca511600007600d442045901355125800250402012903821035044a551300c3d803603446180319a04c0030140001081c0c9142c0b01480144008540182640a68242c0c0c82c0d00c01400362003c140c1ea0700210038948203480c0d6681180382c80c94082850f075030704021071070443d0214580c04180303455414450283c032000d41081d55103a04403400641110340303800040c0780d4142006290701c1901c01d050b61000c03005003448004c00c00300b8014100ea005150483d0341043c0c10b002e140440c200500d9150048040c44070003101015140c440d10340b0b40c040c0150080820403840001018648100b40140d04560003c01003045040900101000c4e01002d44100b880707413040044a1480b03060324015480748205190181703091038500703c00c5c001d0b4100101035450a60190380f4000c525 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 793195467 1250 793194217 793194221
    0x303150103240303030c110709050604090c0f051516030e012c0909011e0203041a04030507031d0a060c02030325060c0c03090e040f0213150e1314010b04 67
    0x1805451420b08060145180360280c100e801900390007080c07081c144240301804101140300822186d04150104865039901c4c00603005042100d402048000c1c50200030034900ca2038036080382039610507039214102c1d8075007101003038070f5020348088070b07808580c01844040082e20070310b1070a00c084018101144410128900702c0d8100550031864554038900480303003081c41ca0980c0840313030000d400b0f00c020051501c401c0d00c460020f0340c80c0726094030007940001c041001c102d81c038002460003a4207003120846a040c03918005125030302040d0250001540c900d03e100c808902d0460900320804024070001c04c03146010015500e0b000007244c00e03a4140401e00c00c0450b003800c100c9400396900900b100c039040ba05802d140c200c1c00c80e900d5000450420000a1244001a4000701d9080541d412000d03201104e03a11450070140319120404000d400c4040e101501440845e40e801c00b1700065540c0148421719a00c403c243c024548080720082c060340710000c15280440c00002c4180500c6141c000040b601003d1500801c0c2 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 793196717 1250 793195467 793195511
    0x1180209030a080318070b0c03190e0616021831050d090303020f032a0f0a0302240f06010f05071406070f03020306151b010f060305120c0303150103 65
    0x4501811624480d51100902900d0094070f81d881c441420400600e140036541e014060b58039840d005407160303080124bc0039034442e007004400180120758881100c403e440c9034502428049000d50300050303405004000b0007280610600c188980410303500c6140a102010048117040344030110b80700705460010400c00d020907226800c040e10341070301031440c40c03400a191101d860314080e4103410038010010404c21721444c0714422081e81d500072004040540c3c3d0142016a40a411402032280c001c402040680204000c40c07040e10200785108c159910501e00c2080c22021103410b242407448c4400a00c4540c06000002c600c840d45250480c1803081983d9415130403a050180f61032a0742c8810704010002d036200d44651081003951400f58250308108000c1929801240c1c00d078a000000810710072910303181222a00d8400c00380034000c2c0245140d0080070300c01031240e0300054905000724044900c0c04c081180407260807100f0980210301e16500c0707419000b60084190140d504140d280c00410200c01610780d0445 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 793197967 1250 793196717 793196731
    0x1d010e0406080f1c05040312050c0307060e160b0301030b0c1b030414040e0a0321060b0301261f09200111010e030a0311090a0f0f0e01180209030a0803 66
    0x3d81c000302220320301c2c180304454800c1e10002600490b0074034990003001e40f01165400080f444801c0810b20041d80c241c061380c00c6d404038600c0042070350741c2841915000011049800340507500f40019446d1048203000250150344030b0003a0400040000985a46000d0752111002c5041420034002c01c4000640c84a2500840820b60000c2028016000c0b031072511402c20800b00c408111111748143e102d611000c1414004d02409805108190416604550350380329400b00242000032903103400d840445600300307010302d510560945154003500005082c034030b03614401744001003541c41c62005d02e10016140c0b1102c25480b4a8507210f81038009061301c3e1400145610300701c81c44001c007a003000010040440103961000c16810a20002a8140027004a44294590345000708026818001d0780e000c510520080700c1d0000404400015615803905a40041d240b56070811140681d0340d6009180c0c082080c0900801c020f002510b8000351507171503004212103030b00a01503800c15050741d10744108681007114a0 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 793199217 1250 793197967 793197973
    0x140a0204020c1c0c0c0303030518060a1d012c0c0904030c030314010b0f07030e100206010608180304060c1104060f150305090d11072c060d031d010e040608 68
    0x1048051004090441203d0610703200030081c1c500d454102040085102c003a041c5036841c000b045103101d407202c1c0718403645d5241d811a0041d0400d462036000911922158005003d49490199244034040c001e11001071400d25490740901080300c0400200070046c401c89010344034550103001c2035199510030700d22540c041d445801e4405441d04015041c1c40745481c00c6800c014001c0010b010701c020f0384c410348101280410800351100032914083e902c0c1108984d0030342d4462410052807200e9030380010300c0ba068685c15624120342d031310380d0105a00c031041418054850f80d0130900c000d114443c030030071192809500a404102d103041000000c141116003a80040c01007280c48072041c0900b001900ca25900300c2000e180411580c44d01a07101074940d03d070b0b06681400c1100d41a100300040b181000030801500300008081404c80742804070040b01590b00d1503081c2e82540f40307000a030300d0786048191408401d40540b5800e0040800500394120311a0408469060141c80e620452050f04ca5108540291843c0401 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 793200467 1250 793199217 793199233
    0x21c140601091a0a060305060d02030a11041b09141f0f09060905010e09060d1709040b090606033108070614061804020d0b090a11030f0307140a0204020c 67
    0x110300c20f4441e5040603140600300c0c101548003a84401ca07400044507064900024a40c03500000100c20401850000c0e5141c0305002a480c140321040f034000a14103403ca808100c20f2075800f10901d6805000641d210109440c0380d0304014030419055098907803440104416500e411202d80301443c0201c0340d680740000344081c400750b070000b60802c00d1a4040c100302d09020703840c189000b0009010b24a110505405040d05c03c2c04240240c580c94003200d8516403100d400c880d42559040b010a041e04070480c003c0c451401d201c80d01d181401d003044c019003c0d82c4050301103450b5985100354140c0d006001000400502e20070410004801e00e0084640301c0d0510494006035107446909100c0305076002850348401c004404414040103a0302d12805002c541c4401c14010401e17a26800040d18000704504045d101c4028034003001140800490700814540c840d200406144191038145590f1386034030002c0f4045588100130307441c0860841182d0036220240741c012112200d040fa800709060381c1284908000035070142e49 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 793201717 1250 793200467 793200479
    0x20c0406080c09061f12090b0106050a03050c282a031101060e0103030c0c03151407090b1c061a1c0b100305060105070f0809030f010e0604021c140601 66
    0x2444e4012104448031030b030811588600981413410704603004280003840324041040c11140d0012900b864100750820744e1581c0d22800603080350f0150514900107440d000000b100d12000f4010381c1c540c1c0c5100294007070031111401801c044800381d055404144900760080800300a49070301180c01c052020150080780c22041d241c080d0507400211040403559060403c00e100d4006030f1000d40d4112601880e0801c00c0d40b01d142840f006090712a00060b080803101400c060000030355400c841540403c400329075003160b9815108444030303000350283c0b5802000820a00080c1d13020072500c248200c040c44000034059a035094083d240140c40a82e08643c00e9001c40d200555000100b420340c07002034407182c10f2101180001c00070b035400302504450424036036980e01141240e4494000c2c1c45060f80d1100010105054a084c60384181d003100101c40e00c80c0c82991003140c03441d00180620350349040c0780001418580c585608000014600c1c424003258210a1283c40300070407945650a054528003201030580c42d410310b9 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 793202967 1250 793201717 793201729
    0x905120901170f0c0f0c0105010e1012020f040e010e03072d0b010909030908030a110105010602031c110c060f1005121b0a05150c0106060801050a0e07020c0406080c 72
    0x2540380d00d0680d407040d0030003500940c00c182650b40802e0f44d4200603034801220081c241140a490400240e66203403c1c008100b40980603490390240002c041c8441d42e041d500c003903541207040300d18402500031240700d00b500c24a05003074100b4032075480900300102341401c0300c507038451844d0040341c03058034018880d00201551000b900300b6030400e5212100002402c5100d5150481c00c00c2d4103100b00b45845035540e5044041c50300c900d00b01c201600418094981d91201010010b00f0b9541c407001001603940307000c00000c0da0390700000498200e0100c0c0c030100b4008541e2003080c00002c050003a583c0b0781010f404c203c28000080c0900a052042e180d82210707502da0300f07002142481509241c0c1250340210340c110149801540c0008445210210039022818950300040100344100f00ca03038403003a00809508801c10f01c1d01c01100240c40d50040c50b10080207426a10300d41110901d000384541781d00138521810620403c0c00c0d04035605d85c041c3c07043c0100c0320503487d141c0110b003c4a80691100c0182c8c0c00010f02c10599103410 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 793204217 1250 793202967 793202987
    0x207030c0b060d0506010b0a0306150c0b15030c0411070602070b1b03010e061c1202030703120203010b07080703050f03010b03151905040e070801090c15020a051b040905120901 77
    0x5071909800c820030f96441541c0d640d07040c000c410140c20081071422200d44a50003080140c00c08000000c80308890500140c144000324008580e41d4801c4000100c00101c4038004c80586a001070050450104c5078083c07000421003034511099840c1c04002c51008204513000900a07903100d212000b1481ca04804070701d680c01031300462918800d00410040020808010308190007801c04c850f00e403440050004803103504000d1400040c51420450380f40100e46801102500806010380c95030304415a510049904038030003401215000740b010712100000c01c1c0d000c8040c00c0414840d0821524025135901e00b071000b50002d1380141515240001048502c1003001030011200005480c0c2c0c401444168942d66400401c44c06a80e00650707032680c42d45030760441003099200a20810008000051503403d1a801e0203907035010328500212003d000ea6a05440040e113006481d81090103410180e44020b8560010130150601a60054682c804000406d07414010384206440260302141d40c0c1e008940003604500b04 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 793205467 1250 793204217 793204219
    0x1c120507030210060308071716030e0a050d020d03030903050f180a0914010e151905010801060f080f100302041401140d050303043e03120c0c0108090f010207030c0b06 73
    0xe0404c01c2000075082c2094990300c40c0d1100e8903140d4418a015180b0850050711448407500d203129003203805141c3c0240010384111011f4074002c14440c1c5820500c58913001810b0000d4000a10080c9100445e100e940b05030442407091030914904011007521104541040050040c0702028900c0d5141510706001490005c042d02c0700c05202400706034003200001c480502c12180c100e00803400141700c03c10080405080079200900880c0180901110000e4030710050003064042200a0004210107001d20020380c201c407041d94590400d59510400c0b400382d880080d100192100442c0302c080300590340d50140031901d5180d802074002a61604e207100b5050118071425500592a05140c140803403070200c00c5070350080e0000e50044039a8500c00640035602a840200c207940f50790b4100110355004090300311043d40301c0171001c44442c400a80383c007403e40d101d80c200346d400a0f444800c0e029481d50059142960140d0020141d84204164220301030aa80c030040b802c0700042c414081d0481001200b4501d260007440c = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 793206717 1250 793205467 793205471
    0x90b0307090f031b0906060c0f1113050402100c021003020a0e131e0c0f1803140a0b09031207030e0c150c06100b0a050d0209100801031208070206061c120507030210 72
    0x302d02003026200d51008c18010300031011080b661810310400501082c549100035080c281d0002d818140308000303040681d0203d10a1680c480114000c0f881420b90203903a540040042c15080d00444050340254003441c092014080e81d100c8002c10307540d41c10401c0c4d00656a803400465042854403016903968100c00c60749140c180350440000c20650b109880420f844884d0501c48075603945134580006240131540024403003440c5c1209887c948402050100000d8451010440300d40c0b0791811694aa010b000c051540c2440c104000400c01d0b0b102e5007000c0350000000e000e49040c0c01c51100858000078540d0401220305c20001148406c1036020401d80764041035807c169400c2c3c500b07082d10a00c461040d07007082e00c2004030206062030000180d034120340b00b6110041c01d42206406c1080040d1281000744010b5800b010380c0b05200d403ea9000d152403138480d1405e43c0c040c1ca190394640c400c110040880c091003c035051079000e4001c001840200310303007040c60903585405441d12031515009140c1883c10b491f4113074681c = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 793207967 1250 793206717 793206719
    0x9030206100303050d3612090b090402031816080d0903050a170c161505070c03380612070303141804050a0504060b0a0501090b0307090f031b0906 64
    0x82c1d2080a445c04001c183c07001140c0b48400c4442130385034544081020803961601c16948030440207840650324403502c1090429840007003503030300341c0303520850384589050041c2c200046271841ca00b46e8000d5174824090000d40d81e440c82504d458900d44141030040e41f40a20159000b030240070300812254418403800e250000a00381150390f429110181c8540060440b081c40f8203502c10300c580715040e2550150041d0440350410b1020321030001d03016407482211071a59044c803121800d81d2185045403c821f8202542e4000645140d4490807007203206142d00600d0f10704135640200d134600340290155150300000c8607583c0390420b00b0401c5901c80362446c0c8980e842e03111100400000381c006c1e040c2d030300d20040d8405154580c00071140b0751820110003403600360f10502d4002009540203003035000e40d003c5c0340162001c108615400b0248428a056070107168045502020104114030101c401141d00c089546010b404a59070f039107401252078440e8104440410754803c0c0d07e405000560040310080030440c41c00c0c8901 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 793209217 1250 793207967 793207973
    0x22060f050f01020a080c0a051545010617010608010e06040b0a05070c0204061d06030120071b291603050c07030c180f1505060c0a080d090302061003 65
    0xd120740c400010140840420f000c07000040c240301c07440b400354110713007558120b0540309100d0030070271400c40341c1d2401004c1c4184151801191507070070340c2482d2542440100d01e0200c02c004480d22268116511140f0340d218807000c9400c103100c10400d04448400c0300007007285401c0c000c1450035106442c80401e4998001805c01c404143c49104840d04254420340005032910307207a030300301c40d4095401c2d0f01a4001e4101a070000d960b01c071414030003100900f80c41f00e003003094603414101801c0c2c0d030180400d00c1c0340074002c03800c580d10110b11000802d02144148110350020b0104d075100025103450741d105242c04003402e101800c100c116000c0401c200145500c02e580780034101100900160220341016003009400f0a0640c0c0d500c00412409014540200311070f042680d40b810a07a651a424000741200b8074109030401ca00d0301c1e96406800280100b014460b00c05038100800d00099402101d4901d8403403155100a030042400305004085050700301e00042060030300ca05001e0703d0440c01411035140344a8400c010004 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 793210467 1250 793209217 793209223
    0x70c080c01080c030c0d11030412020a0228031b0e0a090519050f1c020706020615100c0f0503040f080318041a0411040501080702030307050a0e22060f050f0102 70
    0x40080b104100b04c0e241d40b07034079440c810726000380401000250710b0400108a40b12105024504c80c1e4443c110b0304008400e202c000b00c1e01d4003541d20000350030001114400c00310407418110002400c3c014038103000720719a00c0e26202604041c43c20688284070f5450014816821040011075100c4c6c111103083c4520000ca0760351582c0c42450408052450074100401c01c200681805400c07241074168040b981600d0902c3c9101110340c101032a114054495050000380403800440d003184203410152002020302600c00a03c90303001c800505040411612180f00c00014400c400c10030300c0319010304021038031642803120b0b0101d65402908202c8048d070040c00721502000580c0b0204c1050b1f08103403404140c00b030010b12452078940141c541d0700d6119007821401c05504410388054811136100740c2c1c3c0c0603400e488a80082e030316440255150700000740c0400154410900812240c00303001000f03841c905c42021030809861566420681c030042140d01c1c2c00003009140c000c40c3c0700d40c0260400315100c2903800c10320f50020303503 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 793211717 1250 793210467 793210471
    0x200319060c171909020f090411040b19090e0328080a090803060d140307060f0b091003030c0512031f1a0724050112060609090f0221030a0302070c080c0108 68
    0x3c1158032132402d542151500b8010449140f0090800b00300f41c18145090190b0346041c01c44240201d1070401042c81038030b00074110080c8016400740c0c10511504041c00c8801405541e1011000c2d84030400a280e1540c00c41013108001c0581c46150142013891540010b0680314041d0258201030709004030381d0302181c14001102d0b041842121000e004890504d07241400c10300401c26448a400041b035440144145a0050100d1031045007007001104c02b60070070440c0e4100d0030b0f990086c051080b980c2c10f20009006071682c01d107180c000c404807110b0003189108404680e0007106c40020354401c00310b4082011201c1901c11000e80540701504c00007000c9001c416240c1c0c002d245001c0c10fa6120f00000801c00c1001c100c3d0b02007601c105070010b00156840b00c1b220b48404407604821145503203002c0000402908034429071071440c0c0d014420f15400410b13902003040c04138041072003401c01407030a4044210280100002c1006041c9070314050b860f40c80c6401c10100c0072200d584110745e541c020b006450150303079000c1c18940d = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 793212967 1250 793211717 793211761
    0x50d2d0b210c13200d09210e030d0221040b0f130806040f11040b0a15020f0111070303020c120f07060e0307200319060c17 54
    0xa090001080001e00c2020038032049810703503107020301c180720740400418191881242a1103600400040c0d600349400c90b51580d243c100d211010701e01d0002a6240740b070041488071298440816090f0450700e0311418405490029044405030020301550a60821400d540c03110084011f0a54a0300200010f0b4a6641c4605055560700018548400c080e00200c15a00902008000c59440c0c0105a02000069201e40507000600c4201840080d1000e0300080f100e104960249120300d000b4071030b5440407882c900b200c0c1c066034001c2c0c8034803031105a0307100c01009400828040f40c8501c2103140104e00681080d080d40720244180c1d041c401201c0e001c284d110115800517615160050792034903200c5005050100c60310000c00040c80001d181010404000081c0205a00071142080501002035a850ba00d106404000f444001c1c41802800040700382c45422a2150010703065800e03815402100b00c00784d451510741114426a40c0faa08a041c6500c600100c460014003802c007030031410401800711050300c080c9084 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 793214217 1250 793212967 793212971
    0x90a0210170a020a03151d1003020306160315031e06090503040e15010801060c14010f0e03190804080d05070302250312020327070e0403050d2d 63
    0x1000d49244a0840a641040114040794003420041c2c0e103100079500c14a54000003c1c01c2c404031188030100c84624008803500c0b4200044080411005c160392120000e144080f0030703a01c99800409a141408040e20a02c42c1480100302031081e901c1c0a000c4a0b102c6850810781c0e1018102800020b001001c81340d401c21303928070400f1801400c0c0c60700c0f00182c80c0403c6e006145020101d03001415080c111059405102c01340c01d51304140c0d01b410011201d00d0024170440c400640001c0e44000410607513505d440030200c9840020410380724080f2208107a80030203003240728036400007454102c4000340d0501c80e0b044591901c1c003000380d0300f0305440d03002041c05000811403201c0d41d40d80109416900980c12200400c0c0040c2c4d000c0007414003140e0006428050417015800b164600600c81c1400455200303c0b842520ba003840d165001c1c107410000f0f410300c2d800066694941c824110b0108034880081d1610740714030711031350310310b44d03600802d28583d016250084c1c2d2814040c03914a070100350f036070500001e60440030b40e41300e40 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 793215467 1250 793214217 793214239
    0x609092603220f0507080706231b160f0906080a0b010e1e040b061002010e120a050408030403062c0303241009080124270516030f0203090a02 62
    0x320386000d0b10400003130080c41030340c000250200001c15610300b141ca0686800002c07051542ca0550505442c0c50126007401c402c001c00b00d031240182c400c0c01024000302d001c5a4076003000c42d24800c00c202441e08003c440d0110741104212255040c040c2e1800342001e50050075000c0c45558a00185010600441c2d0402c5c0c0c0700c0001881003250f07038480b14100074440c2c02c03070390740c1d0b050505103506020029a102c50003401d1b22003000d0741a80c014016a112101e800c00200840078a1741b40310b00b0581c1000382207408111042100155a0724100040c00185004010000b04069025407038500f8003010210105602004045000600404402d49501000301c28600e0310316001c1c417416070070b1280744144c9291f200490000c0c0380209a4018400029144903900802070424085102c2171000340540c074056015440460901c45c1d540403545400f0a02c0c140890281100d40301305540041d248115684800c5028600d005008554540201c000703010840d402149141014200240c42d200f0301c1f20060b01482c44090 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 793216717 1250 793215467 793215473
    0x6030b1b070602030703060603050a0c0f0806040221060a12080403230604060e06090c0a0b0a0203040506030106030c0806090105010e0d17070c03020a050a050a0303030e01060909260322 81
    0x2181c0240b58042001c640d02d142c4900003900800d401e0280000103482c103400500c002203244915150546c0c1d940b161040540003030411030b2910401400181c0080e000d010079146820042c01c0307031401001c5074403410181d207002024002504940d80c005130181402c4850440813a159004039000d41c2d03003004400d0b00d001c0164060030032600181025019034402da2041006002199009645040c0c569050b0340050315014050baa407407003010b015541c04014502d08025442d04180145095902c40c01943e003000d580780001125904260710102c04603454002c0a0621540b04004551115040320105010f5042000090400130300829540c01145000c40c1c031801e1011020b000c0a14a800300d500740d035104103500c2c25840a207010b100490241049130004a00c918000400740192100a448002d2161964508070064208180c0c3c0d40b109541e02c0301e01184a00442c080e03001a98080c07041c404120581c220f081e1003000041801054145061062200d04100b003c40c0d110040080c44286141d503010782 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 793217967 1250 793216717 793216771
    0x9060c02030c0d0602090a050a0605040506090d0f14100626010f02030c1312050d1209020316060f020a1101030e120d05091902061608190519020106030b 67
    0x3044150f40541c0350000542005070b6900100307841e82e01a1200c40c12980d656060020700c1c00e07140540c60104000340300500050a0401c003500600700e00500f50705901c40c00e612114030100b02ca0100303840003045060301601001c1d040107521141c050303c02e800c11010b4904500c10b03980861807458680c01480e904088011804c09411120030341e42160f40441d031300c0c1001100b20010358062940708020301c241150000751400d80b404030380d851036001805404000f01d5090304580b0001c0c52080c0c5401195100300120160310100020380306203845c180301d00300a80c01c8c200043c01107251486010219445002a81c0010f0031090007190019401e090114442400c2c0e10308a0900f650002158002c0d400403031000b560300d04940055005481e0102510a0009103080076503402090304800b0f504540200008040000c4075484075040b1800317480b00c607041c200c50300c00ea00c01d41c40310481210300007000407452680d0181010351051844860b8002048040e20315611540300c1e01d00203046600c45070000340360182c0b2010407 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 793219217 1250 793217967 793217983
    0x230111010f0b030c01020303010e0c07080418050a05060f0a0303032013060e03070f27050a05040c0618150e061b16030506060d02040216050c150a09060c0203 69
    0x1040081c44407000300201803009115040929100b8070800390341003142c1d4004811a03050b038800c003180b0020365440702940c1203640e01c030040485041a01304000207652241620400004030b110b08041000d061001020050740c101405043c0b04040f00b81410304290340745400c0c002226418140807401c00c45081d00a00180d4216417051800c08001801a0304085076440d0002611056100e503074605018030145a510b9180340660b03898a0044001803001c1c0303a0221a120003881c202c0703141001c600040f40f4000968000391034031102c590303d400900081000280b0039401030b21480c40c002010208110002d11b000f8168800c501a40f02e0800f0b44030070661180001e03034420341014001586c0d0f000301e0a01501400341403405000a4000e0386c0350b0340305070145071003008112500840180001d4a40c901001120b100303854080303911641c00c00140010b4142131492961241c00360700944500011401808154a120890301441c5402006400c203000d400664441c140c407500e10b441501141c1a1001c46e1500e218 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 793220467 1250 793219217 793219247
    0xf040608011d1005010807290a110609120711031612061107021807020106030215070606091820040f0507022e020a17100815012301 58
    0xd02c0e5400a01c42040c1111844414070300b811280078000b604407070800c5601c20f01070f030f0140e41c000300c2c410002c100c404403100b003c1c0c2000c40d4000308081c06441c1080403961140c6031803004101943c01c01d4082400500840d58089c800f04003914000c2c5908010302a07501c20544010034221002c0c10301512502c003002084004125143c00d0a41113881e50a00940e51441c8541200d07801e0904181c038192441c5c40c01503943d00d03580a4040c20a0b444148203c02407540003c00100c119942c6180010160751040b1100d500c041050300c40550303c64950500b20709803580341d0002c0ca44242003010b118070311b0340c900e4503031305a980c0c2040d842507888000b050006944015044919809070801c031001103004580e61001d4050304154003190803a00c149510600c1d507951881840d210042e030f4100ca591585140d8000f00703003041692600c0440a240070002c071480d980c00340d40c0c04043c10124041400100d00030440700c4103030140c4003550351896247c81904083c81c540a030021600440c06070074861164003824000c001102 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 793221717 1250 793220467 793220471
    0x1b040509010b0c06070f0c0209180d0509040b0a14040b150703090501030b030c010906050f160b04020a0b2b020714011b1d0f010c0c09050403090b180f04060801 70
    0x699059070b1465070f04005884051405000013180c2c44500445c001c1c0d01094003500c4218189040f42c00f000400480103000c204203810300c1c1c0440ea8840c03c00d02008241c08007175126151509034410a000494004a00050040059000504c00700c40c44800300c0002c8042220040307100482c80010138007180c4011028001c61001203061420103801401d10400c1d11000c3c0e0302041412902e00c01c0503034544041c0c0c5c0031808502c40c5001403010a01c183c0041400b502d40381d00e01c0b4039001e55406001032148400006079101440001804114540300f01c1210040403240859400d00c0e6001010000348103040b450164080c901b082407a042e51030a8055451043d00040d985c2000c820008c1d02d5800380c10740c05000c3c00c40711151030b1600032803401100ca80ba407810f1400e52580742e2a440d68240184881c21521304c0e0305009c0142c208c03100052103c055100a000c04c01d00119250502c0c0c500a01200c480303402085e55100e042c44211000d544400d08056548422150041c024201401190041c0459002408294 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 793222967 1250 793221717 793221719
    0x290d1b06051e0f031f051203070c08121b1009060c0f03020a090509060f06130905010b0f091c06020f04081e1c11010627050106081b04050901 62
    0xd4000c4040c02d180800d0390041d40c4102101a071441492188030480782005009002140f11540d0001181e1080314821603501121078a60000510409102d440701103154400600a0200416117801400034020400100086501255280c01601400505103408031501e002030003c40e60801a646605841200801c01a0100c0c20407030050442524060301044c0301700d00c4c00c541e1a00c40d1084959580156032107003007042c185010446c40c01c20140c02940c1c010b07410580c4016a03601c180003401c4001c2c41c20305d0a05c3c8180f07003061200a80e18141d00541031000140089000c900c2820100c80c002581180c21203100340b000c911103480b01400070405845944045918012480103100500545100c001180c2d892000a6100f201650041c50101c0c1183c000d031f01045054040000182d038003800500300310030b403010000141ca003140e240313034040c034011120300100c1200140d024074102c10041c0103001c203028542c140134000d00a140301400c10394a4101c10400081200491410b9502501000b41800d44c15 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 793224217 1250 793222967 793222979
    0x3070b0d0b0a09140f220201031e15140d12120615030b04020c100b0121051b12010501050d060305031801110706021f06090e10290d1b 59
    0x1e0071380010a400001070301c400700d001940c8900015105488651038100300040b01e0582502e030b21140c0c0c03000c03410300d078441d000820064400c0f80c034440c0d005202d10b000244800c0454919082078225402004801a10520611292907810b011881240c0001521908030703840c010843d046000c58600a44507840d000f030200d0640786050007203840c180389642c2480402944402c0000320700c117032812400d5542c00072080c84400300c8030f504040c2009805051a0b100441004807422002107119010020296680100100e805080850303000700700421490f40e00f083c0c851031580c031f2a0700040c00342c01d0510001250041e109011600014041c6034880d058030b40701c1c0d0170140012002e580034002e09011036500110a41844070000d500d10032141543e0050004d8503401440c40000b80c4812501040b0b19259000410000f103a40a048250f811110007000c0c0840d034900300070100c0c0d80c0d403480c01e0440101c02d014200c0e00194000c0615215804503070b00c20700f5121500d800c80c910054800c0c09416030350012000203070 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 793225467 1250 793224217 793224221
    0xc0f0b0a06031b050a050f060f030103060605010f03020c0c09090c1008090d0314040f1104020c03030603010b01022d070e07110708031608160212010207060f090203070b0d0b0a09 78
    0x2103c0c40350390005005400c00c2d900e07840c0e001650140b2904801400c3d801c200d0b500c1c20010892050001824091a2040c03200d02e40000c4ea209800503030f00c541d1101e40c00c0000796807290195521000d285411810805100200d81d11000050005403191401c03c0100b10148001d200491040070002c2c585000c190740088060b02d41241261441c07000e0081d0300240c030f03516001e4000d0706040100040340d000f140d50789555103190048009801d45614800c1d403003071885516140700030014184800300864a034034007081054290359200304902d045422402080703840c000e8114403168180c1160f0240714103150681c800503d0440581c1c84154143c03400001e001141f41c100c090072000300088829503548584400f0015603034405c000c2c50b60b038495a40054030f000b0640d60300142c40544044585100c070710065400040c2c1200240000400c50f0354001540c408002c01441031400c120103043d001d00c000c00090300041e895401030b07c900c039183d000c0040c40c89640740c030075844116030410041494000f50703165204a40 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 793226717 1250 793225467 793225469
    0x702010903080f0105090c0d0b190504050a140109110706021201180911040b0102031b060105040b0a150809070f06050307120216021005130e0609071d010c0f0b0a06 72
    0x8003152140010410fa426140d0455042c2c55001c1c0c000c55983d01c0d2421645075a5015030140707100282c0e0b442566200e0750361000481401c1e15402c0b801d440321400c11040108417071010300000c116a180035015084000d005070200d04585a88000161000c13401c1c061050600c29400001c103010720016104c0200411b0b0312190341030711b03503400e251131080c900c81081804030342501001070080303103005800b420b0a19107504040380300300061050b24101100f0720050b99540300031811080130364011400511050a29203c0d803440309904680340d850306460001414268411820007078100440c0b0b40c000b44001004008400c000c00810f030200007a07a640350380c0101070b41c00030b5415200044400300092024a03040c000d6418850b102c200c201501083c641c204403948002c020003a040c404103100c24102d1008036403d4400800c1e484283c1100c5290800800400c40030013041c840501006a040040c1d4020800c10954900c2e401e082052456203141070000c524014858010701c403010900800442c0345094000c08 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 793227967 1250 793226717 793226723
    0x803040c050111060402040908120f0a290d0c030210020c040b0108040b070e0a0f0b1e1615020f0703110d26041b030c151b0f0302070e07020109 63
    0x340c198581004440d10301c9202e0f0401c0071a4484008a0003501c1d09900181d551071080b58110701d488940c00e03201482810481d00c0003a1074040c2ca0820560880c039005600f01c090340c2020000b03520003d0b0720f4000800054010007409980e0291120040080da00001c030701954004100400301401c1000003583e4080e50050385000b5070824141c910294095100d05000329403184101449a41e15201181c0c0c2014034107031154089003480c00000e2150803031296102400318400403540d1401800029021030b40380f4590341d21902c43c10000005190345130704a4000b220340c001103c81c813424070700405c4000303400744081d240c1001d000024403c040540020f480300d040c3c2000010b5a004400102c030980702141c514203510b554100558000c3c05503c0a0340d0501e40c441e2250b114200032100c02080912207044c1ca4000321740e16a0900b109110525101ca00f08105d0041850302800b0343c980c5018090b07000b02007002c0200f160700c0c40b587c042d0425000340416006402407122610080c904141c0081c0a0007401100f9 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 793229217 1250 793227967 793227983
    0x3072702121905060a030209090a02060a23040806060d080408070e0601080a060602030a0c0501091a192a030f0f1b020102031501200a2d030e0906010203040b07080304 73
    0x5422107006010f25882940010107040080c0c0c44e64003801981c110040580d0300c5405400c0010005a9404000c1c02140d0a551f8a040c0d8000c6407070380300d641c2009c10103920318013000280001c1003843c0303002418641c4100c083d113080c0069a01c0740b815a0580c01603400c01840e034002c442003c00c000704407412a80c4039000c00d90368074407035132104d03103000003215070500600d001030700104070f00d4115601501034451401e104d02d00014900000f5198114415990301107030205c486510b042c8051101b4684e0344400c003c010407000c120009500765441340040010b44a0600c1602007140d440011340258094003040c03044c07050501c800b20002184000802030b0802e0741000342013001c08840150f10505c02d69101d14400b5011011049100006541320b4040098180848410180c4484480700601c201d1149c0c0b0f10900034a030306420f04200b4148407006d074404007481c4420703003094640880e03441102038034181010380341c201464584000403800c52143d9040917519031000074280080004480c0154801e602503144 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 793230467 1250 793229217 793229251
    0x706030b040501150c0b070e030106090204030218250c1a04020a120308061e030a03080403080604110a110c030109031d030303010f030b09210c16050307270212 70
    0x5405509581c044d07006002900349118140050014044641c0241c1c0504044a1008048001034203650341504000c8000790040b40c100114180041c2e25445502040d103003601626203c82e81014003010020b5031904080303210300c41c209242c018500480c58942010305189041e6040c0301038110240140c030124080c110300c42c2c00061050090f2190300c2040d81c103503203510301030b180c43c3c0400175103104c50031030101368582529000395165000c100310481244a92941d031868030b031a05010b0468030b401892140100e0074141101514840201242c044a455080080e410a40a0000c42c1740c10b050442c45905503280002407410301d40c0011001d24488244072958142c04a00390505859000c04c2c03103038001d442c00c442d03c288001a030804010750b1100581089403420200ca10258000207041c0b800320420b0340000810041c148010300008036400454072101040f14030b00307404681e481c3e000b442900b865006601420b0302a9082c141c824520a6200600f035484240d2621040c00b51182542c0b085941c503c0c985c0 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 793231717 1250 793230467 793230479
    0x1603050f041502100c0e040b0a080f060703060906180207060e010507090e09070e0415020c1237050702040b0306040c150f0c0803090313030b0105130203090c010c03110706030b040501 80
    0x81c1c41095555566143c02c1c6e02d20400500010300700441001e03500c0544501c0100e40e5010130401c000c002600d2000503c1d1a04052201900f15089a003120240c1402e10788103008104620018011500341d99500503524030b00b60800c48010030307010011552550915040c0124140d0000b411000d94421000d08286034642c20301c0e0b19a41d2010344241d0003803400480c00500071984090701c002e20070300d6a01d00580340c41c0c00d40f070440c1e06003c03552032080140c94003c03400e94850002c0f04010098882000714484840003400302c824800104184071004003d8000390004c11500c5507084410900380240407550a41007a107131180d10700c41c0a010b6100d0365075098086140d0f40e4415403031002650a5500c48240c814195101c0313002c254401401e041c9248010095081c022a01c40e012030011405220182440e5050004020f8000b1400040241890041c01440b074600408507809a0900c02400c011008645a16054408050303507119010a0300500c08002440c035095040300c200480215020440d5a80b00c4d6 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 793232967 1250 793231717 793231721
    0x6050f09151c141b04090219090501020604020906040e070308070b0a15030f0f03050f030720010903050f0307020106030f050a02190b031f050a0b180603010503031603050f04150210 79
    0x15407440d0f06a0070b2607000c14001c2520303028140d25525058080341c5800c0c2c80313803101000c1c0d92101d0040750861004007400b621050b401325401003d0502440941114103164000803172021b00070b000c844c0700310740d513660090342e03580c0800200c001141d101c05425180c2c60242841d1031054000c88420780d80c182040c08221001c8904042c19050f40d40c4804010045144c03620f840b951204608401c8080c40010070110302c085100741c004d18032030b403407594810f0f1510004070000c1c001034580d4640060903130f0400c00c00100207504175082c0c60794143c10891403030f1282c1c0c0740e1200f00d02401c1d6650002d0700340107254022a0074000040b07040c04080e4001d64502140483d0754101c0d2440413028440c0c8506444148046004440c802942010340030401e1881c14440b52a0400a03003031340d515902200210354000b0360280c2220340d807000d980b01c40070101c0f46182558544804a502e0703200b01c503003c594142043d00710343c3c02c25014105440760303204902d0b6815142c6856641c81103408c20b0b001c2000f0094070511840740401030540c = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 793234217 1250 793232967 793232981
    0x712110c160e091207080309070e1602010f0c0509010c1511030406140103020d020402030a24080615010f0513030f06090605060d03091a0702030604061418030406050f09151c 76
    0x242861a0040075190900c0c1504003a2030904030307008228002420040f00c00300503000c0cbd003030355580c0301c4a490f0110740a42164100390b5070720f41060600b9420400d480e004030030343d800942d003030810300006003940c68030f10303444120801e19260b60b620300840c02416459103c0074500c5144070351400c0000031a40c841070600c10b8801d200081d071020049440c2001410581c019640106010310701003411030f190110140340503440c4d4401320080705850010080d07004200718668118801e0101013a03800c0301400001c2c103001e0204103020a100c00003401b0104152701044190066030400c12164981007146482e2001d081c0b1004e00307a80650078a00400c03603a01d00801c0c10304216506807182c00c0d40c945402c01d408411940d618140840d02001d005030405a101072140c0361003103102d09070009a0000c00c905c00440c3c4040600030b111a0420008106001000081201c081c1c9030142461502c61004810180322440381e0882c20360010003000d012182c00c421a40075005194107482031044124181d4458801c450f0740c = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 793235467 1250 793234217 793234243
    0x63d09120803060d0501090605041101031409030f0a02031b01140702010506091602030906030a0203010608100f060311040512010509060114030c0f120303101503050712110c160e09 79
    0x420400724000c2c4c82e020901c000503e11541c0003140e25506501c0718011244101c83c191a00f1004030300d40521517925120b42e01542008510b810658108290004d03a280181e070025105480001303440807000d0b0081094480e842d098182c0c00c28080c645003174084c041e000310841c41d40c11079848030209804034010b020302407103800007520b0383c410b0340d0b500c0034003141004c1c0b401c1100080d80003c01461080f40c0310000118481d134903607030300941d0369450503400401c0c918004040394554004100284251681240c00720101d550a24022070685581d5144500e0f80c0702d15070020360700006188078104c0390710040d0032091007440210141c030896a41e614005440f15071a0006030703450740003088504070905d80340110556203103000d8081f108020045407030624562044c1d42c0d00001c4030203141e00300901d09582d07050640c215100e180500450511200140140110b00782010801e91203465100c10076004038142d88203400903008503030303200c3c145851508140e00c0a01601070740da49080001110f0b240c0008501c041050 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 793236717 1250 793235467 793235483
    0x20321071b02041e0b0f1c121e11061f0614210912070807020f0f0307060908011107050d08150306161e08063d0912 51
    0x50724511106080807100c0c02c030f038001c0c4d46040307040030407000e072a1030340942500c1d44000038015200c2c0b0401c070000105281c0035201c0c44442048003501100121005001944400c106074405440d0b0400e45076181e40e03142401d03400e010b0a503500c4105070300004207410b294800f8156000d9480340d550121031100d82844046c4201000603082000034071401d1600b213070380703c0e101c6100d0914144441c4c0d5405e5200d20304400100c00740b1181440302e041001d000600010111004030b82c83d1132042e690702d070701d1400341003400b17803080814001185142c5c551a80c1040e080300300500f82c0d0141a1076100250015403913000300b6506600e03204c203000c07000d024042210385458001c80101a84410114210707a1020000d0045952083c8000c01c91440d8804120540c065171031000025040e40c1c840000600c50f00034001609407203c1c010601d61031854111030300c0c9401c0682036a02d8070480081d548400d0390900d00c05418124117954640c10b40800c18804403401740515190b840f070885960350342940d414040e600102400d041 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 793237967 1250 793236717 793236737
    0x70803030115020f0a03020109021005030f190b030a0b012105030d2a0c200a060e0312070b07080f0c0d181209031133120702032107 58
    0x802d102810300742c000c91441101c50301e4200c505950305050780c82070f0031001b40c0c0d160701486045181500c080101d00f034041c0303049070039454524000d081040002d04400340410904200f16100c10a64104910003600a400c4400744240342c9400030009109100e544c0740c806403110007070340000148a802601da0f40200c021400c0c1100086030304014004c003007080e2900b002400c2c200300c5283e4801c0c42c8008024041e151581403540e10300744086402d4250b44207400c0742400080101c0e1582c0ca20a00d0010b031601c40c40c10b4404d16a84901007031400e0380c1c0e252105d00d030b100086004400c200c1416544c5200300c00556640380c2ca07440e503411000d9600c0095420030100b00c0c092243c0c041025003a4003010041100f217000c2c107070080031502c03041510b0700a087c5100c00030380380200920038080c00396091070400c8416500810221010100d02c0c11140c81040100d5600c00300088803407ea07403002040d5580b07a00c040002070100d05104001940d29031141c0c0c2001036404820341800350010300001c8841c8103040c15240c81e5502 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 793239217 1250 793237967 793237979
    0xa1112120f2203120c0c021f023a050a020a060e120403050303060a0b0901050d0b060d0608030318030306400c020f01060305030a1d03061905090708030301 68
    0x700014101d040d0a440318000c41c0100c1601410121428040d0715007000d0055440e220800b51001e080d11801442480010100107032119002403290074010200140c100d140f0113000c80c02c0420511804a040303039031801c0741c4007000c05605040c41c1c844042003261a5160083ca0a1314039014810008001d81c2242c1c00c801c01080c526045841c0740110202510b03048003130a041811541c00a41041e5042e034000b000300103242c02d10f00f64141c068050b00c0e5015041401000000306144a09040740651b680c440c0107004817921440c050ba000b100668078180002900c6100455503a002165003040b01d01100100500910300801105e008100140c000380d00301c1040360642c1c603003012900d00785d038100e6512030741041d076500302121007100000303014400b042148d030651000f45070010b4003540300440d91514104000040002044807030110b910b080a40d01025465150302d4410400c600098040c081d9408010080d422402c42600310b107280e071410071058440103005565100d0314060112140e10402c018484 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 793240467 1250 793239217 793239241
    0xf0106090b0a0c05101a0109030507090b150d050603061803030a0c17040606060e010809100b0a1a09040f1503060509010b03150a05011d01032301020a111212 69
    0x1490000e0f080215042d0b0155035131516055101000a02042d96107801000e0a5520396a9500300042482e2500b40581562901511401e942c41020301d90760b50341015007a252240b142ea12400c216103010300d6180c0c011004034802504040762141d200c1d016017030010b4044001405100724101001d0002d50541c3d64541c9003500500b00354180e481400900d4883c13080540307041c06482e100c1c1d40300f1200403603039520302000039107408a25583c6d51b052050740c50070000b07a0270001440c01e4074229441070100301e55010001181c00381c2c4607504110707a039400c05881603a18035000001810742c3d01042d01c1c200802038090010300202c2d0810750324008482c101c4442040420480c0e0481038011180600001d11a001400028030b0700c01803510001ca410a24410407400144601c2054010140c0100b1060b250740302240c01b10007010b0500004050b49418064041c032803100000002c407802014000315a01d81100e240504125040c4506d1181e03441551810728801c00104151100429507270704503101900e44c082e0041d0 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 793241717 1250 793240467 793240477
    0x70b070615050409060c02100c171e041202100e0c010c1b031a061c0b0c1209010b030106080f0d0c05030706020f0c1006050112050a11210f0106090b 65
    0x5010044101c0460365595512620f4802c070b00c2548001000086008003900f020b008940444685140c0340408104940040c07140300d000003d59062034182e0340d5010700c031000f43c0704411109e004940007004c00c801c0040c0032034138200b4504a50200e525144581540e0b400b56150380006030b105070040c80a01b295135000d0344558811034424071502511141c002d01c8036000860a910646101d9446504407100f40d01c080030b043c0c0c125005550409003040103000b030100c0405a610000e142c00300740d0001420030407400301500e4010301e2201c9450454103048600c6800307440081c218511a510f0003c000a044500103100030304011100060040308040142c261340c1180d0020041d00e65010420003800054950720040c865040381425890b00c816440740920718090300e100030302ca800d034074028080c882680c101888040701c8a5021012403265a801d807000c01804003000c141c842e0712001700f009044022082c00c40f1040c104160b0b94204a0360b0754001e0040c7d891000e10070b0201145100380248940c54413800180 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 793242967 1250 793241717 793241741
    0x151b0513081621061e27120e090709032f041d010c0918020306090402130e01050c0418021201120c0e0f04140a0b07030b040b0315090f070b0706 63
    0x14a5403078164850f075090720710b00411028082c0005214170505c1c100d61240584d20001081400241d4070504c145000409410030050102d001c40840c0c018018820640181480b00c0039050310310600704180090800c04450100b02c0d00c47e0303160101c1c10782c500540803803404c070b001d00010200211002c100900c40208141c212510741d0081c0b2450400c5028424012842014500d030369040003545016072070600f40798025160f0325254010014000340d6522a118150800e07011262808010107412216009100e42d001d00102d95080c20204561f007000341000c0e02c120b030180c1d002140c1560078044001c0c03c92040041010383c5e28482001440601103280c541c403039091203861088003080d100e054440f002d002c100e40d0010a1400c2c9001c0108010400344042d5000c0e0010b4000e1080c2440c41e42c454a00f014024410340405940324dc00001e82d80d16500044410034024059480e0144d12900e8401141c404070b4101070071b232061080e012005040081c41030219142499094200b610075a620b1018088004d090 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 793244217 1250 793242967 793243019
    0x303270c1e030c01020a0305030615070f05010c0e100c0f1a250e130f110c0c1804080a050f040b1602150a0507151b05130816 55
    0x199251141040d076641c050141100050804000c1c0425150000b0101c031541150400700b18400080d8100e401e898110400b1510201000c011201c2203546001e80000a80492195400c0c0001d01c00194420b0f204484e43d5a5401103582d200c005004541c10a440750b08005403400ca08440850803171810034059501c2200c4515028584204442041c0740a07a541c101c600f650a10f0038200c51a2040404401645c9081c0540070481c641d00242098038a1090140c0740da40f5502c84000e500240d60150000f00b0802c4516611a40c0c818541a901d100a6903520b008a0503a002c10200034841e1200358070a90348010720070316080c0039000071070b400d4008508a121005041c4030100c0e42030300c902c000d4034180e5010910420300402d98010000d1090740c00010b92960501000032080103684074040f1140144c20060001d076182e0103a11450007040c460300a0010750010413881100954800002e1800003400c1c011003241c50744409900f40c5822400724031309420000d800c820040710101803c001c140440314134072 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 793245467 1250 793244217 793244233
    0x3070206070309060e031209090402030a020a09140a1803050a020309090403081e060a05040b010903020a0b04080706030b0105160501180c21050a171b011a03030327 72
    0x85006038104001c100d000c00d9021034180b068a0f8814000541000100c0040c07410318812400c40344188100292240580310032000541951410800600f0055010f0403001c58140d84800e01801400443c481c1c0e8030300300d41c850202d200030a5034001c0c0e50036030300030b5203503481e5610980c1c5e004d54095203c100340100f54007060050384156035401e0003980c400c41c080e4954000300d2401084001d2000b8409400102040d80e003014003442e074a076901f000081da0b0043e1000140030031440010b0f40d40c1042e03940001d6010681c910302043c03001c25040544115070501045400c11511001d040d020b450800000b52300081c014440031030200364030341c4903882c6140520000650f010703901700c0b44031107140704940580b26503100d01010403040240e40746400607001040318459802c4a82e9441c5030721120500d4000d40a0320600d0041c0c040e00c0f001d0030890703a103403240d68003142c040b050b143c4006029100b9003042c16000d03106512556210f06020044070301c5259419148000781c01320b048000c5802e00d03042006040c9101301c0007 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 793246717 1250 793245467 793245469
    0x80a0c14030301030c051c0506041101091a0712080c03040809150a0c0203100606081807050a1203020d1422081002030a0605030a03050415181d01050a0b0901080405030702 75
    0x1107003e1801100b103c034800c0d044c84180881a2042c7e01100b800d40c40c501c0c0500c01150303000c940123400c85c0d44801c020720380400d400d0049030b50108642221902140203220600088a07401c020314085119104104641240348030640321402d00f144c0b0100c20400c00c100050001d00380200400f040900101085072954240e10848100c1c1c00290041000c10300d07041002003035140802044480c88001c0c0b40503c8141c0c1425070080c080000500420f5520400c1228500050001d05c464030260901030515554141d50352800c90000402c8001500503000d0003c46900451041c000c1e80c41d8900103041c1da520304895140155020410080c1c140b406140607a804260313070342d0600011401903e015005600c034102102e80700d04940301030307000d81d119038007140c5030000107508034081c0c5044403842441c9a40c40c41042c002511900c520000e0510036482056010400710000881c0f001e003420034080811903070307803584188034060b40240074604010405105020141d80f2400805500c41d00c6481545c2c101249a8 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 793247967 1250 793246717 793246723
    0x705030d050403021e071d220f12052802070302190503010506100c08030901061e0602010506010201060b1c06090603110306070810060c081c021c09080a0c14 69
    0x1603000c50050b00074601c1c02910912180703220484e01580c0002d070102615000301741d1007d01380c08000c07401d59109407000400002400129405040d100201281510000d2900014150500320708841340340003003580e032a0341e030301c181c0a550301e0724000801c00c2c02c0903e10100d05c140115003000301d80114800e008000c401a01c41d008049503200e090b092b541e441d00d050608040c01d691000f003180d406080c00402400c511548800c42c4400e0a400110103030347c1b80c0b0f402c89000d02504164010880300c48002a06078280410517034000111907455008200c1929154012803e07190356120f0132031402d5003480041c00080c07001e0090002060040000a0015902d09012040d40c0340ea03802610740c00455518240d0750b0505000d00c0d903100586203001c4000e4980a0800c058224141c0290f00c1008100b084000811640340102d50075080404aa40941035103400100040d500080d88041c19030882d140d0740060320800e010343d848041d072000300d850811407040070445011015480c240e541c200c2c04890124401801c0c = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 793249217 1250 793247967 793247971
    0xe010e0105100806090d141204081201080610030209070e120a0302010c091a07231b0d05030f0c0106030f030e0a0e15040c0e0a06170603070305070b0705030d05 70
    0x1040040307034074500301250020844241e840005250040c4013007200310344001c40c280161003114200b00155045403d104000341c002c503114141e02c6042c0905102c14000400e010b003210340b481c550000000d0380c81c1d00c1901c0d1101e0b819601400080400742040c0300614050700139650184892600301132103c580c10000b070041849503816070280d080004075905159082c09811600422828007441043c508120700a800024403090314281c0d0740442c44000300304003085c03c0c648406d40300c59900c6e0700c011100d4485d91298203801d41040000d0300c1c2c00c802501801c041104080003074200000d135080201d5245562021741c0811707410b000f9950780700030200c005907241a94803603e80c002d0783e400c00c0e0038005400b8004403a416030031801e500341c0008100508101c410701103580500058070040380340412588180c0307202000b0700030540d0081146e500403a0070365006d106103000015034015039509441d514141034459800340030281c4150460749051051840c07410041c102c1604c50000c90749401803190b1000b0484400b = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 793250467 1250 793249217 793249241
    0xe1c05030609011401140f070204060306020d0e010b0148030801050402131203090905150a1e17030c1e21030601030b19030f150b0901050f040e01 64
    0x2100388101d50405210840c05070001c004000c00c04d60260002070400e031030705401e2008203000025004250070501d42910101075010f8004d20005880340342010194000740f440302d801c10300d44450b12250700414002c0d1005424181c6500364800c01c0340541a01c503070540d8003001d401548029402020340403084080501018480f0440003030744082c0707401081c1220681c8094403590052080102d000310825122049501c0e075003c480301f403845450306450a41f4260b000c0722049140c0000c221205a0715400341081540c119a4a0482d54483d1046041050740008050000b0b48002c0c01b4032482d070300c40340300e5446541c1b00c0b0704480c1041441c8840618040346031441c8503244800302d900441207181080301c401c4410181001038016001c800c0150003501008040f0750425494050180040c1c0b20401e1102d01502ca8400d000c010949030f041c044c41d40c00407110101c0310000c0c009841500707800319106900303c01200401e2401c25920344001c10603204c2c45d11f0005544159114124403a100c000d205013101008 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 793251717 1250 793250467 793250477
    0x120f1806050711060702060601080415050a021c050c031501050d090f03140c0a120e030114010e1807270513050c060f03012c0c04031b08100e1c 63
    0x2414000003807041401e0029425550b018005101751540c0204211742e01000c2031920545951316801d20010510720481401901c529002c280b0515210503002400c0f0040065210790034401c20051840442d50112510104000c060000c21048080e031040b825100754145422810400b05030815030464000020884520700d1001c02d8504042e0000343e00010002c01200b40c41c10b03c0c070a00e12460710358500b40c1c0010044545180c02024a40c0541070705510224090000c0090540b02d022140b0f103141c081c041c00452015100004d207801240448202c2c5281a08000d410040d14000719004413030b003482c0314820a400c0000382c1510841c1b0138410140304821640350b444023069a0b0a180341800307a052100b0b4021042041882101000c2ca412a411070310501120004054001c180c02c140445100740c0403120f101301b01c144010610b62502600a49020314825014503010441600440400e80304141198025a11480340c90244d5840078400c0050300703083d181e0410840c036801c1101c040a16180c00460 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 793252967 1250 793251717 793251721
    0x10080c0d15090c091406010e030303070c03110708011410080a060e0307021818030f042616080d02160303180b04062a0c051c06050c0304051507120f180605 68
    0x21400664a83c2c20640038241070f82e08d140c41d480820b48a120040886080c00180010f00c020507100e010074034100b68004003600c0b5001d07140e4440d41d010300b0045004070000500074000c100b010303400039802c0080300d000758020080b8a0b07840d070301c05c0d01030720102c160450030340001d00c80040540c8131503200d01c0924102d8094181c413882c12180200391641072504034201307a4020300060740403461b510115030039a0b6124000a040c0504004003509514404503034200d14055200b19613640140c1c841203805a9070440240c1785500410841260350300c01e11881d41c3c074901c425210420221b0700130840000071243c0d54000c40941a1180b00c4070420351703c558440f000154a41103a103c0c80c1c074180800e8030040c1035170f00742085051000e44810080c00598080c140c07144051064482d1000c142203c982e200780d074011805d005526241140782140d420468003943d070740c0105a40031004800340040148500481e8407010008400c58440100402034541404c0c1c2060707565214a94505079408805001071103010f0200d040c1c = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 793254217 1250 793252967 793252991
    0x91f08030415110703020112090f021809060c120705031302100f0f03060b0306010e0d0501090b060a05010201150b1804050109200f03070c15090b10080c0d15090c09 72
    0x3c000c010501c0040e40c0107071005100503a0b000010815004840d840815502c00d04c0c1000081084a0b15000754800090344208a140b2601140319105201d404140c64650b9180c90115106115100d50305414400001c0015202ca001e03201840c0c028070b14418442250301942d002c03c4007907107101c480c800803803469000c90050b294451900c40b84440f403880c09000e01407030030062b1252400080c10f110705104008111000c9500c810550008141e0004024001001c040c2860001000180c4080780200084003000c81c003940140955400c114058030360461452800710b0f5081240c0081c02d035043c43c0b107051080049585d542d03004007806094100c00000360340000b186031403044c01c0c0720b64401e5481c42c0d00b480134030442070100064a90140b00d42c2000382c0102500d01d410000d1002c840c0310701074020f10307103070403182071140031303041c840c4601003480c3d01d100b2072525030000030340d282c82c01128240e01c0813001a03003138001074101d2040700340328103903a45c04580114143d031151114401c40d003103c0b1b4600e1b41c0c1c072507404031 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 793255467 1250 793254217 793254227
    0x11100c06050606040b0d0e01111209070e0402030c2b0804170d0f030c1e030b0f1903140307051903020c190506211509090c091f08030415 60
    0x542122a0b615081c175001000d0361034042c4000b8624826a2800451a10b540a4000078024005050f41568404041d0103207965030900b521111070520540da03012070101084c000450096400070b0042030014071180c20882d811406d8819a12281d074a000c40c01c500705203405981c4c0c0e19511885200d07440e40e007050346030480310041c0360b00c021b4030303034802c1030101196078003c1503000b401150380c074012582800c21030003a6402c110b40c20a42108603074041f03d40044680c903511103004060225920b80d51031222004104c000b9008140300c4460403c03004040000411180c203070302c2c0744074410054901341700d82c13030f1551824521601c00030070044120101c2c1600705641403147d1248414201c5000f503080c3d09030501c90218600d01d0081034050400051089505070144140f003030325041424240c1c505e441c022216196800c0c02e0303a41d017030058002c3c00126003800008038480e0328400e000740030016203a40b56884600c0ca41c0903140f0350a010011560041040c280502c010b0025002020719100000446100200 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 793256717 1250 793255467 793255471
    0xf0703020f0601052803240b15030c0a03090b010f1703070c06030c03020c010504260702061206010c06110a08010b131403010b131b02121611100c0605 66
    0x1900b5082600144400d9035040c0344200199150504800381c0c43c0d068000600a031042d40000e01200303034455034083c0c1000030b40c0d0715110302c0c1e89a41c0144490030007141800360b460f0141c915500c90170070a000180d421b0509001030565000e1515010602e40c072140c41d003401c014001e81145081402c0448144a601d81044a4991042206000b1440d1414903140e102c0722440390700030101010745075010001c0d107a00c2034050f60070001510000300440d0425191854000c0741c4000031081140a144035105845000400c0d100c465070041d142c0341c03402148115000604000030105070510085412020104800e80302d50408a840d4101d825500c0041c904083c000c17060507409841660400c0041100c21102a125501210602085150030401501c0003c2c0906001c20602c3c0e00414185001c145041003a08200740c400c50800041c00b032407005807401c0740c40f8404203000d04018141042203080504001401c1d01500c3c0c0200e40413a844441c0d44005002190781c420303950b002a22801391a414040180700c1c5036 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 793257967 1250 793256717 793256743
    0xc090c07062414010c0b0a1a0409150f1b02011e0204080c0d020402040b0c031e0a1d030c0d11011119020402030c1306050a0318021518060f070302 64
    0x4100104403814516007182030700403180f41070071030462624107074010741c603152031180e000c4000b0020345801400c10000b010010141103011802c0702000103141494403803a91081d0f000a03c122460380300c07000c84000350102280d0303203054554450010000360680107040714110426030010801113802d49010207541035285d08021590f01c100410401c54000040c0f0840c4280300340c885541880d6a40006070003405039503c040890b40300001d0071280c03200702200400f40c0d100d1810120020400c071000b0740d5198001c81c1416008104c00904816034030102c015a162514030003011510059500800b0501c140c400c01e40480c0c15001040e0702d0300242d80c0001440f4100c0f01940c000b4640c0c084186100100c8403441ca10213400f4650010100f81c8004241c0100c51880303814403039400300345035200c10040c0258030060000c00000d20b03080d01501402032250038071480329001840c0380d650000c240180850341d8411042d86814000000500d085c507142e050242010510f01c0ca919600d900c140d0030003034203089502e0049 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 793259217 1250 793257967 793258001
    0xf032706040605071b060507210b01021608070b0711040c030c08060d03080109090f0c06050417191515090f111c0203041e08030a0c030203100b0c0c090c0706 69
    0x2031100089031043d0070205d078101001241c0780c1c075020b0342580e070769032141c141c14244920340d056181c0401c9581c1100700b400500707900300c074000d00005152044403005401585810703005904e0820401c680d0b50084c002d91402403001b000024140e800040803944d090000d900441d840d10003481c0c209400014141c0d12030016200600013001650b0000c01c0c8020500441894035a035107004000d0040050101c140c0c01e6011f00d1003980d031516080050000c1e0400d108501c0d02e0700a114800e03030280030200c0c46000e1911000046005443e041d5600002c4000b081d02d94004c090703450300006003070300040b5050802898952000a0302c1504441e001040d12181c000041e80d07028100160b080707410292500c0081100078060042c0c07030341c540c1d10f82000403017458111401845410f941540500426074002d500684404404000c81803030210705034180c1c00120b890060703001c0d89810402c07604c040da00060100e407018070141c0c0c880401000c0050608074007500d0340380344a940801c85808019440c840c2c1c010906081c444 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 793260467 1250 793259217 793259237
    0xa050d0308061e031504061b0c03120e0313050f040b0a050607060e06190c17040201080c0d020706090c051801030f02130e0a03091a0f03270604060507 66
    0x30240070000007034202e600654958074544401c041155510000c40030040c19520449110702c90b103020100180c4003603908a2078400041000701480d50b80340303031002103611104c019104649090b10b8240988814400660700c52401c00d0030680b0910090020480b104a500c207502d00f00400c2c03041c03006a21401c68010b03480e01044103140d40e140d205100071203078100c5a183d5a1039041c94804060041107411000350320504041c07010780c0e542c101d91091000350743c510801c6440c0a4030300c103c030b44054106c03d5550000242c4046401340d449024890780c46034900301d0680c03900c640c0b00003200032a4440c0c03405440d40c503030301c4418070f0030403070a03111480081c030003115041d80b031003500b001700d104038001032000401c02d615140c1403c046480761040a1255414101c00704024011440003545400103050110300140161901080c1c0000070751015014000111150f401c00f031480404e180e10343d0000c1c01e660078a071140314080313119a00c6508081403881c003110140c021800c0c41c2c50403600350398000c1e2181091000d9000 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 793261717 1250 793260467 793260473
    0x918072c090603030d09050a03120b01140c01060305060717010f050303250203030a1e03050c09010c0f12110f0a0210050d090b010902090307050103050415091a0403020c0a050d 77
    0x18140800c42000c036401c0c0d00725102c6000103840c41c4180c1003084181d41c01c1032484014800c01050000016000751500c502021030340f01e5aa04842400c1d0040317010803643c01c2e03c081000b1225000e01007652132500005105a102d0700e540c3c2c548001103610000144009041000485c29508054010612400700001160038500080c0e10b82c041e0040c4440f9456145001e080d0812040b0100200703150094250303a62442c0c05031004140c0e2007020180c183c2e44081030302c182e40c5248030b8403c1500c00c44010b0001400e0410b54401145c82c0c0030a45000d640300b501c4e04d81c41001140510002281c69503030391f100c02e009400000b85a90030140a208140030b950400b007d102c0150701d9541c440025030345103152081c0d60320007498900c0020282c0c0c1201500c1d4404850010441194590003081048002c5040305c04496403400110250303042210014200d03410710310380b00000d80c01030700a100c107580705980c81e449d110390790800b40318443d00403601600141c0c4071135000c14041c1480301c8035201900040c0e8000805070b440c1d032 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 793262967 1250 793261717 793261787
    0x3011b1403250207180f1407090e0c07060626070602030706021c0e0c01090b091c020d140a03090b070218060102100603080405040c03090c0b0f091807 66
    0x5581c00344441e0180b5021400501c02d00c000c0c2c0207084d50280d2004079000035010700d00140008015524450310b44072010b6110610741c003e0720311585031559440342980c00c00004103402d8034090715040c00c611060080c1c000040c11402100040e00402c824000c545c1c203e03580502e042e500c4800c58822540114009002c40c56021044820ac0d5802403000360f81c5074940c001401500620701b0514280505e03118110804500100702d9111001e400d0340d0700140c454840200c2021840350500241c0d02110701c3c10a02041508000c000c0c85060000b02030300c3c0040e4071a107425a2410607904100714a801c6002c50300c00f0150045981c0b000381c0841c0800381e040c0301d80c640c0071503b5483c010600002d81202c4100140441c1c1c03081090040d40d040040f41448181da80b441c00306203d03007141c024503105905207600341c038005201e4425040d80315007103884600ca0500e028440081030748010012140b001c010000c6400300e40307a581c41914402d00c000482500b03894aa0f500400c400850322030000311400c00989204410440303 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 793264217 1250 793262967 793263001
    0x1201240302010c08160609050f0d030b0319052817070803041b3204020f0906130306050f04031e08070f09030f050c0111010209090c07080903011b1403 66
    0x40010140e44e14009541c1d1040b542032140700130b2503035080c010351004000c8c020501031040520a41101c0c801c445640c42034055a80800900f074040e44640c40c078800f842643c1005005150240301500e07400d0307003081c0c10f4a000510b4050f00ca9400b1810121500400031028801066a88040061810034049540b03803209480040d1010f845c4085060250b03e00c028001c5d0000b00030403100d80148241c88060000003003200d004005984280c90b112140c8849060038000c40c0d101c118050b6000c2c0c074104c034030760811040b9005000c07030030140000d910010000841c10301c43d403405045414a0ba40c09440d0034034008120400754082c0280c0704035614020b84490380c12100054220041341040c0c0704100b02400112441404c0e0b0740084c255403070020000c0c05108020400c191910300c281d03a00d0309444000c4400c2800d078400c040d1307200c0c0c0140d94200068805204070000d070480500c01c40500d0703e0034230900c0c0001d003521000c6035007580c1036480b0601c015442c1c1d0484030303c02c80031800c041514198a0301d401010001000 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 793265467 1250 793264217 793264223
    0xc1706010614120103060e011802060304020909150405100b040c1707020109050a06091a010e0a02090f1e04050a0e060402040b0102190605061302030906150307051201240302010c 78
    0x100c0701609041082e8054982c4120107035281540c941c0c0d80e062400180c030308002d41091551030240e00388080f0f00f02c0c05180c804c0d503130041d003040c1c030f903840d964280524148001c1c603074402406501c8010038060b09409941e80110b010740000c212401903208940c0880c1c042070308061142d4901415034501c00e800c00c106100c85d540f4205208880e954521003603004d01940540200180035000c2d4450402030580d015400c040c3c000c0101e860070045160250074454800c0c00380c0305003500711800180c2c490207036400a20200b0409000c03401540c1c182d00104411848a5039524241c907a0310400c0040b604180c400d013584801c00e20005d11031079140c0a0007540b10200680f019006a841d001c00d00d900364000c100760080070001d1040304005074a0f40c00c0220040009a0701c80d8800c03a11010681c2c00424180240c80c09011410007514058454161202e8100b070425100c170b4150003440000035169032844829511075900c40f001007407002c1c0c44a81c402e4080f103800d040d2461010508001d00250741e1000010b2022b580c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 793266717 1250 793265467 793265477
    0x60905090a0e07082d0c010516020103060f0305010c020c04051b0306060906031006032004140109081c03061715070e0405040f021807081612060b070c17060106 70
    0x14081001500700f83e071035000610548205008059148040140b40c1d2040d5152100206070684070380d03c8a8640401601050020700280039105039040f55005e0040d0551050500289160361000daa0320300055690060703130725965030082605000d406100d94a0310754000c440800c0740c1c0c0380501d0244a0b402102d0b01081002c24044000f5030325403555002c850b001c4c3c100401c03213916440e0141c80aa40000140108000a07013041d2501d0154201c000f21414a0b5400381021402d1a0030000b6400b6140040794115040100d2003100040c0f140007400a8650075040004402c9106e04400b0007405480866020ba401e000441c14540c2c082000492811301c40b00d81c8800141450321031000c200c038801600ba501a52240c601001d03c4104101c02c40403040340792080c0c0e0f039500710081180d070000c2e030b141c070495044012604860020300089080c106c0c8003000012403c028045080c180402400c0360a150000e0034103050004801080c0084a0510070091400006410450490301c90380c68443c0412310480d01400 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 793267967 1250 793266717 793266731
    0x1050a0f021e2401030305090913060e03030603010b0102071d07020a2f0105030402030c091f0f140607030210020f07050f0114150a0e091507090f060905090a 69
    0x1d20911009032280900c0b0b10841c426000704841580707030800c01e001d10143c001003030048824040d414107154100c0e5003580300d00c4e0070700c0c2080052140d05140100000c9071100140c650000151403446140c0011580e0002143c9900d0700b40289401c40342c41d00c000340e0640d40189002c109215580e079a0011000c482065202d4607150030b20240d14104851900402402000072501051001c0010034100880285580c2c01e0301d00c20724006403014481942c0181d0140c200343c00100b818200301000380c1d001131482d82e5070321001500a8400b2110710f00b80d0043d4a213800c42c41803c000d001003841c8076113503c440490300d81c2c1c50300095a401035510b11099202110b00c1d0303008200300c012410000240c503902c1d90440d094511000d083c2405900074013855911540354441c041c00706904440352588000504000f409481035039052008609010200030030020301342c483d194a82286004840219004200a807074104d00b0034100400465039880d079400c4502044006801003219a0b59040c00a07000710b41001c00141c42 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 793269217 1250 793267967 793267997
    0x180301051014121e0a1a07050a031a15040305010506040213030b09160905091608033f07021c0815010c0803181005040f0b090304180b010f030b01050a 66
    0x4968030405400c100032244c0c1150702d0034103001ca01140c0705481154035401021400f000104889015a8000000b400034407008000c14029030184001b1000f081040c18000c010000040721f03010f00c0020140114804a010400c010003405400c0d00070400f00d4041d0b083c04d030b51a201c0c1c0c051201c54400548a940c410f004a4600034060000302a6045849280c0414a44442c050b00107028256884c24441c80f07492a5145802d00c05d0300d40d18142c3d20400085e61138103000e050390804c1d102c00342025070030007105240103400c0382c410541d443c8403968900e019160b261074100406810f2882021100c00004403aa04103d59581c0c46030040c0e0340500701c00c400c075400701481c40c01240c1100041d003000349651000000e008240f8024070728030314000b42c03210455200c0c4504d039005006883d016030f4000e02002c00f5071071810000740c4079070016600c03400721b00c200c82c142581d03803604100d20207c03003444503240c0355241300711011941e22101200300041d06080900454402031f00003031144c401d40410380100b03c14901201c0b25 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 793270467 1250 793269217 793269223
    0x100609090507051e09090a05090d300209030102070c0312091203051605070806010f0527040f170928051005040e0c04060807020f070b0f0d0218030105101412 69
    0x11448010340700b0565460f0170785051f0000c01003511100d0403885104a09203400c4d11400725541d51400d40e140c7c0e131120203942c21002d100c00041c0c00c0f09000076a002c1c131222480f03440910142105500034143c00c4c04031843c5040c030249004440e90309400700048040240018120140b040380c2c0c1b140d1501c8c02c1ca43c0c0d8450758501c01054911030400030058002d00100040c10302000507094142c80404901c0c0c1820344d515003c1200c4081d107000b0400c1d5074032501c8080c1c0a0000c991010a510501818090300b895000d80e031000038650080881303a040c000c0109290120b0306241d00010760035155040700b1301c207203403144050f40281e1003144101c0f449010707442d0450608034400c0050358000c101d041541c2d880c50074420700e60079030f81c4c000e400fa03007000620340c0000400c4a44005034403000341ca4020302030b160b15802c15110440941c4000c0c1d0103101650100040914804207200508074108074002da6000c1c0c84040c0205825903001030030405c404d1071920750030b2250b12a10111500b072a24110798000b208800c02d0cd038682 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 793271717 1250 793270467 793270477
    0x51014070b01090e150f09071214010605040204060e04110c010204030f120302040501080c0a0c080a0815100e01030203130f0b0403110a0b0429100609090507051e 71
    0x5488801080ca501040403580405040c2c03030440000340101101c07010351996440d00001a480a031a6805c0802c180b80d40b100d28030340e00101d03940c081e0342d031082d12420000401c0105501c100ca40c40c0804008a5000c4802e20034075000d44801c80c4c040d464245040c1006114030f50101b8010700c42d540d5001c1e030800994400d01143e5008114000035525183d50b07080c422840c05c4079050680e0a01e851044080706a40b283c8200e41c29514161226a280c1c1ca6600149060380c120074403040c18440822058030110312030340080e040040080c0d07100c100b586401c49455060ba003802800d0b501843c49020022100d0340c02903400c040059082c03a0041e1a60f0b42c5040150a10340901d00103000594000d40c06418040081d41580c0f090340a40c8a8440e00101d2001c2d0550781d141c4020040c0000107a8000b040020f0000f41c030803400d5030301c0b40401920000220070f09091501042d00c5c094424103001d041045425045090b003401024100706c20011854504000b42c01485945640301c040f00f05244940d030003030280340c00d440f = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 793272967 1250 793271717 793271747
    0x170a0b030d03060303180e04030c05010f1802120d0824090106050301061407050703030c1b080c10050f0409020c0708011503210c030e010912060f050609100510 70
    0x50241c00103000c090020b04280c002500014413260100c2a0422282c002030100d40c00c2d800324612542e00d07900d040b01c08441d50a01103890b952141c1d104002d41e50b02d03025030300c801046100d5070082d558651041006a404200b6207080b543c00c80b1482c0700c0c10079003021441d980400359204900c581e5a48100c210b460079140c1c81c802e036000c903002c000070a000d81c0c4200690b068400d6130f144d40404460402650000780035000c40108141d001744c40500c0024820300c0d201403482d100784017070000e00145400680d80d60446822031015a03001c0d00202d00035141500c1c00c0e0403403600d0707030070300c00e14000d2041410461441540106809180c0004d00c0e44240c600c01c201313583c024119078008001800d10714100703417410082c6120540b001e000e0743c154046000c034001d0340c885e0074070465201d1003022141c554055072065401181c0a05225101c800098044400c0e80c031040707018403c060001e19003500d4500301c000c40310040e18450003107518030100030396030740804040e03000c1d00d100311400e50b110600a201110340703200d405404 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 793274217 1250 793272967 793272973
    0x1415010e0109262b02120901030b0a120b0a0c0302040e010e1f080c01030c030204063207050c0901170d080406110d0207020906040c2c03150403081006170a0b03 70
    0x825003481503c1d41c207500a0003030303410080140d010304022a50303030300b1041c0f01b40a02d0304100009889580642c0c44808484400b0b09000c030030035900c0320f410007840a0031000341c031202c000c2010400c2840407481414880e04032070808500701810030b40304c0c0b40004414011411401c20403000f00f2800d00f400142101046049607500ba044c03030f1660306003501d03000f00701d11150209040420080c0000d000780292000e40d15940e0791500300449140303200303e07020008071082c6200320380101c2180d0200d0f201002418510300070002402806640018490300c154164004114041045000c3c450741c003000c80c80c070041c600c0d149032520b17142c1c131542091801409040d245103062240010326024001494004c0d140c00341c021544180d080c1d4885007448141c508000c100b0000403000020510140416081721030b620300e90440c20f9001034030b40700c04a0324100b50014420301c40800101088101075111880a501101e00c1000844807803400718064500a18a41e1001d02e081040c000600750441c6070380174140c009001021 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 793275467 1250 793274217 793274233
    0x501050912032808040b0a0c090801061d0a020901050f0a1803210201050603060a020a0c0b01030c170c090f13120f030b0312071704091415010e010926 66
    0x140007840d910f10307980b4102d0050701512a440c0070f0046004911403500304280301200e07039441c030441d0014140c40c403401041c404000fa002c50f40c0e24013441240090725048a5070009410500743e8000184401003d112085004000d00705003a60710a05454404000307035450f03a143d400400b42a90a200356613201610004005c80c00406d000c07000b200805034045c103000d0b510641a110300c0032820703a8001c980541d00740c5e000c4000b03d6100c80b2154010803420044d45010317403a40420741e44440740d40d075081e03000351124041a00280444041c0500784030fa8010180000e000c02070180340401c4541800a060030120020440002d03044c60078420740300d10711a8400c01079145899680c60203841c03c88440d102800180c5001041041070400040c0701d5003219001c140700b420700c0b01c6680c901218400d81c0308683c0900e50140400190304500707008519054041c00151134803440c0c1a1580100e041280c0b0031541041600e2440c0100c2e0b0340c10000c042d003a03d050070540001c5911074000700e4040d031035102070003031140b28600d0 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 793276717 1250 793275467 793275487
    0x305191502030702010b040c020d080c210c04050f09040c0302131b0206090105060a03030c080a090503070f0914070c1704170106081605280b0703020c0a06030e07050105091203 77
    0x80480c1902c1c0045a0801c070803031116004a035101e030060a141e02141c82000480c502001107005000c2c0103041cdc1346125000343c1c1e05d0192990905060b2000c1c006030001040920042c13400048140c441c0105960000c01e034a01500e64590011031480041c1c02211000340c201c149541980002000c0e11794088926849407c0f0b0500070365401e0215070f42c508551a000c0403030381502d4129441000c507030f019075466030005002c2c0c440c107800b988402d58140900540303120025464070148400390040481003814202c092a000d41841030b200c40c420142c150510400c10042c0454000e0440b141c1b0540112008040407034030101c0241342e1040f9000509031050110100c03041a2054100c1c4003030392641d50036100c4010039003190001c0b07030000b8010075030700c011200000410064403450044498903800b82100120341d40c0d003440319155010340c1082d401a00f028000d01c0c0203003080e0903490010002c1e40707400c000780e80c207202005403511014000c29040040004011000703541e402c464440210403281580da42d0b40c1e000c4 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 793277967 1250 793276717 793276721
    0x901030506070e061912060e090604031d0d03030c020114100f09050f04020904050106030f03110610051e270709061707140705101d07030519150203070201 68
    0x36505000103000c14034040c0b05051803000d41e924900361445480b4401d103d20360541b8100350002040c2241607442400207103600c2d1500d80140100e1440b805085541441e0800505185161000f156488140f880c81040303074035070341001a18190145000203428400c00c0d41203001d0503e80907006d002c01c0b041400c0c888847c4018024204540c903400708150601c1c0e903650300c1c00c00d440b400c40d03a08041821031400500981810582a030b48988107600000b81d05459680382c103050030200605400044500841030b00719002081469041124100d0300040c052900700015021904803da800f00702da80e9040c1e00416456100c00300600071081341c08181c0002e1000808140c08038100c0303810000601400c00098500d005003440400754900c410350144a030b941c04030950310b041e400590100b91100070044d1902041040c40700c09969500b0901c0460f86c900140e2101c000a080450103000540200404200041d4000343c4025140004203208261064034200312403034201601030f41c2102800081000a82c03913041d = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 793279217 1250 793277967 793277971
    0x70215010e09160302030601090b211b0910030305180d060b0102190b040b070e060d050f100509010320030f0c0114030c0a03201216020d02030a1803020901030506 71
    0x10310b04442000d003044a0442046050b0310010350590070000052002120580100408880c0603190507800174a04800d8001c0ba2043c801d0003c05800080640040040107815410341110032690017405040035036003204080c00f41e2000809010001804c150540c490301810302000c000141401d00c02d5070079060a901030021601c180780107000d148000750300100315400c4642c1e21a00541e5400195803a95100d00381200060308030b405000c4215504007440c0d442000820284800000201c0c00c2c0c1070400205c880120040d1101c907524514035000e000948480781003d04481e00540e140c0b074010111400a013040501c0c0c1c100b20341500902ea04180650000100994425401c5e43d0b02c0d0707031314051038070074104900055502400c032240802103130501d50300c030781c11170030030004074400b03180c034031442403c2150940d400703901310415400c4100204440060720046a261009860001d00b180c499402030013034a03071080d0f00c10300b07080c461640300c42c0c40700182182441000e9a4082d09008480d41c50382045a60341c801 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 793280467 1250 793279217 793279231
    0x123090a0b031303050a03200d060602060615091504030506190606090501080403142a0a080702012001142d07030f0906020724020705070b03070215010e 67
    0xa10303400181c480c0c0280c007200d2040311110070a0f00c01d1030301542d00300c9099100214210801da11146842541d1060751401008040c0020b110342d41c3e00d6046260034241c40070303940424150340060041140c0c540b00c1c110808080e45089840540d940300301da0010b16110740c070b906014075038800458040100500010914000c0400e0034810840c002c0003a8510203461947c010000019801c070810400d0394022040c884d00a8424140005900c052040100894010b466800c24240e001d40182c030801d0080020240080841ca0180641c091a170b00c41c400c5512500030000c0c10040042600c64a65514149440358848403000074000d030b01e50786036950803820040c1c42c0c0303460400c48551900440490138130756040b0100301c02c460200c2c583c3d404501f900103141075625980155158005d01c00041d40c03903c010b0902a1041030030f80314001703004034980c14903400b45a40c10180ca204101c100c01107400040c00400b00c82a4a1150381d50303940e046401c03400c02a4a1a0120355104810000f00e06200304128007441262 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 793281717 1250 793280467 793280479
    0x1a04140f010903050a110322050f090f0114180c070b16080115031d0303100e010803030109020f0c0a0609050c0102011e0b0d021903020108180c040506012309 69
    0x5100ea100c01d003242c50300c14000300494800c1043c100414018000c82c01002840b10543c3e081c40130101502000600b100702d0100c1001c083d6606002c10301e0500d00c1c512800d4001d07540340c429850000d08221805a040c0504404061656540070f40f0b40e03601401c1c01c288a00222040d19641001c0900b10a41d07000801c044030260310010006092030000301c803001c24410550303115012a440c0103400030381020303192a10000c041e00d80c5a00c00000300d44400e001d1456543c1c00007503980e40390500b20240014103c1d0803010000d2406401000800c40001c01d0b241541c4003443d0040c0d4428200f02c40c58024881c0d0308202c82603018088903142404819413003c441b1030301074010b0340c868a4441004900300d4020404208504204851104c0c0c004440d03031168840b004094007180007143c0d660000340920341892180c040e1403050003014011560f10461450700000c010141802d224801c141007615074081c00038003409039950704002841c2c1d0384100e480500b00d0503440c0310310f1900300310340d4407000b81980b00e6035185010345 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 793282967 1250 793281717 793281733
    0xd03170604330807031b0503060603030a03050702030405041d010b040b010c0f140303010b0c0f0d0503150a031e230a3e011d09131a0414 60
    0x1060034003a18000e14290814144401c56698904286402c0c0d4424039581e02e50070300c800300343c0d84400c003c0d810143d402201d40100b0400454400320201909400c2036000e0f130407900a004150700c0020566401d0341d0182000316203980d581c0c00c120b10314025a03000b03542c000c2c00d0015698030104407542d260b4420340b070b0070300922106280e04280403d03201c2e50800140007402c03001c01d4901103000d10f0860071840d445004079801883c5110348403807868000b81c1050028110000341040e450384200042020b140c0c0410203807074183c002c0301001d0300c1400010841d51100b852401845065034542088001665000000782481e6284462002c4008403918045482c20352141c0c0e4000c0d041032072118502032809245c001c0c140c140e41da42c2c40e4410f60031600c42d6003800702800d2041003840c100112180016a044e6002d010703034001c8003000105070a151080f02e007a1001d860904807095182d18003400d900051412850307220a06516110311031460381203041c810385040ac01484200f1203810b1411030f0303070356003a402c0b01c07556 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 793284217 1250 793282967 793282969
    0x31009110102120405040c02100f0606112b050d090503310510021014060a09021e250f0c0510020c0405070527100203040b030c090307050d031706 64
    0xb00c03d290b11920501200344420811031415410480550f0610300c10b4074980703a06490164251106824805441da840f0b16003880126440341c03c10006011150041c4100b09030300004100c1050025903001d10591440500311541c1c0c0100d04440d000f4403044400c02051030a400d01e60b8a035000302c503095034288044405200030711400c03c006842510603550070b030301c0315240204029039070f180085002c0035400744503410304002c6c030035219a42507981d4001c49004039150003006c100d405107482d0412960316206001100c88081c400d0f03011819104002480b603139034000d507144465504040301d00700c40441e03003005600c800c100348803200c0100b0520401810004941716010010907043340d0620384010303402044640c4880c902500300b5504a40a41027140c5881054950080c062a4100d01c940c0018203406045160b424900302d4900069001c7c030141d428941400748401a5101c050720603180050041001c0a0701c0d0390a100000c01007a008203071142841151901509000c045000b01c0c0000504030300040c05 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 793285467 1250 793284217 793284223
    0x1c18200303040305030904020c0c09090c1003090302061302150c01021b0c010c0609060204051c0b06091e1017071d0c07030804050c220e120313060b031009110102 71
    0xd60b0380c13040c05541040b0030107080c8802908903d505050b21b12900001d0025070311517410f814025410b40b000b0380000d250290a008010001c680a0020140b8200046002c6940891861303003000f03042c09200401e8100e4000111202c8600c1c81c40c560100e0001303030036100204150700500c02440c00c895201c40c1059506900e036150703034003846800d011440d802142d10008086504c0650190311030300d001410240c80380045804400f122261800300d80303107090b13100184082c4400040d884903040781c00d844a46030a6010580054070030329031140000c1504049a007030010f0711f1181c8040c0090303254142c11502c0c070211f00c6503990494820290183c2041c004100d1000240c10304502c205105030103145032240c45d47d000c84032400010002e486031302402a074005180c2c0c0c0d02e01d1402d004411070f40998051040d444081049810101d80c9440d541c0c41100080d150004040c00d03a5400001115204ca16840c24204030025000041007181e1601403e0301d2080b1410300740c3c1c000448070340510704000900240e80d0042e40e13 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 793286717 1250 793285467 793285469
    0x3150106080106320901120902130e01020d09050601050916231603050301050a0f0e0c03070c05070e0a06080114060609030106030501090f02090c07081c1820030304 72
    0x18039950014001a40070740a00003031803200c10400c0403145001c0c401580e96111390315018010400c005030b50841c0f0b6a1200196842c0c40680c1c0081061a280d81d0007c1c1c001005003018158298030307840c01d09900c000c03c8d415621822044071050001010505d0420b403103540034040c05120b15040c4003c10844889004c0d480c20190403910b5402001444068000401041d00000d41400a0401c50035000c41450408180c006101c3d84420f600d83d41041c04204400e0741d00e8001c41554600d18000300080c1c80300084540e0424040341541d907694403040c034101c4451440441c045d0841c8180400044c03070680750a4424801d4031050b80801100e501c5205031804e0340d922600c01c100400600c0c001c19003503c0c00c9030017040c001000030000180e80c1d036a95240c0d800d45180c0d1100303a8400d100070b1900410350510403025a40f00001010451514469503216131b904c0c0103101d41070140e4685003035103200c13803080340c0e20125681444801c40f0f040041a45098041d404c2c04054198040600040c2c2c0c0e078142c180042520 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 793287967 1250 793286717 793286729
    0xf03030708010635090708030703080606070204180c0501030b04022704230a0b09100e1902162a0302040e070906030302070e010e010e04060207032705031501 69
    0x914a0340303003420813540100300d94001013844041c0c0d400100b40088030080440c0c950003104071200700740380c00d0410034146011540f21002c55081008a60000380c0d0109480b607202030b0440d200e980720030860002c1002060b2107081620081c01c000704074828014054880412074600340e905000a014010600003603029461407010290050301004400705484111031400141c054400114140c10302c1203e21101c034401c94170200100d0103824000c0661280c0a040c0380401c0595030f0310000d0510b90068070341c6e01104d1148200b0001024082007038401c103000c00c000c035500303052001d42d154000d14191903290a20b028044982c1201540d000b040f024025006240c440005007040d0403140c6190240310160409483e4600d01d40a107403008541c600042c400c00000c1e501a43c01000b6107401d040c4a0343c1c0131203040e0091060304450b000100680000c454455504c541d02040142c1c40e070204d80340603a0ba2007006050300c040d0381080da071070b400e40b0180c0035102422517208070111084040c41e0b0b0765000510000780140 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 793289217 1250 793287967 793287977
    0x1050c090604050918030d090228180608030711090a0501081c090e0906010302090702191e06240609080c09090a0f03051305040513020f0414180f030307 67
    0x4129502d0404107082c1d000c6405c4c0314603102000c0702644607042da44104903030500d15643d1081481581081c40001400000020200d444060111008008446607111b041a0341c291106240c0848120340c12000041075402c08480d21185146803070010003100c12138084c001c80311000042d04180c40c5000d05412510000080c003d007414811040200b800c2910840080c4a4411000541c207810442454450801d80c03014150341d50543c4100b10102401034040421948607080c40724109880001e1000d107241d2195004d810541c140500c01c80c050b850322800381c10030785450146026211410030440300b01e00c1c40c0340022469a00c522050315008802d0180c84401d030311440c015465410220f103034a401c810070340d0407aa06507055545400c0380414240c000c0740050346c007158400303032007500400303401c090002110240100d01e0040190342e10341e6180311000e88140c0684820b8002e035106c5a011603461860244903107800d20300702000c0700040071003810044403403040c00880720342d291003c0143e0f0b0042815540c2c0c = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 793290467 1250 793289217 793289219
    0xc050105090a0e0408071727040603060e010506010f09060c15060b030c0a0f031b031505100c05121e0309010b060703020d02070614040b0309010609020f0c01050c090604 74
    0x449150700500500d68125014800c003150320107140c03800c24415446480d225030303505000d14114090700c44d41c101c000756440041c4006000303402c8204802c8940201c060120403140090382c000760141080ba4409000780307127880081158900190001c6204007420f0321550400281d1110840d0451020310030400000e4081c0140350001d0a005080054409441001710b800ca455030342c20f41c21680140c9805403129000200164007540104c3c080369202043c0c181080010703280c1c1504043c001c21401c510341015641d04079120924090031410001d080003600490101c07006801c0501050b44014095456201e940400665000c070344045175101e051075036010b0f140310b80103d00c40c401900701402e0003242d5502c0b440007080ca515081d014001c0a4000d40c010a080404548081e00300242e80d003081c0200008401140110b640083c1200c040f1360800000c26a2039440b00183c82c01401a5008124490300004140d02802400b002030580312545a008002c0d07600c42d2a8509810f00c20340d440150020002c0c08 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 793291717 1250 793290467 793290469
    0xe01050f0f190504150e0304030c15050a081003050f0c0a0902090d08071401050c04180506010e2806050c0708030a0c02130915060f0803090d11010207170619090c05 72
    0x8180c000d40720b0007804409015031104202030301c18086c0ba0140c103501c041020024170051644450040c20142141e0701072410200008103d48640301f00b150901c46103c2c04542240e07820f850030360040d5004800e0311070046050385010386650008044c1441420302c2c103404038030f02c01d41e44210341c0b042d10010072030b000c1c007080d035903900040d0707002041c054034083d603e42c50400c03807004280a0140324000b600312496441d4189041c1e054002c41e04082924503600d030070200420350340c1004000910607000c076080560341d03258607002c8940d41c004542c031541c11050b00310000344481e0030801600100300c00c0c40948420946591500e40e0700d014102c10940019480c040101c05070a0000200c10324040140c5c01181800043c0ca550a01c212103c036442c111550f101d50801201042d00c404101a1081c2c002851a004600c8001581e003484508080c0c0340c1c2c03081291548450380200100d42c000e003041110082061020800f41e52a01d000300e484148180e00e1340c0e00416001c07654480e110304554803020120b26030741880 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 793292967 1250 793291717 793291721
    0x7020105010927021c0804080a15090203060406050604060f0e15010f080a020d1410060315120b07091a040e010510120c05090a0906031a0c0d09020d060e01050f0f19 72
    0x4401d81742e049140d001c1c4008910000028405010301d48010440712aa41c607100801100d044042086e487c6401d0440e001654081409038020760006400310f0580c0707071f800008000b00007aa01402484501841c001145c030710fa0f0848600c280031881d100c50702a210340005603100c5040882c9480000c4114002074690a40c0d030380030b00b018038084200025100f150f54684914030105494030040524814402c1040320b1b454011404000158040701030040d03d0f008540b4001d90440c90300914601c0804001007420b48984460300041c42880910584c84516010171a0103034010b0090003000400e080004c130b05428a126403c40340a215030300c0301450f003280040c100041c44480d00c030004029007004452003c0d51091740250262261220014096141d0325003c420300f480b0811b460f040340410420846503c0c024000c0e07420710f03441d80001141c290300f503200203000c680300d00c5801884503151a003250120700d030552207188207500141da8441d45803202203a00740801c408480071741c2d020520040700098190ba039 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 793294217 1250 793292967 793292989
    0x4180c09181e1403271219050d171306093207060c14010908070b240a21082101090603080720090702010501092702 51
    0x410a215520200c580d1000700100000c0ca0b440400568009440144107800710100b046201e414025450800030540d0350500c181e0314058100c0c000c03407074a54500541c86400490044e40814004d80303c0446004180084d1004d031103100b650307548150b4104201c00760103102401c51003c0081c000544540d41c40a243c0d400f161745280460b603650301c49284400050041ca4140e4071202c0444179442c200603404040103140000e01624460f690040008000c1c191300700f0818140d66811140303054110308403060342409803040700700061500030700040007020f1110f41c801f564090000707041d460b081e02c01c00780f141481080300b483e1000e034805140030040200e20b20754001202d000410106251143c203850b210030074181c01c9003400c560b841d2500c1050301c2e0039688001049026080c5001c04200640c03e540303c610242c050800001c01600301c1d400d0380c42c40c42038166441080d045000307045038181e15111034024040c04081c440c0c400c1d0b450030304c1110312042100c4200034203951042255040304031440d400300014401f00c = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 793295467 1250 793294217 793294241
    0x20409060f050a05070216120210110313091a0112020d06031a06030606060c060a0506012c040510050612071416051614010f02030f0a0c0204180c09 65
    0x51403111003420110703400744034407a40341001c00050529118501034100022800140d0000610742007e0203030036541070705407584980503204a03116002c1094280c40554038499621010310010524a040d60098008181607640354181400352065020110580750230003801c00c0e01082040c00c4018001400340e0140c4107111200300041a1135a8986817180e0b01a0200b15084501c0781325010007260741000c001182e0010810341e541450200031a445a854840c05490401c072203860340c0c04150b4580c461850a0b18641c0580034004d110300d00c003446081c0b41e5421a04190003107040500007144500c40040303d07411214050b02c0b071840c0001800740020b20210040c112420b000401907110704008454001c0c0c0302040b819880001d0700042410a189401da803c540031991040d0f10b03900b840401041440001c0000007820018142000900c06034214016500740d81c0c441c40021504000403a03001b039810030b0050096808000141c0b0800303802c400e0f41c8800401a024844143e0200036603021a4003091076441 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 793296717 1250 793295467 793295471
    0x5060913050c04020406180e01080615031e0102030a0c0906020c1314040f2f011803141f14040825082106030c010507030309080406320702040906 64
    0xb00d00040c100e0300170340c01002c00240450210196000c003c2c8010001d081002003a92003589840c5003276a40d8a001000d944004d501e1444001c290384041100700034803040c2c0400d140b0315480240b00d0381e0007500121103401d4003e0811140c180c1d110f008880d65001c0d83c105601034074403294050103020022814040b80410295600390254a05480900c428051031290344810180000c0d41000301c205003080140c81d01402c0c8041400001c109a521100c01015082c280012900c119004002c0141e080d54005400e0381e01c0d50a12a8055002080c180b0b1103100c1240c280c10900203509601040b0742c117001c1a00030380507022010070081071429028010824149541130451142008000e042502c00181180c0e204008103c850449902c3e0340c082001c0b401c0e000d0120b0302032030214002650b90320904c4646040c0440001d0388020325200350010705415400038806580c0f0f036a2080010640004022140c8800c0069100044128050762501d09001a1418200c0c03c008042e0200300c002d012204084034102d0b = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 793297967 1250 793296717 793296733
    0x9090e0c0303031005090907050604090507020c1302211b0f0c070803091507022b020604170d050a08010603050c0c060f012103140a0504030209090c130506091305 71
    0x141c0c0c108010b6101c2c070000c1c1031105243d071425003030044161000d001000030360080c182c2807025848110035a01200c40111300454103446486013641400880b402558000209000b110504a4507030000d0640002c455030540380500c4070f103141c2086000a07644069480c00686141403c80400006041c907003072546001071410a042146600e8480c42c0c0c0c2c010460368002180200c0c55117428008260b48141ea4002c0b40c2c5002c00940c006003596128a20084010100500720018141c981741460300140c2d01a1400350390300e07140e210040c2680b41034045a100c6108d134200e1050700302e2052003500c032804481d4551030f4059003843c000380c000d40001084220307004014459440c40c04410442075002d080f00ba00740034841d5041500f0303d042034800204120400040d40280000281d120000c56080c85107603000e42d4132b4511840081764a807141d1350005c0c0d48040880180005042c010030488200c01041f2045194199051034100580b4800c482c00c60340020841d0010354020b101c090600c040510960a6403000c0f = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 793299217 1250 793297967 793297969
    0x2010e0f0706020105060603150d0507051207080105060d021305041b031a010b040b0a080606040e013b010302010c020103060e010b0a1b0804051504260d080709090e0c 73
    0x244440240300200e60281004120b0950207102d165008070040c0c42161551414021b201e9190304004401406a00c036481c115040c482c00340820320240030001c150700e989000c609406940c030f210394001c264546d403820010590a1400b0854032a1f0190b01030400006030452581540003440000e100365240328134607503c0c0c030407484c00f01e0640028500c104012082111210718070704041e1816003040f04c20203c2004280310100c4500161040c3c2d210300e1070311100d01d07a12607011542901039a407043d03001008003400482c0149100000114200e400c4525441c00076403080300f003d286503e030f080b04540c400854010301c09544120304202c1c2041c010306020400c0c031f075965a00342c030f0a2400d91081d400d03500040707148080c0550044045440c1c00c0c2100c43e0140b6428144c50307000c0b00d1b208511030300b441140315a11446000405405417402482c40d1085e010016543c82c581b21314070b4040b080c100169004050344074901901440c01b960013044140c1c0c41400060800107402c00500d10402000000d1003100c840d0405 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 793300467 1250 793299217 793299223
    0x1050d0209071b03081e0108060c0f09030f06010e07051e160c0303031e02070b2208030a0207141b06180d050309030d230703030e01051e0a02040501020303041202010e 73
    0x122a11a5803990b0b2a0300d0021b0550f080810340c0300c615410f20344801e004110f4014002001034101d20381d03100c4550795141c801d03c00100c3d0300c52100466014092114800c00500d00400d50034100c03544006601003a90721070400b1141442420f8280314540680c0c0b40c81c0347c284040201501d119030140a6107481d140040d240c014901010741d01c1103000940300c5090030b9204403e0048608503009000c1d003075060100d81d584091030944018440b40403415860800242c80321284c050321f9185410070301603070303032800c00c0d4a9001c0a94080700c002d0303400c03a00c0c5190a030603402000428143e0340c44000c1e45c00c048010000b0405c60306a01c2041d59141c8a0746260420a240d52040e00c611072040c860401103580709080002c6c1418000c2403040c0c2c80a1126400400a210b845a105884000041082c41741e4400301842e003034004103100a140d0a22b5842c00041003040107080b0220400402603201944007995001c51030000c1e40700e240903040c016002031000c1030009e590120f0705482e024040c000850700043c0c9011040c5 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 793301717 1250 793300467 793300517
    0xb03040b091f32090d020c0109090b15030906070914010c06090c0801110c100c09030b09030d18030314070212130b28020724360e01050d020907 63
    0x81010f03c04014881229010004444610b28134005803406031081750000e80705040d40c3c031541440a499045161040d510000d03140b4401c070801c00500d44034117180d0440da40d1105c0488850011500908000c44c0007104030100012101d0140d48040f80d41c42c19503240c10140c40c04100460b44040008004614800c00380038952041c0000e180d940d0310f51503407031200c900d4030700c1e14180d01405510f01442c0c8070800d90b0181c00c5005694000643c06010740f51421014038500c500f00c80c0c806000d240001e1140e820b140740741c0500d981ca000f684c3c180900104a80f071400300d284c00f612405c025034084020562000320182c0070700f40141c0000c41b00e130710003507941402d0107055000d0b07031000d0300c43e05046840701d440058010301110191110702c0200f00403820401540081c0f180100301c000031104403510055a24801c0c18601c0c04540391990a41d03600300b041606801c4124004207883c02285021804610142c90444090407a0002130000100005035000d0000480010b4010300801c0b642c0340c1150018180000e50b51 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 793302967 1250 793301717 793301801
    0xf0906010e1306021803030d1a0d0c17030904020a080106080a060e0a090c08030a0e13110702060d0f0c1806050c0a082119050c031506030a150b03040b091f 68
    0x1203202d103404806040c4008809c00090300c1120b141103c0008a001060210151000010710103034410701128850320314054848400d5025000044880049510448241c100c4005480b111440d4480328110820b0342c400d40100c14200c1580d0300061510802074010001c0c0358040c10341c0f00342650b00c070760342d090440d4454218100400d90714840c02116081c030341c0880d8022044004200110b00d00c0c002c90040074440c014010348107580101d200340740089594441d161150055000300440c00d0b4489000d8240c00300d60b84c11000040c6c07041c1d4001100e9000e64121840006010301410351003066603103000c042d412440032849003c08140c0503500940801d008640a030b041141a140e555401800003402c1c0c480003008804440010b00038004072101680f103903500d03090220f94541e2640e0307898003480b000f819401c0701c143c40e001d500c050002e8280d00c040021401a40070300c1d40c00c0c002d50b880c0e455aa0307580841c5840c0c400b806240c0042c410311841c9641c06800d44007041c010500c500740c2614601105100003410013 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 793304217 1250 793302967 793302971
    0x7060506090117100213090507080103121d1005130e011a160f020f060d0f20030103150b130e07050a05011719050f0906010e1306021803030d 62
    0x8821145801c1003070600400c202c0e19091046011481c0180e25900b80150721a0219008542004070215811410380a450310100c200400c1c0b40011000304061801e00c800d490060a428164510505c91201000c44030b050858558000c0900340a0000045000c41140d003005410f20400f429140814905401020b540c035030049070303504020040074080781c8840008084502003118514807411407241116164010030006403410040c0007180d0708042800341d603070f8030500004e034000040d001503000c1070144c04c0582c42009209000040f80d05403076602c0e075031080402420304c010400502c0d401c3d00b4209042d0031441c080345c0e6884504c00320300202e41e600d04401046403900800e20360302d01c04100d060005d0004803440c1401600d840f0000c0c00c03002c500d090500c00c804980001070f8914052910300300540542803020030407440c2022400940041c01d8803c040c043c050344000007005600076034158065407400707020404501040c2c0e01d4400079403140000008189145010071354a40d4107101603c10b201d481a40 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 793305467 1250 793304217 793304221
    0x3040b040c120c0905060310020319050606070203060415021608120f010f15020a020a030f02031908190c0506010b0301150207080a14100f0c0305062d120102070605 72
    0x501c14091258001c1d10710b001807440a40e022820b0152010210b48a202c0000745580320340001c6818149150b4000f19a81d00010038002e241e070340c0068441d0300c2240c0c100d04010710349440b01085841d01c1401001781d81a44414080b07408101c0003d652440c80d8624000180b07420700301e602a0116021940b42941c408e500898a4a03903144280202a44000d0040110146606040b460302e06802c02e4055594a90100c001c401c00707141c000c02c0280340c0790b50014446a03806a403450306001c10940640300b03c1c081d02803050b500a940303820902019115501c40e030118104400d02d00c824051000346221101048000c80c0d11001203401404400d02a041900f46107507a5818280101000e810340c2c11010f04541c04072104002c4500045400c2c05240d5000c01c41c8c458810300101c0051601d081e8120b805440c074901401050010802d911540d25001070707440600981d80d4040401a0540e12725011a81840205519400464080541c1e6a894000602e4525103a14540c103040c00c90700500000c480403959901 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 793306717 1250 793305467 793305473
    0x4a01090b061309211404081b0d03090519050622080c0f04150b0a0201140c12041506090f0207140c010f050c1c23090604061101020705010203040b04 65
    0x9000d03180c02080c0c801403011102954a01c1544003000d0f0800007944d10f01a494000144141913080b0b880e032840b40d006441d40e03140e090175520b405880510f00b11030300e01000b07104440d082102da56030b070594054640f40622481d00d41401810400c004140c09000340c20400400c1507500d0700060400011103820b40395822004413107201450206411400b05603001202036502e40e51034104580b4540d00c01e59020400c22600c558000d04c400c00340c0c0141c002c1e54030116100403070302d5055004011a4100d84003000c02a220320010700d10340d2045600c2c0071884010300e800200031501001e0181d411040f0100000344084c0c0c0c404a40b008c50f90300d08510b20080303400094001c20710007c0b0051003003c9822101a041c0385500100107000e0314a001c04e00c41c20702c00046518441c03c40c0911080c1c408892128050250b023906801c0203001310780913400858001140040c16007403000c0d100035500307500e42c090700d880c2c40c15003410b6050704e0120001c070310410190740070000d1200140081c005903000c0c911038240d604440c02c01e45 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 793307967 1250 793306717 793306729
    0xc0a03031a060a031e051e01060e06070f21030608150c09012015071e1d0d0c0803091e010e09060d050d09094a01090b06 53
    0x80c050000a801c0421559100c0e602d110071500210a00c0c200040ca20b08040d4640a1200f0b104150316141843c2c20108865920760001444e1035041c280501015680c07281030650785196298007264021009005281c00110310320210b0700403c0c007031000e00780c051242341071603180705904030b0300b00001a44442040200f417030200b00c07d0314401c203140244000d500d800d9a41c0070003805254502410464412004850b900d44098065040c841c00c0c0184d49045a24102955210b50150b61f03c8000a0b490f50101c0203010038058001540c10f11560f52403501c201c904603082c0082e4107450f140d83c0c004058a5500300003080b051424009000c104059030721103840404005514400d50340c4807024011052030000d5a1f80e00040388018604122003100481d01d0748004107100c032006050042071441510144280d894003c9108000c850f140308040c44000107111720144005800c0c01c10b030701d01c88548000c0300c59106244051b0001c940b5200c502d045000d0740d0008040c04c0da01d00e090305545a1f00c40e03005100c13a60a0003 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 793309217 1250 793307967 793307981
    0x605010201050f060103110d05070305040c050906010f0f021504050706090b040e1b0c010e1b0d0308040605070203072414090318210c0306100810050c0405060c0a0303 73
    0xd000800036440c01420b041a662402000541016500e8070311201200500c0140d401410b414001008540380504024000744001e441c00e444200d91240c0c0050b46107024600a8480c2e0303010383da0440b94003c0050141c0300d01c101d402810043d8010039940700d504000006c142ca00c640c2c010402040c107185062000740c800c030182c0e0001c2019500c2080b0520800407031a0f41180c00c01c1e022007440f200ea080150000315035000d0f420741820300c0e500b09821041c202ca000203000e400400c503e10f54801e01c0500008001681c3d22801004000c580710350b0002c0d003c80c8040c2d00c41d5500150b80c1c0152442c03d0b9150742c1d001c201c4102c2d4425100c4804000340640c40700c075082c0c0308151000c008042c11304480d0800340142c0ba5a4020f610840301715494540303043d00c29489000704d04a000d503056800030482c81001c1c40031078448441d410030501901c61280086d0b070030354500303110b070b002c03100042c02525142a000004802804004040c0400c03135030304000000b5261650401030111424040203450307041603c0c90020b0075030f120 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 793310467 1250 793309217 793309219
    0x170408011814010b0102031c0612030509090603060610050d0908040e1e04030c0807110a081e011112040f170a030b04140105010e040b04090303020714030c0a0b0c1c0f0605 75
    0x2500840c85a681d0300002207501a80e032801c108c036401c0c000c00414902a01040c0c1100d0541154004d80204040d0088040d10070103400b21104501a51000145a55101c0484807985e011540f160200c107094001d000510071a1200900814044542d40300c1a40680c00b640c018003640c200682040f07031508130b07509146e4905c6200482801181802d4030001c128081c0494083c1c803a00d40092500c2c00c01980301b16585c00d40c1400ba0a008100d81e980980548072a950745e010040e03a260b000e251a0000b00611400316001d40b007540c46410070707951401e200c245440051040300d002030031042c0080411210300d42078581035400048103a45840d4504010b0035103d0007500c1e01e004609210442c1d020303280b1100601d05481c401c0c43c041c07030b498622a0014003d05100d40032a43c0161900b4580d9081c143c2c0760300104a1140110b0500d0801514440c8a82d564030580c1810380c110b0f0040f0750b040000a820003003035a0807100022000f403c241e103420f5401c801500d1000842ea03c5075aa0b1400e09504141d40102c00007018 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 793311717 1250 793310467 793310471
    0x16080f070c0305031f06180902130b0912010f051e0415020903032a0706090b030f07030902030d2001060f050d0212031818060d17040801181401 63
    0x30300090107421245809001001d010000c00054080000d03014030704580c0801c1c00c0c1c1652225070b41e4401500013010300c01441c03002000c91801003284c1203203000325001c543d0b0109040c4940361800241c100a0f8000c1c0180681c4680d800e41e40a01151090042c4040081c406000140c01c0c14a0079590014040a84c01c081e049401c181c100000700b940040308804003400d00b034025946000d41d07000a8254447c106101800708154804c002080c21007401e10a0784c880401c0445100981314401035824000520070742d00c9402c0c04200003182455013401c0a030b000390982c10049a44e02d0075a00203420420b0301002c600c001641800d00320008440800d040304074040c0364000700003003030401541200e5095240604d03402450004100005c54603003281d440c4440803810152a01c031740d0380901103c0703018007c400051050b480d02a01c06459540b207a001801060f00500400800c3d001760381d06950354070032228018031300406200004811000380079110100328100c101100400d4079152401c4441c0164915400683c = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 793312967 1250 793311717 793311721
    0x40f030c121d0f030a0f0c120515010602011b030b0102010b090a020d2901030510091118010914010e150c0c0310020304022202040305101b021501051207080616080f 72
    0x18a020691100968006c5c0301c80b80d0042441c00c029041c0d600f10742c007440740001e12600304418800d02045118004944400009050f6603c44c000c90985401351031941d4010070b001860324156000e68010080104103000101e0721601f07500004400d20001c442d0a00f041d6000601d0204001c224400c0601c48030100e1016581540fa03280d5500d090484802c03014145582c2d031000c50440316043c40d01c03038000d25090500303002c40800f00c03050b001c05e0f0b0800001001c0340c43c140d200b442c50a42c0510070300c5065a8440a035050441000e40045481161002d280c6401c1802d03031302c200044e0003890340144620310300c0f80018180340004400f810718055a40343e9940d5440e10600034040107a0b22524100c00a01589882030301d541c1440d400f401c0203104a90000f0f0507403055610b0703090030200720380240320041a420300c01d01200fa0074401c1a40c80709810f60582e891050301e1030060003245840340c48c901007400240226820305441d03845541c038205082c1d8003ca508062a0b10240b44c02e40e10070300780e40d40400c0c4124803104038 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 793314217 1250 793312967 793312969
    0x60801050d030e0d150b03210a0309021e1806090c0a180312300902060c1b0a05030a031218020315040b01080a0506040b0415090309060f03020c06040f030c121d0f 71
    0x482394049410121030030001d48011098447d402040f480c603002030840444a42296aa01b03088035409881c5000e14464500c2c6900040715441061040b000504400e00554a103c81521603a00100d2800c00f4080c0003400585000b410711401405903108200c04040100b0f9070a014082d200e81d11090b1702a00f40e0f52440c60030742d16100102c1d214101c41d50310007150f01c290030b200040c1c860041a41000302031040003c005141020034200101c201c80565803100c0b104d445409054456082100140104101e014064000807042e808250882103c0c40c0f90004c20501d580001e04105140303030f10303445114101080c00140614801c0e10790041c400240144805025569859200c4800600c090112a0300e28000b07030502c81d00161008031520946020403000c03c282c500500319102034010200020b0301050344502080c041c2c82143d0303000c0c500c1401041c66648a40d203440c0e0000c07160b003003102084011141903001800c4244141e04490366511514600e86091700034068070304189000610954000c5010105 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 793315467 1250 793314217 793314253
    0x1509020a0e0f0f0910061e05090f0a0906060518030102090306010311060f04090c0815281e080c04060e0c1315170f01060801050d030e0d150b03 63
    0x40c10a09071140e4410b09841c400094a0300300682c0856084000c100420003000702c07840f86207007600d03015211041c15601d5600075400303c00f51701c00500003040080011304814079003c1800d04517240010054010241c07140030483c240ea03510b0344103a010590100e010b1910300c445004022000c10240c000711b00382002000002e41c2ca00e010701c0003400000006110400c503445400441d108407e4481c1101d44e9140c1c1d50f19580c004080b65000c6100040304440490980101850a0401c000d401001400d07124800309615651004500b2880308410144030001490100341c40c140707212000c0c2030501c4403180e18100c0750700d040031801c8050030301c00c038580f18090009050100006802c104201d03003050b03c6040c0f4104643d005260b503013024891440e00c0c114002c0340c1d5403000c2d02e62800382c0c080110f5042511940749520807000d0a00811000c24181c000502c4103050403901d05a607680689461184031401d140072810417000c80c0415985151944e5045c000d210280c0100d4032540d00c10b80003440d000002d0300300458 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 793316717 1250 793315467 793315487
    0x40302150f040b0c0f03040b070605060f031011070f05010b0a09020703140307020f100501050414010302150901021903200f0a02010e13050a020c0f1506010e12030c011509020a 77
    0x3003c1c201c04a5200b55050f8104074099442c817203134046942d01ca0b118601c1f0046a0094034080302c01c1c40c10400000c0c2c00e400c0c54042e0317080442e4050300074215412465503c1c00600008100c03105a10340c240b00600c0402c0300b641e0503425080c0a03000001c0d07000f00200c10700c030070140f40c0d81091200500410035000003950001c00382c68031b54642212140c03652034070302c401c0f0b003041542d91a05020b4840d140e074580003842039a114604071081114200000000d40070300c1c80121509200c003039030001403400440704058801c0c0080c01481c0d01403065407490741e020130030412501d9200e4010b134006031b900240098102112001c1a401c0d461a4008000021034211080c0c0c0d03a03081188002d0400402c04a038240a4559070701c1c01c11a003c0c074040510891800d24801e4000350440c040d48051845949280d005200005c2074403484c40340720402010250750303404010341d0408000344030070750018070050203903104210520240c44850323580c3c2c0010850740c8030190081c81c0309881d40c0060b00032600c1000303045200c80c0c114030519 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 793317967 1250 793316717 793316729
    0x1510020d0f0f0c0f110109060309150b0d14100f022a070807060203070c0e0f0f22080d0509063303031303120203030105010806091317040302150f04 65
    0xc0582c0340d40b200d08440803a6a80001000b030030b00e440031102084882d16603110b600c082a60f5445240766110f1003142903882d5080c0c05400c0c41d80c0d048200168071515002400f405002801000f800030b11a6200e03480070b4601508904035410030401c95409424031b0140ba181e845c0c0307064040d401c014820320555015000c015400004144200203102100007d10100008141304030a50703c50720341ea5074004c6c3d01e82c0d2143c981104c251022080101e0445185406107005003903414407010b4640da0f90b03a6411040c08058001200104401c06404211020002203003006100f10602d64803024004020010744d10060200c4040350080303c10441846012500111103820700e50652405c401447c0c94104010f00c0c2c20203064060000050003400b44000089401c00c80384510170401081d011074030b04a03101d00083c000c060000d0040004a8107500e46040c00a41140402c9800c0d080310006544e03100c40850391070401e0041100108040056261001e19401654401081585440b40030f80c00f1103094480c5000705 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 793319217 1250 793317967 793317977
    0xf0f01051b07060f14040602070506070c0f0603141302150f04050d030c020109081204060509031f050910050c0f0703111002030f061c03030b010e04051510020d0f 71
    0x2103801c04030000301ca855030203090400d480056071150300080600c0c1d8003083c940d02090341003001c11015070301001218111106540981411760404d02000455481084d09440c462080680400c0810b40101c84000822440d2030002c1e08039072040c0a50308140000f064882c51008051030480135071240c40b07950402c80c000c131481655501144080b081c1900694000c0c07a04604078106800816400506102941c3e000740c031a0300c000303a42d070b40645030350740c64030784211081031000d12040001c280518040c04200c0001415203a10110241c0c2d080440d5204e4501c0181c055201c201380701c050507041c4103803d40b20054000500041c41e00a103030801ca80b0454a1140701d0700310000c6c040c400e05d031146040701640210704054035841081060124082d400a13209104044c103100041826450300c0c1584012220441c03030745414400b41074809400030016000089e0500140e200440035076900c511030715100e800621029a4010707501010b100806c024400038900f554011011401c0090300b112141d50054003520f44 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 793320467 1250 793319217 793319227
    0xa030c020913140a06050903030103170708040b03100302101b11040e030c060403030b04090b0711010e03040f0819080708130e040809040e0303011206050a0e03130807050f0f0105 78
    0x440030b03142040c0400989030038603050090500d424049407003008107000385014003180d101c524406440c0c0c0b0080c480240780c8a1500704006503520140040d19215000b4002e0506190b82c4d0402134060354012030b81000b89444002d0140110700d1304540c14009514689000b02010600c000c00f16007c1c02602800341c862548200806499515900088120f0700090103403904c41420400c0256035613003d0360100c0200342886029407040c00c01f4440d9400c00c541010a150140c1c40343c1d44d095819201410071480c00355240c5002420901040000300010b046803042210280c0c82c1021003405c121441d4845842c240c010360101c008500040c0948002e1a00880090360f01c4030001e6040015810a41c8452114181030f001c00040c8aa90806003400c4035003034906000c04480d5848540d00ca2009015030040c030825010f140001c103c41354403290784440030100024904185514040c43c40d0030001144100c1210701c0414440c0280c00e01101004082c01d44442c001c4030788901c00111250140e40c03146040000100f5 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 793321717 1250 793320467 793320481
    0x605040b1e0c070605120f060f060a11010606020327030604150207050d030603051506031c030905030415090602030306010f0c030509090406060617040804120f082a0a030c0209 77
    0x8803030010302da00c421901002d984800103480c83e0041a10081001450781c000f41707039101c0d054000e5201d0358005044404074681007003041403e4000e5450740f0f00b003007400c09401050304000d01c200d00c05449280c0007181c803591403100f40000c4007900014141e90442e0300c03420354102d45001800c0d42d0460790046200d40050070302d41d0480002e0107000b40240a40c41828054032415400d940081c0030340b03001c0d4040c1d072b51244202900c004480c81c20344003a034266000c120780d002c0c842c2c171542076401600c00610b00851185100c0d00c40074910303080b50300800030f41481c00c50035803004c030703000030a040080c111070018501b180741000010741800d08440e500344c01d04c541c1103401410184514100c8a1050005000a44134101400d140004001500854002c100800b08043d02c07034103540740140c8510350101045103854200240c6812058204808540d240080d00903900010f1640d00a40100f141d070309507504195038181d00c04010035600c5542c082c21a04400f5012001c00c4e88403002803034131070701580d461003a6100d00d0 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 793322967 1250 793321717 793321777
    0x61806030601121b120912030e1f020a030b1008070309080c010f090308090a0f06092d02010806060f0307230a030e0d14160201030906050112020a0605040b 68
    0x40081d001091400d079000b04d0401c015840e1006444040d6168481480d01c070755440c04031142d62030003401e4a01d14a0200c80c1851194115800b921000d405a42408036210360000e0310380c48aa048010341900414a00d0100354140303e414541c0c0800c4030503220b81503c011006c3c1050202400130f10400d03407141c2c400401c1c0701c6205d00300d403018203c031002042a008202c2c0440000c003d40c610440004000b180491000980002c050503056040b00103001c2000c3c460303680c0002415035020454810405020086000c091403400f0380e108089014440220714141c400103261010007070040f84643d10601942c5450380c084000d4aa02c41543c3c10084000055080d650194055002e1034840300c0130005424601d199040d04030b50100c00000c41101c64005c3c0103241607480400396481800d02c88801c1c0001100e025604044134110390040c18001500b100a48440050707400980120036003080728681c800450030701c018100020945490001c2c102403d0440a003a14410003c00c0101c074001805103103186c0c0715013 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 793324217 1250 793322967 793322987
    0xf030e01050405090106051c020921010b1801030501050f040b0c030403090812070b10062a0c270c120b150d060e0a0b0609040903030f060e090c061806030601 69
    0x281010200d40e1b44110040440d8040418540352585200b1070041c088507900a5079058a0010000d01c0240f505900d400032005100144007415902d03900d0075016515038245c10554141032091048842d0f0460074082d00b55a005080300c1533210481d01000081540107200a4001942414099070b944490400302d4401f07080750070080c2039003d240b852100104030140104056407041c03440214503600c0ca1030200b0356110500c01c120110341c0360f1040004030f00340401c20211085113901141c80001d516180c400702d1103040e400442079014081c00c00c1c00b103c0d0300000d2640f82e500703d14605014a001c00440140100c8541004a5446403220005001c65070f400c0500782100d80d00c9c0c40303815118a10341c029007000d0315852080080303602000300411001d0b10540100350381c101d00941058503009915003408006d100c6044150101580d9581c403030b0300d0b1070b260b008980040942d24480032180c00c0c10b40240342028400c000c0c152003044200701d00201c204c3c0304915040e0584003220119107075a103981c010398080c1c0318 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 793325467 1250 793324217 793324219
    0x4020d06140603160f0504050405120414011b210e042301050d0f080a031e20040e0105120102091914010809100e01060b0f030f0a05040f030e01050405 66
    0x7030540240c05580040c0d041e6108810803001c0302c4541819440d10650920540a10464001a81c0341441241015000540c000b44503000304d8602400740c084020054019822115a6100422440d60b5075a440559030710070903580855800300380102d68800b00b20094003910101c2402003010540d0080d4003c081c56260b0990150003030044000b4550000701000701581d47e1021400004004030b42e5060001c41214a0b030307401b4000c052562007503140c13404a90413529101e4100f684600791180505260000110484032512010902102d0704d000000300351440120250b11080c144000c1200344600030810b41103400c103035071140710107000030700d401d0292003802421900b042c0b54014485280035058080b10858900c0e004414050010030f004440444040c3c4110000354069000c509241c03000354880c8a4204503a40001480c6a43d41c14071401500005400d41800308080100031103580114102c66100c0c024000c00c00c40c601e000d030341c2c180750400311040c050204038444200c2c0000c0e9000e90b00b210b0142c80 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 793326717 1250 793325467 793325471
    0x304050a060305010e130308040308041707060917030c071704120503030906060607151a030f010f0f060303021510091b0f0e0307150921021207031a04020d06 69
    0x81c40d1200900508028807680e0002c40c45080050f41010304504078181c1c503a415541d0320141c1c0c0300c60f02d00310341c0740c0c001038000d440c07011030343c0200f100c1c0007030420051140a00c22100401e07041641d0800c0b20420300301007503948030700e00c04204204202406500f100d10850740100a10a405403190040f001c50149070001c0d00d55191600448007882400405544511840c5003261000e68408061200034020014010114611b00c0032680300b840e0990025000e42007880f0b944061030a1100010385024050b00075501d203a55038003640005024180506100c0c003013038040034014945141e80003980c50075035024004130303100d0b660b006c070303c1d010240c4030502e005241e40c180521425024544009113402c29014103c00708010110390744000d4042c40700c5080d00c102c0100074010541c58036016088510766004001d003044010070010810076040340c8802c9410140001c607000d645241d105001e6110101441c0e4540c03a0b002c07440800000e07101a140000c40c00c01802e002e20b184c0c540c1d20106070469a0040c0042c2201c0c = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 793327967 1250 793326717 793326719
    0x10f02030a14071419030905011e0b400c020606130b032e0504050109020108011a16060e0d0e0f04020a120c1b11030106090203061309050304050a 64
    0x169500700780000c2004030303280d201c55103514900762000304604d101ca4198420600101c4509594030103e100004494100850180c40556803d8210b801095081c501d19014100c0c2d044803070494461212204010303a0840e00104c03051010000d03654403056040004081c4003280e5406207503403a9a090342e405e0000d01400712107078111000c0e488000840703070517000700c3c1c01003091010245e070f41c06503080719840540036220f0003403401046100c0e49a14408040880300d90303104e500645120303108140c400d500600001491140c0b82c400102141c0d01070744144a0341883c008070740400d101031411030f0240d60b200340b0741e008150003d190403400f800c5498416102c90180f581130101d6180c0146004800100440d00080d100c4051020401240204850a0300049100c0da80343c01d60601380d4040d800380e0440b0306044c20303008c2885414100416942000b03d845031905111a003150801340034030000360010342800c0d4294076004010408242d000c5d10600300550b102e0350070400f400814021a4054480903103442412 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 793329217 1250 793327967 793327981
    0x91a090a0b0106091e030f02040c02031b0a17030610030c091508060301050c0f0f1c020f0a080a0902090624030108251a03150402160209180c060c010f0203 68
    0x4031100b4803400c80e4600d01c0301180c2c02d110f00e90040e0341046d0303a480410118407500e141c0a0200424004c141081540310800840c0c3e0180751205805420750701c804021b1542e6512403800700241012583c10114840e07040c01400f406540c0c4804500c082e001c1460b0020b141c032062482101c6148940d800b180350a803842074403551542d40300402a1041d4001d41c000c1c0180c0d201c2d1741c801006841707102645015503009000000c0c030301c210301c00141550781c0d41d6100244403080050040b8100c0c0c2c00240c0c02c43c4102c40000740170707007402d401c130300507642c08410744908000c003580316004100b811100030049442244802000841c0d40301581d80b00c0440d140114079640c4940c1c4550f0040d07950f013a81c0b01600d4442a0780c02a1807807000b0116490780684950700504d095400c40d10810181e250030240c9048c00d000f00c03505004940d900c5910283c05404c0003421019082d541c0ca0040c0921041e019140c90300181400f15203074030600001440030307403000b01650200d58411105010900400036007140210003400013051002c5 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 793330467 1250 793329217 793329227
    0xa030203040506091204140a08030a03020c1b0d030c030309050d080601141c1d010920100905060901020c030109050312251803080d061701091a090a0b0106 68
    0xc6640702c1c8049030415102e40c2809907954206800d0001400f10800c414400040500140c0a81600250440d0001516070130014290742000c4054400664041040301c50303a00308001141c8622150385045c411905804081040380c040294080d0610408108035403c2600c2a4030540013030350040191040d402c25902c0041c42c100301650400e0000c3c0e040c07840110b1803c044002c071000f0420030111510000c00340301d96000070b055200703001d00c1d6412217445540c240400a0003900506846050102d2101d614583c44a8408555149081c0111a030301c100c04442600880d03584107a030310850b5516290030b00400102c1c502408801980c0d09542030411510403c200000079069003c114003a079400c940e0b841044080342c00300d030706190480d0504429809117071801f03004400d45584801700142c0149849882d101503550100c00c0440d08665504401c00031401c411407030411141d03510000b803000c44a40d440d0b0860700285200f0003110100355002054940d04204442120309510406c0d02d1a95a520700b8003400c = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 793331717 1250 793330467 793330471
    0x61503030906021f0509070308040308270306040335011508090a0b0405031e0310050306010f0513150816060206060d0f1b09150801020f040b0c0703080a030203 70
    0x1020070001400860307010b0000c42c2034903840c070035801e00d500c940a80302450030182034090200070042c040e960f00400400c00c418010400340d07010b11540c2d5aa00303007079030b06651442070b0b21070b01007404000c1a41100c1d2a58011500030741107071f09031509070400300700c580c450300340402ea07107400200040d950004101e18003000c100080c125261041c16101b6411011800d844c8070404858000c8143c0117044007e0000f00c8011955801501038800c0300e0800f003609004d0a12070b400d801000c020b160000c0308200602030740b0b0140b500546000d801905440d450410100c0391040306000d142d00c01e5401000714251072a40e580100e501070f0b203100304681d00a40d0303005200d407200c0f0003440030151608450800b162040c00020954081c61000d80400384480f040c0c0c4408603100071b8840e085640707400302074080004500d130035000000741c403404800150308201c209095141c2000c60f4007282d0f4503401400b0540d032244040382601d0031210b000b0911036803200950b00b068144111034100801862000c101409000e070b040d40914 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 793332967 1250 793331717 793331723
    0x9020f04090807150e0706030e060703090803130f02190513140402090c09040e060a0e060f01140a0e0109020909010501030b0d1b0308041514180616061503 68
    0x2200009109000948600e080301a150040030008080090111403a1110080b02e8040c0050941001074500b070400c1e00961040000039180c180207020040103010305034000c1c4242c1010040c0d103159540300305c40c0f400001d1459001a000031692000d2100503542108407542c0201004a80c6004582c0040320b01840e001d2a030084001681119000d06a8407406c43c3d088090040c0d100c02da541c5908000d90244002c201080c2000180b207070220a460f00e000e1580603405140c080d064900c0c10013440c5080700c192880500782c0d030b482101444003409104d02910f0544500c180003000c500a40c2001c240d030307180c0560185281e91094000010001e1a0381c2c003405000c0011160f45802d030341d0b120011000c1e540d03010011740d4448002c044841c0042c80280f4114540340e402c00100d44440c0c0d5030307254080c541e0030543c402142414080d1003402c005502001c0307a007661a4180741070b4204581d094210306c02c505501c810074001c070b50010b036008034160070641074413459a20003800d02411602c40311a200d03800c4140f0040b = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 793334217 1250 793332967 793332979
    0x121b061803030103060207060e03130503190c051203120108010605040c05040501170603240a050a0903050720131508071805132f01020703030507151e0902 68
    0x40350345030004016940c03058801030000d600b10f90a540703c04e0000e511802040310801c0d40c402d1054900c3c0c500740003078a4446d0210f000481410301e050140342c144002d05041000320b109090150001400c114205000d8460070749040c00c5101e1203060b41461445902c410349c0101e50140c00010f2480d40541148090380c205480c10b1050500a20083d10117005902449001c5822012020001c16403140c555612690040c2140c051602004451035101071400082400042000412400000038002c0c960030004c2c03690104003031849070b10020f10600a00300f000b4446021100c40340340d80e41a0384100c01d42c0c12001010319000c0208803440c407001f444410000410084007642c0001e554030003060301c404039800c2503101a600c0c2d04030b01401004104c01056114034000700d5004001191007100d07403410160070441c0588034a0381c0b0358101448002226080c904542c401c8106100096110040e00c1c4900d62213082481201569440d1901402442c10f00345002e21012400c40469107aa0700f14854082c000e03603030 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 793335467 1250 793334217 793334221
    0xa080a2405090f240a090528110607030c0314130f0e18060c13090c05030906010909050a02010c061e020a090501110312130f0f0605010b090120121b06 66
    0x580c4013410740e400c0b05440f2400080003605617821504810301a07071203031007501e00c0495540d0f00d448000300040100072465403004103e90400006800c000f410150803200541064640d80c0d00030003206000c84002c0400c0302e01894044d01010610541e8502c951454500b00340b1034031103040c2110003580e40f1074a124440000c0100b00d06101014150040381024030141c01503546405008809900103000140900c000c0e400009070308805204154018600d030381c030326a4908004110b18074008068108035289494049206e00003407000802c0c0c0c40803503083c00c14102c003203410300b4040d0003090782d900f01e20b00b1880004651805614554010b1400c00d15546614a613140c84000440e031140e00201c00c0200340d4000c00400c1a5030480e17642c000d1744044107041a011150007a0f580c1b0b000112401012501c1040003200d550401c039103801018090140010760505150130400020802d100500ca01030b005071700880d03840149407050100421400b03404580e03e03568404400000b03040d5408210401d803500503100 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 793336717 1250 793335467 793335493
    0x20414040203060c03101a2a061b07080c2521060213080a0c05060a0c020f03010204050409030809120304080307050c0c040c020102030403020c0a080a2405090f 70
    0x20103006540140040100c0c0d82c44805074106540050300f421000728040600240315150340c41c9100c0000719503002c0030f44822000100070806c40341000d400302000c690101e98900c4150004085230301603034006400b26165449460391486200d0500060a03902001580d00442d0350006441e4510212036403190341300505660610980c03020902850000e080e242c0d10b4a41130724010303104c04613890f00a00c001031805e440031601e02842101503003d003065400504196042c0320901054100a00302590f0b100d103004900900100f030040306d44002480341c02a21100c0425450960580f805004050004c2250014604000e04141c404456881c4030b4440c10683c50400620a403d03203004030343c4050464119140d041c0300703480c903420020890000f4802c981a00e080d6640300e0051901c4d078085500011394905290500a00f88218800c0050280808d60300070002e120002030f82407000c54120862210048010081c0000b4514110f84513081c00d04210601c00ba9000102e001650b91050004881011400075 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 793337967 1250 793336717 793336751
    0x150a1103090d17010b07030e032b11030a05030c0d09050d050714010209150a0e130e061303090911070c1d15010504140d05070f0f0812161e0305070204 66
    0x1009038005c00001740002c0d000a40a4100d5035001d0900405940c42c40c2080344000e40f500b00402100410303520000c00d420355442d00300f1910798aa04040c4040c601c0c215101c8406085884007401c10419600c0005664041060f694082007c00d40d01c00203440d450030507283d0080c40303901704210580f00640c649130004606e8005100722042c5000181c4003451242249030070181e00c1d00410005801e2040c1540101010b56400c1600c50307980b01201d100052080405d403d4034030f0900018041c0c507a01408a400d400401e8000034004110741403500f001c00c0301030b031585101c0039078010080c008004e04106840482c0c01d0001c12102540c0095411120131196188080e0900c04512250002d0114004100901c8018402c02c000784800078040d040d0994136025558162520740d0940c051002d810008800f40030164403111124010813107030b4010407200d83c4102c0704408900c10b160a510174040140105000c001180c003c1003c1002000c10744501c400150030302038103035442080304a101c5d510b02030040600340100 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 793339217 1250 793337967 793337969
    0xf0f0c0305060a090b12030f03070e01080702070b0a0207080f070e06090106080c0706091a10060908100213080d0903030905040e0a0f0501020904091110050c150a1103090d1701 77
    0x5014840851800c1300c0c0c4002460403140d20794008803d080c0c0b04508074002c00041c2040845100001c2d034034501038800821a240120300941000481d00a0001182d0f0015000040d20700c00c1004598a10501d03c007a4a00a81c6a01c00f502c039004280703440f1490000481c0f64003c658143c1c240c800c0f15520042040455502401160041000729000c6020031500c107029040d043d03c2840000f5100455494901e40c40c3c1d401d40031800c0d410044e2080144022540c1400c01c010725890070042e440509002c60346032550580306400f5016517022458014030746041101d100200707105425100405501c200041c803017070540c041600881c0341c0b0344000131141403520500403c1640700010b040400342907516540c030303100c240400303491641d002d021500b81c0741d5462084400349441400210781c0c840240b801d00c0031a08104100900380f00c07081c0320349040282c0c0030844041030a003401060700c2d660349100c441401081e1910101000c0800402003050b1107800107504815248030780c940035900b8507520308510515500b = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 793340467 1250 793339217 793339219
    0x602070b1603120501030b0402130e0a08090d020907020604060b0609010905040b21070302180403170705040e0f240f040207020d0506040303060617370f0f0c030506 72
    0x820104502212100c650042580b1920b0311000310024000f0400549000303030410b4581c4000f6906010842c5094040701e07402da01e000c00d040c0491213070004102d458604081e400382c130004000461044c141da409000c09481e660041c02c0c1d200d241041c402c002c1d40c0e800104d80403210b803031074840300005500d40002070ba0b01800c0e05039242e24406d402c100c01c0c0000303072034044420380c0c002c104413412030b9104a00072381c3d0210b5507a100004040003443c7d401000103190000104090446040c1706200120b544030249100c42c60740d101c05441f0303a03140e04404480c2403041340d0041c60b8403d0040180300e110a0201c44090003010300c0b03400464440c800900c100c2405030112182039012155010300c40c09410b03d900030300002c034002001038046c00415141c40741041c10460341140040da40c0c0308203006680d00415540c800007004900d42d90070b4078042d1f107002c3c0300040c482201b0005101d00031290050313a180c1d89a141d181002d0780014408070041c00000000b034528669a150b100341481040500940b003441010f200d048 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 793341717 1250 793340467 793340489
    0x7050a0312200c030d1d0106060302160b06150705011b020c101b05031927050103052e170d1b08130810110f0a031e1404020307060207 59
    0x51521a8125030340f21031040000340c0000d02c40340448030340b68401d5850701038501e1065003001d4041100182103030710031340110003494810701100d20210055106a194283c1c0308200c2d00080d1105070000d41c001c00a031a441036038520014507001040780c10340010a0b005403490319850008030042060740c82d104501c184c2c80e04402d10400404013944256032910421242074020390301d480c0192641c600710387c40f04044500e860b03081c005000b441540f0001400501012030f40504902d0190002c406a0300028480d05040549840c04601200110f01d14540d03850f00118403081407840c880503034140300c4024400c56030060b1a22a0b10303d4184130225494218408a5a800c50046145000350b111030400613010b8405890901c1ba42001c802c0d8000340c0710140840c04010302c1a9080140894160340058085683e24a002d0014070010400d480603100501c060341408900031410114800b087e070181c108a11440b41003910300034132007140d181a41d0141c0d00035003e80d41e0382da45070b00c010f903940e550a200c0c00305510 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 793342967 1250 793341717 793341761
    0x114040c03060501211503030203120711070b0f0405040216170c100e03160b091b0d03030b12032b151806090507082212030b03100207050a0312 63
    0x40c6810390745040388000030100017003691b000e94082d034400074550003c801507880000e48140f81901c05403200c0c0e22503c40e00d0807001c5d600201d01c01c3d513100c6041c3e102c0d2a59154010409103500141141510050803004d0001c540380c6407c0098500548141102550034407241d414030070701d4505540843e0500004013000704046200c0000f184001d018145c01104a40001d118050300300d8801d2007084e540c3c5012360b54804413420480030316401c1020300001c07051820f08007511010152150301c2d120040760740604002030118402c1c0301160010220110403001800005001d0214003c030704014040c140010850050703080c2840882d40c00c640b5034401051914803203032000c002c08030490001c4082944640c10100350f5a035a401c60100341c45017603078501c0202d03c0400070007051081c0068020620020f6500325440f00302c89491303114002e408164103078209070311252201e115403010004491002c507000f10443d900c00c0c3c1c600f070964440201490440014000e101c81960f260414080c113203481c0ca04d040402801 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 793344217 1250 793342967 793342997
    0xd030309260313020406120f0b010608090d2109060c0f140301030b040510050a0504140d1d0d0f0f0201111c0c0c050d03020c0907110601090b010306030b0114040c03060501 75
    0x2140e41c40c3c4100d0b0f1194031454007068034a001c41d2500c2d4620b10034452041111240e2802c1098400c058100c801000340102c1086600340300040c8106002d20f2605004d02480c40a085010380007020400c1c0c650304a040181c00c00401586030f210903180c500a0b03031403446442440d9401c0710002c0b4040145600c540f1f05000501c003055081c2800c50b0404d10030b100300c3d414014400b800c0000d03220126501c215090b501e10800060000e03c0340c213600050f00130400707042202c41c001d002501c2c400d0301b011103070b000885001c503c00c0d140e00c845900044494000a0700c0e2030440d003514001541510300c030300480c0020087c9040340d282c000c0001d040c076100b42040d02120300301c00032518220f98180202d2015203400c01e00000000301c41d240c804d1000010380c0258058662507074039409210343d0000c082d0443c0308001800201b20441c110204000b41581d943c1c2d40007098540d9580e0040b0048c00c1c0c0e9030400781407200e02c80000591002c01c141e8045070000c00340d0381440702c91213580701901141e0b018480c442c00b04210318180980 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 793345323 1106 793344217 793344241
    0x60a0902190c0c050d1110020304051003090602070c06030b040c0509011422170f0a020a172b020c030705030d05030c090d0303092603 59
    0x10380300424950780c52505400c44108100704503112200304000b50301500d8801000028401e01d01c25001382481d4001d0142d010780c0c2c034407480f601c05400000c14000b0040d181220070041001d00a549003a030240c003d0301e4031543c100d500315401c00c10300b0001a59030b031140e07015140507500041d842c0080c005000480f4090701b06142400700902540b40d031070381c0c0043e00d4071000303c0340d013005900c98ad03440c0458107a9845000c06000d64043e4210040364960070b03100009083c1e411601203804100700b0030415500e078401298040e4100c2c804c0482030081100381d0403122108141030040b180c0c691700d5030729924641e4620320040d100e410040403500301304660402c020b02c0c041d0800c03005400403500d804006a500c0c007100003100c0510002100190203084520700b076507040705010300416551212490000c008101021040b01c50480c525900b40311020035401036014420000501c13032940c0c0780c803600c0440d = true := by decide +kernel

theorem cover : BRFrame.Cov 793165467 793345323 := by
  have h0 := BRFrame.cov_init 793165467
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793165467 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793165467 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793165467 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793165467 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793165467 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793165467 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793165467 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793165467 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793165467 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793165467 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793165467 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793165467 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793165467 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793165467 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793165467 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793165467 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793165467 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793165467 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793165467 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793165467 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793165467 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793165467 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793165467 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793165467 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793165467 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793165467 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793165467 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793165467 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793165467 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793165467 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793165467 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793165467 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793165467 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793165467 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793165467 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793165467 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793165467 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793165467 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793165467 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793165467 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793165467 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793165467 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793165467 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793165467 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793165467 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793165467 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793165467 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793165467 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793165467 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793165467 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793165467 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793165467 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793165467 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793165467 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793165467 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793165467 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793165467 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793165467 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793165467 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793165467 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793165467 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793165467 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793165467 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793165467 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793165467 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793165467 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793165467 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793165467 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793165467 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793165467 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793165467 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793165467 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793165467 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793165467 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793165467 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793165467 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793165467 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793165467 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793165467 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793165467 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793165467 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793165467 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793165467 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793165467 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793165467 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793165467 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793165467 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793165467 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793165467 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793165467 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793165467 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793165467 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793165467 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793165467 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793165467 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793165467 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793165467 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793165467 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793165467 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793165467 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793165467 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793165467 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793165467 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793165467 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793165467 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793165467 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793165467 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793165467 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793165467 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793165467 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793165467 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793165467 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793165467 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793165467 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793165467 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793165467 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793165467 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793165467 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793165467 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793165467 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793165467 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793165467 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793165467 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793165467 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793165467 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793165467 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793165467 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793165467 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793165467 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793165467 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793165467 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793165467 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793165467 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793165467 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793165467 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793165467 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793165467 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793165467 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793165467 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793165467 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793165467 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793165467 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793165467 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793165467 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 793165467 ≤ n) (h2 : n < 793345323) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
