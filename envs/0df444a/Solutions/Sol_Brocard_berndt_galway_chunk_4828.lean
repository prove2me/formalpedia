-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4828
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T13:52:18.756982+00:00
-- url     : https://prove2.me/submissions/ddab1c81-991e-4b4d-b175-30d0852d05f8

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 868165467 ≤ n < 868345323 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 868166717 1250 868165467 868165477
    0x4060c0219061512110f0109090221131e080705070f050f0105040510030915110309010b0a24051c0222061b05121606051e06130e03 58
    0x699241d03034083e0f240c0d41610b03400e0303044010010202410500c402d030761550103a07081c2071140b06005080b0200e0050550380b0422044010f400074031011510303030010503000407000d18480100f06102d010000410040a01002c940d03c1d072617480110b4454845d003c0c1044025101c002c202100c0c000010701c44180091800d00000015158002d520701d0f0071490182003005000d914030180e07040c882c0c20001440a61038404000e00e07440058200030440010518011081c4004081d00a8a0314034104a20011854240003180201070410091010811541c10040e240051348507082c1c0c02c8802c0d201208210094104014070f07101c00e41019421b00c0c1c82d51282c404000c12808011110650000b10804100514400801d000031030540b103002c000d00307114015050075a8480000080d81f4612588010081c0c1000315500064040c8074058407a074540001000c4188071190854045e0704200001d014040d505e02900e103140710a400d40c524503100d44086c080700349500c0b040d44075620344440810310000c00401c0142 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 868167967 1250 868166717 868166723
    0x2d170d140405010b09010b03010620010f1e0204292205090a0917070809101808030703143601090e1303030c170a020904110703020604060c0219 63
    0x410103103090b00e00b09084640c0064410303c919501401032110040010075a810b44106003045140020188401e49096807110440c1070b803503007031159403110a1819001506003103140020406000407154440c81680214003441154070700c3c50780011002d03511003440d40c6080e41e402c084c07540342100c80309105650781c0c42d03000f080d01001c00d00c0c1c60400c0a81000d0004541c401d08041007001151a940d03a00c620000c41c403441038034201d0300401c40c80c0034086800c080710010f0000604203a40300d11440406030a50b180e1102c219003480c428400050900808011a81d90550540e6880c15442100c4000e484682000c4218201c407007002c00d4030507030764412400c44003404c950704140f44d440a03458800103080265581002814a1003003040c00645515051805005036050401181200705128211500d0703205001d04403004d08030764140f16021190f50700500d0b81001c152003c0c030540c24a0030180341d041c8120303140240182e005a00040102d8003662100d03c60600c50320650b02f50760149203100c0840301c8603034026 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 868169217 1250 868167967 868168001
    0x40c0c0c090207030f080f040318050301020d0c02070812030610051c060305060c0408060f090109080d05060f100c0209060f060a0e0f090103031202030403020106050a03050102072d170d 81
    0x34000c4c5600321710030f14540e080b84d15080740a0714094070044a03517071015000a0a1200b0520015070f90160000850040d1401500840d1a4003103200c05402a00401c100c0300054066040c2c04100d10f040400c618420001000e041c6145854010034004541541075a2008000060203900c4012502040203402d45500004c04a009030441c00c010742400f102510302c81c0719800c1008200030405020401544c4100d0040100a043e075503003000502401d411000101090400548400940800d5100a01900042d104580111401c20601403003012112460011500340303049440103142c16102d0f20b503c004050103054000a40e0804950300d40c0202d81084041038a40d20800c1c614207020340d10f461694400ca0703641c3c1c0c82d5455510003074503031483d01d102c003c042500000001d0a250007500321000034174029200040250752410306078002d4202000c11103001074010200c0f41c01d24140f0284025032f1a51030101d200c00c0724140d036051810307060710072402c130b006505000d507a054402c98440d00c82d090122000c5 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 868170467 1250 868169217 868169227
    0x1180f0f0f0f0b0f150c0a14330a090519020906090103020616080c0d0c230607050c0c0303030106050705070611030a1115041b090b0f040c0c0c0902 65
    0x100784141d449000940044030701e8907050030429500e8810100c03516070305488210a41103124040340c15407007044840000c0d03218075040d440c10828043c0451200c82910410b440990744500956600703913444c481070884401c40d0543c6000003211004016402c40314601d000030381c6041075540c8504041c80d200e00043e0030000b5201d00001c0d4100080b4080d4420000c5560110640c1150b00007038240c058002000e00c141d070088688000c0100a0b0102c0d2800700e250b200301c1f15544a03031803000340b160350030b904116000c909840c4419500701c0081d82d14a651148407014000903918114111000c0e0010000100203210302d003907809080c2c07014401140a8812559025554401d500307202e403411107154800801c001540c0e484014000e00801a103000c841c03245000b107149160061064600043c00d00788200520b410801c0c08200301c01451031010303982610402c0304009a5541c40441120700810305941c002204a040d0384440ca0a40c1c4413030300e40d0340c050030b0200c003101c000d0b1200145c401c19030f004400c0035540064 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 868171717 1250 868170467 868170491
    0x30c130c020111070f0f1a01151101200a03060915050f010203160803060f131407030e070e040503040b0c01090b0c04140f040216081306020606010801180f0f 69
    0x1402681080d4041210704d00429a40c40b880b40108408000e010700e10301c290054104007807a0740140302180c144c100900b00d961030364074000380c282580d80d509010031701c1c511140c40c2c508818001d01d15501600d158424007020303015100318152b8444003030f2000309540c074030b00452a0340c640e20410020f079602c0c141e440700382d90400341803002c0820405011819940203001c0c4d011442d503107801d0000d120384e1081d5080d031a5100c0c071000c906883d038a1028a940720030140c00d0b98541144680c8518030f00090800d9030262a02c1e803503004e0f400c40b410341b00d0345002600452000d10643d080259030a030058400e000720303841d0940d00c64041e2503d40154029500c00d035120742c2d4000c10b1003000d550994124440360031561800f0310749508449030b41100010f082c021103890040381500e0741e565050302d02e254854140c00b03102a0440c644082c042c0c4c0120003001000301c3e4040d02003102440092038910901042e102c2105590030701000700a03c09a003904d41d44110345510380b11200c0300680c02355007510b066144d404180c10920403 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 868172967 1250 868171717 868171721
    0x212100909080d09050a06180312061d090c04180c0e06220902041802090a23100f030b0a0b01021b011107030803010e0612010b10030b030c130c0201 65
    0x2500040300c0600708260000802c02003001c0714100c0d0000500043c04200d03901e4090b003041c054180c05050b0f1450701c030054140740d4981c411140361030301c6980d40c0007980b44061203c50844d100e5014030b244271660940c0c0c0e08500b000010030590816141003c079160b0740da00300c00180c16039512140c1c0b81c0d03520201311001800c03c59801400d00241c22070150701d4541c1c0c6010030204003084414003810240140030400b00001000a03400808442d4001d4801d04c040700f1503d0507101d1150f499541240680341c5000021041c40d140c0c45050f207103408901d40c030032070300140c010640c2c10500068040724040b036501b040081c042c2c80c03000d4410001d5104511a00711494040711400c1200c0c641284541135400030b09943c1c3c42c4c44001110415064070074240240199001913038149416183e401c02401c8040010001c505501c80010f2140b052000f11054070301c850740e04d1044c60994a00400d0150070010381081c420038a8029003224294903030250807540c11130341080001d2020036a030400005420741d60415107002c5c541c28 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 868174217 1250 868172967 868172969
    0x9091109030d0903050d0e0d060c030b03070b120f1b0424020105060102070b031f03050a0b090a030e0904060f0c030b011d0102120d06081506040b0909030702040b13021210 75
    0x60401e041511320f5915181d0300d88a002009000f0010a0b07050602d680c1d0f50040d0209016402107001c100c04860944054001c20000500912078400c0c42e8001407400310b460122205240c0c0210703103503c0354503a00c1c4901800d0030050040542400303c152050b04a0070400d010b400149030801036a101d146904c0600e88110f44150320740002c69051008000503a44c00103402d000b1035004003078440d5070340c7d81c03c10f00c000c5140c41c1580c1c07460aa210003000105001c400100000c443d030003108003082030f8a500e0180c40c0c0e07501d0305030801000710341c1c182645034007407400c803015079486800380c1d82c080384640c2d00e06004021aa928031001001c02d960304119002c950740301c0c402003103a1002c600e40411100390880042e40da41c10291000807100d1b40024085c580c0c42a41c0c01020090200004031040c400201c0c0b01c6c4c0c0b10010003205c04d17500035484c10003161154070301034400d2402030500c08065807904e03000380c007800003602e140c0c031a15410030041c1e82d010400c0412071000f0b00c120300c1410f0840c0a94145485000504109 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 868175467 1250 868174217 868174243
    0x30b0c040618030201021902040b030a0515010f0e010b07020114030f1b0f0d0504020f191a0f09060702191403010e0609062404020304080d1805070b09010909110903 72
    0x140b40c800f0300c0141d800042203c00260802e0024200140c140b0014006c0d012030245103402d80030f074803064030404c40c00041801480178803900b040c00daa178803403400030384c2d061280c8919049541d5040c0100b1a103c4000002c001d00c1d4010300d06402545000307008100f06900c259120300c03084041c00108904a446212242c4404e03804214840c50318600c0c080900a034059140e940407030707943d5800230604560350740a02e5001884068441466018940680200766145124010040b40b84984400f075400b003020440700303c4101c581340142012142d1060003416000407004036001030944289031850305141d5901c20080402400a058111b00e00c41072600b511904c1ea929002c030750069062000f00c40000ca14950f02c6106004050303402c4c0b1400001035901744068400541041c400020302062040040060071a00000c0c903003480b88105074420400c011102e0b00c4050100c1e00000307800c1c08030402030401490059014900200d4203034981a0350812208202c3c81146140e07400614100d85090501c01c1c0c00f4a900303 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 868176717 1250 868175467 868175507
    0x280f030b0a150e03030c010f051e060604061d031f0c05091e01170702030d050c1201060509060904060b040f06090f0303030b0d1401271505040c030b0c0406 68
    0x850070542d50300102d8440145810f01c015100700c1c20b030300e40b400c0040e0b803170800540f0000d0100f48140980303540144425500d0303200c2c20341c000b0061406440070307048450003142c0140c46d152400386400b03c226050075072240c0305015190b2204c561401a40c0801025000b440100d101070302d2303520b13200c1c2030808035048411314405021090010700483d50f64090b00030881c001e44e00c1e032079160481c2c0d01e004032141070b00440740071007403804030090211040d800400340c00d506e464800300700441d4031000040840c80c0a8a0ba2410103105900c0040c0002c9110350040c0280420103000c10382080d26030000502942d06941007550104408107013003007220b0440d6258001003005080844e0321909103860703074402401601001d010702d5100e0210031115142c00700d80011258003c0b400c4a03c2990100d9035a02801c0c079a8800c410300c20705224101e40d20010260b03034940782c42d0302034420910013214040200161000400903143d141e102140040495100c9045a00c038642c0c013030807141e9a50905202520000c20340e14015034444c = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 868177967 1250 868176717 868176719
    0x50f06071b060c18090b0a090504050c040b030f0a0f0c09020a020717030f0c0606010f1b02011d0a0e0907090b0f090604060b0406020a032012280f030b0a 67
    0x1101407080308000d68005038003241c001c05010082c4d074001c0a50004031201c451500c0000317070f0002c040e1b000a00c50b00044130741800b1580da0f004220107481054070050306682003e01c05444614060703100142008000d0240d600142500e0803c1e03040a201d418240d84400d90400b9020403c80b501c00040d0103048031250460912103070b42e4000b5038030003803030217002c58107546444520901c2c84100103541001c42600000b60b80ca030081d211854032002d064444a000c9480b001d01c1241103806418812001d031040c80f0017032130075070031600110b03048141c00f80308208415000c03460008a868004036070002c0d00040c1d03101141803c14141d5140f901045d54092102c1c5464000c2c5103180c0d681d0390f0403076000d21500f2501007107107031280c2c0c00082c01841c041c0d1060f031169100040020f80b00e9004580b015180b80203131211040d10403002c0c00320b1070f0354900c0035022a098100b00d100304000140103000e0000065008240c0d20020b1110034044000c1550f0310713440e0085051888010303401075050003101e801c16015a010b843c0c0d1 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 868179217 1250 868177967 868177997
    0xe040507090b07060b130903180501120b010e10020d080c12191d01061805060d0b040f080403050715110c060306010c1a04060509070b09040209040603020d050f0607 72
    0x1400c002d000c1c048500c400083c000c024044da42d004420560b0008040010b821402920f0100400d6040380403808500018150000f06000c03a281c50112075040c2c5070207000c03400380480000100313800a03006050000492481c54281c58811021450610310303001080000605003000d41548002010a00c402e10100003410b0445040d130890760704140d03020101007106181c0f03080d14010308030410f04501d04988612101c620000305400c03080803500304526941514424201d0030307041c1d0f074048038519080310415a15000051350100c0c00c991041c001c007211081045140e81e1802d50b58010345c01070740c02e540b0401050050128000311840c420089041c8401d000301c3c004545030b00d8201030000c05101c0c00b4003100041c6164000c4003144442e03507200b07018004100400303042200034041036a06880302d928181c0002c01e041c0c4005030102c140c50000d40307207508010b80441080041c0d40700e40d4205400c2601d0710340001c0180c4802e580400e0307940c45000a000b0f241c454820842c54503400030124810002c2e414103008034 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 868180467 1250 868179217 868179227
    0x60414010b120a0e03070312180519050c0a0f061b02010e040c020c1005040f080106050102100b220506040b01031808070f08040b0d0e0601210501110a0f0e040507 71
    0xb0800b6002c120055645400c070860082c005004100214000000c038801019481803e202d084221180704000b1801c0340000c1040600300541c1c000d095030f1002d400640c00c1440c251100001d64812405c0b500c91000c9200032a900740c006900601c1034080c1d584003402000e400403d0800c91007102c4c800207420300e01c990002048802a54903c078011030307848142910140c4240036501000b00c02038041c00381c62004140c01489a0b0103803007a501900c0303445d000480d42c40e00c180a09800c64205a00400112680e00f105200909928541603030100c041d540307200b00641100480003a00c4044c520016a42c540234051005841040c040f00e4105441c15582c00c0076038040d4048620500c3d046013501d40c13030b4111460254800c0035101009423101c2400702d000245034192000400709a0b081c0d4030103009101c4244441c0b96605800e002d085c2e02c407034640910900d11302080c44600d0202c0d000b5000855012083d04500741c45501041143d400036650030640544542c10070b00700c0558407401e49007002540340032400104 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 868181717 1250 868180467 868180477
    0x7080706110d0503061804020d02300703030c030809011803091e032f120c030724110c1801090621030f02240f010914010308160b040b060414010b 64
    0x45408a290041025522601841c278080381d4054041d410508864540c0d0300400642c2c0d4100300d42d05d025002460403004080f50407001c40341e2648940c184d014013940c041e211240c00610b2080703030390760742c0c1d406030f08890340b41207894011070280d03d6101c986420203c404040d0804600f03107944003c03503180d0800000e0807100ca440864000a80030300691f084840c0821030030505540c2c2d8a500051002d09805100d81c04286610802c0044044522142e5180c5112081e00c80369140e1104581040e0b00d014501d03805003049865201c580340070350303207880d121030001014039480d8400c0416804601d80140100221072080c0400340c0444884030040c2c05104014841000034035100404000d500c00d2008965802040f11040051001810354804c40e481e0f102d020b104801184c00701d622505410001407020498403406008180e11070007031866a0954513403141ca60300c203e1203a000b455498606401040c2980139181c09103100f500703503040c0f0703003044000c000907251b003118040c0c40b005080f00100226484441121 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 868182967 1250 868181717 868181749
    0x3061d1605030619030b0609130309090c1101020307030606030c02030f041a040b160618020d320703052401091e09142b1107080706110d050306 63
    0x5a500c2d911070012a00d002c1491640c0c0c041c0e1040480c1c01300810030054195031086071f0694040c20587c2e1808812081c062400340040c0206082841c00e10030300c507042c2c0003104071003da41801810a442440940e0899008481c1003000035665002400040c2c1d060040311200ba0944c4000e600300710384020001d003544600d02c5041c0c3c004031006442c3d00720000702c205480052084601c0203444041402c0da100303a100c245c0320115260340c80d2800862a1800140c0e007800240e030050503040492105580d14403c02801c4180400c11070b4842c0440760070203100424084250300c8020240c42da941ca507103049840c00101181c009100f001d01c01e40d000684111504641c1103408040d0007061403603481c08492000b01a00d624020400e05043e9404180542281c140c40c010b00c1e010211103d010f00c1c489601001c0c040c0601031b10700411030f5080600341d103205044441d07103c1d480c401071b41d6001d5564046070745883e801c1e41c0481e000c10303644025410044c41c03e0201859402d0b860401c0c07481e518240c0700094000130105070423 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 868184217 1250 868182967 868182977
    0xb01090614030a150b130501051312050c0405010f061211091c060203151f08070e030f070f0e07020102030903091e040c0e030c0109080d051b07030303061d16 69
    0x80c20f000c03158003c0d280140c44480801c030b005895440d00e49890340300000b1010320381d41c45e000c00243c0d9482402141c400511090601400908007030b0180c43d01d03004002c007502c2605c00d48910202c5e96846100b000c1c02090380a00c1801c4582c6803140103850803080c508512082c1c1e01c2d020480346001030410032a4054001101d00d0500c80b40c114500c208402d4044a015184510100411400c119803040b200841c15044403491011040081c00c1900d10790441d11090004140a0215074558041c00d440c5041d000c000341034650f141c9000d0305041c588000390b400309602c00c14210082003049a2408142d03007011491000354558940001913036564490200343d240a40904280100c1c0042074140d500020311000b0414444444141d00c020904151810f581e4401c2c0181d0303240080d190700622148040f143c7d50406000040e124040680b00c6030021500740c1d142680134041c41d412254203011100c0507510a0700d001a80b0380c2070100358158510550001a40c1e081d00030306100031904099812641c102c04e528103 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 868185467 1250 868184217 868184221
    0x1103030c0403060c020a120206061e180a090f060504030e240d0905011a10020a110d0c0b0a021b0a080c1e15040801111608031e04150b0109061403 64
    0x40f446c100d025038020300300210348096102e01960119078180284022680700007558980400c1d620b9054156002c0d030fa021787d100e11580031000005030080d0b480113050320000717400219522680c00350042400304131209503031202003000f09504081040707039006040d00c411a424030f480c204951074407032103082d00c2034100e0082581c00b40c00304242c21408006034170100902000c502101001c0320b0501180800d0701c944202004c90424610010352800d01c640c1142c2002070090004d0103000c1100c0780844140c6e2400074410300840c6004000004010b050025030042649400c10300fa203855280d0384a5480d4410030010508018004c0002001d807210107080741c0c0d8010f140925180c0100d00707070300c1e85e0580760001c40b142c20f22020302100320b0142084590100c000c1c44403005a80c001013052050350200c0c5031505c11840e040c008140c800002c1c42d03108000c8010aa240101d0400307039417011804440032a03c035507807002c1180000e5094001d2012218007802e04400e1582802c00c082c00640310b94030b080844e2100800 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 868186717 1250 868185467 868185491
    0x11406030706050702370519060c0204021b06040c080a110402030a090501180212030f0f07060b0a0b0702180610030c180603200304030903030503040219080d1103030c040306 76
    0x1c42d10741140e1001c454121450b04d8042900b0b02d1502150144d41ca08046a000111401d20105895030b0231100404a03001034244002503074030500000059800a5090141e44404860440400c41d4080302000038082c503d03040c548815600c1058010000780e030048034a11001a0900a1800349000c0072100548c0b41e6481d03007140002000c5800001c0c15540c20046070710b8030201401c03018026180281e9508030f5003079214402c55500c0c403d10340307880c0119500f08441c00c0141c503400094020742d0322410000c10401103030b02c009212224541c00c02c41e150840020810218500240441e8046542007509401c600d031060000700301140e0641c6440501d030f01d8503400d00155100e075807000c441c0c1d40d8095540300480d844880050007025640c245505a03a680c48041d44000720794020b8074402c60345961000d80ca103040d1381e0129819003019008a0308a40461387c04c400412294039080050481d040060120903000240184082c0480e641d079603113030b0020018041c0304036010701190107898020001049400e0205 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 868187967 1250 868186717 868186729
    0x200703080609060d150e1b0d080715020310180b031f0f110304030f090e040f0816050d0311120c0c120a090e150117060109080d11011406030706050702 66
    0x81300090071950740002502000c00d250344030050300074220017255051012450181c195002c0c1c641e80b80e84c040440030008001035002d070000c0c010036104904000442d50a10601c609a0b0019604011842c9000405002112601c00c0c0d9841646040500348422b090000119842d1600b054400b1900301003a1501c0c0018101c0342c01403129420811004c000c028060300c5070606640007601c085000868504050501520a01001701552a1071060440a403640d0350f554075420002d030012145400107001c4098100d00e58070681d00140d003d0400b03400071b0260410020100c03000000341412421042c00f1b02c0c0000c44200030a258040c2c855140f03e641c44150009440c501420703590a841440800110350820300d81c4094000c0403134006000d0703290b007a150700381d43c40d100820844e0f005000070300c440e13604400c584001c840283c001106041071618561944e4901d42494a10010140441d035055194140d411091180c051907140910114030344d4102003000945074111031180c0d4040050205a0100799a030700 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 868189217 1250 868187967 868187989
    0x90803070f031b03060518010e07030513060c0807020609010c12020c070b0a1107470406021e0a020d0305030903160b010302040c080903090d0c050604030620070308060906 75
    0x14151a22440f44501001006008580186406941c61080e250030901c0d440903014140c40403103000f99195034a24408074000e0030014080300144103203500b218082482d512502080380b040c0d0381c807030a20b4a410f0001a24000d40a0422406a8500000211180d500145500804103590320140c1e03148001010903142c841d50f42c00109640000040b140f54080d04608805c4252040c0ca050310f18055513007160848186c00c82c82103044002c898888200d00c1d01c0f246151501d03244007525410040d0f03081d0410b801064000d40c002c0310140e800350020020020510b516103051007400001030802c000258040340310780e400c0c42d100030b042c03140110200303104100910945100104240c10702010035018109120f01d04028402680921f00d000e0003242603920a03003606200d50548001946403110701e03803d02400581d80c03c015188880d1003180868603030f5400005000850140c9000b0400e14000141046201602208d01200c0842003203d01c0001f9040030f13499611410850700f441480c0c0c0c0350404965444a5 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 868190467 1250 868189217 868189241
    0x1503020706020f0912010e0307030c1b081e120a080408191211130e060a090f020a3b0f04090c0305060c07020d0605090102090d0f15090803070f03 64
    0x31a551070203c0c42040540300f41e4108a5041002240f0714030018222044c3c0d4141600036001080b800d00403074010f107501c5d4401441404040e00d245586a081a0101d15a41104000d500103041411443e032080789400e24504041f03028000c0e0700c5043d240000140300e588161000d2008803400102803040800075101d8035100d10900102405040500a0090143c0c0d604030225a1421500140052401b4161414070000d0020401c4080c200240718954400090036207500c804c42c04000310301c005042c00344840050201c800940caa06008802520145004c4002d40c021407240c400074210044040000c0e01c1c504180685042e01d0000c040440d451a102410554005013005c07444020045820643c80480340580c0c1501e544d80c07190b505800c403511401c00081e600c51307103030100d800209800f039100740d80112606000514104118010401c60780301c00009aa14580d0203d05900780480210315407184501c84d5404c100c4074200360f581c50b00c1d030300001d484d4904010305510345c002403500a500c504e6151071 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 868191717 1250 868190467 868190471
    0x1b0f031b0503060411131b120f0603030806040507110604080d060b0c06160302031501080c0919080712032c0a23040e06010b0a031e051e09071503020706 67
    0x905410492440e44804080c14002c8450300b0140104a44902c01d00750444074403000540b688001c6181203509a0140784230f080c04942d00e41400210781030380d101b03110003548a51146091490600c04000848000808450601500c01d1504021210208082d9442648900c41d81d4070380c7c00d80e0750b00300d00034101900110f100140001d00c90346402c0000907400e02c110145941134400f189140800c4050b400161100d034031040314680c03100c201398090303a0420b41c4028a01c40403070515040e00001074400081a5180d40603802c000c800b440705280510440c03019110742550320014054558000701040d5254001c903105443c001c01040c000c03181210400c80c000c80c014030b25500c154a13001c0c010748501d64100611f60f00109620300401904180c01104115075010780a0b1180c0e83ca090781a0030726511911984040683d500c80380100c0c00301c0038003001c1d65052800310010b81071510010010b4180d1b0380980140c0d903910b5000c01c01883e40400140001540d85441c0c001002c880602c105070041d002e802d2005140718 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 868192967 1250 868191717 868191721
    0x7050319030e06060f091303021906090b0702150105091905040309170a23030d06080a0b0c0903070b0d18060e0c09090715051606091b0f031b050306 65
    0x10754160400e100510001098641a4480c0420007070f041050508464000002030f0018002e420311680c403100b06806801582c2c0051802c415810380200c600c00304540f455030380d26080d010b101e2a4000c640c5d0001c454001425034400a040510706903505101d201d1140300c602d800604645941c0e044803e200c045460144214142482c2c06007055003070340039040300c555111011406c11480040c1d8a011580c001d04440c10140e906100000003d100004030030443c841000010200500c911540b001050b40c000035007503040c020b1901044a401c05403055140010920950005903404250f0004aa400104007540c504079039440c003000d4400041c0e000d0510820054040c2444400d030020244001000c050321000110a000c100d070380703002a16050020f80c090758051040000c101116500f4000504100d801c0c400803054040c5948005607041320301540310358140303007004003500700c0c6414030a62018108075076003000c092031741750140c611000c0c10b8880c1e45c9882460407001d415043c4040c200190a591040c = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 868194217 1250 868192967 868193017
    0x41b0504180b07050a0e040e0a0209040b0a0c09031109060a180e0f0114070e1f030b0f0105180f0409050111040e0a02090f270a0b0f1e0105070503 64
    0x810303030590549400502c1e00024030200c0c803c1040b0766050b101901d40e4040c00c0c006106010042c140c40c05114058416021180090f07070b90148000c0c8103610070880e0000380d10784000078006482c43c0b100c4807000c1c400d05640900024170303031590820003a40250380c503090301c3d544c1074005a40170b100b56104800001810030b800b41801c509030006800801c180044403010821015450700303c2e15122038001440e1441c5011600d45480343c480d0124490009003100340d04010030465403980c2c2820480180402c0d5150b40107801400d116083c2520346400f42842d07420034880c6021192205d118400d0a807081c819032103903d00a580315442448007940200080290058007250703c650341e0b01c14080c2c41c00709018040052041502402100c05503000900010002c1c0680024031420340500403034014180f19a83c400c069283c2d0001c2c040d4480d40e01441c02141c058147c0041c050440003441c02140600040d040c20107171446840314012544500b803038001e6a440642c00d14504600444100031440070f844d00d881040 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 868195467 1250 868194217 868194251
    0x3170705130e070903080a02070b0a0801060f08040507060e0a18090c0902041827060b0114031b0f0c070b0d11091311070b010e0f010b0c0303041b0504 66
    0x1681801810542058403001c4407a030004048031101c000981198017400090008000781200d9a810b00480750410344510b0740702d8454004a02c0107000805042c0104402644000312030802070040c1000074240c03c09440e640e03140d101c50301444042c0800380e1b02c9810161079065840340103022070f030f80d400a10140c1c800c208028000c0c0b02000d0301d110780c81d0030300802c68605038400c640c12030b2085064003170f52000d60100741000d05664801101c0307020f891480c01c0b24113009602010f200500c40e20001480fa00c02400140a905148101c03801000707048c410070450780d068031010704655102403151516038007000380a2030544240981030602d40299070000404046c80c0c4050f00c29440c00a20030302405001c0b2140151502900d0354030340c2d12910030540c820082980d544024400f604d0021183d182c0030213500c541c104064203030700002800030f010003000016440d43c00300394054030f40c201c0040d01d003501c1e00c5881c41c0d69002c068000381030601500184029501c80d03926420042c140074105100351941e540f51004 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 868196717 1250 868195467 868195477
    0x81b070b04030f052701121d07082a0307080d11011b080a0b0a08070f0e070203030f150d0b0a0b0424180f02030f0702100612080703170705 61
    0x2059003c001000d4280c040c0f03083d950501c01403800b01c000001c010202c0711525091444141c1440403403181d5481c0b485490094901000c2560f482c80440740514505502c0c1903025030102e215a0041524105100d000503000a400080c0d0607070640b5844103440042c1c10b10446601c007507014807031444610310040c0c06c940c00d104040380d0307200200216802c51201080c0b0010030310000300041e24200024044620990107502e40090142550b01c01e56202d41c07101d4035003401e6401a401c0c0c0c0c0e001c000304001034140a05100d82c03200c820b00c003540c1141041e22812588004c003a00050720446040300406094071000609004075403c07a00031101c41c00c0080140e0b0040c500386045501460134186c400100c0e00c0c002c98110900301115116807120351900e14580451182c0c00c82080d10b03d038882082c03404140550000d9400707501403007030307000d013609100d01c010740741000c0103411032030303c50a01d0b800300a008020004080c0d9160044203890b55480349140848940d101d8410000a10040358244030720954441c02903c = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 868197967 1250 868196717 868196723
    0x2300708070810060f030b1302040311040608031b012a020c030604080a0f031d16090c05190302090d030207060f0302120103020d2904020f040e0d081b070b04 69
    0x6540c540740c0501c1121403070700c100d4510400100c0d450307080201511810044802c0b010710b1800150301c80315200003a1a8801c0c1300c10101040b03401040c1407050240180c21803035903601c100c500708070140c07808000b5900c901034071990204450342054180c0ba1b0643c00c2d08554400d00d207001140d450250b842d08420f2205a0700500c8500510500c1003a000f2402c0000305180119000b002c218240788008100315070080403c1c4c11241003644404928908004505403010030100f05000b91809008007040056488030790b900c0321040c10b06124540300d1003600b0104550340854080d0400407898030305081a40039104940005030480202050041855030105203101901c03519521080c080100120460a03402080d9582c2802c2185500400040c9041c00c0c9c20309007148a400411025000c2d0040f0741c01440d8180c0e03100c081400550200421840c00b41d07000c04410b00203c1d8200302c681814050556a1404452804140701840d00031850007000c08421142541390010000d9940895203401807200304159011 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 868199217 1250 868197967 868197977
    0xc1e1a03070530092a0d05030403080309010c0f080f04030905031501050108150102120901031b0503040501060608071d040e1b1002010506060f03070e0619090f050f04023007 76
    0x200d5406103002c034170602d00b5038007103218480105600d140481d040105500056010424261400004200340f0240c070066000317000090700c030700d844400a03081d503003540110b41c100025141507540c0c0c903402013140c6030810a200200040d580c0c8510b4140c035581c1054108580c144a203030481d0b2000312441842a040e900286d17105001610ba022040c004944003090960168000c50170f01c854014242c4041c1616074014540442c03c0e07403500c1c04c0c600c1200300324486580042c6001040005002003401068002c041030310b0402440d00c0d0440005169081200150b0600400c16980b00e002d603807560003080c1a04142c406075800d49102c10300d0507440942c0e0306d00b46402815201c0381c2102031801032043c580300d000080c0000e860306480000518003580010046030078050100801c140d07584400c00a07000c800782c002c070b8084100c070401c4009000c04503564000084500c03d105c091100340c550f0541644540740603240961940510490300d007c41c1c3c2907940300500b1700c0614614032818012405000d002d548943c0701d03 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 868200467 1250 868199217 868199221
    0x92a04031e0c0614070b1504062301090e060402030a1b09060305010f0e1305030c0d0f030f0e0309040903021009060207021c0201051b0a0b01030c1e1a03070530 70
    0x1003a44d8443c20100c5000c01650288801408104510942c55201c0450903800c0d445d01000300000341140e40e185c0003200c59a0800c04841e61450102d1043c131007215007402c101002c1c605c0c1541e41070b81039000404d0f00e0b0183e074010021034502042038015100455101040703800007021280f00801000b40d0384201c030700190900000140340f545800c100c0e070603a00ea240039000e440da5078648141d4420000035049800e880100b01c0703e4454141400400c1c0d60411581c0d4207025502404c1c401400e4a000304000c41c2580d1038803031054942c07030340003007200d504110595010424038150f007004e0741000110000100742c1d500b09080c5d001000712030350003031011134402c40d40ca46403110002d2000c4030301003941034024007140d000c015926001d80001e01646410401104448806203a80d0752000041c20070307441203074a20010003050286103012076070054a081840c004107800303490120000a0202e40035501c01c102000000841d464074414821920989030060340c00740003e41036807101c104250300c006048600c1d404000 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 868201717 1250 868200467 868200479
    0xa0b0106023a050714010e0309040e19031b05060a1d030301081f020c030703110f120405060a170915070f050d0e1e0a0b06092a04031e0c 60
    0x70b03016510310390b8110880000c40909451550003a0401e42e0702e203004544210900000340a0b00e0701c0d95003040080c1d500c40400906010030f641825500c440d19412095240d0301d401c00c0c25203841900350b01441d10f1032000c54222849445042c03d243c024005003c0d00c42049400085034011611000c071240205054486150005842c0d000078014610a41c01101c500100c141020340d103c4840d2400c2c413001450510351440040c80c41d80000422404120700340d215000415080c011a00c003c01c80101074601d50780d000c41408110301c11406417500c100000715034200050320407002c0240c541c0c0b607141090200c0c20018002661800c1c01c1a4902401d500310000a0240e441900b03200700c03031902c0f6215207040000aa144a010b4070000007002545d20070280e0a2429044c0501100140a840000340118010b01c0c103003850000380c002d0000c0c1c0201048018840c10791001c00040d14803040000e120000058a242d8640c0d5030b2040303900c040c02d50302008103041c0101143e0300c99415003500c10001d250b030040e9259 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 868202967 1250 868201717 868201783
    0x6042315150a0f1403010e0f010509070905010c060213060c0c090c05090d11090705090310060506070f0c030803010e150d02280e011202240301090e0a0b010602 70
    0xc0e045005034028000022094007030300c81c0208032000ca04184150160144e982c07412600f09a00c400c1411301e2070418019002e00e9404042d014010582d10210305140c642000b0b804400caa1244034100400c0e0300c4984141314155040d186421008040100c82d5555070800612140400d54113030b49408068000041d0080389109980c203c0031640c65581c10496581d0810101001e0b045c81901d81c10000034511440340d845d10142880340010303442d800e890341c5407001410328044c407051124000320710704142803100307603540700c1503030855940214186805c203240d01c0e00703e080c1946076000801c2e254000c000800c24841c050601c1c0d00c07444051040103503180c075603803c02c0782c1c00040d00340c065040b195803682000c0584203404800b100d045220030b05501c4583c0c032410030b08058030903882030400f600e15681c21011454000350110900d4507124a0350492510807142412a04c01807140e000c41982e14030301480c07090420300030084201d800000c0805150380d5020b000e504c44c00c001c00909a4440b2742c000c9039440314051 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 868204217 1250 868202967 868202989
    0x2090a0b030c06031810061406090d1b0803040e0402041b08040602030703110711010e100e04051008010905060a150b0f1803070321080402100806042315 67
    0x1d0040096a030041c05128640d807010300b9840c1441940c407184090b002040200700b110790140900020070740e00d0100c1d0f803282111240c0407988180e1080021002e1950340a07a071000320b58008400049450850b503000701e0601d640da011407800d0101180020f10240038020a9205500a540a0010508608801240441c01c1c8000c101048200c000302c1c0208686901840d4800790500b0005450595181040c05c2900130420445000c003003561140d13010750703200802000d00c410944040c460a6400c0d5800b6207c9440949401d0049643e000040e04950f030020084000340301d89802000000500d0034000c0c0c40b038034200c5100f08501e09080040006010f01000c1208981c180300c0400d08103094902d2400d0380d075000c628840c1c200201d0034a0385041e82d900f4040c1c003008503c80d0f034242c440003120601529801c420341c07100302d090240711010003002da1260300c05d012a2003c9454160456554103001400600801288140b0f0035030b200601811b940616800ba03004480074130f0782900e14201502001908180 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 868205467 1250 868204217 868204219
    0x1a0106051603031d160806090316050a082a0601050d1b0308030106020a0303050f0621070b0f040e0c0f1b10021305040b010e031b040905030d0902090a0b 67
    0xc1003186010201c000780c88400803522034079000c603051030741030000312941d21198281a00758010102080008070000c0740080240741e544003519192030b01504068581c0544211a2400407000d444041000307001e1001c5a110703640a600b980d2541300188c0303a40715501540030b5684c49108030030303050360000100140060407100c1c0109100350442641ea1898000342c86884101011126050003000003941075010f14003174100780c1e0040002660505004041e140c014204e901100110000e0000d01d03143c1c5e540082101d203030303554611400e01d1500c54031807901081d58064118881d011400b903040c0413041c0700502c11110520b14041c0380c1c3e2125183d805107403041e0048062141401c0200011001d00d40501c403807603020020964a61503115070b03820b000d90307101c5180740407141c880a9051125180610409141910a180000c1095120340100b5520300c541e08107410540740340e040300d8410369229001260b02c19440030940e62035504003041c40c00a045d04c000100c1c850345807100090f410085510400c0042c01d4 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 868206717 1250 868205467 868205477
    0x403030b030f07050d15020a020c011b03090501200a0320120726030901020423031213080109120807080c0a0f030e011802090a1a04050a09050f0304031a0106 69
    0x2180070f08114645c48401000c583c0199a9100594580c544d4809480d0741c0006801800c1c05c50003046c00100800c03032416461682c40303203408240001c250312401000c10703038100782040d480340b4801c51f40144001210f40038440844c40f0b00e00513117080581c0050800d600d00780151b0054120f030080001e1940b58a10440300500003c01030000c4804504e0700d05c5800d8a10b9000a52103003200181c0d6960342551307004491110141e03400183c10005180306402440d20400180d180040840400000030340b2040200c1a0401282003c42c2c41030010014190303610090640c60020480c40e003c526114419040019038140030403503a00025015030300401100d449201140c00d03680ca0503184520075140c40203000d008100700342d510340d040c070110042481074150070481c44004407903070402c6104000c0503c80040406c8109410312403001c003601d040540d0409882001c0300c010400d50f482840c400010501c4281c0500148200101d40f460900044003e000f607a004042c0013070b03903181d005a02c6001c2d000a105070b5000030 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 868207967 1250 868206717 868206719
    0x70b0d02070c0b13031502030c12040203011e150e060105040b031b07110a23120a021f0e040b130c03090210110606030a17070521030403030b030f07 65
    0x2124035801800400e00c2107039452052601c51080080c0d50300030201e101d83e08a10f184060062140d0141e44e401c041c1006a03056141d80b4101c0c410341664003540c04243c11250450001c01c0441d50f083d0889600c1d00c0c10008101000800b0041240150005411250160602d5080030869182c0e10785024031030801a110280f0302841d240506041c0d9100404071070746100e81003000141d0901ca02c0061202d135001d581020144802e03c1c0812010940513071201d9542c3d44112905022801040480c0e980e038001243c0212a0f03941c3c2c448405d00701411400002c0d0b120041c420552042140c1018094a1080542d0303803815608070381092104448650090300d9015841d035000809400b05504215900c51003450003045041c0190b000c59000207000d07030b80c203001c0342d0f000c2d171904005001004456406001140102910300c6640c40da0204a0902d54400f024600c1c0041c00c0c40600008103c0000003000c58600c400c415002c031100701c0d6241c0c1040d02d0460019080015040040c5000203841551070280c0c80581546 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 868209217 1250 868207967 868207987
    0x18060a14090a030203070f03051e0702040c0c021f0c061b02060f010501021209030102070c0e07030f0623180a090c0834180605120f06010506090a21060c02070b 70
    0x900d4101f204504002e000c105841407410f05217a01d80441c0e2108503a1900e40116104100c1039490b030344028010010394a00040150399804140031180c4e103068110b4100c0c100500301101c0c2c085402c000900403904010528a1510184a1108a460340f40d8240d980079100e5a00800390f81d0700078860240107901003c03842020f401410700901c600203004000514100095884000d09501ca903c0403001941a404000520350140a002401e01c84c0340303000c00004c0c2c200040e0403000707810300342118480c80c0c0300c2403554504e4072054071143e0340d041003140c0c000d22403508078200006232640c2c600c00c40300704518110000d01c01e400003400e03601e0072a807418100a03150082d1140ca02044008141e910b2100f0503440008010f070f440c44102900112146003c07a1560600050000144005900d080b156002e1040d0181c4010302244450545d01d003220900c1ea249540310000300e0440d00d6802031503031008580d0b80d40381c0e0384000065826240307104d10001d0016146019082e0384031005403003024030b1a80200151080 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 868210467 1250 868209217 868209233
    0x5160c02210f0f0f030f04030b0402180108010f0606052d0d0603032715080403030b09011710020c0c01110a0501020309030406120209100818060a14090a03020307 71
    0x4200110001e01c0008500c8504038901244124014090380026580441a420a0118184220000008514100485400c07528620452001400c00ca4111010a00310b42d00c850403201381281d010341408083d42c48610780c900801c9040004d8400b00c0c44c0c18030000e01103004101b5158040700803405d445951101385140c0304111454820340012540c2001120100d0503180320781000303140a039550800c0034101c620f05041200384420041c01c280c0544808100c40c140d8505402680c03410341c94071101648540c075054025201403a0826407145444d400032946070025401d03180344c11120802c494044000001c3c9008a1251010110080e04469818820703540561504840c1590703100c221001d13081c40d515100c6c2260000e0b6020181d40c0c200003020030080368032441b4041503203c8943c0c00c5140c5040c82002411884030701d2034400a0000f0140003400d04511040800c10503842801078684910740b00c1c44000003000395801e89115000c1d4076010481514000644000d00c5515800452503da00c40e110603213 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 868211717 1250 868210467 868210489
    0x703180501180b030901090204050a0605210607180807120210031e09050a0606140a0602010c021b0301180b011d01030b011a0c01060e0a0516090302040b0102100614030105160c02 78
    0x100d69907c4542c0900140c460317109480c89400da0300c000003a611309000411040300b442c5007003010546902c41c41030410f10404240c25422020500704240d02001e0072000c024114201e51206a150041d0400050f0030a290742a204803103100302c40790780752910580c1054007143c040c1d02c00c1c46400c24440d9000c12508140358000e1030300c00d00400807079030544013035641e43c42511016004440030100043c00342c856802d285c80c14001400c6240002c0c002c224601500a5a41e0340131700c429801103c1c22030509004e62000c2d40018100c184252a6400c0d443d00390402800c401d100381700b4040c102d000f14a02c01c03409881604901d040e01d92100c016020390746004142c4000400e0000b9003410241c08218528031b2040c00d1143d18002c0c400c0c42c040c01c07414a030010240c002c40f50f004200b400c07200d40382d61407101c213954400c100341c0590740d0445000075440746140040717241240f60f001c0d40c8840c6140050200301000301400707607040041c00300c0090209a0b00d0208080005c1d06179801075010034a4002803000501c3d0050b42c1034 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 868212967 1250 868211717 868211731
    0x3091b0307090e0a0c210b040828020c270a02041205060417040501020a020108090f0304090f0b0d0f060207021f080906090607050901180b0703180501180b03 69
    0x1d2019a00d030368502c0c0490b003400241d030110b540155803110030019510f81e030300c008106031b180c0c0b507030101c5510340e41800c80e0780c108000402140c0101c00181c10030140d17606403112001d1030340c885070b030860740c040304040a40c05107030300b482c003522070901c8240103850111031910700711603044205c501111803030045840301040a40710000c40340e020300c00441c1160250310840340803809a4000c05060416003010000086031406a1400d103000308420301450341c002900000090b0b081c81c245101e41e6401c0c0d90700c0c0c1048402d921083e420b0000060014065880390002e10300d149007518100012103170641009010501420001d00b45030f030f02c2c0000804103030b0581c003415559001412082060490031108207240d058110381002240815040c8850310004210b00c40c2e0241c00e000003001a030801c0300d8081d08900840e60214100300b1621070b0707c58602094041040105807900240c1c1c0c0303e0300c0c10b00d03000e8060b200c010840c9407000742e007910008556101d40c0050b40241c43c6045894020380c01c10003104d8139540014070b00 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 868214217 1250 868212967 868212973
    0x3031b0c0813091e051b0306100c020a06020f10150b032509140f0a0512031204050c0108070e090118150b2d090108220501061a03091b03 60
    0x28490a0350007205004007072020100d03013014282e04c9020840700301400700c0c106d0080c404012100340007401d0840b0f4020b802121101c1c40c1140026046a141d07028034402034000b07480c01c01c0050f04a400040761034862145005030390300b091540101300200c40c0c0000040e080700340440070401c00102c0e20f034001c5070090170459254104642c034200c00c404070800d01c140000015403841c01003000e410307044001c242d000c0c4100c0341145415280000101c13550f8290188038400c00c80101c50884440041049601c0740c001c01e205c12100e0302e4181826903d4007101045980401d200b40e0014041c1c920070300103924804401051140240d0902d826001d015076800541140f00c0d80d2141440604200000c0d44030081640c0804a49d44200c2a0a0350911445e41a00000e1480c5105000c40c10702208030251854601d082c41c20500ba40d48650f014032110b09407442c48002c41681071060b0040c0070f03040d00700c107041e100c600c03d0b0190044441184082540710450340041c168009060741d0068214a40c540c140c4008000e0132 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 868215467 1250 868214217 868214219
    0x3190305040b07080c0705030c0c0907020102180f010c021207062a080703090b130609090207081204020303070f111f0c02040f061e0801060623030421030903031b0c0813 74
    0x42e880c13442d0b001d0020b2004c550322029070701c020741c0341c24407403140c2c0300014dc4000c1d802d01c07a50198480c00303003840101c0288920722000c1e040c481c0d40d2183c105002115001860780807800d07415102c0c10380f035280c940520000520416001510707200c5080d0104504000100440e071445d0054840d80030941280394101e040200900000501070140c101410301c1a0b007000c07208034035901c2c0110180166049902c168043c500500015002c1612881034070510461881079440a5441d440080c0c2944070b6102c00130304aa0074111200c0600014003c1000d0590040e030f0b00b48111010500000301c5850b42c2d00100d40080c100006d08030060416802407420a1404880400e0a030740f0703582860089844500c3c4e12410701d500307070400c20840e2000d001d104002c00d568140407421900343c41c24007080444450400019000020120302007184410046040f801d90340c400c103c1444d80c101c40103020b0300684105a001908095807a04441103501c41c0d1401070180744c0315080740e4100b41e81c801d0955000968035001800715610 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 868216717 1250 868215467 868215473
    0x3061a03070c0803150a0e070e06071b031b05220b0117072f0c0118030b01120506090f06070e0d210f05090607140c040e03190305040b07080c07 63
    0xc0514000c0c002c2180030381d81304075036000340a21b003074040c1c0c8403e09038641581070240d130325000941407440072020761341c89603143e504c0d0800017091801d054a2075281040444004240306146000c941c0d002c10a81420306e81c160783e40c040218107102109603554500c0d140c41c1e5400c00a849900013070b00300f00706050000c120148803003007885903242214041e01041d004142000e011041c55504200d04400d140319001040c94071804965580c08031303058034144803100010707100b101c4200e0f9000004503401501c6c0441907131034000c25592800d2100c402c603428420200810a2004041076441361801210020403140c0e40e6502e040f2202c864915503160000d0940381c02101103880350203c00700304803110320389882001d0003107001011400c1c50104042001004d202c0d9189540d5030800711038035540c00040300b040e200c400c20845424a00c482c915690300c00d2400c01800303034040e03000c030250010703200200807600591014601902a21402c46008040c402d420000401142c001c3d5183c6802006020680d410504140e03 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 868217967 1250 868216717 868216733
    0x20d09140103090b070333031b3b1302091008011b11061522090c06120b0105040e0709080604050f07050f13380a050103061a03070c 58
    0x984c5c50360010392611342900f990b100e1501c0c0d5500c2020036407034030044800038659111008510f4000204100e4880003d18030340c2c0410030509015003042080b88004002c40f0150001c3e00400745142d030b1007c0d02e4883c010091052000c0040c0c07045400b00c1404407010080d82c03c0101d00b02009100709182848c41d070010410840c2403046410385121103400300303140502160040d040134010410004a07910110800c0304128810701c01e2180c2e001d040d20360b541c03140300c1d1401014100c106816540c2d0011b18141c100014805615180401c6801d142c0f101150103220510810503552091442c0c0e01140b02040200a503401c1e0004040d40a00f03240f911694081e20f640310a410010103460603640c2d0f42c01500143e1249406220721700080204442d0000540d0800e800310f150342c10300703003200c0103c5030b52018000c2c004801078280002e0ba8000d00ba1417a2020940b1011900c0c00e44e4040c0010b00924000001160550107441401e094403415001c2c0e5101c45000c0790341403029840140084c0130820080368030700006041c0 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 868219217 1250 868217967 868217971
    0xf072d03020d020f041d07120903031404080706050907051509030a0609081305090f04030e2803050601090203060f2205130506090a151d03030903040e07020d09140103090b 75
    0xd01040b070350740d81c6050042c18070040c40e80c100c01042034140e011301507000c2e0441107800006404440124100b2120305052f001003003859815840350720807108110400c12404010600c4038401d210800843d1652070081c4c1d61011280149500002c02043d5024402980405808500030090842e1082d040755540c0c00c0640d4000c110803100341c180440c0003a440c4400070001009004c00303070b40d40d040701e18007503002480784940130384080c0500144905106440e210509103e00503110012500005000b00c01120251840c5120984450080300b00109210240b03000b16130192000901c40080340302810100507500004854038280c11300315a06d03101c9848100e00400d0702c10b17800d1448030f01908035507080c01400c0c02001007844409030004107040e40043c14122080c08806412100011450b14002d140c1d50051820501300070300784404403c020702210004003c3c030a9401c0c0091983c5140c45205080c0d0b61001d050b10143c020541070401480000403114640e22004c9051601103109002c58641c134240c1601 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 868220467 1250 868219217 868219237
    0x2032a0609030a08041202031207050c1201090c080606040e16031202071701020a08060126060105041e0302010906021203072339060f0c1b060f072d03020d02 69
    0x1031b0003c84029490309005143c0a0200805ca19107440090390b0341030340f44d0000d800240e00c0f0fa20b4440442c0d20740c650942c80300403855807200b00500060f0701c640da400e5a800c011030301c0b0f80c0b249040c105221440d410200b03000c8540c0c043c100c50249414159911589c82d01075540c0c0c0c00085102c1c1220000780d0707186151610b07203041c40d04400181c0c3c5c1d03815401c0042150030300818188c1400319180c42c010140800c180007009880303c501042840d51107440040b180d500c03ea6018902c03107283c2c8000b01d0b040030002c0c2d1540003140e1003600d0b4044240d40c1c4541c01d0b606c4155200c1d43d6800301009000084003a40580c29040c584503502600f241ca50080203030320b20300c94002074081d41250745041d0b4070f051003030852041c4040ba100c2c0f00450030000740c2d0b0814159070722074008102c00000c45400020030541116034003922001d4000c00c1d140c00307151489006050f40c1d00f50885e07030b400c1e500502c0710200340e03100d004958620800114030036240c0070118502d06500c180c2d102c030a2920406a080000315183d40c2d55101a1200c1c0e61 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 868221717 1250 868220467 868220489
    0x20f03010209091006090b27040b0d03120b03060610110a020a09021308070b04050409051501181a060a0c051617100e0c011b0f030c02032a0609030a0804 67
    0x5c1809002843c400e036640007410030745001c000c0002002076039805420802d4005050590b400740741c1000c00c0150103082c2d10325801c8840d086070705c020182c005000a040741da000c1010401c4403420820075582c1c40003504d509400c0314030b04070200c8006110707110041d200d44040044401303901c1140c2c041401d040d0aa400711034820b0340401c0768003000810a800c04010321018005004503824003c001e2494401e40c1b242d113120300e030340b04040701c20460188000b0044040000c1610055a920005801610010315801c0c079224940700559440101c0b00c4130040c40d001010f40381034100442090309884203180c403441030f40d051040311a14480400b803000101d01415245428805000340d4410131440c1040c141c0303c0d02060b40c10100d100a00c180001180e0006d0320092800ea451500780800e10403107940540400360566182200c5d49041c95000780c84d9007000d920a4040b211040300300122442001040d00c401d4103640c3c0d00000f0b154280c54000c0140050340320041c00c1d0b52905045035500b4580343d01560000000c09 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 868222967 1250 868221717 868221719
    0x70e0a05060a060206280c03020703120504031209020102010b030f010c09081c08100f0311151204060b060c19111207090c0302040e04030e0a090b010507020f030102090910 75
    0x816a01500c0e400000c281c41c0c12040a0a140001e03440b0200107000a00d4603080e103400d03010001e842d182080b180da0b10342008002c0c505000c10010042c1d03200308425808102c070401b042d0022040752007494815500b40c2d94120030682a403141801800e040c08080c2e046640b01c5841680f1690b0600c1043d00b11003008000047c00d00290758083c090500741d901014140d04405030000c9090118030201071500c445217407985803a6292610607000c41100c0c0c000303d0800940c44804000c1141d04070345210024000c480039050207440300700000e03162289009044295040301d010071b0000b07031281c02103501007170010121820070400740c080518001d8161181e001146042c56240c0602c00c0b02480c18000d5081615254145800c1050440d030b035403050321039031038020340c0c500e88001010312a40c1600c000d0300c080e0001c0b103020304182c2801001c1d0310003000c159100c0c0c0d178a170780c0003d80c42d140380c4143c040800c010b8658500b411055020028064000c4850301d4141d5000c0100880c165181e43c0001d10031448003c1c500101 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 868224217 1250 868222967 868222981
    0xb1e09011119110d210306030b01030308041a01061211090607150c05030c03131703041b0902090307030f0c09020c03030106030e030a1707180f06030e030406081308040305070e 77
    0xc610301c25000d8020190600d804c404140d024020b1600341221301200404400020f030200c00801c210380c0f0141c05058440004020540d00c0f0000f00e001d28011408400000c05c49800102402000e1082c280400c079080002456440c640c0c1018040d2584c2e00c4c030450401070100c0116a60ba440400d044483d1445c600b06050040503d00c9a2401c00354030740382441c01d61030410072115091002504a0329070450f244501c80070480507a00c080c0151030140a03031901c9040c207280619003044146c3d1403842595070800003040088040c403c0c1c44950100400400c142d40ca55110015840754110060300c20800c01400800c04807403d00007000410840b00080d42d0300e6140c44001001c8429010750a0201d801c01c001600c40d059011f00c0407000600d4280c51111036403501d4009480525060510300c090502e00000000c00300c0070807a0350030440d040c0352804d0184914002d00c03d9200d100da402050701184501011604654484070702c0c031803d82c410b400040c50036442e03450700c40c075040950b8460551001201e00308440 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 868225467 1250 868224217 868224233
    0x406060c1a04020a050d17130302040b180c0a05090a030f0302060c031303080a09021e0f010c1205031905040803181903110307061503020a0b1e09011119 67
    0xd41034900c1d10509450070300780e000070050401072240700e1103040e035006404140550114100002c0c1c1d850824240c0e0b0b08400300034400072020902c42680b14518203180c000709810002d00c1c00782d07072603000e10541266640780711111a00350070000100301008818001c8080c503071a079400010285004c1d5aa0001c03008203440c2c001d183c68002040903803c65420300074414415500c04031241030507898100481b055441200c04802040042406540040f50024123110481c103000649000d41c4151002c03242c0d0ba4a040c0151482441c0501c0204600011008000303400d2242001d950411400c0c03180708140c0d5450030050050350300945007950300d64800420b12940d41d1041106060420303caa0161607881200300c0c00402150381b0040103414801c0520000448040c18022070f10b181e82d00c0303c0104980d03007036031a60310b070a81c0490000b00d000e030f00801c0000c10314410580540340c03010760405c1c000128a03901105103205410400c086414041e0300c0c1e5880c50148803d2103044040303500300740c2035640100d46090000d6 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 868226717 1250 868225467 868225493
    0x1e16120b220224030a050f0714031506120f0702070f0803031f1703030f0705091c231615090e06060712170106020c0a090f0b0406060c 59
    0x10201180000001c0c548850012400c44640c04072501002a4038100c004440c4602000640c16844800403c10500c100079900a83c05004403440340c04139907403001416515283c02c541c14141509040c400a800c00d90409020b0b1098070000c0c01d01c9003058620712603170300700c0181910b80d0001441000c0400c04c101da410400000241103004180741e00301e01c3e0900c0c1640302e100c058528404680c1d1b240c40384401040c072110b520010070348035240903444d44da0302c2c48964882e08255642c1a50b00a2000410b20fa644204190b4005810050030b400704480540d240b0600007003001421190004412182112601ca549035038209080304005440a900c0050b0f1400d0001d0031500301896110b60420340800c143e9101d00c0c040281c80400c94006280d40383d040c002081401a4040240440c08a044d0031a021f0343c040030814840700b00303a4040903a039032124420784e21041496181034010301241c01c20020803019810400300c0701c0790454000340c81000c220208090307400340d40107140401c0003444c24504111417401016 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 868227967 1250 868226717 868226731
    0xa0504090803150d0206070803061f05090a0905090303060904060e01050a0608150705031801090c0f050111010612300503241c02011701030308060f030c031e16120b 72
    0x44c0c0e80300381d6a000649030f005402c4041c1c40c190f00400025000d4490300843c08054009031246008916019001402c5621043d0450302514400400041c80c1c0c94038007800b030040154070091400c42c4d40f56800e01c1884140240180c450301e0b00e0307202c0c3c004950000c1c82118064801c0901c045034840c10a407825140000703100c000d062402a920401c003846610030700f580c0e0008000c2c0d01203100c10b040d00484a024203c0303003102805156480d0390010312420024000b204564080c0c035508264004000c186080f10028440c20000300964007086d0300042c0341c0c0112400700d4105094058040340384003910f40074000c0804460010840000c18805d0700d40c0e48039441005040b000e1040c410380000100030079000a24202c0801525461400100441e0f0240440c076849426400d40d01e0080c0d03070343e810020940302054540c58025405411200c03601e0802203140d00c0b01c604064001c05a042d0781c5080e0a241000301050750b15680140005c06868540c00c104e00c200510942c5990011859142070840c8900409071130700c = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 868229217 1250 868227967 868227979
    0x2030702030705190509010e01091104080c090414030d09110d0201021506240406090b0f030601080c16061508010603510f051b090a050409080315 64
    0x1200180d60004100c0300303950f02918062031a80706043c0c64010308455030000380e0320208800001c616072072041d8001d07040300d20f03030030003131014a03080550166948202c1c0102c079066000000003410034102190025001031003074104165a11043c0d400e40c1c1560000910b8a0019464400360014040c0140144c8204501240c2001c0c1e0780740f03558000303556092042410500064041d00050703095a5007007c408001600380f2494600805582c801216944640148008106207401c0400d13190b645000307031294014500a91450b6403924001500d665100170019400ca80d410002411b80c0385403030a001c100785124180104440c40d90000381800c565298105109c1c580c540b000030004224050030800c6007a500102019003024445030b114400004103603424410528080c0310f2005a945204401800000302000c02180d410308491205540003550016200e1200c0707a1101d82d00c0c00da8000a01540c80e000380b8000e035280d61a03012030180c80c000441030b581c444000c41046440e44811003805e9030b510084504e = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 868230467 1250 868229217 868229227
    0xc0504050c2a030403030c17040b0904180516050a08160b0c0705180405010c0305010e1602010b03190219150c02120708010c020106060302130e0924070f0203 69
    0x400e07a00d0280761007180d40c2c0160724018501250145100d010600e01d0320741580c2e034883d00d0f42006024a04101e0f42294840944016280700d40a480183c9091b16484803d49107049060800c00019245d1000070000441449045400150040100703280140c03d401c03040003181d10344002c00132001c0c0158000e09194000c0000d0199411002c01c11070151500c81403100e440303001840d0410314007001ca800c126040f0f800668400c40010300070000c140b00d24842d1001340821600201d084007925000e20411200716031321b402103800c240c0d0380ca0249103003000c14400003030689008000a442c044000034a03082c0c40c804c0d4000d038011f40c1070152602e1074015070300791f4102662380740c40e40741c2180c4d14907052a44100604560560210342e80c400c4200b0749081c94004480529440702d408500034100144614050740c82c00e10002500c038000d000b40d5540284104044005a00d03010380071014075002030803d0300794081d04000300d43c02c10141d402c3d4030030809081002142d40c5030000e0040d10300d01403681c0140540d801880 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 868231717 1250 868230467 868230481
    0x53304110c0303060922030504030b0a0b0a050108190203100302010906080c0412110d0b0907061706061b0d2601030b2404090503270603013605040c050405 68
    0x1007100d420040544414007140d032010b8607011b40080010300481803a031362008080074507034450040c0c002d90b0f028250303c06c4940c440d000c10300201c8811988040c0c20050b002801c21607580142001135004441c00860702400180031180001c0b68012a00d03940307003140e10b000610965901081c00c3e80038003102d0500d10700c98102070120640c18041c074414001c0079030780005450f080103c46e112402c4503050190001e102c0c48040c0c40c03c0c04030210b0480c1e0101052081d05400075002e445214801c1c0b500145015011054484805020f0390340d0241c1e10000601078803030400c0c04680001c00007554a40701d95034411200200c914440e01808208a1001000c2600c40c070043c40440c840122090b007000c050303a44003a034802c00044100d2070b00b104d0107025502501d0302d0090303018001c0c048020480e80d071542c21001030101141c0b0a00394015100e118141c0c00603401c0c4011f016a410f10000004010300e07203405090300302981000c3c440c006105c49559250140c40c1c80c1488100f14800b485000900303c211741c180f05914040f1 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 868232967 1250 868231717 868231723
    0x901060b04181d0a03170c090d020d0b0708070807050a05040b09131a0301060503210c0f07031a09010b010e100507020a030804031a040803040204053304110c 69
    0x100803102c0c0d600400072a007078055542ea000740e0307031030200454141d0355840c0111000d07100d80d1400816000725025440500340204d11140d01441100d1640c099404c0c41700100034001401c0d403001040381c111804240704408119800c918a102d422036543c0c0258a01e0b04083c002c1900602070256003d2060a005001d091508003058905645a0708500f5481c0c10451380044d05295a08929103207844c5803000d50100294001007500002d002500207004490340c410505a40c1c44810580e22003272004000c8000310102c01e10028001d180c00c0c0c80884041d01002d180c254100320481d401100d852100f40304001032191b0a0208561101040c8002c0040714000000a081ca0600380b0301e00e4070540c86134031000729880c043d2081d2081f00c1c1e0050180030110341c03030303103881d040d59403090000352150900c0080401c461403101184507c1194410101c03800c40d12241d085c80302030031f0060410b050300f10102904010340c1b6120260001a54894040100b95040160a000403a149103040f07800c154020010400300403000 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 868234217 1250 868232967 868232969
    0xf051606080103080306180a060602010b0d11060309030403051c031406150c1006031a060307270603120c0b07020a0203070e270d0e0609030c0d140f01090b0901060b04 73
    0xc92016070317070396440c480001c0c1c4084444003034159003c40e002c2801001d44065001c03400362403c036002046068034042c01c10201c0c5180490090000c10304203064003045c184600a150442816070480b070034103869a40d51030810780741e002094030901c2c0071800790f990150305000300e0b0100ca80078141c14016041030004102e601240c100403400d01d220004403644003c0c2c04221081c110304114030100103003600c91030700302d08141c05c20b1903000c1041c0c1c034600401c10925000c501725048543c5414800c8022003039640d10f441c00d41200301000e84540d0f9030100000428000e190800440003d9070b112804004a45400c00790098090720020455101c1d104040043c3c400080c1c090035502540d824407149e9440701c1100003902078810101d001c8800034054106525000240c02512060780d4640f280b00740c0000c0e00340f1400c0e0050107280c59050388400e8140c0110300388100c402c0303c0d50f0301078110000214401030784d06250002c102079610060b9595500c0c0018000384009554100312140e00910a072898004141c5050160f = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 868235467 1250 868234217 868234223
    0xa171302040b030f01060f0306200d09020d0c140907050c15090f0d05070c080a03050a03052703040504110c06180c04060b0904180c151b0f051606080103 67
    0x40e807440440e081d501040b902880304c01400007800082d49a4982511004003484122800390501c09030101e83c00070b24503c1d42d601465484043d00344482d011b51a0040c00c40c83e9402e90300700344d26070f00306008606040c4500340070704840409603040c0c0100380c0500103000e900402c0b000070000c05101075540c0034408910144c100e9410400c0240b03d458480d07041c0d08041030348a002c04180304649001038880e400a000d002c0090081204d00c030880c0d40e40009948034085c01a0090006404014401c03a0500990005421040070303c2c0c050b50700c2d03451864100c1240d545c0c1a210b200b40d403000c01c0802c0185040c0c010f403148460f211000500300000e0310405c81c3d6850029000401c010500e04090244850402c00280d10700d100400c1440081e83d40c8184d8455070340304160680c0124206000141e0f4415134108101c640c9600c01529a0103915004903080b0003070006d410b41040215007140308a030340c618901c2c5000c41600a41c510440c00078a441c01d01d1802080301298003043c09008030401c501c54200c81800d04603a0 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 868236717 1250 868235467 868235471
    0xf0c060a140d09060c181d04060b12011a03011812050f0a080f09061311031002120a2406030207021309060b0102071e0b16080c030a17130204 62
    0x6a40664141d090060760000402d6524100f800d0040c04082d40100300d0100454035a44101c18112804103002815400b0342a10b2900040007004821050807120f5849800744c28006400d140b1440000d884070201c3c41448180c2c1e44400100300030800654180c0150031088000300112942d00380a0504c400c62903001805070760400c840c1c01689801182120005100c0740851603450b000054081d02c40d1900359120503050b1000c1d0000750345000001030b00d0b0b000c0c01000d4070900405c00d880d500d107a490340445e2081505801588581c13074100c5803900203022040515100c04075613151130780d5820b0031100c004c9040030081405a01c0303001c1c01250b01c4681030a460070303850050fa85800740e0010812550030140514802ca01d0901c045051010560143d20766800c01d1b8290394482c4d070b0703520b03101d010103900c0c1103507026102189004000500814000f012200359203c0c10000078030f5903880d80340e604c1d00000140c0e401500005400f000a552009807440008500090f03516139042c1103445001100d91018002c1c0215 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 868237967 1250 868236717 868236737
    0x120b031b030a02101205060109032019030b041e12180f030f0308090f280b0f01060e0315010506071403030723190c030504030615080f0c060a 62
    0x1840500c0001c0c0c8003600581104400340d14240000c00d92501c51400301703842850400491020b6200e41c5610007141c0d04a0580e00c4008814010320041e9019840c0440d40a090b2040c40301345600449040b130001c4d030282809901c203280a0a01a100b0a031100c4038484035005840b010000514284000d0420744103450007020380c030800b144c3c04600c0680d51b04998115401248000300b0011800045041c4a20030754480c3c41503291544402c0d91a04144006451900407013440198000c541d940100a50740c1040d0b890507400c040d450724000041305513131a0000d501c409006000040e0071503441520408168001c000a010100c8002c00014060103000d02c2418002050001e1000d00e00c00d030901c1541090580b59a41400200603001d0724890380303d101c4459000701587d10040342182550320010341d40003a46643c14200b4411580715047c62012002e0100611010011514900c541401d20541c904c4c4040014104081989031a145007554010355002d4400329286807200800ea4800c9140341c00c10341c02035 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 868239217 1250 868237967 868237969
    0xc05090301140408031f081c0e011716090e0c0307080c1c02030c09040c030c03200d110c0715090915050f040204030501090501060504051003030203040315090204090b07120b031b 78
    0x82c038610390101090384a0f500c01910182201c800c4600403234103680b07580031600724400c015145500811031010380e03114000001040c1c542030b580d00c1e050072045444c0103a800e5483e0340000041c031900303031100c66103130001008000f101a003181d2403a410040100000e030419517030000c4501c00d0a41c04000404041d000700c003140340a1103030015100b2140c1d00410921a030000d00d500100180450300c09000060304260110802c00a0000c1c2c400301540792104680c601420100010050308551200502d61001000348801410382801081c002d0401c00400c011040d4601c84010a880683d4015511040c0f91443d441602c00d08519140700b21902078035950300040c2d1010002c0d00034004d550000e0b20039420002e1002c1044019808441903800482d4100b00700d403070307000c1000c0d481c0500f404010050b030b20400050010880703d0a5a1448208030030000c10405a15400b0600b901c0e14000115110400c0e403040c04603558103c1f01c048e0000040b24410070100321281e0001e650381100c1d00e40c95403024188900c160b95 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 868240467 1250 868239217 868239271
    0x5060304052a180f010920030601020a080408010b090c031e04050304120302060907080a0507030305030406150e09010c0f09120c0911030702010b0105040302130f0e010c0509030114040803 82
    0x2040b80003802419010804108403001e90401c84602488618480003c50225818401d00d10344456110402e002040f0001c0000340e80c0e1300207801c4605501c5140683d500140f00340d801040a00a0000041049690f40041c0030440358040c0142c90805014020071900241e460340b42616002e0320610309034261201d080c02411442070703030018031065001221843c24103800248550041441000329040181c5e2000943d40b60032000c85c0080250300580c00400119202d0000346800c40d000701c40015902d0400b400b40416000c9650040500011800400c0740c8144d0a103d00c101d0f0072524280300c0400c222040d4020b083c142e40e4081c1150144010840c03609018001e1034400180014003010801403005001d1b5503e039410403205400107600b40010700301154811000d603000c50f6406401c140040b03613001b0443c1c010b850503004042219a8440784451081d0090107071f682501003d441d4643d842e81000c0506080d00e01c018160710020700300700240000100903000300c980c00104a0743c80804100e8100480c20 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 868241717 1250 868240467 868240543
    0x7050f1e0a08011b02071a0a11011b0f02010b1509281e0b0408070e04030c0c06080109060e040803040b06060d05101d064e01060506030405 61
    0x100c00d42c40c2c196402907003510745a09a4096042c1c0d001c441b2000d45d94019944540410700c1d1003042c0500c207101041396580130f0525103555941040002c43c40c007002e01c1d0f0903004842030a44140c00036020407446412160284914a0b40410544000050038084400d0a1181c442c050010b4000c03100740c241c24010800f00706603032417060300d0000032102e410380d0359200080c0d40c4422080050f40303294070390000031504072078411501224403480281411610700315100484180060045e03040c00000d00001c00002c42040181024168030f44504820b5410480340804036a81d581041c50141c0094040c0004128142c007039176881070340b04c054510255a43d40100e0080d00500d460030358868148000c1c0403005a2000d420000c7d6903070b07100c01156028060b4401c8040030720503102d03203070462030442ea40100030041c90f810510442000401c610000c94030b100036000440f8043c01303080541c444419402a102e420b000724001000211806400c3d800c150300d80a4071034420411410015035564440c4030280c4280391146 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 868242967 1250 868241717 868241729
    0x60809120706050405070b0304030807081506120117010204030f112101090302010f0b180604022104290c130b040905040302070602070f0e150a060c0507050f1e0a 71
    0xea2507010a1a042002c0c2c01c055400325281e008418001c0344803070404007560702c501d03010394410000f0b0711001801d845856000e0810480030800c010320242903121840101800c1d45440380e0040307203600d070440460740c003001041c0c2e240c902c2e4010007003000846c2405444e0308141d40c104c01c00c000300500031000210600341020b20100b1883e200f12411080e08419070001400a020b50002d210303454411030b211046680c0c0c00c00296201e00300c041c0c5802d000924001c415030001c4090b000500c1d0259220584051250020417030340b140000c030040104005041d0011149890000b001240039807115410f0160600010250444080082403101e00e4603000001e0301300420868194a590b07684501c9054090a000c94060700944284400058000e10007d0f1520480d6520710b10f039100385042c4003895550300405810003005040355440104103a48020510300142402c3c0c80c1d070701c81c10400d0314245040190030361101d4400e4485c00c885d04080e0300c84031410010526003003ca07100f070104007000100c0e004840e4000c0c1c = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 868244217 1250 868242967 868243003
    0x9021614061906030803010e09010e34031e05010f020d0207020f030d02070b090f19260606010f180f05031b0d020d02150a090e01050603060a060809 65
    0x10011601003180c50080030002d05450705840e202000b441550a0b5120007000721104100421070310b0f0200c24519000f4032500b00114001245d09429890400300c05017080c855026080720040b03c04c2d003010000b0702504483d0414021614580300c1030943c07801500700425034400c1d0351900007081004c1d030041e1150764a24074219103c1032440407d000170b4100300c404a00400811030744040070300d80062000d02c00142e0741c0c0104042e50419440d0481a0020070300140c002d0308d240b0004c1d81c2c0340d0703902d280c90700003000002001c0161441c100507501a04801801b03c410380c1007030000c1c848882c4d0003280d000c0e4444030a00f01568907404c40070727040306c02210091207030300021030000020034103181e040d0010084800427822964075000b440c1d400e0341055140c0210742e0b8072020f548401401810590b0103a281300c0e000429034042ea06030090b00108991000a50400203980b80c0c405000c11000080035501510341135910300c0c00e41c50120082540c0c040580241001e2080d01c40c000b07644c24900b0013408410342000744074 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 868245467 1250 868244217 868244243
    0x2722050d0512011706071d12010b04051305071e03050f1e030408070306051e070302032401050d1e020f0403050d1403130309031e1a0106020304090216 66
    0xc1c1560810aa0784454089940000a50303048400b0b51500c01d038020006031445440d91142a41c00101c00f0f03102e5254484964144030b80750b540c7c503020034004c0322001d002150911600081200326400201000502c03018614001c0c04110b000407248203a44c402c26511440c2c00050391018030090301940001e081c2c0c881d441d4850b40d82d840200d50000348a491051401074081d0314a2415100c0c041c6000b003194583c0038080c20408907182c0e8100540004079083d07404020100d0302500380221008860f21404a9000014048121001c8602c801c01c1e848010f02d1040d101c1116000804c5845034865103800c0366201c01d01780c0400c40302d4801c001030041d4008811950b6403021031032005141c20500c025180c5005104104000900036004014034180d000d00c11840d40d46d47e08160f41c20b0000c0c500080c0c040058010380400026001c403000007680d030500740440700c416101d00c0c0048000345203820740f40075050503030010841240c000050f1825194068005a2282449401303903400e0119904081c1040700c40c40c070 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 868246717 1250 868245467 868245493
    0x601020c120f120c211909030c1e120c1707050102010e01141303090302090a06030623072a0b090d020a24020d09050102030105272205 59
    0x1c0ea5605125400c8243d80d032018102400046900411038041941c4c1c02425282e803480b24103d20813440c07038110203901c07030804440d0001010761400031044480403451299050007840a16840c940042540d0644869481401d00d8454803240d2644100e041c00c842c405c0d008020404020324a00140c0450900445842d640140240e61080c4911481d4050f510f081d100704050281030140c5503041422050540750381d1110113040504d540c0b40b0350305504000702c1030000700050340c60001e024012040c044011541030304604040003124094a00c05589000c0182c2c16144c41a00c3c40740305034450700c0b03401d21491008941c03210660414200c0fa0460300c003000c07400f0300f5040081c240311150151207004111480c60011180c10ba03990f400362140600300300e131030340b098984020050640e8401501c0d95070f00542841255860081a1000140c08940994010005001c1030504035002c440070042243d9500000d505c0951151030b9100c0680031000440c1000c000352088844a41c649075290390180c11102e403000641 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 868247967 1250 868246717 868246723
    0x11090405060a0c021506010c020303130b04061e0801030b06040e0609031206010801030c051009090e070302030d02070608130c08100c030b06030405060f060102010f020403033c05030601020c12 84
    0x4440c0030380300d8a44000c801d0001c0c8000317003090070400303481803103062516000019606035658a6089078584810010150a80005940c00008012959110b9100d43c140000078003100243c5075031303d0b084210000503c103200d030300c540b000e811a50047c3d6a02600e44078480810042c019100014a0714440d620500c444000c00000030040f441c8883c240c05000c0c4c41d190011074800c2c1080c8005802e840441c8010b00540c603043c01d0541c401012400c0602c0d4003070b0350b00c1560301510741020480d080380d0003584013001035040c00c6c081440c00c01c986c0d2014140040c01c00d000034280c0c0001170040052140c0b807044050812484a030840041d040840031110318144441000006e002400098000a400c06204101d1414900107890080c0d500401910156440417088280c0240c01041d007411036407100110003080800744024406103010b0307602c54604406021000b82d4000710402070041000e03803213000120035005058820200300183c6022681da03101c800040789005449802194001a10310241c10060000 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 868249217 1250 868247967 868247971
    0x5190504031a190c0309141c090b0a0e04020706062c010506090f031e0d020c0d0804031506031a04121d040c09080601080d140403030507030c1109040506 67
    0x10310381c554019400b0080c5040803801980e580c245410348150401d0b8070302d099002454201c1c018500090b0b005450303110028080e410800300000d54000c0b4241103500c403030003104244902c1942c20b0215850345089954000b51140720100001c2040000103202d00766150b40403140c110350404000c0c852a500c03103007202641440000c00032440d00b0303500101c044101c1c0207440b6a040350402441c290502a0b28403c1c00307203503c042107060750b02d0300480c0e10b0000c800302441c2201009050802c0205158101c1e0300d400780c80c2c2401c40300c1040c802c000c450144000a40440f0803039055aa00c6050450078140c60b54840d0040c0015420083c10500c4900142c0c8640d80c4885400e880755000d12948805000000c00030765003131580244091031440e0fa0b070764000140c00c0582008101080919040000507564103410342403160a80012100d60442d0141d0700078140c3c080803181c040900c11100900d024619034016002d88201100102400030b15440502840b810f10b0300c0c03400f10701c8050000e80007450070340b03045030702d610381 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 868250467 1250 868249217 868249223
    0xd050901113a050904050408130b0d0e060103050a02060c19050c040501090c090905150d0501050405150c04271505090a0e0307020d0516150f0f17070519050403 70
    0x300e01c400380c0d2102500030241d4403580090303c40c03a141040c44824080540f00080066903d48400c00411484110702c416450090100c0c410700c0d51112800c00d540c4040e50046801c0035030640c03040780144040f400120300604000ea045800710350390550313640c2050030100885402c0e800404500b0316981407100200d00801d4403041118200240d0b0f8942c2006811550854400f5000501021080c001b42e500e80d400250019480490342c11001810400141c401032212012101380e515400be101c1007040c1002070350904040190070f1102031611810640301d0340558071681d08105a80d100034060700c400c03240c01e1510840b42d2282030103916082850082c14480e50f110b070b070380211a0440082c0c5141c40d540700c2c00c110300c21490040c3d840c00d00990200712490342082c105560f2800390084800f401200c48492500a041032a04075214241c2d410003e4406015000c101c000c0c040c008001040d1320b0740c02400c10600c0f6040e43c1c1354028540781c00b00300b00d6550280c6201d000c03015900c910b0303a04400783c001c0c016000300c0384 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 868251717 1250 868250467 868250533
    0xe19050102100216033009020906060a050703030207061b020618031804200c0f06060105031005010f12021b10020c0a0b0c0c160e0a0b030d05090111 65
    0x50b2581d11002288580d000c07440544036a010828002445541210b00101001610703500d1000e1000c0765078405442400a12049507403480303010300714204900381940c03051080340d200c1d044c290107520191442c8624030000b0200340c2c1c00120703003041058540c801d60030008a52040d02504100c07480c041d41e07841003510b00a44e038010b050601c284424000013141d40a01d8614000541001c9100511001d440c40d0f000d9441d1205504d442d03000580121009007a1900c003130b40003401c1c00301240c000103040c40700180c03082c8e040003010000c02007000c3e10403145004907070080c40e2541e00503440c03800c2180d0900c01c0b084c9588205000141d00050842c040030100c1402082c03405a882c14501c2c40c40f440308078401c0c4400411107400c460110b01c041000265031715401941058980d140c910040c503560306004607a038a4917402030748130609101442d403d0240760f90220310700310200222155040080c0d91814484e180d001001400900c580c156407151200541d2416080d0456281c1074065040c501071030340000c07400740410 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 868252967 1250 868251717 868251733
    0x9071205120301170f2b030e1212090604031d1314060f060c06070f02030409020418050c0c0a0b090f011817040e0f0a0603080304050717030708090d030e19050102 71
    0x10f14041a0380e80e51a036181100c266220448aa01c0000a0186a10010b0503503400d401c8c0340c424421301c001540744120f200d07001d59a1541d6210100d91810140c61402158018010040080c3d0018402071040b04e441c0161200c0081b0200010f0314880881d440203401403c040c2e5030381c8005082040301d400365004949624000c94140244941802800c030fa0750b500ba07002c100895889070207011400e909801da441a42c2c0b5087e1605411816a03000346d2168500203100400918606070b43d10500e600140c0415a2a2070b00c40030b404d115542d44803806020304001d01020224842c540100087d038200c05601d070091042d81130b942c0d8200701c2c0b00809001030306c08010121120404207040d408a80503668050040c3c481c80c3c4801002c1c015010f070044c40e1401041d610003000c004105044042d40c4514465001082034608202d04064200740100c0d881c0c2c0f4940c000e000c07600c001840f10050303855416060714800300005050404883d8500c064540b9034100e2000000070020801e243c000a054031000c3e02154040 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 868254217 1250 868252967 868252993
    0x12041203020c12070501110304080a1e0519181409012705190204080d0207050f0d0303020d090215070b0603071409091c0914090907120512030117 64
    0x40d214028488526400003001c01e6280701200010b0b00c4d00d0740c015400007031a0018100007100990040e0b505660b0302002284112245600c0000413440c0c00200c0340b2001d4803460200040e0460003402440000e1604140761088820703c5003408110040500302d40d0b8450580d80d1380a203101e0140300c074a50b4001d003480400072800069040c2c48a044424500d042031100040000d2400103000140042c01c0000c4804890081403520b4006000540350520280c0b6001034034010207864000030754000d501556980130301c2080e90740c1d030313808400407603406050242c0d0b5202045401001450701c803074000c0d4024140003002c840101d50401130116113105026040440d110281010368940048c03249041414031580900c0d1203007031002c00c442e00183d4036011201c110201d402400c030340003000d5030040006400c101d0b080008507049419110b03451810b07100e0034090f04200c00300d41e417104840e0081310001c880075a05541084800c1154210a4141220883d142c0d61541c1c401c001c120340101c000b00c6030b072245411580b01 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 868255467 1250 868254217 868254221
    0x31b0509031917071a0c03071e0212090103090503041d01061803060b060d0c032003041a0702100f1d2a01020f01090f0323030c07021512041203 63
    0x31298000705203007403a10f046100f541d80b56020034030880d82003012110342c00c1c1480c01c02e60200d0040380c00f10030070f0b5181d103060140200040c10f0991072141e860510804558050340100300400031020034000395544480700001600a40f020710341c000c00e0751000040016801401d05041c0311040c0468514024503607840780d08603a01a900c8500d8040e85182c1c1c00d0400011f00700741d0080184c0d503c058013490034592030340d8040048031440110f4402003a21410041e0002600c4082c000ca41000d100c0400d0441c180768465500c20301c403a00d01a072045881070301203074505000700243c4090986601c424054504080f402030f0140c03d0a0028540358590402c1d00c448070400807451a240c440c44007070340100d02082c6413800c0f03c000207401d8128158040c002c8a452a8407083c00340c2c11159020303400d20b100441c05440d00419040c0d07000d20b0324012450741c3c00345040d1070002900301ca41000c500240740303480b03c49900010b011200d40c2942da8902660004040d00480b000100840c480d80c0984900703d40c000c400001030701 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 868256717 1250 868255467 868255513
    0x10c1b030b06011e0e04060306050f0115050c0a0b0c071407080d0905030d031a06040305060f06190308130b04081608030f0f0c070b0c2b0816031b050903 67
    0x540b051300e1400d004004d2103084001031101000b080402c19650301e403502c0c41290019218400d200c0d8900c8018400c400658110a07000c108a250a51a10511805540c0ca60f800c280004004140d000701041910038038105a40d001500f048420710014a5091010b5441c1070601c204480c500940c400c5003031190240c140300701201c001034090920b03030a003864210028040060485482ca00102800c00c3c81d4589030064405184030300020140e07402d114500d0800101c00030318191248082c10407181c0d000c6c0f5000c980d43c0c2102c0c0e0044209840301e0743d0040d103850101e40351300440ca010001080000c2c25000000d078248004039800d412151a40d2182c0d00c6588910540184490b061010040054042c12010041090000d00300554030010b4441c8040c110301c0d80000c42d0240d0903130101c0c100e2140c40d0458541d4401001c0d88902e00c4103405400034014280c000c00504c460742c02c0703501c08405422503010341c22540202c010a900040f0300096a180a001500000002030283c031960146d038000c1c0d011004c59076 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 868257967 1250 868256717 868256747
    0x703050c010924031d1018020a05011b0501020304110f0a1401111c030b09180a03030e0309040507021015050a0918050d030522110f010c1b030b0601 65
    0x1091601907502d00f050f281c010320001d104242d580d00090841c8601640400101c2d00c4000240002031a585072241c10740b40d10b2880700300d9031070302c09a03140010b0f62000100b808803142800d01c00c2c500d612044a010009050380400382c0194000800c00c0200150703080d0003012074030201e5421520301c7c3d000052010307241d002c0c0120f150b1128054400c2d21a50702603c00703440d540003a01c007120042d101a840c9241009441c94a40c40420b441e8624200d2a2420700c3e8400e034003841d24051400300d01c0501c2900d550300c0200c0c250241c01d0580c1e5a8022443c100c00b03004580c0c0801c4041c00511035402e140350000d540e00410084111f0301460034844090004d0781c40111012103d004264913405030914a015005214a007910034154a600c2081c8000850a0016801580e00c5e0b80f0001401c1c42c00c81407201025244c548901c4000c98403140010010707405013001012400c095a04101c4641800c0060b10402402c134000740901140b600d101601400c03410101e015688221002802916090015507607410021462 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 868259217 1250 868257967 868257989
    0x15210e0d11031c110903030d020a0201110a0212031510110d052d04080f070317040e1504060911032202011704061107050a38040204020903010e0703050c0109 69
    0x30f41c1144400e030000900e245140000c9072401842c81c0000e4619806030f40904031494010540401080d02880b440039003c0e6540941031428501a100a40350000041c42100c604004070219020740200c4010130000720f0082c0c00218440145803010303100014203100c21442c0c1c0700785440c0f4600280300b230083d150000c000c2200c0d600b145400480e41010301300d00320705440d07004030280400102d0010401c0003003900d810b100d0107090720a08504201d04100d25440d403c003040781381000200b1a24000060080c1c0c0080941c2d0280c4860740c000300050040c2510b907224a071190f0034448103603510307000d1030011805840c0c1040d24800d003032007a00410300e02c4c951900029020518060b61200d40700c9251483c158054801c4400144041c031980c2e201d411604955000e40d8584d111645410030019000b65600c0d19116a03481d084041c000d000c1500d0610032002d0400c190300700400081421174960340c05075280302c003006000380040d4140d08459940c03400e01e44820348062043c00b40d0094103501030700054056428240031 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 868260467 1250 868259217 868259257
    0x2041d091005130b07030510090b030709050a0605010e120a0210021006030308070f0207050319030c02031b031204050612040218280615210e0d1103 65
    0x11402648100512210306405140107031032140d486071140920500f40c42c01918028485030901c0b98403613000070a60b038180340c5013406000f0322080b1140e42e2000c07075035451008500c1c0300260703000c281480c4040c0c0c0003070311886c00c01c000e000707140d401c40e040075040c2c0d0300a030380d5030071402141002c010700c00849014031900307500301d640b40b40b01500304185100006c0710540100c90356055841c8504040b2100d0354015800115181d00380a115039200b590380031646441c1c8010400c0c20300f0940025141e64420600b0b64441d90089000c8003050b0040c2c0140480b9500101030300c500e1400104040c804d95011502c01c4c1c80ba0103a146540850526202620140d82001d0310241c01d10084100c010301c0a8030142051780c1c003d083c188020324540402c100e1911440c80300428a0300640107068100707401c801e1448000300030342041c1e01480300c0020881e8101c00102289000c07000019031421035068100320788410400541889120700e0788100c0040c1c400d0200d4225661001c6124040c1960754407801030400d2440ca0f0424145 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 868261717 1250 868260467 868260509
    0xf1d010c030c0c121203141911031f0605180d080c06070c060510030f08131701090b0106080f13080f0c01060f0807051f090b0f0903060a0204 62
    0x210100345100b82800a61402c0c0c81d03c88180510042d4030003440140b1034003c00041082c503a03c100e82a00321428184020200e043c070340018490010000b00100c0200d0410b41d00c007070140d422280c402c0f10092066a03036820403060038070030040100c1d0350340c9140410210020b03011348641c0880d180110890081c607081c0b10f100341007012551007050305071102c2d00b003801144503402060012a001d12403544500040c04d0f0300e4642034080e284002c242030202120188100045412001e9030704142ea888100a541c4074101510307051201666007020b03000c13102e02c0c0c2c000014124154842c111407401014446030300d030303a03405044801990480301100316800c0320000ca60040440701078842e0041c0320300c811a0a080c01c10005503000d030013030b9282c0c50150b9150003041200355024a213420240206902511140e070400002c2803040d1110307074480a880c407100c0c0c58410f42921402c106005070451403040d0f5030b581ca41c0c81d210a119000b501d00c4920a0140d030001c5901c03101c5074801c07541106c1168146802c4144882 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 868262967 1250 868261717 868261727
    0x8180a03090b030a20090f0609060414060c0607200c060904020714010213090f0b180403090b4605090609090a0204030b0108030f090411160b070f1d01 66
    0x3d0400e024054403084414102005170401c0c0303c1001150301c0040d2121484410007103291401c048483c02244100143c00b0240ca81c641100c0680d0007480c9080c4069641d540840e400d03111f00c94102049000d41e8003401501c50f407000c114043c2c9800324021040e01030755000032035120503042e542158462010010802079081c140c002d400450b02070b414600ea008034508402d820790748400c050481d5400c01d500305022024107441100c4129240c02010040e0307182d11004240501491804181011110000542018442c400400140031541d8002d034441c01310000074065404404041d41c001d00c0200115505c40d024851082d0b06496869400041103919807401c1e1000d5001c0b80540341c2200302040400074503103460301c1942c02003010640041c0d48600d1070608120803075042c0c00011203508100030314500f503803402080e03e0807038004071000500c407011720045404910030460f284603042c841140043c1484000c218040c8608003544903c20130340d00450040f40d07603056030341d002100c400c1d4040440c54654454 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 868264217 1250 868262967 868262971
    0x10f03150f140105030111030f06011103040f030803041109060a0303120b09010308092b1e05060a090c12080304080309070f1e0f051e130c08180a03090b03 68
    0x150000384195079000103105a40300240071107407a11000d4010130542c14244250007030800c05c00500d50650a0030b1018480b000c80207003c0c41d042052500f036440d054401401158002c01c0c204503500d001540ea07107800391036a00211819a41200d807240da0580d941803001240f132150500911200f00d060a595054039040e00c000e0030140000c2d81e42078105420380b1a0050315018602644c06d05886254503070800c0f020340d0342d0084800001020018031592071140c5e0300c0760b84200d0350080752503486040802c90042c0d00000c44078041c02c5445400203018100c07031580d010f200302c140030f04c00300c420b070790b0312040300c0c5411200502c00140381c030b80b08100040200f8800390146400c010781c0e0081e10891a0303208030300010032905404c16202d11002103601d0b02c10011401301e84000300700c9903411740561882c110008480443c030320842038a03032080e440d418085948110702054031003400b1004024a00e401240180602001c541c5030300718101c02255070248040000d074074258298555500c5150f14204490100301e9000 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 868265467 1250 868264217 868264253
    0x4050a02042c1f090b150a0302120c030106020a0b1e010f08012901030906090b0c040806090a050a260f0307020c0d051c111006031a010f03 61
    0x109110218266441c202094011034450003014020860502c0d0070311200c10140003c1460700c829916944070000c0b580128048500152002440d46540004035240c400c101100e00303805500003404243d00e0f60140c0c0500218007001044d05a00e6560443e41c02e220b100038050400580e11051100b030018001411150780301d4511310000000c1240001c5403900384d6420f0300328568071114080d0a10501409110b085c00a405241d101450011034501c6120691000c4280a0416860300340311800c0c040c50343c03c850b0b002d42e404035446005140c210081c0545400a0054050b80c0c0a4034010a801e1803002540140d8103402401030039045815985500c10660b88a510140c0705080b01c00c4144a03240c0751011b03003d107440c40100c07a9030340d00e00840020300300503407885e8041c8549100c440e584082040050202049220b80319000d0707842d0b000307103010350705110a403031000e03150311809500ca0480c98151300442e04507803103195140d00c00201c2d07520310450103100740116448846600010000300c2c401c00130380107040309 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 868266717 1250 868265467 868265471
    0x150b03130f05120a231c0e100b03011a1302030402011b080306010917060106050309010207020a1509050d0506132f190303050904020a0207051215010f120204050a 71
    0x1655500c590802948001aa45100000c00d140c0d4026400c46800101440c0c0829200814401303040701400c680100140642c1c1c00c0b0b4010900500780206d07600640400403c3d50840da41c04801603840c00207000442c00e03041c069401d01d0707040700328151107181044090b8001040c5452403500b44480c01d0007500018801d03410452020031050010340400c0342c0c4510240140c50680d902d250110025040d14029070100300c0d481507070050f8841c0e402c40031481c503043d64041c1c40e100c0d030350b510380b109010b01a005100000e0350003000d8803400602e40c003000c00050b09005454a13074010142d9504104000040309a40160258110b140051410000a092400b0091150700040138607400103410080680c0f1026808115103459011b10380c2510700f80c0f1000d100a885064003550003402c42e60002c14a0046005041c012038001c94241d00280c002c1c006d04003c0c00010302450b607140c10011035143d81d407400c0c1d560f450090940200124041c5448ac031100207032640d107001c0c1c02c600c001c2682448001e2900800c55442c141d = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 868267967 1250 868266717 868266743
    0x120c10090f0b040c140d0803060d0c05210136020307320f060403060b0d17041401030b0a031101090312021b03060103030c03180812030901150b0313 65
    0x1448924158011402803648820850170229500d12411140c010b10344905840140705000405a100712580910141c036894418403003450024140350180e000300383d01c52030602250500300e040303417500e52403540000000e0242d18015449010f590082140c0d40d030741c804149681c0c4503085514940c000100d4170150403a502076a4402070b000d032810180300c1811404102102114400c0d150b60800403a050b0100c8803c007958441a00040480c8a00d01c0010103a41d255201c00d102e969071080200b02d9a500010114100f00100c00b2400d03c41e4054040e0801c0034031002e000e141554400c1c411906d6403640501000846421a1652004540700c051300d103040080240c0e0101c0001e00c5114500d551a01c42e80061045920111108400801d8084802d00035848840108003180d480140300b02e0882e01800c201c0051624040c400c440403403079403c007980500c034451015000418400003184a40c800d80001c010814134500a5601540e90f031140e03803004102400440c1200250120f1141428490b40c4500180 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 868269217 1250 868267967 868267973
    0x120309030304061d030d05090409081b061609180509010209030f0c010e01030b0d060c170f040c050102150f0c040e010f0504110408030f130509100305120c10090f 71
    0x1540b2070b030000d00014200d00c0d1141a0b10b1003026082040c0101203029103190b14800d24000c0981c05001c44241c0f1030354036110288103001c050400c40b86040082c0501240c02002e854009640781d90035140318080210743d03001c54010354801d4a504082d5031561041001c2d400c40710302c0c1f41d0090700010300401ca043d5820480b4000d41c0d601000040d02c50040600074140c010800d10000d0040000303024a24141402e00c400c9034000d035140000a001150312480014001c6110f8608446035140380e100382103000341e038000f40701c42e400117040c003a03103d2131292034100f07119a05d0f00e004a0711284180e441c00200040744010a0a03200c07100c0d440c517484008002854145581e134000210303403070020780c48200c1e10201401c084c8403506080c051562100c507041d60b807600c1c0900e840e60392542c80c07191103440c5003800b0011820000201c450713103d03000100030040c844a05c0d8140b5941c80c10070551b00b840125054800c60409411013840c0c4020354001c1062800600401d0b00d00041c40009865085011a01e0303903903181c1c0d00000 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 868270467 1250 868269217 868269223
    0x11517060412230307180614040306180b100e0112020306040308061c1406090304030203071203030b09010602011a030115061b05010e1b0a0b090d050c0a08100b090601050912030903 79
    0x49000c2d5546c44420b1544c40c140620b07003640180c3c01c07800800600360b941115088821040b9000c2329440384001611105000030f01400810f02d682c0104004c1e035040600001b4500103035440251003021201c450b4903682e070000418007549180000f501074005e0000980820300514085030700002c00b8103410101e922003000d4050030b221401c021945401c102801c0b4101c0e6100b0001140e0051440004501c3c050460300003d941f8a40c92280343d00c1150305c81e040c1c00401d44640c1080180c81d0015020140c00d50f12200081d001e024600300300c0c0154060703514848411700c3e05005688200e502c0030328513403015051980443e03804038544208410172901c12641c4001950921031441640d0001018240280c21401c100284540841d0398a10899860006215000030300c0200c501c003040442c0e0844034044a403070030506080d940410700354000307940e010000d21800c0c0820f6480b90005102820461380e0451010012008001d85446001500501617603400d800c2040703200c201000380c0001c60342011001c40010b45 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 868271717 1250 868270467 868270471
    0x9050702030c070510080f1302060a03050402091b090d0203330106030509071518080606011416030507020a030605040c03020909010b010815120115170604122303 71
    0x180e100242d004841038042c4081c5000d001c040b50028150341100000a2090501820a051a480d0310340410800f40c04600c0e5108000c2e809040c0c9a11a01e0032440034005000807241a4080d031030b00c100190f288050380d0b07044841c030021250f44504084100043c40105880f40303000702d8062003a4289049200e621640c20900000340b480c5807a8140c40402008110310fa042c1e12900505007044103103c9068800302d01002614035540c1042021403941c4d038200c61820302c0001845071000300807030120b070b030b65408100345100755401c0c1c840c803144e01e80c00c0100c002c00e880b90300ca403090300804001c14400040c0c880d9005211481c001403902e12000c0c2c4940f200d90840d0b800341c40c12644044198002c100b1828102441640b20062030002c02c0311289a60001e000d800e001400c84010f070009010800040d0f0303450680c804082c003640000c100d03401481001c0958031889000785002440c1065a13401c001c0e00c0082d03180c3c4a00d43c0003505070b0032042c02f01d0040d180320328a2652901300417440b0000305644840040518 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 868272967 1250 868271717 868271731
    0x803010f03060605060c0a030c02130c0f1d09060d0204022106150408190606091e0614030703060f271101021b120705060301060c03020106050a06090b070c0905 70
    0x28841914500c0d11004440c00f0341c0c48540100014040006140404100b501d000e030741504140000b40418030003d0a100300525440314045d18107803ca040d81c03903004840700d86d804000c1c0c03146036030340090b41e8a428403d0f0b801d088641c2d0220714080028014100310355800715041c409000035084c01d050350442c0d5203e80c04503480e80c01c420302031000c00c81185011901d0f148480c0c4208441132415041c4000d20f5210485003003880051500420490200030280c0c1c0440002d1140c5002004111482d202c000c0034580c192002d520385d42d04249000c42e00c20001c01e1200604c0200500030300c02d05103582d440310082d205030380d0200720302903941392100032400c034400c41c15541146200c0c141060b4006403500c0001d2000a00b5214110340c4014035000513b80500000c0968603400c40d515008500c0402c0d0540c90032001e900300582096000c00000f64183e001400c15003200c1c803e030002c6c84842d40710414405507041e14842c1100180315003c1c20481480f9420041c111b83c0c0c018090001901e40310740c070010568205507840 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 868274217 1250 868272967 868272989
    0xb01140f1303141f060e01050103051509090109020307051005090d030e0301051504050f0424090c0b03060114090a050609061e04090c0c020306220b010303050d06080d0c0b0c07080301 80
    0x4031300c003120710840407203c4401804041056908080d0340e03d40d0740380c0502807541415070b110046071020780000d50401106c080200303d900d0619200307807600d010b8401541c040b8000d1194030400f06082c40d10403611b41c10f940d403540d80d942c18600102c041292402a00c6415014000c1411b4a60030f0b5032020b000f07441c0b09801c10f003c40442d41d08000c091008845008020300c1148101500303002c0040c00e1074082d26000c0b11441c0040c2c00c001641e80b200301c0207244c00e08000b019400c0500d170000c0d08071506000b81d480344900362125600004500f01c2c02400c0e00c580d002c1c0303903404280100f052025150642c09801c40c3c24010b4401420a1f8080003034240c0301c074580b464201e001201040030000c422580c061190481031614120310881c0c01a0301103542c4404c0078081203000c0200a2180c83c0625a0581c41c0140c0f6030400d121031a5565642800740950380128640c030303a500c2c00d00b907001c150340000051880190706c6581e40c1e07068034000c54071803a6298802500813120414100203501c0841d03001d00165000e080c0ca0440 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 868275467 1250 868274217 868274233
    0x5071403040b1603180201200a0c14100206060907031b0206150609010801050405090a0c03030309060b0406060f0315080709061707031e0602091c060b01140f130314 72
    0x1044000d210074001e600f08050521182d460704406025000e03210030350a081481540b080ca0720815044103c0c60301c400c002d4400c80f00c60000340607290309014203d03038603410f00350031f61528031060280703c0340700e2110b440c00359020300081030041c1001e40c0b605500480501d4000794845000491190071038000000600603842501400403040048410382c1c1314400460301e4520b442c0d42880040c2c41d00b80140700344c0d03114540e0364000800c590028440030b0455a489044003464617120f00d4098000c19030900140d43c03840ca0f1207114461824a4802c2800f56465502c602301051003000003140605541d00c51140b10101900340003030400010803452015024078080030503802e0a0000794a40d0744861180c080036907104d0030701000410f08890300c01c811451104100c2d80c5402c0c0c1c0d400e003500a88100c1d401d0300d80080b8114051101c1c3c2d08002c50711100180302e184140154440035004541072000f2400d00180c0030800c02c00111800751000003486425081100302c200e5955a8498204801200703100329160b07000041 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 868276717 1250 868275467 868275481
    0x151d040611210a0246021b030c090f1008031204020d021906090e160c02100309020d0c1707050303031602010b100207031202190f05150a0c02071a03070305071403040b 73
    0x3c5100222841002c080f070400808120003540c0d41100b8070b01907e540001c10300315010351024018003a2011000d003a60203581007000c1010f002c1a401c890880302c40001410110f020000802101c86503400c194840d54580c8070f036000c101900700c2c490300403a4030400000c0b841c40c2045042030490000c01054482040071860124a65000c07100181004810b0b2081100c0c0e510460b00b1880329905550151514030f444444d00b00c0c1076005109154001c0e5100d00800141c8042040019026080d00c079415001040400d0f010031991723841c001805010b41c1a042030001032101000d9034001c4030f0443c11031002140702039941000c585030000c01d524400058010f10b1040c8140989455082c0ea10142440104903903031a448072007504c01c1e98802d0060007840d0030310210060000420100031000d1050404001d03034100751803214000c006250001000d03005012002500c500301004140704051424982c9240d40d5801500b1002020300500003000c0c041c040545c0c9100031220b40286204078418201c1c1d81190034400 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 868277967 1250 868276717 868276807
    0xd02040f0605190f06080702070806010824070804110301060902030a091b0e0118110c0114010b0901080112140d0c021e13151d040611210a02 62
    0x100f4968440302c00c0c000c04103d0ba440c519180d00c100c0d00145001842a122a1000c0b8145940c03a8401c0f01d4a00c24480040788401000c6203500141c4850000c414027000c0d1566102e0b409101201c010f03000c22920340004000c18103100201d15203802c02000001c274030361905140012a04244c0d240780c2910743d148070041c100b1030001954071b10300e05100911010f052402c0380030034415005020302c404d0024814140c2c4507005040c0c008103036421441c00c4140d2511100c1c4c201034001e000308040700f0600701350f2800001d6a50300c000e0441d600074806950b04000c0c0d03030910142e85243d014000b02280d90401104803a90160070a10000d00010083c2c0d8074508545410b00410001c04010107860305400c8107940d0004035039842c100555441481ca000c0401e110501d4a80c003101c17040103134044183c404c50600328002e2030130b00445d1148510f11803203081007060f504010000381e50090000c140702d440e840515011030440c81c80015540001180805071414110316040300900c04200000444c42d000194600070100d103407 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 868279217 1250 868277967 868277989
    0x140c1b0a0504180f02010302040f030803060922022103030709080607050325020c030f01150906050105400501030506100e040b0a0f030b06100e060301140d02040f0605 73
    0x2c58080c40898066100900c800702c00500080035a070f03581907000e046900036010780c3c00800049202c414019641d08051020354001c80d10b0701d20500070300e4009a113850400c01c2c502c503d40c0c1524010348200a00b50b0078800220072600c404020b020b0b14440c102c100c0f203801c03c0158401c0340155540c92003a8a0581d00c940b8080d409000b000c02d20405204104900803001d00c1e1541a40c07484a6042c0d80c003201c06426230a001260283c5501405003200d031911002c0150801000c8460000310b829020b9a507400c48011510140200b03400200b042110550841c04448100c0c4464a01c0010b5003515034401c5902c03182c0c454003c280c0004070b101c28810483c0c0e41e01441003503881801075810304854000300c80300824003141ba410305445965202d4034003145803111b521000180c5411823501288607141d051150310b00c50102c0f41c0754841d0702100150301d18180b04030207110420300e014001c50300f16400c0014190b4406c10740105260003402104080c0050707130312402202840e50300d60000240d80c5040c881400110052 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 868280467 1250 868279217 868279219
    0x2701091e0c05030f04080903070b0316080603030d020319020d090b09010209010c170408100609150f030b06040e1501051912021c0b070908101b140c1b0a05 68
    0x1400316070040c03041d00a02240c1d40b01240c90107100040c1d5591414a07100e01036040b24a4152003100c1d404200d1080210042d40182e0128032075103918a403664040b60b14040883d403180d0190020b00c4440035002440c0c01940d041030002d20b04980314540d8160703003c1282c1002020350040b035141c0608a0620104040d04d0b81c110b00d81a009610740b070312800010b00382c409c01d07000046c06600490304a510300c03420a815a0003034201c44040e22042240004203001400c1540030755a0401d10b00386900c000a41c20f100000c01303c2300745031181e02d8214616218040440802030000e41c0081c2c4400b1845201d1809101c1100340d4142c100051846504040078028410709101c4100d04404440da07003400840c440c21004d0001e079604880014014100c0c203004240c0d80e629400050024050324140319203d9000781411081d20ba0109c1101c2c003030a42d9500324000e0318103100b001c500051000d02101002c0388580d4049000101d0288641d25110180c1034151404140c0041320301c100301e104030a1021403401a92700401003c0c = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 868281717 1250 868280467 868280471
    0xf031e030702041118012d030218011704030320030a021908070207090f0f0905060a23011203020c06030711061302220b0a09020901020c0109142701091e 67
    0x1130a5817528510b074011030607040c0900211001400c8408014025840c1c00001c648101c4218060025002c2d4000e100100c060f075100036900882540314011229040300304440f000b800782c440c1d840c2a002000286c030351090300700c0f0901c0c491014400510056000b0003445200590720341c031910090410280c490048400c210044091021480d0300081e40303401d075644031000154580d4510001c00080445d10140c10315a400d01070100240200490313611f01c05c00c06441c0a110400c4404078949940418500c0e508000405c1001800204540a00586100d1003801254807500c00d20001881d241c0003240c0500004800944500383c82e82c007404155040440361201c0520400650300240c0c51a50961681c4102030500140c00c06000c8a40c200f000101c2014113001e280c0c6803200f0300403019500c01c40781d441c0540301e100c1e8543c03542d51007003940310700725421482c0003540d0014440420064030b404002200600100490680185119140b0b547c024000201c1c0091130b120725800792441c0300b03c68016444258 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 868282967 1250 868281717 868281727
    0xb030a1814060907081e01061e0e01080316060e0a02040f06081908040314030f0403060902091e01061b020402120f1b03070c06060305030c0c01030605040c05090f031e0307020411 78
    0x1800040d00b0001c2c03010948183c2e002c1d40081b6110340c01441075900ca030b840c0502000e181d911200c60345c07010390150f491100d41010117a0701d80003a80d50300e2258070b0551f02b1706604000321001284050740580c4109000e613090743d0743d401c1140c0025040e01c200817454005a0b541388401c00080d2010041201c03101e0600c0d883d02d028142e15165020a8000c40c4009130110740e1213003540d8072000091040740c498243c807800c01500d4036202d0800c82c0080190070802c038000d00c41c46021035100c80320078564000840c41001115443d1b03013800400c6a1000d41060005070303a0755805102801070f0f4841c0041c0804002c803400c901018030706000001c0d801030028000b40203440d160220b40341d200c200c000c1220340c01001ca0400040c08125840d101005210660014049000108070908124000305003a15908000d0342c0900005860b5000c100484407c4800b07500801c030200200c285600301300c0500b81d40000010242d500c42a401440b04188030b000b100c00d240c4030b80000642c5c604501d480d225081d41c1d25000d25600e4201 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 868284217 1250 868282967 868282979
    0xe0c01020c330c061b0408030d0905071d150111030304030806010c0204050c0316020115030f0f02310203072109060e1e0f0303010b030a1814060907 65
    0xb00041080c00190604803100450300444015180300300a50201151541c4921140400344c50b00703425540c040a110028485150a050900035141565210b001452030506240e51260090014000803a1940101c00000621415200422a10303042d2509200140d1800343d0002c2800f50a250040741400400301c01908940c500006130303036015505003403c4005440300c00050303500c1e060500b00258001d0418003004141411800a1401511025003010f54095881010b13404c2e04c20b03550705032105e1784c0d8050042001c030324820100c1c4c030307514021041000d00500d036802241620100d50051110728100c070407100d449480c07c442d041715240c00c0030400c50031403c103081c006024000c001e81c8083c00001c641417080c4080155072046000f00c3d4170010421982c1180d000c200c1c2c0754010a544440043c00101c101c0f4100c550100714503403c85845d801541c61a820142da5000c1c0c2c2c0c10240030303250003669030b15100039180341c940100840c0074000d1403204640f0310740c1c0c0754030391500300c0040c50050300c1d4002e1a020000 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 868285467 1250 868284217 868284229
    0x2060618010b03330906090601051804110d021c0228170709060221030c07141207021309030f050903010b270106090602190311010903030e0c01020c 65
    0x191007103182c00ba6075a48454008104034410400301c10380304000081c034081c8000d41e00c04400c0c0003460541d00000c05a59803c1081000082103c03818042a02048442102c070b050000e1803100150003840060310020f00d0340000c0440d003041c800c10184640c0018040b0180c0c01c0500b42a030315110350f040640c0b40c0102e106000c00300781d0b180307004500d80501c00c040e903010441c019000100d6101d840c90001076246014000141a41218440c60303000d8050510150358441080003507241080b94013401601d991601c0c08600381d15072010100740c07072500100f0031440110030180a98404000741142c007545035801340c01013005908141b0700c1c00350b00c80d180c1690800000d4004012030700441380c1d8142551a41401c0001c280541200d6002075801002100e1001c0d41081e2221b5202405850f14400341803aa00c8510903202070569004a0300945d01025021900b00160b0604040c001c0c402d00c7e0000c4d0010340c030743c10182510b0640c8400c03004281c854406c01c3c8541340800050b500c51000340f00904c540c169007004900 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 868286717 1250 868285467 868285469
    0x1c0b0d05100c05040308030411041112180f060a0f05070e010f1805130219050a0c110307210212031e0708090d140114010b04120c0b190206061801 64
    0x42250b4035010201803042c000e1069a00440d00011001d649280625004500d0f40300c02ca01d9521461512690b451543c0e682d90079143c0e94407800d8038001154071542c02c1c0134000c0c2500020358115200d03100203092075030000d02c0b546005001d2090041072841458a03000c00b40e0384000c0540301040b441000340c164607a40100303d00140b0042c0e052401e040b140c80540c202c40a11180c21440d0800d5401032180c1a5807035030307801088046841107a510070330844450444d078a01c180c10900c40002e0500c5034643c0807491448801011040c02400c80350b20a56500038012010702407035001106540d200840019401c00605036540c201c404006545483c0c0400340020340d0310039054850a8030341c40400c0800810220300e013111071211006180210100403460308070f0711045d42285036000c65081240c001595001c100105c1d040c0c50382c44481c5800c15080051100141003028420b94003001c06413400944c00000000a2803100304d4001c4090341ca071034000b0040c1c40c140c0050082400384409200c4000e0240d1101c100b02c1c = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 868287967 1250 868286717 868286743
    0x60d0b10023a0807090906080d020601050d02150a120603060c0e2b030c050111030601180501021c050d09110a1e030f02010c05030423030a051b0a0b1c0b0d05 69
    0x43c0c9241c031881c6048070140c84a03003295419034130741980400c0c0702c40002000120019035500300e500a0703072a03d007800000001d03002c0003500400c403d4440032083c80301c0310152001c400f491500814484034000c0300c4040c0d5500e640f0a803509552020000c800a9000c003591860000a48000faa02e1030038043c802d4040c0d40d907500883d40100100100b2003014800d00c040540d85070002c0081c003510108001407241765000b41d030030314041091142c1c00100d45005505000450300f05070007a10400161310740c0780360596008903a000c2042410440e83c46050200d200d8076405500480c91600d50041020504c0400f8486130441e44225074000b10098050380802c401200782c03a48441c41e4102c0ca0994030043e5801c1d040640001c01900002c03401041c01884032000b0203c2040308511810300311801018552079180241020b07000d500f160b6203513084160f41d407884080841340501005042c5a80d040f00c1091038001c082146261000c40d03100c407808020031f001d0540102022200351106801a0b9107031aa5841003021a03 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 868289217 1250 868287967 868287977
    0xd020d1101050c010e010506010306120b010e0c091f030f0b091f151806090308340506040b1f120503120a38060d0b10023a 54
    0x8030003940d02c55400d8640d880e003044020b01000e000f0481d440e010b884100d40c400e002a10b803440c0018000c0450090300d0406070845940e0074140d082c500e03541a42c0c900140311a1240004000c0040240c0300d0745145c0e411046500c2c00402e80204000009044d03c4098904403449410125402056640d030100c4039040b49203491503001b2562942204c802c1c2c081d803a0705c40400700c101c01499061240d00304440b107c01c500c40780d510b40b100c1c645a840640d2048403601001d08403180600c07110100d813001099a041d2100381c0380310079900360454000d1511030000144103c0701508098148020051519642074100100406d4484d1a88140e40502115101481000c1040940d440800c0c1441002d200720b0740c10b624002007120300c510b0001c0307040019280c50700e132074051440001c070142d0701d5080840d040c02c1401c0c100f5011082e501108410820740c1e401050300c3c0c4490035515802c41d03910342c0d5a00d039910440002c5402410200040d2500c00402c40e44030100501c2c10140c1c001c00c0c155071408074036603404600c1a8184 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 868290467 1250 868289217 868289243
    0xb0f1b010f0c08150612010b0702010908030c0d03050f0c070308040f0b010f082104060f11071d0c1e0d140103061b0e0f28140f0d020d 59
    0x403405422510702039084145040102d03100e080d070000781e80b4400c202060050361040800020301c1014441d10070441c2840e100c5000501600118000911600c0d005240c0015078640342d01c1c03020b0456002191185a0b9440303007a0580d845501405202e502003c0c440d0101c189142143c9640b07440e22480d04010304011103540040d0400403011070641e1041d80084a0f44055038441c51045c0d50215203005181d5244566014140304402d8000e0b0300c0040501d03035200342d0400c2e241c04025034003080d00d14044024031403140114002e08904029401c0182040c40c0714410020010302c0c21035544202401c4c0c020464010061000303901d0303c800b4404120b0800940c0c4940e29282c0c0300500c802481d000781f904020300c20180c000024048650044a48643c4d110700100b006503e0443c00e0700d0744240781d403409402800c00c00c03041c140c0385080110b14024040400c132203c0303075942e2100351011041d0107030003200000c60051004441400c02082d4100c1d00b03c4291840d244416850300002c124028100b4020300c42c0928182d = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 868291717 1250 868290467 868290517
    0x11e110408030405010516050a0302030417010c02070311010306180504031803050a170d1a0a05040b0a0e070504051005191b060506010e040f06051206061f21020c070b0f 74
    0x741f0488150808142e070114401c07890b0081d100e0744141b15403120740c4030668460351108070600c00c1000300e1302c25800a00c2c14174903680c0c1d1611745800503013589043c1079070b4040000781c8001242c1c00b1160340390003143c002802d02d0289030140101c185020490750302d414844080c800218005003840d00c1035004280401c0c001e0001d078ac4d858a9200761400100e0890034100d00035200601c281c036030340403c001110301403569500c400501c0200c45203085002e50010b421842040b00307005a0000035001b910074503100d468a5283e0000c1114910460069800a100050403400c1000c00d1410741790384040a01d4080014260590f04280c044001c1402420850313440e80854050382c019080030307a03034040c0031303005001038035814506a00800d0350b80318582c015070b100c030585140c44070041555845020300030041449641107200c03c01404881ca0703503d205111031000101003d03207001d829a011125010301c05a5601c0715610a18200350a80d40904920f680510070944081c030100f05940142005170700511000c55406 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 868292967 1250 868291717 868291747
    0x706031d0d17091c0203070312110a1103070c0f091b0e0f0a050a0914180d080a0915020309191101030221090606090f060108060f0f03011e1104080304050105 69
    0x1102070030008004060848140c5d40100c06418000d0007030700d980e4009070402d52490280d9164810079149501c08000320841c282c040c0c0c28941220350300c85d04407424079185544481212031690801d40300683d60742810411940e4901801b4800358458400c0780b40e800e003145015003a0b12040040c148650317041911181c19494140082c40240ba00406c00354500784d480c01031000600340d960151004048000001c3e061503444420a40c1c1510301e440140704030a0100003c4075005005484010700c035417901103010100c2c0040032480a0381d40c81a8006aaa00704540041c0c40d2900f607568611450040c8480800404e01e031040806a1b04c1e401e003005a6184048800103c017000f0000078402a08141011321030701c48000621184a80e00694011050343c4030010000c014400445080d03001a120500241d22410a00302d070b6614480c0107020808112204000a03080d11404508460b103402c10782c5503598184600d0042089500d09a503610340b4150a2483c1076461f840f4500400f41400b1001803000480b40c450 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 868294217 1250 868292967 868292983
    0x5121c050a180e0709080604020a060c0c09111305030c09071103040e01090209040b190b1303050a2117040b0c1911010506060c030703030b120706031d0d1709 69
    0x5480c442c0303000d40711000c00c0507810043c1d4603040007035084040825143c0d40091060300541d0018110701ea44d40c1b07011400c0712602d900f01c90841300c3c907a0000000402c00700601500b250952651480c42d01c0710046c407070142a013042c03030703204604c250310070207035803c958a411845031f400c40300300d227002000b1a68100c4410b2461182d64040310150034054000a004041540540003201c0d040350203210900d60407003048400d0510200e103084844e5062000c001c9481c4c650300a0800b1003511002c510f206a5a071221380c00c20b10341e81010350b400c00c2480741e201041140003000c9403080c50142071000213a6424100c1030804800244018031141c14400490201000b0b4001c0d41c07400404c03515403c2c10410300707040051001c0030500d07000b2465030800300030881070b14001c2c0c140ca10f003e0b40c2200841c10b1503080e89084000d8403034012800d4020103181c1141c0c400500c1885500083d1505480110700d110181d001480b42d8009a50a00d20a4104200400c07910750b000c00c04ea034900d1030300c40c2d9491564070b03a180310301d08001c00c0c = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 868295467 1250 868294217 868294247
    0x806040605030d111e060703150308630a08160e190f0b091311060a020d11071e0e060301060501050a2111030105121c050a 54
    0x340b40114800c1d90b0700c28541e40b140c090a134107403003000b407007035055410707642a06500150b42d03000310380068146d034481c3d80300c4409070314000404190b01c0e07500d41300c021880d80f101070b00000ca0444804a0562802058400755004c1c0e06814003034200c0c3d4a40e415028403e08040c402c1800c06440e4803944151000c1d042c41610782c80004002c0c0e4030b034550300c4180c03540c1c44102008401918081d0038002440c000300d50300e6644541c501101a940b46103044142034000c151844240407902e40d2482c600c0d010b41c4803075401038480d8002031110300c030300009420800750090900303040b540700d81d404100da0394101d90b0125480c0c00030842ea0034070000b00030310400180e003030007100d8000c0b80c0346c270640c0501000800cc1083c0003030201c60075060482038544501e4203050a9590a001d5103012400c20010000c1c0b851050480607001100281c4481000340d0f00c0c0300200035200d181c4040d00c8a81c1d0040014041071600303001700f0f50a1508100100a5502010004407048183d03219003401c1c403101041c2c41400c10f0003440c11441d034403d = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 868296717 1250 868295467 868295473
    0x20a0902092704051e0c090403120903050d0e011109060319020a0305040209070503160503071b0b0405011112010e06040f052401050705070506030714040f05010e040b0d03080604060503 81
    0x525002c5405103290100e03000d8400d8400c2c0403140d58030599207444c070102e03206070001400440c60050300380998902c1c0500110100100702041d409105280d204480016100f5034401d69035550b40180e220903280c1409070114170340d1500c01801481201401101c0c041c0d00b084d10b03150b869039a981390391940701c0d086003c202c605600008800b6030542e41544440d1107980700320b0341b0158a8031940c2d0120390500044412040e0305603142e0f40c02c02c81311b0050003e1948030141c2c2c580008243c0e54002d810301031106001c01110500502d8041c402048400e02904440749182c28615003001403048440007900818890580c650610701c012903042e0300c554100d22007261002c90305210908010404018404204250441043c4806a060600c2d0f101e40201c41c5144e130020001e2040300e0504081100b81d07400075008405003c201989010f1194100002d04001c11521617070b9505640307410b0000d0b222800c5290b62a11491070141c4055860790789000d45101c2c107415141c558820358584021a00800f66034000c0d95040c8 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 868297967 1250 868296717 868296769
    0x102040b121902040e0601030b0f030d0c06050f0402180a0902041b0908010b0f150d0c092c160c320109110907020a08031503010e0703020a090209 64
    0x525000c409030149031900056081d20400721542c40072070255000d45072250b194100411640d43c8640c10101c603c11b07000f0b05150301242048006468500b04d61004004104088010401d00408c0d00c205ca070301c640018100c6a0354501940041c8101c040d04980e00740400001e0085001080198001060103501400403c40c0c0c40a9010080681070003148440000d40d07104e00100342110f0601642600b500c0242c003503c2c00d143c1003c1009600c3c1d15a000036800180203009980d20007e881c01580c6a5007410f031540002c49050040058400707141404012102061100721041c1170a10350750258070201c414a802449071000307108070780c0025102800b4001644d000c114a040d92078900e100c1c0e0103004249180c0144140c04c120031070903180c551b2409400e04000c5501c019540c01c1022080b54085a03a205035811000f00d9540d0011680066942402e6141c3c80c0440a60b10300b024880d45914030a1000105081482c660015040123114082c140324103801144801054551030a40500d00054501c503907009 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 868299217 1250 868297967 868297987
    0x81213090c090513060612020703050f070b06180708040314070c090501090f0504080f0c120403050c01080a05090c1e03030c03031b0c071a0714060f090309090402040b030102040b 78
    0x2100c1074000d0f03501c070340d030081c0328420040428482c0c4401c071803007602c401c400c4d00001c1961034000c0d00031500c2038051007000c1102c1120402d20740020048035102d41a61100b9007041e03414020303190154800007000c08076850074452130b507400c03408aa03445070b4140350103900c000e201c0741c071002d150050140c002d21619202c0d10202c1e15060307a03000541030360f61a40040110f134400205020030781c0c1042d0f42c040c16031a410491f00030044080070080400147c200c00700da1908084103110217899215034801d440c0c079000440006401d40e445018590031680c000303000d000c20700704040410341380e103038041e1500e110f85c6407144018101020715811002c0180010250f9450b10500300e000b603200c1d0b100301e800c08007030395000c2e408100a035040d00c01c2d2243c804109004091b49414100440f80c2d4001440072400403180501546000482e511003419204494070080d01990400010521082c84094440b039610382081c030030b00072a0780700c0501241e840f40d012180802c1e14000d42022900a2042d0741210801d0140000d094202c = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 868300467 1250 868299217 868299227
    0x2704031e110105073204180f110702030d0305090f0d030f0e011b03020d060306020c010c0305090339072403020f0d0506151603090f081213090c 63
    0x28041c40002442503036034144044031085040002080308001d002e0b0b0b4a100c164075182d04542e84840100024030f825141c070078a200100420500c41c44540d2156800701d61200c45000d000300b100080640d250621880742d0001c0e440391000d5a042080654420000f1800c000030000c40391350142c1b550599005411b410b100401800d09607603002035450801c01884c114910503c03941d51015001e4003814071802e4064001c4000e988070100203062a5200c41c400f10203c0e42d10b100512000c00343c01c0001401c8201e54030050b06450004002d40c01907001480380e186084605821203144c48a54104050901004001c040c42d0360302c0d20204050b18402c44c0c90100303800c00c41f00c2820302e0091071550318441f0601042c03011400e03446020041c000b0f41c00280401e203c090101d400c410707003100004040e070307a2000002c40500707180c1d04500050400c40340a001c688040c1a00100c005010b00001c9408240ca141013500341c0ba40c0300c240e404501c48030300000a031024202c550640c21009004650004d0059000880f40144 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 868301717 1250 868300467 868300487
    0x90b1c0e0d0206010f0302061b03090316151119060e0607091e0305150c1204061a040212010303050304031b120314100b0901030603020603010f03060b2704031e 70
    0x9440f0700800410040003400d041c00c100d0f81c1c020490380c94801c00910440510a4564456507a0301c4184080035055500b4002e859408041441060030302d45005000003d00010600400a2000c2502030380a4028007240d0108a040f0324204440d20310003510b09040142600345558205000d03250078000091790000c00c00302240c1200c560504c00e10346c050390014800650380700c0144180d11201013842c00030b4440c0e158039400000c884c02c15092080e5402d4443d501c3c541110308a464a61328180050b607001c040c40b030104d02240940c4d0843c00e20880003501980200180005420320102100260800d440740144120040e036440c210200034200e85840c10104030815403000c040390411558000e2007441254441c81034004500414a0a00c2d0040140c026805450300504140d100c4c82c002c00582c55040045000f09960360001d1009031540c10104110344522290a209101c1e130614030640a0841803815003492601500c20fa40d5140d07450161280740c0c0130480488215024124030f1708450300300d07205907 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 868302967 1250 868301717 868301743
    0x3110609041e0e160303030507050d091208010f0501091406090a0e09060a050f150102070911030610180315150602010e0d0201061d041b0803041a070201090b1c0e 71
    0x10020a6a0f40c540a44900180d8a210903030000440e00700040b03882504116000503840c01c0961808140404100940b43c46032401c1e6900440e03480e42d400301e55880350034a4014619038516502d0241400300003810407503144030f0380309502d2072101c109859070f13180e400312042142c004110340e400319554105400d1009048513030225038090b86000407820000d50241c58030400720404411400d0303031400d00060884c01c03140d045d02c0c110721234014003003840d00061264580b0701e038041440c01d48234039142d400c00c900f200b00c140c0c20780c0800520704d0700c0d001d05525600034141907070760005000b0001c0e00fa400c0d505000340302040f41502003134a80840001d01d25019803081d0034403c0c40b18166600c01c039401000b40d0a0312030741e10a84103170005113078990100210301480d098004e07100708500703100c550121f0a070f5108101d440c4c2200c00340750400241000158210b0604000307003005858098206017980d000a01501150b11441c10b443c48000343c192071090070103025201da4800520704000112010364080c2c0e480d03d50100300 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 868304217 1250 868302967 868302971
    0x30f0c010b12150a150e1801020301120516060f08341d09070f11010e061905011a0a1b0c0f09060b03150d0b0906160e0a03110609041e 59
    0x700302c4e00310241c0501001300300007080701020f282c0b424042002104004000d414406020403020181c3d04d401e00080d8000c1c14003130350651141b8554140030f030a141c501084d95207e200c22090401c40740760003c20220702420075091a01c0782c0d580f01c01d5044030788410345000e0140040208101002562003414101203d2580e43c5d0b51881d03007030030b00003411103402031411b45a880310400c000914a9446400c2c1c0c0380b060492485d120814000030b46a050070f580c000d94110a45421400800400702d408400303140f0240351450f0144143c0d450144a202250000f8062076160800091089200c90242c0e4564403010b1411105d525802d046042c02d0181c4901409000d0854904150010303405415014074005c0e140c07540940c91450b22440d03584180c2e111080501a0441c8911a500b40800c1c02c012441d40b082007954094036052800d40c1403c490410396042c0e5209010044021124030381303a80303803010152507200c0d80031307401d507164000003503647c0c040d10b80c040350700c1802d007072050a0100d011003031801032820384042 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 868305467 1250 868304217 868304221
    0x2010c0906020d02150a1107050d390201050f03161e05030a090f05060c071a1909060e030d0603060e060f160e060706090b011502030f0c010b1215 64
    0x32a20f036950000400016400318501c2400c90307540078011600503141c40b90001d0446080c43e0020040c0d00540000d803500d030840150026101e80001c103002008078012814400d0700b1700d64414070b144a092110b90b4124000c69040310086900580446e0000201521843d40724035010b62071408104000b124940025400b00c00e180c050021601002840200d42d1070f800d042d55100c20b41100103044010007620030000010005021039000d201c030768061560f0100e8140d4070510341c200b1001381c10305201c01200f544840410040708281c1e09680c3c03a004c03060068082103481440c02e142000c0c00c40d01c0940300ca28000010300e6510300040f54041c0c3e040f644218024456500341d440003d86900382125900401a0300c2000102e4001211400c0a49602c1d00c6c100252180000030100799640c1282100701c4542c2e81d03c413800805c0c4641c12400d0350041c40030361120a00d045000c507000751280119082000483d08c0402e5110407082d080d002003076a0b22020b00360382e04080c90080001e503203070401d07901c26041440e1440 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 868306717 1250 868305467 868305479
    0x10b2b1d010509070b0c030904020c100b0f1f022506020601080c03070b0d0603050a03081f0b0a03090302251509140607031b120314040f0605040c0f0602010c09 70
    0xb036501c02d03034000300603004092400c00b8100c0300d98004840054140006c101605081d581c40c8054035420342c0d840028110301c0007102d025403c8448001c1103900ca1a00000181c0660340c0b80c500411002541a0301c1003104602c2860980c0760103031554142c400d01001d590010900e401c00541d0700109c0308641d00319821642d0310b15506032124111910b45805400c24142071000c22400d00003008003001da84e01c0040d00a80e65101c5506090784850218000380c00e2405101e040d0000100300060040c00001c1c0d422003500d040c1189100b84900d0105200741341d221440304040c18000c0c845044040d070f609444048002030000c00c00440d098a004d50904150440380b00c00000e80320320032410503640b01ea08045089d10f018000c00000e034005d60401c5017040781c41010020341790760721006600303658492012400a0141120058141c4030741840704206000107004000108050200395504190820341c0082c023503c442c02c0513045160503410018092007814400107007142d0540c0440d2800715140d940b9500b40c2e4443c5 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 868307967 1250 868306717 868306721
    0x18090c090f020d2d060815060619180e0906060910050409080a030c09120b100503030a02070305010b06090108010b09010302070803071101060e010b030a0b01051c020c07050d0b010b2b1d01 82
    0x40106d052650100144810604031a1502c0f608940014001d504120707101d040c424500c40000c004030009003d0840e17500700d03841156014030203404084142a020302d0484d405542c2c0e0100104440d214170054030200b01c0403101070300001e000d010054004e01400d0306c1c6040440061b440750b4030010000e03181c0f800309401248941208004d5134911858450381d01038a840e0740e0f030310120181c41440c440000b00c10010302950104001c3c000340c901500604a000d00d181880c90856420700180750181c1010403080403980c0c1d01c92102415030700e001c0b00c06030311001c401e00101c00901800c070005010860010500c07024a0b005400007a10b480c03a20000c2c09040d8440e0001a2514028411901c001606002140ca80b038001d401c5100c1a90062414038103149440c0c8024200c1b40d0b009400a047c540c1c0040c204a818205014101c081e020984441c402c0f4135943c0c0c0d5100e1041d505104500007000c010588907055151071051502245804520900f000c0515030740d64001c012640d640c900c80c01556040010051040c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 868309217 1250 868307967 868307969
    0xf13080a020604141306030510060603050c1c0b06070309180902150d2d050f0c09010c0c090f020301090c080408041406091918090c090f020d2d06 64
    0x303005641001e2500b90b103030313080000316915550301900d804001d00c2444680d00c01c190003140901e0040c0303d50094401140304589898001c04101402e03c001c016001e000c05089a0204a07000301c3c0d10300350201c00c54508000c01d000b61861b54400c40011b4030009059004440d581690120741001003030b50860880d100495082c030a009400203190030b680102900140050840d020710752002084080c400c500307401042481e004840c040d01603d0200c215001840e01c076003540840000b4501140b4105005415810b000d00031480b810041e6a5801c07008024011040d0401868242d038140000c82e190f02c0700c180a50404d000b80c5c0c650500d0f0509401c01e262252464602444e00703c41080e107807604140c91040c61382da03061301c0c0c9030f00000304202441c1c05480d0580c00041c000d10001c07619030b038a818034580000d512070307018288684c070342002c4400010444400c050f02c100e510b406000a1000400542c4034040c0c09400d0442c01c0040c40c1000c80014900d040c5c201527080e02107455400e039122401c4289504981311 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 868310467 1250 868309217 868309219
    0x60f170a0b04020105180405010303020318030a02030c09041703090a02040c030b1e01090b0c03040e0709030b1906030f0b040501061a09090705280206070c03051c0e030f13080a02 78
    0xc540702150155024200400005181901c21408800c155000c10251407083e0300c12070041c0c1c400690320307203100e105002c0702c80c1c6107600318050010f0b10802d800003a51361034841c0ba0140302e0b1110902080411101c0d07000d600105810b41030444d128035191408030780319545003509900031410300109100c501c1c8a803142c210704040003004250000255958541c4d11406029102e0500046042c0843c10b5003540d1b024001d000c450200461382c860030450081071048001c2d00000501201e420103000003195640d0786a03115015924507101c00010700c09010140c25254400381038081341c6501c66081c01a07182d000752040f40648028881c0c1ba40c0d0721100011001003000140e000c1c00706004103105403920f40c0c68941c01520070302d4002c2c01c120500b10325100603c481103800041c0d2001035010f111342501400641c1d8480c0f914248246840f480741c4001c0c0a911444000c140c6034041c206418a040c0c0c90341d8085082002c5450407032751250265a0200c86d20741c8580803142c00a21080d0000070442d20004003800d0080d4 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 868311717 1250 868310467 868310483
    0x10317030c19121118090105100c051f0504051c0e0607020a0e0f0108060f060117060a080d0320071e080708030c0703080a061a071401060f170a 63
    0x5042e0382d03000c92004280b12a020032204440e0707030746a4040ba01580e83c8000840c1866980c2c1c00703940550014000c085d480342400742031404010850383c3c1d200d08030890b06215070b04142c000155645044c2d41001e4a4180e10b03c030303034115015428480e075010380c002d0b0b10881c0700c0c80071602526030890f01b616a02c0c03012401383d40001c3c0040c0600400d41014005804000d20103041066603070340b11551650f003201d086070100390000c0355400410404c10304100c1e070382c0c010004c00d142040604007040001c00d8200c84800c046401d00e02c58020a503652070380c044100041c507a007400d6400e81d54180000801038013004803642003140e101955042c2ea00854000c441c0c54135400b000c50503448120081c45681182c0c0c544050b540c4803000e10210340415210310055106403018104956510300c1c9181c080c1c499000609a02e404514001c018002070b11050700301e044881070282856100c0626140128003c86081e003044070f2542003100004020b2140c0c2c0340d40040d100c0780c102c1c8001700c410a50486030390f00c18038280501515 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 868312967 1250 868311717 868311727
    0x5180c090c13080609010b0a0609051e1311031005090f07030507050706060b030412391505160c050c01050a170f011707050604030209130515010317030c 67
    0x141c000c00408111881d10416000b4580d9221620b0400350100d0b0390040994480e0f604038081e20b0502843d00c054501d074100f07480c4090400300441c03800c0400c0d40c5100c1118550003841031413aa500c0da544002594068020700411018601001e06030b001510402ca003010944800701c2e040c40c0c203a40e91441460380309694010350391541012006000c01900201c01c1c444208004004a84a800740700041c00c400310ba41c40d9281884c1c81c0c525058040c4d417258504029030440101c1d0702d06a0020b0419000300141083c0103840840c41c2100c1c40c0f01c840c1c0d100100700c0d40d14407005003500411500818800d0070820ba9038942001c00ca201503540a00d4988014416040542c4178601c66014001800c40a005460002481c2200c1d80640d10300c8a029580c1040d00c40c551401007291921030f9400c1480b2003101d0000d89401403410010a41c00d004034003000b442082c141c00012210703288005901c1070f6a400c2401c6449121081c105407043c200c00780001da03a11554041d14090802e8214100c0f03020b01c0c1c0b07440300d242c0382c2 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 868314217 1250 868312967 868312981
    0xc0806060d090c1e0906030f020108091009110f060708040608040507030f03080f07030b0d2d030507050c09010f0e060d0605010b0408150f060d05030d090605180c09 72
    0x980e00a0100e800300035921800d5001050340704040e1005004c044000c02a285010390750b041e01c01070070b0762108041a0401400303000003a80300404510701582070801e03089607101d1800407030404140d0552905080e00d400b212009100c2c030f510f901d1144903029a51841c02100302002d1142e01d20842602410303000d003c22081003624807541d001d90b8080d01510031744001d40d03241c1d500d424034041550001d4002805103820f00040541c06030340950050340c1741c20308100c40c00041e00401c202c140b103100081e2041c0304145084100814601c1e28046080150045440705107203458090081d420104013039070507205100c20348025003007200c00d00d4117940031450041640c40c90002003070412400144815048842d0481c1840040c01902a19020301451444c240e1100e040c07007006450008052000c05584100d01e040c4500301e094148903c0d000007095907440d10301c00142c10131514502c504111485210f10f45017241c014000307982d00181c0205014142103911040303080c00650707a000c840c1e0780f00360301c034003070802003101 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 868315467 1250 868314217 868314229
    0x120307031e0e19030f1208070c021f03062607090209031f2405030d05030f01060e1507081e0307020d26040503220f090906140403120b03010c0806 64
    0x8410200f001e0010000d8503503503070725266000702d0011503480b1492100da0100c603403c1650503a1119042c03074447c003c4045034000485031000c6810684902c08810000315026210390020760290030f410881701c0046030440622820402d400381e407000a80031740c800100e0004000c1c000c0313a40061000303004100030000c0790928030481c13081c081d4405001c0e580da150580c4014801e1002071641354641170341340c0024030340002e05080011f8200e001c2c0c2004000c20401980c0003047c4012410344006d4984180840c542c1004110058031864080381540c1020400038100b21201300104449840901903180302c205442002004d80006d583c000096001419101c260501c2801710b00110751000030150356484104246030070240301030b01d0a44094100052a030b03a07455040c840302001c0ea100c0741c01c9a41e0301d450100c41400d41c1c8114010003854548640d05041441641d422030143c81d43c03000302891440c2880d1074080d25000b110f040e0a0304460070041e8802047c90103104c1c440403824139465a90380c039a108010096 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 868316717 1250 868315467 868315489
    0x9010314010506220b0402210a1a010813330f02071e020a0b0c03030604110a3c0f020c04020a12020903030d0203160e0a03080a0518120307031e0e 64
    0x10f0816400d01800c0c803014238400f40000382c100c0412030f016080c2800c813150015581a0301e007260580d01a000604c1d1a40d0707015801c50f9114064405072000c0704000e00d40307a21580030007511707c0d1801040c1d901541c1070b407401c0040a4000d1090043c03c0101d0203a810a0000f030f4003d0541c05810141100a90440501200a1090820f2005017003c40ba90748882e10340c000d641244162441c1039002100700102c50410b0f205000000d40c0e503029841c01c200135441c0040030903402c41010701030420046081300140946020a4003c4280d07403884000250280038010b2188090f000110014442c4500d0821181442c5c821a40411155a180380e41c9001042c00c1c94040c1d400a03006a400d4841044a4003078515244055402038820090850001d4031040000b0b240480d24032500303100b651410300400002d020902107039011b0030141055512081c0031003090301170340c101c075850a420400c1800c40c0014000040009c00311039200b5210181d41e1602c1c1c0507200042d000c0b0070070103408034203181c08003d01c901d80034402e21 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 868317967 1250 868316717 868316719
    0x60904030e010c0203010204140415030206030c0706022703060703060608010603110c070e0403140309070512010b120304090c110c1c120302070209011211010302030a090209010314010506220b 84
    0x2100d000f8890340441e089a000d03600c2203054220001141e02d6070715041c0152010504104101440581960002021072001522100c00d01c074001038403104006694045e00c20103a9884c8c451781285c501800d4012217201c030500d005120303020307203000100100d0003407180300181c807415990b2207001d03803d001041c1e000b0021040c810f00382200501005488810402821340985556242a1094100b9140107403410790358123032002c84504103104011080c1ca00048080407100e04644a0768001359030450103006020840c03429800800d194200000390000000400841e400800100041000704104071980055292201c016801c041658240d030314040b00c03e035803541c03d40d51280352803580300d5450300b003059812501d407000300c0d801142180a500c0c1c04881c090040210800381c4182869544c0c2e240c2414000d5000c240c14154044003144216480d039011111055002d0117500046d61a0300342650b0950010521607020342c03d00001500d6130070610080c41c01d1015800803000001000e0710004007a04482e0152 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 868319217 1250 868317967 868317977
    0x110301051008071e0c050f0d11122706070c0806070c21021c1116150c050309060c150108010c022a090c0c011a06040302130b0909030a17060904030e01 66
    0x85c000c100240101d00d03900ba034140003443c41568031701d0054180030500f1801451a0848540002074414400803901d04051070742900e003400c20700b005080c0c1c218030f00da9050380d04035402280c04800c01403850710700c0041d45c42050031503809070b544040445000c2c0200754028103558021080c0d080200018941c42c5000340c442c01503e00e0310b410f00d8203588500d03238194440e60005402030310002070100b090020310148140600000e40d91400c288051a4060020075058100403c84103403106011050003a5803001d000144070581da2021038001c1640c440782558568840d0480d0400001c1c4d06005116464100f5603540241005143e0608000d104074501000411040403c14040c00e490707840006491041101c17183e02c40e1981c0400e02c04034212000a170000e515615100e035105115641c0345c003500d00b201c0c0c1c100c8003200c51200c6100c088020300b40080989420260032410703c0030880022005d031080000c0340d07841ca94520a4040a00710b420010740d9003580100d001e00101e40880c2c860156510b00715418182 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 868320467 1250 868319217 868319237
    0x91f05130f05060a080a0f05100e0c0315060705010f0203010b0d0e010203091513020a030f03030e120904020d061a0301081606050a05160c1e080303011503020715110301051008071e 79
    0x544015100f04540e03a0702710312112403051010700d498140ea59003204002e4111820340c0780034502502e0805208104030711401e000b08000c0100b02094114440072500180b003552a56590038040076a6000480050700d21402c0004030340230300c0c10502c2a40e00c944c040b0402050045000c940c09002c82c2c3c0040d10350600344008030a007601513125860504000c41c031071461132004000d00d00340107003122100304041825401c07000203900b50b008450b099500d685002c60700140c1c0d0b0f40541d03641c20000d11042d40405000409404000300c00400e060180d81203a81620a840c2c040846400d00d46403074015014a5010810a005840e0074134455009001800380ca0741c02d20001514079144c900341030f500c40e4407000400008400d882d01286d5400998030040050800460071035062812400181011442c02000c05a000c104801446800c0c1403026105900780300030021031409600e000c14660090140e1030080140d103010b01c0000c0e22aa6031035210340080e07503c9255500f50004c1441701e44c4901c4202c0410828000a = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 868321717 1250 868320467 868320491
    0x609061b01061508060d02010c1e140d020c060f0706050c0f070615091401050409240b0907080606030a2a020f0105150a0902091f05130f05060a080a 65
    0x220b46005040240e14086030603e041ea401003200740c0041045024840c91180840140d0704071060100041d0b00c880c000800d40c1c403401841c2442c49074142e002d004205035000c946d403198000304246954040d20b80c00c0e246031000d41018006c480c070407000700c6101072500304145004610744c0d511494000c1d9943d103170240352110b020610340c030980000c44291a0165150070030740c101d05809080304014003110005001520f0711128000036194140709150282e5107925100e82000404440e0100c4040000d68606010402a160303200400b0074507645405503a01d207000c01e40d4039020b4440ca611600c2c001b4080c514654510f02c540d8060424480741000d03018071103615407001c0c4128801d9104110040d1300074040191461102400d64074047d1900c0c480d0502c2c4d00104031170343c495048200c2134501200015958203114004501541400e09a02c81c808001c0c0c2110410258090700400420b4103485282c0d06146d02c0742d1150719050320a04c0754a6101c202048140d00d03d41c042c500780e45d40902c00f1900010039410800d = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 868322967 1250 868321717 868321721
    0x4060f09050303060406050a060f030207060e1606020f0c130b010c0b0a090506010902040311062557030b040f0317090c0f1c06060501030b0f0609061b01 67
    0xc981164142c1010042082d40e003070510034440180400c4036008501850614040c010841001c0814100340c0c000440f8418001c903908003189581400c1c080741c0980b01044964811340086010b000b00500500b0b0320390f008a04002400c00003608010054003c184005140c1c0d001020f00c0b035041810300c500c01206001042804c0c000a1055021000c00300d0261010b00c0d010f810700d10140c01601040303105102c00d01c0417402c030a2920b1b41c4403009445070740e910602000111340d180c14514841012900c21204078003000340c0d08081181c00400d1031104001c0e03082d00303820940e1200c2c41030000c940a510106c0848075041c400c4040d104040d00b903851400c0410340b0b94581c00030918040310250703070f0f1fa5500daa02c0c40c2056484036281c403201000c41510002030a02c1014203440d45d0030260918452108500000785655816056070340414440012200605d150b1030309c040070380600e1007028042850304038190f0b01810708500f074009404008000d0344c500404282003008980100190f60342000f1052041c50400f0424 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 868324217 1250 868322967 868322981
    0x3140c07060e041d030c0c0d0c06140d05190b0409030804081e0f04080d0914060702040f050a052403070b131206090c05011d041d03040311091e0a0504060f 68
    0x2807406903546c1c20502520300d24050340c44004d00e014058450400002c00c5c6101d0201069440d1b9180019002520440e80c130050f018420800314002d1424090207402e0280c0281610911503c00d41404480c80000c2000110b880c0b1000241c046000b55002400007440701c00103010104a83c0c04504040d80400000841d0b40c224140c0d8402d502030004040c032129204201c003242000326450068480341c00c2080c10880200307242c50507801201c021582e00215034540d0450031104440c01420012450b1400d001000740606503954003421070189022086510208001c00140d4070103401001a00c2c90028100350135407000c40645000101c410f4003080482e5290103100f00355010f0a0082084000390038002d6041420390f0185043c024400e8900040070421489901500d5040f02c0002e01c020510700d600e680c80c00e01d46032411507800005004010070134000304001040400703407a80e1806990700201070400c1c4905248030340034850443c002440000650b0040c82e4000c0c0302e43c070003042031002e003104039013501c4013 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 868325467 1250 868324217 868324271
    0x40c1d180f0a0803090609120a1d090720030301081b0f030601030b1e071e2106030b09151305070f09020a0216050906040f1401080a03140c07060e04 65
    0x4000140081710303500700180c07500b211011000d010203c00d07201501c40c3e1441800580010b0122801c0080403240848103105840f030406401c400c054900f00f02c0080011003189001c00f01c0c0c0a10150940b50700c140001a20706803a0302600410002b0021200102c0c0c2551038125203501034a4030300c1c403480c80c0e1030a00001d4001e500c1140000c13100e050800664503040340d14844105090140001c05c41e00d180d000d0540070714003504480001a07070100103400c50342540741d810000702d105145031100191604a03071100044902030220140342e82c41c0e01c0c10607a01c0b020846880d030344812041000c6001801c4512241864500c158205e641c2d2030b5035640501560446940108211035020a60f01c6d40103406101d505e0741600c0610329401d10710b0070840041c10964010300800c2c0038035600e941d50b0901c8042c50b40050070f00c44e4603a40c040e14560392071440a54034042d41d40d0443c002112910240a145c0c0300d1000d03102002d003481c014120950400000f00c4401a0079030440307600c1503d9010132000d074500c581210b160702d82 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 868326717 1250 868325467 868325483
    0x3020312070c120f0602033d0f0e011521020d0e0604030f1209080c0f15010e01420f2a14060f040c1d180f0a 48
    0x107a10700346a8050072403940300d008182d04040e503250000d00c0e000c00b44289542d101070b005840c0c0e1a0410b040c6036043c0c07140d481802d0a68481d8103081155103100000407000d41c41000e40412503100c440140c51100b041c0300754010f8060b18801808072000c44400c10b8031500300c0340360041024828101680c50940b0340140134840d90303400160313a0b00d098018000d04030780b02180f02c0145510b082c1640c0c000c0618101c0304c1c09900304103040c0000600860780c2e400c1030203980d401a00b11912070080e03190003074070341c0c5081c80c031050f0901c11015940451990300607298120b44942201880c5c42c0c0c85c02c40700340c920b0024204503c2d000c076161079003e0841d1480c0080c48629a01080140802031500340000e000c142144070701c20184404e07107241103607550782e031308204806039210007000e0b140340b8452900e0410301e44c072809404124080c01c1c1c10401c40d495031501d4544158040c80c48900000e5807401401c10358504414004d030107181d0301c0002400b88201d99a40d1a007410740c00c00300c0b0150440c48200d18106002040d048600f98 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 868327967 1250 868326717 868326727
    0x90d060b1c140d0c081b211908010b0d0e0a080301140a06081501030b150f22150c1703150103050901021305130e011e0e0a03090b0c0703020312 63
    0x110301000301c2009108107041c0060201d1303003612051407030f0060000c1180411031221440a00141c14004000d41c0020075007a01d000b00f1404200c0400c50300180d01d44a12150340c0642c0c42e40e501e2069249904950701000014a84480d40400380c01500c1004a0000780b0b124450364100080d031280002d60003000320082000002c2d03d21010441810041e84c800301c1003000d244280702d1300701500d0b05617003000750090800040c5041d0b104007049244000900318140781901181c0c018003000641c00038024814910036540c0c018460050710100780045003d5142d50044218495107002c1c00760f01442c0030180030f81c0d8141018807501414028a9004a480f00e540c0a0100b07405050340d6007501401c0c0e003062100000350f007064400e040502480303410341b107054462110040f0585001d070b410b42c48140e1300080c22009002c0c03086400841e412420800e0b42959101d031501c117400c07162200c04121102a40d50581d50940380518001480311030b6004450a0303c4c15001d1303100004010b0764100301d08280c9241e03020800d503c607 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 868329217 1250 868327967 868328003
    0x907140334030c020d0e0d05100c230703051902010b030f030d140402030604060b010c0c0f060809010507170a020405041401030318030f0b450102090d060b1c 69
    0x150781c01680b02010356010030711700c8407003d0700900d04540480c0d054840b0030084105042039031170416110b18003600b440c94202ca4140039680400c0c5a524807001851009850071f60032940182071007101d202400041e8280102d0894544150f5502054420b07031002080c5901c040b80001d00f81030300d207110241543d1000032040c104102138010081d50345152000c1800c5c0b4a80354000c00e840704401480148415510068241241e002e03059002031150000c802c01c03602511031141c007600c49003a004540100720790400050038090140201072042a055941d1b541010031400d003088003400240201c0341c41a000d000c086683d880c1d6124074900000710000703010352549141006048240e083d126210808041704080c80443c0000c0d41c407100b5554441c409001540d0385c050035807040c0c00c2c41440d8007140f06960051151542560405001c7c110320110b02225600181c14124203d2096607699600a01d0100a86e400324555a0061001c480043c0c05002100c2810781803401c001c1e1068022036a80f480444100c0c10 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 868330467 1250 868329217 868329221
    0xd050a0608011a060c030f030f0601031404020607020d0c180209040507030c0519030906050a020714160e04050a05060c0a0f0c020d0609140f0109050c090714033403 72
    0x107050910003000030b400a85105030284001041407805103100117842a0900b008000b15400303c60b803120102c0e01c0e400c0100700d00301da070310303059400764002414007002071818195030030494040c99004100920b802001d5092046000011100380e460109a240c001010000102d8080020318030301001a500d003401d500304030490300080c10741d0040525001d1041031064011084034004076042015190780180c0c00000ca0281c2101180100f90314148001c1c4050702e811600171308640c52054088846020358095412707602c2c01040780940408012203410031410481d8082250428080d10990b1200b000d5038036124605602911002c00b2050002920500c96038040c0350921203034200e240a00020030b2030f8000403040d00ea0f586000d4820b6903182894420440501030350305071440c40300240e4003c5102c0b4400c0364020f203415881a540350084078650619880c00407003c0784207440d0790b01d424440c0074200c0203498490700001d0a01c04040f403940e203e007504e403003240200c0c40d00700d86031669540e0f59003802d100141 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 868331717 1250 868330467 868330469
    0xc0501050910150608070516020607060204060320041401020a060e0c24041703070b04260c071401020a0f110a08010b030a02012615090f04170304030908030d050a06 72
    0x8007104818070a00411750b1143e143c6070815154500680c480d14810030700c00b543c4250500080d03000c50300140201c204000794014000302c50464808208000709840100c0013403860540038403480300104003c2c000141c17000c004030010403043c03046a108040a82e100c004468002240351110b6100c0102c00d01d131491304a0034251940840a084c100e0f004000c1801c403001c5c040c2d8001c40b0b4164100c90400000030104009503000d0309c6d00005084014286420035007508811859180c6d80085005500c201d9011040e0448141c450760070001d2900c107113000e0401035200341c5d003160309046010b1107059101103214180d0301c840d071500500040d204800183c042044101c007903800008983d0400c2c20840381540c002c9503030911542c0a082c40f410300843c01907150202000a1124110a4084000d020803050f0481c60703038101c41c506848040c0c03580c8a04080b44d5581e44122401000c0f941a520290403448020b8007858100c0d04c039013009000142c50300f136054116008119055952507a800801c50941c0160154034 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 868332967 1250 868331717 868331741
    0x2306130f02090409201009030308040f020315060a2306030a140a0209100f020a11010311040b040305070f0e04140102070204050415050a06120215040f06020a0605060924010c0501050910 81
    0x11549030804001900051f1305201c041c091111400014052042000007010780e40c0d401416110314103055200301c102c12205544190140041d0040070a442540c024282c03204c50b1048440c40c900c0d01160104499944000c2c003059045880b165040141584842d0b0b550291000307000250301c9000510a02110001000c40d443c104118030742c8815125402007420102c040d0804a0f204001c000600141c1c09021009864456007000107400141000c42c08080c005070307440303802541e0745a6500c841c0906001d980c0d0141788044004080880c0014000081c0701d049450003c0c0090305105060700080c0480310211001c2e80c2240302240341c448e80c007010303110f0142d01c00701004040110320b0503c4510391007685049070007402150100d101d40701d00c0e64190306a400401c05201c0c200c000c2900c540c0b00a480341c0701451b04550700c6c2d0a101c041080b84c541241c0340c0384a241c0d420039011a05585071040b8180452081e100c9041c4084140d03040c2c0415000e000361032140410900030150802103203804c07012110034124007 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 868334217 1250 868332967 868332979
    0xe090c010302090d0b07030902031c12020c19060b0303120601081e16030603021f090f050112090201030b03070b0417010504150e1f2306130f0209040920 67
    0x2c141c02ea1315600f214283c940c204840c49800e030758000007940100100303200a545445400d4001c20300d84400540402032003a2075403000c0c840a0840e02c0d19050740560b0103a0032454100391142030b04030200727509444000d0b000301808240913a02101003801c5a001c0c90400c80d008000b4801c1141c6540c01110031a0411a148401150301c08650403940040b8000307480e11840f90707061015103000d14804c0d00440051500240881c8061012003200c92116404007850004900003020004003640d1840f043d8003202d40c10b071034841031044042140401800b0300e800490605907103004544041d14208501c04c0640700728402a42d0b00d03400c0814446401c0c1c007107544540319a0421041100090301550751007051a11000003240710000408242c0c1041200100c0741d144404502c4e59a0120354160054001d0550322140101040c8004011001030f410440d89980c0001500c2100d00e0340c0c02007544501c43c440b111820060512040340005415201c4141d0f0a039100b00210031103420013000159603008000c012144 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 868335467 1250 868334217 868334227
    0x151e0c0f0703020d2d260a020405010806100c0b191503051b0102071703040305030705061501030b01081306020903030703170a0c090b0f071403030f0f0108250902040e090c010302 78
    0x4c40303042e40617520b0303110082104821002280e01507502c3c00c0030141050700e61540c020701e42200c2890003508284210b5000a01620108115040c00d00700c12030201c940303507a42c00910040d81c58402500002a08260010002d0003402032404064811100100300525050f040c651460038001e1920441d08010714164068421301a0b49a07000542002294403040350740303040d2200d64007641d0550240390720203046400001140c0c010440d0103e401b5100700c4103618140703a4000100011812107507440c0c0d00f5070105d03200d50003284d0640814013400d0340e400e21a070310261078142ca036401300b4195086200110b011820755000f00c0309038044a064240c1c400c0481d9401c02c103038100d03418000c1c400304651045010060002511105a0000c0b10440d4001a0480012412180c1d410000381e07aa9004441c00c070100004040400d4040600c40c00b414122145140202010740707500c203000c0190303800c0b510f80d0882d00c2000800001c40c0031090014000904161410716494504240c10a041c6040110428109441041 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 868336717 1250 868335467 868335527
    0x60c030c040e040206040302040c05070b01081207031826011b050304080f0408030307120b0103051b250308040b090c031504020402121008151e0c0f0703020d 69
    0x90740d080701d421507646a070580700c3c1d002050a0748502d80001c1c0d009070400c07000074503454004c5c2c01807480750711600e04100681e84e14007503991079107007680701802c9090007001440c01103480f440b1220b43c0303084005100901c00350303034020400f8040c01081d41010000c02100b05445955428840c8451141e05850b20102c40b0301e010400074210b00c4020700080c90000086241d848500050080e500a84242d908595403424040009003412a41c3e88440018a051240018113075203c1c0c0070311405042c116245d01180ca0342510444001d4100344000d01c8552084070410f6110018050074090741402a20385800d00d0820b030030640e80100c001002c0c154564000504100e16440010381c07403007520680f403a40741c7d00761134601c0060040e104400c0d031031058800300c0b000c0c070001d02c004030402c008070b03114070381103407940c41c480800c0140540341161f01d158200080000d0039a041c00400d03203207902085400240707250103590300d078002503604140380c02c0e001a0310169070726403081d40105522000c00b91840e0b050100c000e001c0 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 868337967 1250 868336717 868336741
    0x30c02070e04020d0c03080f07020f030102131815090c0e030a031704030e03030307020c0f030a03050702040207051e01150506070b0411060d06090504170c1e032a060c03 74
    0x40d01c000e004e07010300704064090141a101000c0510342c0869400d41d940a000c1c0c0d490b0340f03504241010b81c490003490324403104900d01403003220316090000c0b805114081c502022401844841d0400d4503c00b510f415044a0403101c0780c98580107490150302c00a8000031600d0020040e00b890f0030103500952040c80c0760008241c1100d03e0380702c05416104030404c0c1741e445181c101d59a621014003950540300100c00e01140e1a000b0030b0b400014102034642840c100403c404140c1e99044509003c0c000c104100481070140c10b0a0300200b0495000328211080c10308441640d90100e048080e8028541e5503824034001414200c0304040001c142c11180b10303041c0326580e01d400104d0500a04006d141d00c2248413103081940360300050321004900c205040190b641c0e1105003a000e800d08550440b410504100c070302c0356201c1c00b01c043d13405440b0f10720300400d04040550740c1e036601c400c0e0020021000d8070003440714000485045010785c1c5d40030f11a8049100300c504040c01035140000161650710b08a01c184104000070b2020 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 868339217 1250 868337967 868337971
    0x1502070f080702010201020403120c03080702120904020c0a02220c020304151d1315150c1b09182003060a09110307240c02030c04050717070f030c02070e 67
    0x2807400d03968003500d20040c0d0084c8240e50004003407550000b00007400d1034000381400c441601a40b100100c0d0307540e40788120380305d200413400d241d40d4400900150b066800c00703502030591401c00360129400324080b500000c8421300e8402c0103004510503c000c83c15500b01a00424508200030f0000303509090409800c00701d03400d1052404d900f045074622032149625021880345000240183c14040d0402421060300064080f03118144540d5000364000600410101c8220b107000c0044e913101c1125884981c0c1c0c000c030300c1110a0700751107500c442c094046900b840612620001600504605400c07020628180c0c407a00b120a005000c9a11a0088049641c4000c140300b6400341192030300080c0345200c0d15290f9080e00000540680600c03480c80301048840c0300c03a1060240d100c07400310345a65601505070807518040c010300001c3d010740100425507034030b0410344c000c180c019005090034140307009414031000c1d0b40c4808030382840c00120300007a00713082c1e181c1510031564035440500c06404014208020a4196240 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 868340467 1250 868339217 868339223
    0xa0506250804151a1521040c17030d0509150601210b01050f0c011a030f07060318020303070b01030c050d0c0e0912040306050105010f08011508060423041502070f 71
    0x1140d0000711207414142101d84c02420050084101e2010214174042c55000008101c04a00850b6020b000590348400c065106070790020f811076040341000c1c0c17480c06140646805c1c074080d10091000ca58106c4403401240d1054201400a09903076200d1118400c0101c009080281406128840c8060340044a65a8981081c14280c042068100342c0d004072101c1c4288805220742e204081001b03a2a00410340020010406034942020320f01203003010035445d00107c4801071420303401040c2c2040103a00a4020343c2071005c040e9200c1b115501c850300881e0456104580494850340808018810488110b00d0103005e090203540c5541c22076080d50342d0b2503d5080c0d5020386820f007410803000401000d8100b00000c0c0340c5603400340050311b03070790b5900d003210242000b8002c1c58040b50b41c0c014952829807160000a0480c1c2048100081e084102a004c1e10300070317006844550800d4640c0300341108415403428240000e40780c9820154107103403e0800c000e1a102c40001c5088050041021034003264020280c14081a0 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 868341717 1250 868340467 868340471
    0x50c240703022a03040503010606080a140121020d0c0608040308100f050603040f060e0a05070509040804170f010c0207050103290613120803070f0903020a0b0703020a050625080415 79
    0x40c2026a5131950046600441d031641c2000004103015030b000701c1c0c60b80104000d810a104805100c2c1d0300c0c911803a42400713050715244c94110b404600710030540c41804083d001400b02c400d001840d840364108ca10854203d000812039100502003019403112585030b01900058080c5040b030300300314602000718980c0c41000e11401c0c01001040500c0130f0039a1b14945103900a1080050003000c2e08101d840e40c095180640350b501812000086600380300008a2199a10409061070503003400344100441c9505002103095110351202d905164809103d600c071402c0e440e40090034100d260000040c250340a000050003d680480e07442210b5801c44504034454003400c59805031a60106802c02080b00090b03070000785642d9107880200c06103c211002140142d03950b43e01e4802c280c030071320b4050300c0c00d03002440002d40061640c0c000700f1010121303801802c4140d1113841a00e48a001d9525030342d00d400804da819038118a45c0c2244403c91012003090070012204a040014941c500342c0c0f1031400c804c4801c2094a1034035 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 868342967 1250 868341717 868341787
    0x2010807080f010b1c0213060809010207022d04090303051501051c11160804090b091501030b0609062a0a051c140c070e09010b0f10050c24070302 64
    0x10740e501c042c600e01100c121008540354400c6140c1f40454528074071070309002c82c1c01540466007400c0180205d0358040d0b006000b003003140ca607070035019048030107a04000c9a050803042c03d40d032043d81c0318010000c1c0c0134042d80d4003252a040010b450307940000c2c1586114140a8100000781c1025038980f40002e030f21140700c2001502641d800b610000300c0c440c24a10741c3c4d212400000c00c2c03040240074070240c415104254000c21812007100c0520000351000d50b0b481040c1e4074454501c0300950b219070825100001c0190104c0e0401c00d0784004580940c008100a0071140a14039003c96904201c0a0b015000171b040030042c441e2000c3e9450707007034031450243c1d0034081200403014031001250140c1140030483c200e0340e02d4184c1c1c3d0012410255110a0180100b8500842d8100030550b0610140944442c0740c200801194202050204003c21000c400d4180020710000f0b0103140d00c2d000c0103001c210300300705501000d0b0204031107540c4801c220328001400ca0301411f106100c1c441c440e40c099002d40310103518500300c3c1503c00e = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 868344217 1250 868342967 868342987
    0x90616021306300209090105040c091a0f0103110705010902030f06160e01021f020a031506050d02091f0f03140709140a0b03130c150507020d17040303050702010807080f010b 76
    0x4400c480103500704c03a0400a001b441441580003e200c0c5001d000d000081d543c592a1042c207440d9281c0301c078401c6403824074020310145042c80200641c08814140026400320300030154103650030016047e81c4613503441014409504003442840a1038403944050040703494148180c1c01d01c00d61140b21141040402003421803280d008005000840c01c000d040742803001e2900b00c0c2c0c0c1c800707588401c0d44040020f00b880f002106619080e00c0c0302e01929500d8440d141044880c0100038000d410401196601c094111801e403040303020f001c0721410320741142e95100b44882c5041000340a88010b040c3e006100e1160004000266034403040090903190b6444c40c0036400e003120000038a104c004c64010075019480041070000c0103c2e0010074003440c41c42954013190181d0365000003494504001c035014046002000048018502500004031749031141c9800281c03104a00c0c06482d894000b0780044000c80c10024402c400e640c1c002c64407507400903052500101c58035188802041c0c4000c18402c040034180c01280180e45 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 868345323 1106 868344217 868344299
    0x103020f0d0302120d0f060b04080607080c030708090f0f16060c05033114041d12131e06180e1308090616021306 50
    0x241c45604d12079107010b5228500d40078042d40c2c1c4860010003045d007803050502070501c1302c4119403601d051901e00d0b031400344041c00b55424424420100000350701d08c18112640241546068492900c030321800e24a407021129103040180225401018080c00000e4402d071404e13414000718070300c26601c13841510000c00111340070f00035410400810130124165143c1c01c01008601c10820000300b103400d106c011664070707a04a10300301c0c1c441c0c2c03d00751828075050088079400c0000f03000e407425591040014a640341c20307500709212000c0010a60301c00746006030303108030010700d0803c180e0304180c18050800c0300800454040d101c0420124100000320101d40030801066a4000b090008182c0701c012040d03504c80e80301d08040ba0044020001160b20f43c0303880d0060704101c1d4221440148107030441c81046405c520208206868a1900c6400c000816001b002e02002180c040c10345110904005030b6020 = true := by decide +kernel

theorem cover : BRFrame.Cov 868165467 868345323 := by
  have h0 := BRFrame.cov_init 868165467
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868165467 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868165467 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868165467 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868165467 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868165467 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868165467 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868165467 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868165467 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868165467 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868165467 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868165467 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868165467 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868165467 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868165467 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868165467 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868165467 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868165467 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868165467 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868165467 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868165467 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868165467 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868165467 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868165467 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868165467 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868165467 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868165467 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868165467 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868165467 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868165467 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868165467 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868165467 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868165467 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868165467 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868165467 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868165467 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868165467 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868165467 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868165467 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868165467 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868165467 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868165467 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868165467 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868165467 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868165467 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868165467 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868165467 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868165467 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868165467 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868165467 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868165467 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868165467 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868165467 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868165467 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868165467 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868165467 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868165467 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868165467 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868165467 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868165467 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868165467 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868165467 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868165467 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868165467 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868165467 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868165467 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868165467 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868165467 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868165467 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868165467 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868165467 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868165467 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868165467 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868165467 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868165467 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868165467 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868165467 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868165467 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868165467 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868165467 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868165467 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868165467 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868165467 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868165467 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868165467 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868165467 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868165467 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868165467 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868165467 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868165467 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868165467 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868165467 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868165467 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868165467 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868165467 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868165467 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868165467 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868165467 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868165467 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868165467 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868165467 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868165467 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868165467 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868165467 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868165467 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868165467 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868165467 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868165467 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868165467 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868165467 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868165467 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868165467 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868165467 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868165467 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868165467 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868165467 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868165467 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868165467 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868165467 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868165467 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868165467 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868165467 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868165467 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868165467 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868165467 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868165467 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868165467 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868165467 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868165467 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868165467 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868165467 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868165467 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868165467 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868165467 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868165467 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868165467 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868165467 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868165467 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868165467 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868165467 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868165467 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868165467 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868165467 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868165467 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868165467 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 868165467 ≤ n) (h2 : n < 868345323) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
