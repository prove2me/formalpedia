-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5331
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T15:31:10.543782+00:00
-- url     : https://prove2.me/submissions/fd94b725-bfe3-409c-b6b4-b213517aa6ee

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 958633093 ≤ n < 958812949 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 958634343 1250 958633093 958633129
    0x2a0c01030915020a0c050304091413031b0609080406050301090e0a111314132a051e0904060b0f041b0c050a080301080303040b071b020112061d060a05010f090302 71
    0x14800000c4d0f00700040c02c06000709d03803000b00e800303041c2c07041c40c00c01c04900070300d150b5048940809000200c1c0e0820226041201c24140000c505481410100040c0446074402010308500240000701d03164850041c5068540e1180c0c203110011021141ca640c69480c0d42c005861500d1880740c0720898900300c40e00c1015081c2d0b181c000700311080c80d14160814203a0880e10050301581c92000312040000d482e903103a40d40c418401d492040c00029020310010b48245003c0d150082c484c0f41e1001e045000c072800364031007808006091268030700d0070385095005040400c0c8114050000d21180380d5403450b00b8050300d00b0590002d200c220415100e507000f114a44854202030700c0c14011108448042866031000b14064003074940110350b28206842c005400078001000c4d68200f002404440b40d0368499442c0d400481c40d02403034002200b5501c80f060400400b02076009070015402c070302d8138940d00c000d80d1000900ca950101c0324001042c0e52107006403402489034440000160301103030f041c40140b4141c3e0740f090900c8200 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 958635593 1250 958634343 958634357
    0x20c090711240c0a0212091206070e12070b1204020a17061509070e092517060603010501051c0f0e0102090405060a06232a0c01030915020a 61
    0x982003410521002c18240c04803025241a440146145074290b070040b1210342450300d4a844548000e40341d4131004c01d03030b0b9907003480001c854a155a8000b1140040c08124095031190304104201415102610030014042e1100c00000c0800c01008140354007105c040c2c00b21075142050040640700740d100004c000300c0c1d201c001ca00e0089008201003001c4140181c0d80303c0186a6402c003800c800c1c0d1200b45c1d6091071481000500308102d1801d41c4504800d68444080d82e00407059290008120110407201a9148070054420b88032009154052140611b43c41d00380e001c1c030b40daa10340d8802e10070503201c240a800d0100e0800c1212642c1040c0b9842c030002d0405400700006070036814000180162018011001d03202d07074020a02684a150500c43c0c40e804c4241126041211460154060314910a2000400d0180340790340b41800c0382d080d10f804540c03401c2030714565440d0807024980d1108030b100201409503145c2c400c07103da20a55501a00c281e10400307401c80a1142c05210541d0b05001079405800d00400308550 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 958636843 1250 958635593 958635617
    0x50a0e0d0c0e010e1302060f090a03051f0f14060d06020d09030801051201050405100903020a0804060c0510020f040902090f0a1401020d020a0b0103020907050c0304030303060e0c0703020c0907 84
    0x10200041029041040341180594542004101081380141c5140303d000b0b401520f0320016070f50030044800b52450b08806544a1400400003040040583d10203003190245a00103800000041144040100348803010881041502c1124085900076815101c520074060041000b5192401445101501c40d041c003520300504111420103580c410780e4101c0c08208030300c00500581ca403022038070322044180e4000b0492450583c440304d543d18a0031020a404981e207004082c2414402e00c1182e0744239800409043d99282d0f6204000c00800b80144191740340d00a5a5134682c6060703480c0201ea43d52282d002e407080c1030905050340d00b00250302000c0f1250340141410340044c81615040301320030040205004c4000d40081102c0060305010160444808640101c81908005460500507d05480e0160781080d090750355140c069400b031181d01d1108245100100d000410107526802220503144800d19413840ca0f140e0000c5141c00b4020001d0040150b001482e071010725003080c1c00745990044c550318142400c0d81e5 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 958638093 1250 958636843 958636853
    0x10c02210f1308010207030e0409051509031b15011a04050915040906060801051302012109050a05060a1d030d0f15060806040606080f13060b09130c060f050a0e0d 71
    0x1540e94030403d030f241d4000c40e0980500d50010040807031801d0580d0144088800c940d1856100e40802041003503010094011a4500030b0030400c0e29017502d4421010b00c914044000c15903681d1120f000034245501102001184500c1547c0340009082042065641840d05020402011b05002080504909221f009500f0243e80310f018501d14507004100c00929a800e00c180c050079500018010010704028040940050b64000c4000c80c2c1401d410a4100010110789160310280a800b18081d11034400c00500c03000784038003c1413940c09280314460030440301422001c0d840f4802c1c200d0507600d00070380042c00000d4580025400c034040102229000040e503196020402c45010b86540008000a010104208240c04e06100c1c90b0090b10107802e1003415450081c655035500e60004241c1c0a0040b0201944010058260049004484001c02000c0c4a143c458940c0581301c2e1501c3c03080c1c40c08841c50f0b10004105008400e4aa8030412a0f03403040c0c0f8001c1942d10983c1c41c002d0804480ea000500041c010002c20 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 958639343 1250 958638093 958638127
    0x4050114070806040609050106050706020705120f0c070819030507060b0310150503121e090d21030504150903090312020c0111030c0303040f020f090703020309010c02210f 75
    0x39241d00c07408070500f401d6082c003045407041c3d0081170402e45044010700c81e9a0300a0b0541c0c0000d136200380f026a4410f09454928185a200c0c50b40d2145c813000482c800700f2800030040a00078803920041240d10380da6641602c10f035191a100b000b0400c6440606020010034402d100a020701707402420b0109140c00700c00c010034a0051040c000355103080c3c0e100205400c00c00c0c480c05080040200f100282148081c40c1e5100c403a500c0b548200030032120182c5075035500c209480d8180e0f20710060007030550900210340c0c2071a0311041010344690009081000118142038003a03c100340c0201d4000041d4280c4841500e07000c0020310050209030305110074201c00200064409410765001d2034550701405a01048000250844a600200000c142c100b03002c0f0141d840000001e9a600540102d00380d00d41e800117001095101c61465003075600045078004100304035403d5001140250708a0008101c800550b40080780c8554114101030190350030058003940100c50340d0090180303401000360f002e04d0501c03606941104c0b6 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 958640593 1250 958639343 958639351
    0x70c0506180a14010f03060e06041d0709062103080c090604051306140636061b2404082503030c080115020d0807020c120a0204060915060804050114 65
    0x6014032442801540c0c40692545d1700000d5040c18800c0303509119480340b4000e001455180a00d03660300000b50040c1c0382d0040c0b203060311141c2d815074004980741e02481c006000300f4000c0c8103881c0d8101c030107801074450040c5904001c0f9010380e100300050710350007191081503001190072903002c138003403101140c41e0362002016000c107610100c0001d006440e0900b0107130042000d101070341c42040141710035401d680e0885030144050300b0040004007041442402c110400164001d030540003035021682400b44142d19851f14003070740e1a007040b40c0c06910400710024400f0007241c21565202466400710b4001110f840140907107150301c40b900d801d0740c07001e000c00d00c0030b040c2c10b0341094000a07228075080741d60541102000b03000d85442d8201790036903201600041e5660308000c114034204000d500c0000c0c0440e109200c1d444111034024480c204a56560110598030b0b007107203e00b60b110324500b06001441140510071014200d5445003d2110f01d460041c058581803002032081c1c2d4195242c046080040d58030369565445 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 958641843 1250 958640593 958640609
    0xf110a150f0f0f1805030f090118092307020a141014010e0c0702060306010807020c03030f0d0e0712030c0c08060c030a0f0515060706020c030f09011103070c0506180a 73
    0x64003c00104010549081a0401e656041e00e050342c200840c201100310b454810705105c49684d94605000100c034948204105008031440c0d981002c20141042c0d00b01d5545130100408400700901c0322104007416181c15101040564449404600082c1c4a202c0300008901500c050ba080e08007012903001c1614200444031089003140e0b001403044075044150650403086150100c0d0510710a41d02280d203520019061506112400d00003501c5280700b041044003c0402a06991300ca600003170b0700d09002c0d04111486c0c001c0c1402c00151100d407a0b000500369040311a400c0b05442c4403030103500d068410521400e02951240600740000c0350042c010411a40101e40c5800701c1c81d5a860804e007100111012008083da041d8145011300201e2000200242d0050348200c2c2d41070b549502d2032600200074032828070f503c11140001f05000251844c0400903202d1840d003038856112925410741180e841c0c0c0b240090040c1881c0c1c404000b80034070300b010b201070300d0413050010b110194040c80100042c2d400c100c039130140791 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 958643093 1250 958641843 958641851
    0x331e051315020d03020909010308030603010e012906090607120210060305100c110607030c03020c0a050a0311031315030e0331060c060504050c09010f060f110a150f0f 73
    0x80e00582c100034014644010b0b150450800b44030000042c082c9034103101c060040303030000c00896440d940a62011850100410003040030240c01c0c51030700c0040200c55200503030f071034040c510b580c91030504004491591030b00615851a0681598401e030505980850240440c0b2034003d41603c81d011501c40c50300903602590003402401c80c240580015200102045420400b1250244604450000d0f10b03d4000003d03007004104001d0410b000c500030301800310781c480c040c0304e51044901400800305035544640c1c080c0e80d6100c0b09112560209a481c8914169118042e455100401c04183c071504400411000e515020500001da00100d0b0b1454104a00ea203c41107003801040014204142000e000381d142c0e040b179420365501d866400303032a283c503042c0c000e4035403a2560000380c04c00c4000c0c00b424580341001000d4000558454544444054003401818042070340c03071210700085805510441805400704c0700030700c2d503420035580c2c4142400951004018054a50610b00d9080a650007810004008420006 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 958644343 1250 958643093 958643129
    0x60a031a04060305030d240308040905150303070311070e0901020d050106030c051e12090a03020d080f1302030a050f030c19022805030601331e0513 65
    0x3050038180c128651049180c22010400124040b041d507a0880720443c0c00210b040c5100c1d110701a844a14240c502c0000203150007104005220002d882600c03480780041205580d40c0c98038402804541c01e10541c950302c10300c06035000909c110642c1d02a0150b01c015600302a0f5112008080c0c03880540d00e004813650081601c0d4003481d1940704450050081d480d0500a6422252010b8458171801c1a00340ca140600d26104158941070811150450380141d00403d4914001400c40c0d1038032034880c0110014020290f242c810213106064940c000c00b0000c02c0b613003158503404c00201c0d044640510890301401801d820300c0100d503082c4420040c0180f00700140d599005d60f4100b550a00200c4131255031200740c2618180c026031075588810044180d00c00450300c00412604a001c403414007a0700980e40752080000100d804808078414020350522218007055840800b491382140302c0b003a030428400940300706850007254103d02c00d40c4e46480c9860600c240340001c2085034141c8103400c2c1d00412082241d001c022 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 958645593 1250 958644343 958644371
    0x3020418030f0215010b0d091b0f0b04231c12020705040e0304060e03070308030c04091407020607080c1315110714210318031b0916030605060a03 64
    0x8207807415564409491304080700f42c08010140010b000c0e02c88020001310700e004100416600c4043c0c9182c000840c41c80f40407194007100b1030030b6000d0040d070580030740018000500d03031710480030340702604e110000034110500d0086001d100d046044082a9000c0c1c4480d0403074015080d10300f030006040b0302070760140c0940f41c90084040d01d40a41c0340e01c0701d40228904205800a01c201006840c00c1c0c3d4680c7c90507010190110000a1600c05507030800b60030b600000007802120075803280104101c070481c1038103100c1c03a045001e40c0e00180104440a00158000000044000e44504040f81d4041a0390203220f0402e20121410110440c103030300068814036080b485180055000200034010703e110100500402e8101800403803240c1c1d22000700c5006458150101a50b010740c50402d001c1542c00100701e81d226480d0014a440240c0321410f406d000e0700880481a0710008145040c42c03800704d018064003030a847e02000401c06d0046061204200342d511100401c241e074400c401006d2030f400644d030115026001b1485 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 958646843 1250 958645593 958645607
    0x4020918090a0c0503121801051b06070f03020f09131e0207150501080a080703030f0507120e0c01020a02060304080702041407030f090b070f02070b0a1106010e01120206130302041803 80
    0x8014880c0d0b21102d01c40010724006c50413a82010a03e440411101340500c00681e00350140100396100013501c1c2d0084601c499000400c240710361440d903214840e0545d88103085e03040784541c010120b11202e0400020702942440d02c1220604021000d000400d00c225552000704049140b00e40850a0b80004454042c421a01e84030b50341d482c43c04004012651400091507903ca003250401007001c50003140704000d01d40643d205100011007810280b04c0c0346082d180040501c00c900e20035a24030b51a05480d2040c10b4000641e040054506030004e001007059a000c200064000070002ca41c10302c810443d0500580b2a40205041c0c824131201c11f00490070300c1c0304083e090303c0044084008141c5004034280206808081c1d89030080402d082400001d1800c4008070b04003401600244204400002c80c04016a07003d00003a8990368020180d800c2039803a00420000703c43e080c41400b48013800011464090710300a401850410b80d4021070005965813a4080b406480850012602c5c120760707001c800c0181a00701c14 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 958648093 1250 958646843 958646849
    0x1719090518070c06240e2a09030610030201200705041a04060e0601120c0e01080a0e010603050d11070806010501050f0c060a090b090102030412030c03090b0a0603050c01091404020918090a0c 83
    0x1b040c44107150142c0f0603440000800842c81e81d802c41c040042080302e40702d80880d083c09202506481071481c100030b50a040302407a220490010b41011007540c0c5481c1d0301c0c01e003001c0c0001c480e005004418035281c204000f8246001052030b2005040718860030316596072186000512081c40043c4040c80c2503c00500041c0305031100040d6182488804540d03e544a150605070040034241240e131515070030340c0c42006192444900000d03600e40403020040c840c000400c40b50714040ea554007a0314140340d0703540300d0f100e520314850100e241c1d00c1040140400d6006101500b15010038810244c1000d55030110701e480c00800703440201e051a03035a180c0c081400a419001680220b0184c000e614509003071b603030110f00308501c0d00d0b54020141d490b1145034001c0d10a800c69542503400032450401418448514402804180300c1100c0c2442a801e000866500504501d011607a031403004c2d0116881d40c0c814080a9888558502d038040d125001d444440180d407400c02c0e0158041074010f0042c500d2918120201804c160 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 958649343 1250 958648093 958648109
    0x1c140a0c090501300c0311040e010620011a1f020a1e080a050403031e0503040b09101109090105030a080f0f0f07050c0301152d031719090518070c0624 66
    0x901040d00e0725220181100c0407071070070000c06262110030b00c0c1e110b01c2d06140d000c6c4d15400c085a081881c501c5a0f64084403b0044414100201d1050100c8040200c081c1031b10f40076030407050303101c3d011034801e0000041716882c00c2c011203101c0a25a849100c250301500309074012038800714052041c141d1282460b140203154100c040008258003001a040e40401400100030000c00e10008991203014454854891100002032005000c0d0705020034164012800712401760005a00010782454001884088260002000c918010746540148081c3e440301c2c0500c4007054082000f00b0003040d14030f0080407e00e0048018010848450b420107003929004c1c208030307980300c050078014400d070084800001c511404484582da24a040c40c0101c0c0200005544044c1405521604c5007042c8842200100b42d03560500742941c07449030a000b015245940140189500079074041d078440050360306841c5803600a4598108184803d1069541006507006907082500d0340d02d10030b95070719521003000c01e2003001e00010 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 958650593 1250 958649343 958649347
    0x15010302040e0a02130e1513060b04150315180f0e031b010b0a0605210c16050f0a140d1e03020f1c140a0c090501300c0311 54
    0x4580700c0b2900ca000600000005039000a090300200c1c0080901c0c001042c902c15030040c0303442c011400140c01d5810600301401a180e5211070300400805100709002d41e005001c91601306410304100820380c0e200d00100c003080c11b81d41e200407021840e041c0d02c40b00051031205040c0b902c1c0d03201c5041140684e040c88004084503420710345800c10203000407099800000a02000c9082200c42000307160151081586154000d90392540100703140e5800001090040f21032640035401c1c1590002c42e0300d5845084038400d81000003400007040c034211031410030300e026015a0480380c22003c1070042c0e40c200126140100d0f0024410940070015890501088040355200e00303250050685904c084040464903c0300380342015400200841445a18001c0c0c40302e41040190049072000e03101c0f031031401440c6a01045807200c0285000908210880c041c1c02d155443c103980f1680c4482c508001035400d0074809406074400d10310421131000440b00c504003c8203006540d6400304103001c90401c094210f95a04070502008601 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 958651843 1250 958650593 958650599
    0x3280302190f140408010209040c1803080d0204080618011b0e0402070302010212090a03031a0f04090c0b070b060a0b0903030a110a020406090c02120301050a0e0a090f03081501030204 80
    0x70900045000103410440116520042c048a01c111a05082c0d11403000c04103010036411415400f13005108015a01004000c0c3d010314207540411030114040c0801c8401a03052001880310340140c07266482c540005410182c40d960064100901101d5a0900f011003884807a0031a40034001e000b65014007091030f821018650600421802c02d00e4490750103960000343c0d12b02018801d6040310a8855450200740701030405103072a5880795881c00c1e040e00003e0419401480716000410804560b48004100c4200c80305503a045c840500b0710100c0030b41d502c1b0b00c04240062045041c000601080d482407558034224a07080080110540d1243c0042400c40c90a01c17902046880c000116940e0001500388002a40d0012001e1440d00102c41c0009401134106400016a002e280c0c0242d411100039400b900c015940c85821b4000c01e00092151980c4100c5005003080902004030348141c1007180304030007066a50080d00c0321804185400001c0780090390a00400c0820071118070103280152091070194500343ca = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 958653093 1250 958651843 958651867
    0x30703090b0310050105090f04110c210703031503050118061a010c020d0f021f020f012a090b0f0a02070603090503041511060a0203090c0a051302130803280302 70
    0x400390113082d041c084001035007511a50758458070119200c00420902203860007202c1e0018a0f0050ba40c1602c0b18070038180c80c201c203031500c1038400034241c42c88241e01e401c1c090a03032012000380041d5003403050743c51500c12000c800b1500038013603845080004503844c201e403102c80c0791a608840e0035020b0600801d098200701a0340e42c2e8443c00303030036681d501181c07809000380103820100717941c0c9110748000f50310246501c002c1340d04101400c1800e40300d0b0415000d445031602003055450994028108009020380802c0c0211510703001d02e8000c0844203ca03103000c68050752a21400206a40b024071015054040898058403866040200c8009000d0740c2c0340900460000f940c40701d030b80e03000b14001c03107035061000541d1400151160504118406540d800c40f441810609641402540252103030092400785c0c2c296200c0509180c40d8a00c102c840180055886c000c416101c000250810003101c11240c0045c0000140c5580c100094203404e4020400043c40451086200c0c0703400c07619a07581400e060050220804801d = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 958654343 1250 958653093 958653121
    0x1d0111070311030d0f05070f031a04020307021e03090306100f0b0a0c1506030b090a030210021b0313051e030a030c020f0a03060905060c1c09020d08040602030703090b03 74
    0x10340c0c14142a4031102c050940d55046004030070205510302e2515103031401c4214030f0f8200e0b07070040c2001d4460500c50001301d40118140d40550f00c038406080700800314406d8034100f0364000e652040e041d10564030120704614200c0109a07000034100655070020414040c5450240b10f01c07500032400341e01d803240180c80d040c01d0444100c21840341c2d460401c404902107100d280190090420700b0342c03160320340445d04080e0007080000e140501098454044120000d080400002158480c030758040d00200350044410640c0f0010f98070152004c20400c46104c81c640d40500d040015151201012040b410702c103080c8001e22200510b52440b4100000c442e02511000da00c01040102c2c0e01c03901752401c460702800900100345041240300d14107401041c0030f080001440100c0e40006a6107110740c041c0d43e01c0361114204070105020b450840040c2410709091044603003850392015012600c00b600741406454076494282d15900542d12160241e00002461400c160b03114007200081c100080300e03a410760030500d00c006449 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 958655593 1250 958654343 958654357
    0x706050a081b0708030103140d11280f050607031103010f05131e150902030609012102100f020f01060b090d060b0a151b0b040f081902011d0111 63
    0x2d500010102c20101d80e1030011110155084100c803980ea5940380b800d644840c050444408060241451140000c1c3c07050300712443d07400b07201d0020001e10080540075205800c200701c003030360100a070301350010018a0000701c05407601d00070b0002d088185040400034040c7e5488034180c40c941c07601000103002c004036441d0b050701503c80c180c9403508440c80c05035803d030003001294042c0d03880524600c2511500304541c1c01030480e03840ca0b05180c0070b08658446409050380420369501d548400940b006002901c107940085800084101e0164034540c984e402052840040441210008000e8801c40d40520303010002d51405000c1c000081020320b02c0e26500290600442d03403007030f01c103421215041d001c0c000c45070420968540c0080c60348602e99a515a00082e007006810410041012600c281d80b2122411000306003032078208160710096a142e44c0da100c030820581104032501c9005000c2da006001c0060045085141c4540002030840019140e1000100700340d4004d00b038582c1021007002c1c0009801060360b642c = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 958656843 1250 958655593 958655611
    0x100812030705162406140609060d090c09050612120a1107092708040b0717070c14060a020c0415120303050f060409081206210309030706050a08 63
    0x998070740e62000c4410344641d641c5044002c6500c14190705000c00c0702c80c0740c030750601880e120018000346066a041501d00c0751041c40000c4c91070051520705424594014508a40000d1466107022071440c1403108480c00c0c2e0606840e20406108c0070320620741680310715a0018004c075440c440c00150800c00d2603460500300c6801c140344c607010580700740640c020610341c0d941260450a4509503500d4401c1c05000b000c01c003ca1a0b40c03c507552203d1548051104051000150001c00c0c036441d20341880040a100d5219a00460b00e030343d0b0848104803051506000b403c1514803032040d410006140c44002d0a042e104000c03218401c0308100516424290001346420522200780c5001c507240002501d48000c0300b581d5401090302d407000412090416905074811407148261008052003030b2115001d200c1201c6400c0c2008080381000c200e0303008440101c9104580c00200100160501c2c04000582406000010380340c084036440444d4403030362890140080300240c01c444c5045406c0c00304241e8000c00058015151443c = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 958658093 1250 958656843 958656847
    0x50a052b210c06110c0d0e1809032703030405011404030b100905150907081b040602011d030703080c1606020a05030105010e0a050f01110705090c12100812 68
    0x1000541c040d4035144480030104190700201615000e02031141c40380b4100c800924000160241603041e10640d441900c90300d00502c200000300c4025508007101080fa590b002101c940d802c001003030202c280c0340c41030100c038014503155200e0455030001754400112250402c08402d64925003500c0020a84048680928000c504401c0e605510402c502c2181c00281620304c0316001c12481c03051498143c030844012010401440da5050314000c042c904c00607049a101c010038010410080c424505550068194101c2440d158240070312403c3c0c0d0b40c4182d0080d800b503512003c00903503108916190050240101c4044c5140030101e41e801072515200801030660082d0200c0c045200200140c12500707400c2d800781c401c6548120000d005800c0d60802d10034135001400c0b8000744c0d0a54240780f4200400c582003d8484402c0204800041d141000c0440795041d0340e2042400001c3d0540c0d030451254002d41801940c0c2c0d0340c91a0610382d6041c640f00040c000303c0240380f0350804100b1100e0002c0d1f00c01c2003042c4941415 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 958659343 1250 958658093 958658179
    0xe040602073e1305131a0103030f0f0201020d090507050307141008090f0d031d0d0e040b040207060609060302120303090d05030709050306040c0602070609050d06020f0c060a0204050a05 81
    0xc1d03180e0a69601c4004418508010442c17050002c00c0c55210560203594400011810201b00e460002402d000050014041c1e55000b40031f02d0090000c101c16a1042c000035050006109121040f50360180c800e64695024540800050a040c4650300240402102d01c480724a520b2000c1112215a444100c1c204102c0b400003d20f055810b05c01103241070000f006448214110220003005404081c0380000040501860010b90080c00218541019465104d00311200d0002003000002c000c1c0c07084580d003003602003003000c1c0010050b202e031702d0243c101c00c807002400d81d04500600c4810b003004000031840f41d0040042c0315202000140340500007129150850380d0340d80e850400c0b91040520790210b50584518020300c030030410782940010035034000d5402c80d5034542d92a002142d0403c030314801c45401060200e903203000315149030000c0a421070320304201454402c0030136610703151400c1100c2c0d043e1403e03404a001c0c0a185000d500c040d00a0104541c02500007490080201350b100c80703001007640f141714000c249 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 958660593 1250 958659343 958659349
    0x41203051e27090402010c05121c05010803040e0103172b0b0a14010e12070e090c03031306210204090212090d021f060e040602073e 58
    0x10303580001941c070000390721010002041c800c0d4009541d114501e0701d1000300d1810224041811402039400289005607a80b15600103460041072510295501c0c01a07030f4541503a0600034000b0102070101c40040807201d0100040c0408441c0184c12481c0c143e0020441044420205078031076040d40d030001806d80c1410403558032002d01e4443d60503c4080c01c0c005131a42d0030500703031a5001a4481c40b200c041801103140680412950010a02558911440d900340145c110751081c80c0410011502500030885c1c0300f07215070018602255a0300500010701c0a00800c401c003042441810181d80003a0029800d051598042d0f00c2d1000190040320304000800445207140201d0200c0b10801e80300418046503510b480f1031000b006944810112100c01c11440041400c2000014207082000031550250040c3c04d00d134070ac4a030075034001c0ac291060061b10b4060109507422443c1d203141c011442402c0040e0340c1e0070b45140022903010404150b034901c01e9107007100068203c1c41c42c06005096200303401640100480000 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 958661843 1250 958660593 958660597
    0xe0702151f0b03010302040f052703120f01210c15020307021012110408060a0e071e0611031608090d0b10090b091303030207020a080a1a09070501020304120305 70
    0x20301c090003601c501001070340c0150301c0e0045050724000d84c0c090100b502a0b0a000044d00c8043d602d0b28250008003c0c00c02090203414183c0070680101007c0d2403904a08000300c801d0341d14191403030408244043d00400000001076082007605221a4042d48600081d80752058041e420f441009070000110380d03030b160045d209101702d40d41c040d401090b0042ca0500700300010240c1d0050204060014500076480104484413003d403000c81e503101004207019901d001c404d801900c140304014800348103c81012805281032a4400505030000316441d0007a460182c0c002c0c82c03006404013101c25504204901c0d0f900c10303801a0403400703440e000b140da01d99411100d004a400000b00d808090031031241c0e441800034480b000301001c007c55900728030500280207410208005403100380c6120501059181a400c006402900074003c075078002080d644103d039444034401d0a00e000403604448007610098210101240ca803035050f000030905004103549410000042d540380300d00d008121410303100c1c4100e00c04261140007 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 958663093 1250 958661843 958661881
    0x100c1e06140108070f050f0f0a080a140d17041218080715020606030304170120090a09051504110f1c0f0504020609040906110a050903070e070215 64
    0x19080101022440c44200c0c42078080c00790140c14013614900044100081d03030b00f98140c880041403415096422000c01c8400c0b18100c0b1040e8001510700000602c0d0002400168140381c042e06005401380050080d080c01c103024800100305201950070025120130240b201158850b501c030b00d20120001180f4400d40391000052150400911000b0b0082070042020400f00708840c20904510811f54441600b6612180201d9807150035500c248403c2008040038110030807624040d000000755200c402a1150b88540c14005c42c004504000440021609080c01010b00811b1340c00010855414105100c00c0d20100ca440241c0c400c0f41c540340503041d00f104910442d01002c01003810a03581b080c840c1d085459203500030001001c0035241510884003050030f40501c41c8a0f580c01003180e8a407240007003c020081890b000300380c42c102d40c2c8c0c0560002460248004007541d0398030744c68103900c3d04640001c0501d00109a00103080601c0c455051018050700040c213010049001c4100c0d92041c1d407040c24075900320305108 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 958664343 1250 958663093 958663103
    0xa030f020d060501020705060c121c0f05040b0f040b071110090c05010212030c070204020d09020409141009080304030c03170f040b06012318120d020c100c1e 69
    0x441074160081503004404591081c2c007591510741e83c68007000702a01400d0001c0d00c0c80d4100c041c90f8084400840c000300410894101d00c1071850120074044400c55803041128180c007a9240b05010900c40803010040d809a419000d44629107420f545108400001900c03682c280300105500464161048c40740d48815201e07040c1c10070001d43d80b42024103000c0010701c43c090250141c04a01107400d034000c2d04603407003407154482080c5448c043e58203000095021700d02010350300d6500c025140050307440740104050750b17000b031000c41c20700c084094040342401038400d0310410141c074100603040010320810983e03502541508000d814560642001d440301c00e001a04c25455950580800450450406c0007502980c082d0130074004e107607a1400152600ea40000d48107006010000017510007020786001001f2290010781c2c0d01c0340c00052940410b05500461586130510b40041d580d082100b03a0421004040e0402150340107180628054003819500300064054100c01200000a004420000d00c4036045503010f = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 958665593 1250 958664343 958664347
    0x2d110616021c17071a0417160606050303040e011403010b031912171620010e0d030b1509013e061b090a080f061e1b0a030f02 55
    0xc890084200c588141c003c4074040b41440e102111022070f0b50a9a01440d4407144840700a0495041504d01080c02070007181e0f40d004060f44003510044e0035015280001441d101c407400088a4074009054490b40d4000c50302039030007400100a01c0740c0c181c0702c07a81142c5031084c0d81441c41e20b4000200e030261441e100010340605c0f0f00c1c2890440b2070030f50301074042500d0003100380c0e03114440e114900708d0f008000752100c0b0319500008408952000400ca900c540f9180003403c11880303c09200f04100707001440c50842261607591175a95504140c0140f040d20030350032340c1d89010405c181641000400b82500303908982c03030410001c00c09480d9a4020b21024038071031400c000900401200951800b000303c840c1c070300310061582c60000c5040705e00d4001341042c02500c000317091181030b202c50b0005201c1038100c1c00c02664450050030000480f69414490400707080c0c03840000d0030b400e10700006032481d5100380e084220100e0000380208002c0c0c0058104500318407007484800343d5501d80100045020380294019a1500741c80 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 958666843 1250 958665593 958665619
    0x1090b0108160f05060d0c032702090906220501090507030807060f0e030306100e060c060f0106020a020f220f0213120b01050f0a0b072d11061602 64
    0x4009102c0d000d0007000c1e41c80056140d00c4200403040c2180a00c00c864025409104101c0c402c8419003040880345150b203000a040b198030705107003441e01c481c4805100f440307180e161040c05505028510541c0300c40c800380240290308002c0007080c46815000c003451844000007410b141080001c1d0407142c1d0883c0c100c03040b02e034095100c0c2000c0c0642d030b1000208417205494180380c90300c003040754003071200b007803400300081c60031503540c6801c1c052020650350b00b200c20451124003840ca180e58482c0078200038070150005219500d05044040c00094041e00f0640940d03100109040060fa07d15010b510415803d84250f1310a41d060411103140100007801c56042c9410a480454152940c3e406040445090004441d0301c591303940b501c0142212400001e0406481d18005000500f4038544032014128060810402c0075680d2004075001c1e04550b43c00c030dd039500d280ba100400c2c01c0222103045100040e13102501803104050b5100c082d50810244000e0150602158003081076070f44002e003e038a960060050300d000b1721 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 958668093 1250 958666843 958666859
    0x608130b0708071704020a17072408180a060c030209031f05070c0b0610110a05060f0610210612030305040b0a05040b010605090d120e030d03050c0a03090501090b01 72
    0x2c12108030b00041e1090522500102000320514029070300903095841250a10750752102c1c0c400440207040700c511801900084600380c43c442103140407600c540c0700c6592104840d000303001c0c4102910440b04000024541e00c850500824401d0790164840e9000440c220203102c190064043d19862035414012040076500d1925803408003403500701201c41c00c1180ea92882001e41c1c40703a0703003003c0c0540b041081c0c0d00080e5407801c114248107107400f10f900b00b902c0c400524850700392030040101801c8403184c01c104188401c4c40f10001120390411021141680510140c01000b4880c2e11070074032042e2140d1110001c482041501c0d403000010340440306000f50103200b58240030b80500f00584048410b02001c00020348444150b02c1103d00455212040305010f920308401280e050f0801184254841d0342485003c00064191011000c0c0c0802e40c0c403a41712002d45c02c0d04060614800c982520300380b506010410561840c12021580124200d040c00100d64080e4100a401089002c40003000056050000b00b076200d = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 958669343 1250 958668093 958668107
    0x6030507140a0e04080d150b0f0c2d0705041107020d14030d1a060412030c0524010e0604331d060307090b0904110118060509010f03020309070608130b07 67
    0x5501140600800c8901480307d2540080c0b4820020042c400340112600d05402c03000414044031080126210101e98401410725495a401640743d1600700741003504035a00140149001400704480402100102c1042420540b04410009100710200e444420410a1851401403078074841c0e01200c0d120361000200358000c00c1c4c01c0b10b0450b40c014410020101516050048509440c2d06216501040d10341b60b4060b07480c1c10303901034101c401780110300c07000c81c11910100004900e00c0b00d40382c10258a52400c80c0c100c4222001810b560301907403c001020402d00b18003a405480c2c4100700403502c2c1d070480c05052540c80707643c80c4d400042300840180e0701d030780d20781c001c00348c20500500044055403005507545841d4007c84d00990885a0410305c50300c00203000c200d90045124442006040500c103030307041c00000148001c52a007151001c241c010603a04400e5910180301130395100e00342000c40c40c3d030800c00c002c5580c895913441650b00b0045010002001442001d00c40d030261035020a0412640c1801d2074040d102c9 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 958670593 1250 958669343 958669357
    0x4060203061201051e042d29010e060406030605100608090706081501030207080d05100902120f07110f01061e0b1b010b22050a06030507140a0e0408 65
    0x10405035182c1000100b042c810940105c20b500a40000d0004030000121700346801402654001210540209101c11810041016031040c1c90500b40150681c64100071b1803a0902140021040038040e8401c00001408000d054405141d04c2a5056903800001006000a5003004160074200303400d0064902040d08110140e80c0c00d030b1214100340d52003140140e0781d918180715560014011201080969154080042c007840c4c0c10314003d4a07241031074641007a5584103800e00240565900c04210b004002054a000980b47d0050b0561900c00780003000e403a20180034040b1184150400f0229420302d00420b120421466070005035442c40d2444100b2600803e081c1c42400c0e102d10030f41c42c61180c04d921040d403007000e50300080c64040c1403468045103908a11141e01490340c143d9a58610800aa6103031458066403400401010300c02c0040440c242068035005410040418200101400061404a00b0f2801d5807040102190011101d0700041c2c4449030355409004010081028803013402682d000801103 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 958671843 1250 958670593 958670599
    0x30f0203060705190302031e01180c0810031b0515030108010605030307150b130f020c070f0e0105010f050d09030e0f030d0e010c1502040b0403020112050c0403060e150406020306 78
    0x55a51600350559040c8a41c1402407041d0143c410904d20b564002d5000c0c1da085110704000c05030400025540c000100b2003a00940c1d40346041c4180640410385a01030845880d07aa4a030501c103604241c0080b8400b0340190000500708420000b021402c001003c407542c000b41030040101800000d03144110001d9032082c040e1021550a01401003424107002086401c00e9070302c00f41c044629100c4514100007450042c030102c0c0c0c000808400784203005c159001c0e843c4211900070006a903a038517403055615007111603100300e5903002d03010380c100320744046000c0c4141118403e00380900c00e0a841c0e54200c1d100c1c4a00364410510a00d0700d1041c0c014103601010450041030159050400c28241800705a031356414042e48400095402c4040c030710a51103141e14089040c841d200d115003c801d107521001c2680c0090708240400400030504000b9581d01902c1400c548120b00810000d50034446080003030780c40749000140a058035543c00d1040684100141c0c41c0d01c602e14030044500d8206031078014007940c41590b803184 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 958673093 1250 958671843 958671853
    0x6200604230c0114180301050403020c19080304060f050d0c05122a0904021b01140c040e010b090f030d120b0f1c2102030306090f06101206050604030f0203 68
    0x120700060080a0103070140c640200710280c080f480413290f4450038807036442403110700d0003442c29202405094040c91198014040c0c604045090040442c0d02204421074000316000421243c0c0e0084200c0e000e0f91024580038420001c00c010079181d07032103842803848003030749400c01a101c1654410054610311040a81d03401c41512000b40e90380d03401150b1040a0030949040d080308142041c644020590850041c101504040c030030310400345d40c2c0a02e40407141031651200c84000b50b0400d0a140154484152180f050810b030030951100d4450f42c05008012080000140e594515078070901c8503512408001c00b198500d8615500c01440102c0002d000ba07a01410721808800b1031a0829000b405010050002c3d5001c141c0d0414400d100c2a19880a0b141c0051030040300c1c050301902c00704a403011407160011a6079041807014486141d4009041d80004614101440015607807110007611603111440c210f420025404076842c01400543e020a40c0300d0b000180c0081000081c40d00b00444e14001c80c19a8 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 958674343 1250 958673093 958673153
    0x121305030403030507170c15041506080109151e150306020316030608030c0a0201270e0103120e10181707050f0607050303010e090a0b0a0f1d0706200604 67
    0x10041c020a62040025000402d230407091018a40c6895840340c0900d041001e41d000c5101e00d0f000315140f1b5085a5400d9443c0c4070601c05204001544022401c001442009103450325980e05251a4141d08030b210351039101c00a407241400e42d41450005903412440465603030502c4070b2410f9108564941d03000c00b1a00b04030001544c1600401500e41888890740075280744061070380115101c58004441c1000da00901c0700c501c140304500100c48028150b0740b40e088000354154288102614030001240080100c200c210000d80d031600c000003d0184e03032508001c03040842c01000549414600d4008030101c0e00003500194040c280000d030401150000e540c49800300c00da04060200034440c299015144d94410001000702c0c1004885040d44080c050068941c415a01e49d42d0100020080d20800d000648490006101007403600c1526158540a0754003803a95803043e00311170b11100c2074807a10050010380c0ac401d842c408400001507000b250740c08207549a0b854249451000141000703140040051800601 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 958675593 1250 958674343 958674383
    0x90d1b05090c0714150712062d09061a0708070b0a0510060305221b030f110306090a02010e040f0e0d3009290a0e12121305030403030507 60
    0x7620110003969504a40e40c460091f140380c1401032a8103043d0b599503000050103a40b00c070b118a000410012000040b441c0c1181c404070092054100c1091140303058001c012404403808075215816000a1140c2c031a4024142a0b100f4000e240c03010f0101c030020007c00c10301001a038862803103020600714801c0d40300d448070750440460740c00301c6031480c00001414840301003e202e81180c008441c8508080180c103240c1b043c031031074208400e60003110418030044540003049110300180309119825002081c07a494201c103110f64880320000041e05002d01c01101062a44480d00a050304905910050241e003c41d9040326a0b1603062030500000241039845003214404001819103410024010203070032603000d0703138118008125200c0c0807107220b003900280803000398450030300d40c4100c1040d1940400a1801041480a0340c04002101c85140c0001000c1c0c01802050001c0c1c6140301c1d8010100940d643d55141103c0c0d40041050015090b448046000020954010010402c030707841807080c081c02003001694 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 958676843 1250 958675593 958675603
    0x110d0e1207030801120c03120f03110702060d0c0509100206060f010801030302070b031021050f01110f070c09140703060e040f20040501060c05060c090d1b05090c0714 73
    0x20040c000343c0c656004020032071100c940c00003841d001d84285914250342c0d90729203403000c40440900c0c0206a030b50860651668040c41600d410340c800300e450074500324003940000e28031b106280d000c0c2c410503a105411060700e8840c0081c0ca58024010344404210002000080e540d200c0495299214240c0b070440410f181d485280c00341e040703da06030014100e0a08054908005810007840010496000d08000034803024030300341d41c0c1070baa00c1c10201e90b4488013a820030b142424850500c4081c141c4c10629100301001c0c01204a8020b282e08030405521100c01d440c201d40d03858403650158078180c0c1400c50740e40d0481c0d0751a142c0e60151030b468400300a0f5540d50601203c0301d40013181e0281841201e0000d10000c60310240070850340e1000310141d001c01c0d00c0c0b880b00240440f4020b801180c002021a0032080421a08028240d041665180018101130b11407002032540d40c2225002455080d5900031002c1400b00400c904003e00b070010f0101c0181d180000c0a40e8154102001c2660481e421460b12003044c800455 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 958678093 1250 958676843 958676857
    0x60801240e0f071206240c0b160909060b030105090a0612110409020a14010f020c030c04200a180e060d0201031802030a050703050c091513110d0e12 65
    0x200700d45596a1500200c0c111800400070000e1214840b8100286074080c4500c0d0b0160032442c0b9010305903840c0a042900901c460000e100030312042c0300000010550840c00b19078400d040c0403240da182c02010314111034441d00d80c1e0102540c00e052840c0402c0c1d00b092075000c0e50686406669508aa6031488044000c0d41e841c0d2013142d10840d800045840030468280c00500c010601501c04030382508154041b8008100d40ea000001070202c505540c8103940e840b0300c51b2402980944000c1070780c240c2400003c2d4840582c0d115251080d0750341e05902107420f10740842d50082400c94402e26460f08000507001d4050030700f01e000702c102d0541520300402c005660140e4580280c1015041070f1030301c050341e80158001c0c103803200c00424100c0342e07138101001a5400c0007480d101c0383c0719401400115244d80b4001e0326000261303059500c16088401004031001070712030710007058003084900001107200e06014030020704901003051280d00b0000340c298102e14080e081169007554140807141d140506034034605403070080701 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 958679343 1250 958678093 958678109
    0xc0c0102150604180f0b09010507030209090c0307170c0c070f18090c15030902090f220602093303010f0902070804050d050a0606081f1d0106080124 65
    0x740400c41030300302a80031980ba551940710110031141c50f61903120100399200411141d0400d80d1080020500081c020030307400403013a0a055080c101540700181d00880d00400165500c5004800500c42c14461710010440c82c0b1806414400d6084c0601124120b44c00804e00711740368418072000250000f10b1801d4501205c100c40c540b5480e9108600c2c5c010003801041e2b030103882d60070302c42002045a91844406012185454400140030401c0d441800a40c0c1c0004041e490b002401104100e005105c103140c217950b10800c2c800c0d0210a0115143c400024001c028105030080042403804c100203007114445039031085265002c00030b11f21480000c1c04103100c00d0033a171400c000b8110082048050315000341400f00d10500c03006042036207500120712140b00c40e00c801e0703505912084585042c8900c3d403096001500072030000d0b049906c504122580c0c240c01ea45088203002e9650100030514408415075800c0707982d41d038402802801c4d550080140a412406403032507004200180c11145d20a0719500704c401c4494031 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 958680593 1250 958679343 958679383
    0xf04120b10030c090b0406050307080c19080a0f1b0b0703031a062205090703150b03060916030e06180d03051501051e040810110901020a061a0301050109020c0c0102 72
    0x300e44504043c04440d03045e241c100703843d400082031555003440440d0140010b80c0c01040207140300410048510b070441d135402d054044a4905000c55500456202d00158118098031580e038024035081801d010502d51402410f1499100811400e0601008202c124003a41c3c0a0154412002d2070070302d070220105141354084000c011503074242450700d4044417922140644904496034440218000000032107000c4002070b501c9044d03c03082c00408c000344c4050018000003070308500d0180c000c42e10400f0081c2c050881500550600c115940c03180c0c0081d0140103000c1c040d0352541c180820041c00303103106054130315001c2c0180040090464800e2184030310550340031201c014140098801564540c0c0700190862544100f4100c64510b0f007180300003403001b441d88500070300f40d15054480000494060071180c0d0b4801504010b0f1034001e0f80e000904d0069560803510004808a05590385a0b1080451481030b400d0350a00c800003c1c040342c3c56029040e034000302004d94080c05501001281c40c1c400d2082c0c0d4002d54641 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 958681843 1250 958680593 958680599
    0x40e0f100501110307080d020c0f031c0f0902031b120a05070e07110607050d0c0807210222032604060f032705250b0f0f04120b10030c 59
    0x1c54501d04101c801c1d281d091380d250592030389901c100f651103002000d100a030002500f13203205d107080009600d40c004440c09181051f5410880d100440002d41c89030603031076100e01030144041203d900c80c5120303c0d0700608a83c5d10380c024000d00d41c415070044402c103100d80d2907203100d2050440c000c43c3e03c0ea9a5a80100509441d07401e1000d0f07460350b120050032403010004546920306882004010703050141000e51581e03920b84041c01605011788485444180c00c115444052200064000c40344100454105000d01001d50031909480c1c028011826044400ea9203c2c4154044508803441c01003564080c5009180210b080143d039044030641c0c0d1340048520704200070410049201e00c080800740700462601140040742200c078a040f403400c241d4007016620f0b80071183c604120040040200c01042140300c0d004840580141111404a80c4910340300110f0005660924101c1c00d02190712005d0400310282d1140d8469205e6014040c8004084603a1800c0b48080303090261500e078004204c0ea4428120b0300f075a42 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 958683093 1250 958681843 958681847
    0x50f0903161502090301050c030108070b193006080609030414120a0209070519180b0f071e05070b030f040f1b0b1c09021003050c0d0f02040e0f100501 66
    0x12002d280440075070f424400041c60740e4081c0160741c060301c01c03148202c0c1c40b54108121a42011825888614011000c01c04180d0800b107607121044106030f0340c200b24200b09039041e03000380c01356800035403155201030400d985000ca40003a40564240c8002c002199495611080d0580d90380c480c60203082c502801358400c2110b5031038075203000c0b2287e80444041e98034094056000c602880d50584a90303000c50008181c0b810015951054541110f2030791602d0b403020000d011000c188201c050258081e44c440018162419000d0041110048ad90110f018400c0302c040c0604030142c3d020081c6e08940c6030054480c000b03285a12282178078054542c0c0150070015840d03903034503031040c9081001c088410040104c2e84c0f00d91800c41d84c561400400862020658a4002506081f40f0650078248000e11903d000e1080340540c4800d002c10524110f1420001190389403144a4031541c0100314402c00f06504000094030403800e01d8015004444081c0101c0c011b81c3c45440a45d40b1040089851038803020032040100002e40c = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 958684343 1250 958683093 958683113
    0x80f0105040c0905190c17070305100b0c07080604060e010608121603090b0307030504020405010501050a170a1b02071d0105060307210213031112060a022b050f090316 73
    0x1c0340010308128400708170440101651030310f100b010003250340104440c082111200c0303400d03800402c03440e04101c03d00e0310840c0040d1030101406150a110f8000ca020140e907035080146202405000003140c6081c031b01807400e00081c0c04004940a07403035082205c00191450006011080c0180c42942d85003000c1500304034104c00c05003145d0a0742008000b4100045d4101d00c0030055000c1d204a5030082550300d080d0060009854041c0d2007241040380c10401d100e20303564031040c10381441c203000540c0600768445440c2040548054810880010703200c84d003a0500980000780e0328222690308140c040950006011910340110921496800c058201300150380c25108148040300b01200303c0c225007003c46004441d400b02d0b00300442a404044100c04140244002003580401c103003412180074640a01040e0740076207640e00900301c0401582c0120300200b814002201740e10072100b40b980c29132400c41d10720715540082c1c0030503076034041c1c2c1c1d01c400d10110710503d8000c0219044032141030013045800c6159070302d4031500 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 958685593 1250 958684343 958684351
    0xa060e030102040f0e1609150e030f0303010b0a030605030706140304052503060e0f2a18060f040c0e0f0406091407080702010c02070b031f0602030301080f0105040c0905 74
    0x340d5403c01001c90075051840014000c1c0c10300e640c1c0e082140c035244c0c2c9140016004d1890b10001d21900a4040080408601c0d000c015400e051130101419140000400d10701003003828003002c80d000201c0046a81c1d00398074090400740b06280d40c2440116641d0051544a503140d002d0400000c0081119040b0281120002e5070043d201d5000c8031500c0719000c400201c40d445181d6003441004110108000740f205500488000241d04409009440b001d5012540d40b00c03008080303c048280c0201c4038203081703048401601000f11026000e40b0684c0300c6105000074000c030488559120360b1401801c503203282418820100c400d007080d1140984250305d81e080200b180550016564400d803a481c002c0740030f5540d4000c141e00c00ca000d00e2003e1050034014000303003103100000c10302402c6a04d40014030884a50000341c10003142e907220085681c80d11070a0589903111000f8030206084880c00300b002038916400802141200d40a41c1690018002c2c13091960030784400352405400001e071141e05000c1151660300c0380d500 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 958686843 1250 958685593 958685599
    0xa0e0a020d1506091d060c0d0b0d08030703020a080f0702100e1f020301060201140c04060813140c0132131206050402090a141506160c1d01050a060e 65
    0x4580c0c02c0041032415202c035504503241d000c0e00c908100c4102408926081d400082d2640500f499207406000c4c545140640b0181d0f19030161104596400c40d10740c03640788110310760400046c59a80c6031184010b406540a00c04900028a0150000f00104a03105010340a4041a40502607014011032080080c01a4001c2030341e040c00b900400340303508080c801d104603080c07161180150701c0350300d0f0100207800c42d1420040c408a02d503036041080a45d0031f2104c112410f4407154103000b010364a8984d0118044078050900a210384400c0b03007224440700c40055890750101c400d80c3d0b590016003540541c541c0740d035400050301c6040300c40d4a10104508104074041d140c12103440c03121910045d5681d05800241d5081d560507140e05a07120240070550402198559220901c044144041201c3e0071603000041001809000704496080d0640f40b0340e0b03100f0088801b00800c8105160394003030309081c1245c0b4142d00d0300c03d041550b208100421706682c5982e14143c12540700505c0c408040d45000b80c1a41c1e440c07202019154 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 958688093 1250 958686843 958686863
    0x60f040b0f070210111020040608091b03071206020906030903070b01090b0307050108151809161a0a0903020307090209010210090203060f0711011103060f0a050906060705011506080601080a0e0a020d 87
    0xc0b2541109000d00001d203418ae46840090030080c9140d4140310003210340c01c0703038041903d071909103940700052010101c640070310001c04240da49043c0640240540e01100d5403041000043c0305441c0d0b80040a03081c601e00881c841429070f66280d0702d10040301c000f01e1460b501608494400c01166008030300c05070340200e04010b0140c5002d18540080c0001e580d04100b65200300426007407240c160010400311041c20308030484c6404182c102440d40b00300c0310075128600c5200e41c3c00126000194403450510005550203001c0320400307525290000d001c1d4109410440c01849500c1d448074010303009018034a038841d00034001d4203050321400171105175844001c000b801842000c8142c80c0c11098244101750350741ca640c0315403913140c0c00e02d98208500c3d03200950890784100d0000500b40185e41d2140380b039542000c004c40341955114560714240e400f4008400c0040582c0c1d041e04400600760340c100e11040c0c0304800990711040b1558489000200304d0303c096504101076802152206c005003000c07590561814000c1d10a43c1c = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 958689343 1250 958688093 958688141
    0x110d140c03120c070c0e0432070b450102120a030606081303080a020c1009050307060e0d02030403060216051f050a06060806060f040b0f0702101110 65
    0x8905100c09503466103108100080c00800d0090080703025010304000c050386d40c214103140c4c1312503602ca0340141d01c194100ca2000320410195010703400c850043e0701440700381c1c6c0c03066136214005e001e00e070401c03110904015800c0c004070302c58802580b803c0840304146e6420444c448604503542c2c050550b01a28241544a1030030325402010b0b8000160841c1c410341e68003c2851804c001005086010103003038685800d1804041000103500318444a50012002c0340040e00c61821a0fa800c0c6400c6030200c020b0361142c03920654030180203012000740304480c0a4074043c40f00380148a12966180e80c1d5140c008016001403005100040b10703500104040070b2090003415800f050381d16007038241441d100c0c4510000c00800762506940d0b5040c06020ba01031150001003000d10719025002e80791301c10040103541705110000d4541c401c2e084100c1a1405840c0c0c0e28102a01d034104000981d8070341e4040d182c00d074400c1000c9103800c1440c521a00301038040d208000050304c05c0910040c46030001d17000135402c400b1035544011002c = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 958690593 1250 958689343 958689367
    0xa092003010b03061516020424031a07140a050702010c02060c01050403030b120c0f180f090c1e0112060806090a020a0504060b0a0f02011416110d140c03 67
    0x614041d0042d611890359a0400c0d40c100250f84c1d40114001e2101c6205000d00c100400003019903a0803650182c5004c07445142100c0034800b441038241000401c2c0c0a20a404024440c105142429001c06440c801c0420f89581301e0540b4a000c000c03030041c00524082004000180c4902c028111041c418100310105400715800504e043d0031108114406a42d5482000145070341406402e0041e02c0c151422600d071050058155200c090101c0d6190040c801e0a030722035070548076654070051a8848580c0d0031441e080c00b2060141d5a002900c0c1c0b110107101d050350040c403c0c680800d00010240c0890070b4030301060015001560f070b07030700303981c0031240300c2680e5407000a2402024080e241c4518090700140883c280c2038070411102e000c468001a0096103080030078091254030034110307103066a140c201176039a00b005030412400742101980c90b445020307481003800200e0a05600741c1700004c0300c948804000c1001c2c041100d0740d82000d0b4043c500024640c0300750039031041c069401041d200c1001c4060b42c0c0307031180d58014 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 958691843 1250 958690593 958690597
    0x80c0c04060308030f18070605090d050601030606080d020708031b01020d0f0f0f0905030d0b0310060612060b03070906120b04060e04170307050921060405010f0c09050a0920 76
    0x1083d00c03040000020005101d108407005588136442100300c070420031541c80080d680e001716018120a0150000b80034102c0c0d91084c154401072540401114146e42c6c50b464600007510b554410030b00d8500c11511a07144450000c203001c410359421030029402c050172502142c0325480c8000307420320503550070002c40000c0e1034603004442000d09078481c00f188200e04481e101c0d04842a640000c0710b10307480e0442c1503001807404405c44842d00011400030400d10720002c0006c1c140160031104425913494210005225908980f01c6258112040c0c0100010340d41d500c032030780c4648400c0b542040001c0c64814240403042c0505000c448483d00303110000389a06100004c03404075840341d000140e0210040302007004004144055101d900040c820103415800c0c040c5000d0801d004952b0300910a2511081c4c5c444400c03240002a010010400308540050406043ca01d00905c07503218000c940a0604076003ca489010b10714410454601074818003440303181500c0b2200a00c11401c43e448501c10007202d0229010314040 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 958693093 1250 958691843 958691849
    0x60c010501261f0b03100903021902010e01080a0e070b181207030602030a020d0603030f08090714040519020703110c032b2a05011104030f080c0c0406 66
    0x24194100014198480584508480348240d1480c030007002d0b05000c2a84449281400c681c803400041800c81a03000e415414030300d907054880e0915071000083c06401550f0054003d0b0280e503121060090310540d0300c070340d1000c0030340410060070030200c255100b503e949a10020320580000e080351601c1140f800d110b42ca0f480510300c9000070812407029200304010700c0390f40f0701c101d0f404070382d556001c2c0000c2d0300c17400c40344000703030142d80c2c040b00040300c02c0e4168044518200554504001d200c4d202d14000d44003100380340070103000401c20000181d4030503000441900b030740c94038180416038000d40810000a4000104000d9443d9100d07440c2c14815207990024080f030600c287c540c081034024070f44247e49070107890050144a80e00c0060900c0002a040c1d0240ea000c0b94100e04141a8005030f400a0f604255a201c1c2d0007440079854001004000049107040b180c54401c000071f1000c0e07109980d142c40903002e103010281065411f580180009240c401c02010450461815a154420000c00250403118254 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 958694343 1250 958693093 958693117
    0x4020d1113060512071505030c1e070b1005030325020d08281e020f07180605012c030f1006212a090e03040e06010503070507031d06 58
    0x40e00034042c0b883d0200030724040c006040001d0043c00d107410702502486c92000014003d0000c00000701e524400044100c400d19080360911407500007459a800c5d200c0d512036401a80d0000d0004041904000d1403542c040c01c40d5401001941070032440c041280c0b10000c0c0e01310001c00310001c200c412005071100d9030102000d42c01640c0c01030300c8080070354a5249051072100c00b10101c02c0c1c400c5400006541010905a05041c0180c080e8049a00d44a05074a046264500c51042e803045150001d5008400410742014901804043c400c00d650b50005603241c0d18103100c2580c007600b5240502d0394500c4141004000f50500070111032024403010001420407039030008d0700d66010b444000910000145182c18502038001504c11000100142c03140c8071246038002131008211258150401003e040103121b001401c2211f030204a24500c0c0000c013540e90380f00303225100c0c01d0394540000a41d00c0d03016a042d07074482d80d550348915240c14161360702110706150001c40866a034000302007040141c0c80b010f02400f0031801207 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 958695593 1250 958694343 958694351
    0x506040c0602150417161b06020d0f090515070c150206150d030f030f020c0c10140301030f060609020307030e1204080703110d06180b010f0e04020d1113 67
    0x4000b0308142405040180c0c4031803000600c00060901c521170228082400311a0752540740c10b08050344100da01007005070030b800c40c0c407034555030a1500080b204100c6000350211010040c40c51401d54081d144d8860990100700c0e01d00e420086400c250344400d800d01821030501d40782c17041a50341d40701c0f0b4141c41d03004504c1f9861801c000700000c640400103150414001440f0381c100145070f00004072100f54500d801000c004081205011940c003c0d089180c0c0350360030b01010f54848542c046415030b90501d109034035104941c060b00c104200b41c004d40c855003020050f021103d10b168210344511050f521010000c680340c035510040021081000d20141d03004002039a0040351900541c0075961800fa161803d42040b130f94100810031020740002450012240d10000d000340c0451400c0c0002c1400492910240c049800d01c1086100403101c01401d88890344070307a0b0082ca0591300c2d03084910074880f003400b0702400c100c0324001040241c6070007181c400456200300e005005400302c8001141d0744021482c031440c00035840d = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 958696843 1250 958695593 958695599
    0x4020321130906351b0406090b030c12120f1b0714011107080303010306060806091c2f0c0f0603040b010302010f090f0602030a0807030213050405130506040c 69
    0x1081c0e6112008003060315040c0580ca041850400902411951140d40702d1919040c0c0e0441248100c010003400c0c0c008001e5400900c5000700310456000e8015030300f40f095103021801300c1d035140c6d28070612540b42400740050200343c5048051001d0701d60a00d80080c3c0d24407078000507a18541c00305000703009185207005003d440d1012090f2a405050705040c4810942e0856281400003150141c104401214246420310018640e10034250a003a03041c0c00100031400004004400e102e2650009022980030f070b4115144da03a0f034001c1ca552a01d00400e50091120301e1031002080303042c801c2100e100d1241d9032452a807901d03150b10300803084901f04800280309542203034000603450b203030103208080001802c0d0340b01c9140d0301e02503588210750380050000905100085d5085481c0511800749038014101b0000101c45458444101079600d40101d582d0200041c89080010242440b90007030b030701100400140c0d20003503030601003007001a100c0101091030a001e5195903070089201004501d004500680c2e800e041141 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 958698093 1250 958696843 958696867
    0x80d030207030f08131b0b0f031f031101050721110c040207230102070813050f150d0b1314040b0708090303010608072d0e090c090103020304020321 65
    0x1180643c84028000384204000e05040e10416281a50f9400000011502d4030300315610900d08642c0c00c8000c0c020380100b071a0024a01440c01140140d08510041e410800a10071150300402c2c20300001b889130610012816480d4011009021014800c00010104841c00050100c1c042c2400109800040b0403402c40b020142d0244482114010103031410b614025040c1c845c2c0001600c003901c1c05016244d0305050404514080d41545c01d140c0e030050881c0d0356000200ca044008500303038043c00744254401907494010b86441104181500610329a40d407d1800c2d14090400501d40860f14a8028401c034a03040411801885880c0300e50703440d035a000d107403801c2500f01141d4000c0c00a00c1101840005030a2203100c45002055a04454030382c03902908a07510084e0841c0e854501c0c1d40100070074001c810782090441c0000d8071420050580ea91031813507003404113040220020341603802000d075490400c400c182951003a0001c50340107002500701c5e075080300c10800034440b00440303110142d200c010210b103190500b1 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 958699343 1250 958698093 958698107
    0x1e0e0606210d0e36070507110904020f1908331b030c091305161b021201051b07020906280f06030e03070f110109080d03020703 56
    0x1801d24110302400401c0040a0340e5901003500800c014071440200305000740d51002242c0e980035095039004680c80e441101c0c1003480c07000c140c1e48240e95500781000241584e1007607003540d80c1c00d0b400c0410b03818642c2c0e2080501548641c058810380c0c020108110b03d034a15242c0041101007402194200110140782035195410402c201200008080000c2a6101e0381078800c00d04610a0320048400152610303182c91008681100d1109204270340800302c200284600e2401c0541001c1800340c9224a804040300c00000c1211000c580f0f40c9480084c010300c9203121032040c0c0d0151400a0a01d02102500030b00d034002903040e9420001c0081039039114002c0003205002087e201100070300300b00d000c5003004c40c3c0d41e0018041c0072005141501440c0a0004400020000280e16600c510031045818500e92143da0003981038455005102c00b00c0d00b0413034801c8640c200002202c5100c0c2e080000312003562030956a0200c0c080882c101e43e0b0400c200c403940424040c505200041100041d901c006a99010300c0c0f0300a0810 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 958700593 1250 958699343 958699369
    0x7120f11010905070302060c0715180e1314070e0a0506100f0f031104030f0b04021c08040b0903010b18161d150c01330b04091e0e0606 59
    0x5a41821070b07040c000b0f00b0000d0002c06480c2d0454480f61201d0100080c1854103840e82e0000e00044180e10042c4c100542095565680c0501020803032480d980703503c1c0d9141d10308015154181d03910b15608000010580b8402c02120070584001035586040d43c44001810303611094844054055a40702882400e140c1781c0740607000d4107058200300140c41200d07030001e8170b090b0000309000185601c80745414800d010380c504843c091a403091060038255520b040c500c0310501e040b5800c0340240b0103460b11000c0c6e074a040c1d40d9a02096806404030f85064200b440d800c000e50070141e0660303015900c03400b4504460340c1e150b000b040c07042080358044105150108002507207159446400060195644508201402c000081200c0c000c3c1998484505007801d130884c107440c41000d0f1103030400d5280a01201076a550600342031080343c0c580030032100200b0707840071914113403c2901c039142201d0401c1104200c0e140003034020b0a481030390ba10344c40f01103201403a0304070103442c0c2250400555420080c200050b92070704a01007020 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 958701843 1250 958700593 958700627
    0x1050a060303201906020c12090a05041107060501120302100507080a150306051009050105060a1e050403020d11040c0906020c130e030f03040c06050f12060607120f 72
    0x10441c03071a10040d141150924420303411000b2004103081c076070700070030801402a44110a4145005190900c00025002071b05425428000c070009801d41060840558000e9000241000041031500c0104401440c251011208016090028070080340c1e282c800c0398020440c101d0160f07001d410b0707842d0090809901c030080b0b04441d4684014032610640c485541030340100c01802c0000e03e80c01e070720610035164a5036440181203a04050420075005000c425080444017980c0060000366224000c110080c06101074100020300254440c107403002c0083c0e00c0140314851405c0c01403401e6202d40204454080264059442441209100714981003620070a8822400c3c2d240207401c060030050020344405c440c61007507104170a102c580121050b51980404105504002200d5859101c0b81c00002690000c0710300f924005109400003586a01600c203c07884c400b01400d9562034030b90180da6070900b4407005442141c00003c24045103000a1044070305034290055911110345030092440020032030a07441180e584 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 958703093 1250 958701843 958701851
    0x4050109020111011404020609040f15170609151909050a02010f0e0d02131d07150f0503010501050d14090c191202130b090705040e100b03070f0306050a0b0c01050a 72
    0x1511002c0c1045c01904198121342c0d807aa10044000040c001d08503030425106011700e810780060403158803401070001c84030305103c8045c0c0104607070002520f407141200c16640c50b4000511135003141c4003074450307281d0240480d144800d6511400400c241100c1e41c65004072519442a1085002d640c0c02c1503060070a07818918180710310842a50100f15503001c0208000d000d8119808000d41c03003401034118031066030301c007269824881c01002040d680c0d00c81a00c00c40005038058400c240c2224403c0035000300c1624640c40ba5465a4038100046030340d80c2c02700340d2810105603103075100488815a689080d010b0b030400303c01080030052030009c1100c0b190306266034010301040140f04221141004100141184d01200c14088580345580c05c4d1001d02205445c9550100c011020061545d8011025000b640d84202d800203607640c800c5c03000320920f00180640c041c40311060001800091003161000300bd074446103804550191b5801c0800d0b0007000b2074020b00c828071300112f0785001246d401d2060310303403181c405d04041c4 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 958704343 1250 958703093 958703111
    0xa020901020a060c09050402210108010920060708040303051810120207021504231e06090112050c0403050114010303050702060c01180602070210020f06190b090405010902011101 78
    0x10b561004041d0b402060303030303480304070415070759029005000042c040a00159545c2c2c40068107450040d5407401e0048030b01c0750090020802500501c101d51300254013a0aa10740700e00303c01d4248601d01420b007509548050f041040f8400034020340050002544a074030740c1629501010322a4103010038a000c2c06000b00d00c41d4102d6145c16600c00950300384460b06d05001aaa90613600210301410fa00e00881c0c02400d0700068002082111101c03112000034405100c80e0141201c00100300491070101e032500e00b03120b000b0040064928014000701012281410106845400c10000740e081e5081114109900d05001ca810420300c8002c0c05400c414071795203000c0b401c0b1581945e83c0580305008080000e4098000804c10303403071641d001d50103450305211110711950155440d20784080a5070141c04124002d6101c84101080180000354805c0103000b01da02505190b5500c01d1180c0c5216040c80e4064502c0d40c031080c4503c01910743c0c41e1014003071800307200003040a90303040c000500441d0a0961006113a80f4040300c01c = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 958705593 1250 958704343 958704347
    0x80606220b0a08031801020d0e06030414011503050f0f0304030503041a130306020406090905060306010501032325091a07020a03050619050c0901021902030f1e060a020901 75
    0x20008006980005800401c1201141400d5800d0300810340700d2000040903040d581104514920b440801d9084684132002d40c21304550781c0000d0110290409400e0000c5400240701c0b85171000500b5030320b000000c1039806120303100303403090345a44180c1c0d040d00503031a000034485c0d00740401001d401d5824025481e20f40f1f9550b4031981c0348114810303401c401130b80b03030300c1c2a10086041003103c01500e41040c11144054503420f000780254441e200c5d54002c0f40c200310001900300d10741d0041034412800140942000d82ca461300660140901c0f05802440322042607540000303005a200d03c40c00f4000020314401c48850403603612580c22090700f44417041c09206641008038150419410705100640501103444134954400b00c0c402c8030351604020b25602505040001c10301c02404142c034100440c0000f4851038891071a040c44502c0746452890060b0808655100942c2e0303a00174582000d440a412140300000010909007070425070040b62000001400d003069900108200040e0000840202186003000307001c00 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 958706843 1250 958705593 958705639
    0x241e05040203072c0612030307020d180b161b080109020f0108010f1703210a0c1805040905120a08070f1e030e0106090609060503190b06120705030307030801080606 72
    0x1340080c45840340000d186070329030442800680c105441280d13207d0500ca40c0203074a0707000340038107200001d400304c69070070192040c0c085040850700030104441c41d1191600316200300b0844c0200c1650b0b02482c50550085c0d5507103548400005000c0d500002442d000644100076403014107098845c10491300e800188a50880d0002c00c4080b41c140c0c0d0002072580c1b518503890fa080d0f0050506a42c01d40700d07441420201c140000c0a03161083c803090408229015403e0400c0c4e424012520548003d40c0d9060414400b0b410503a00081240c2d0286041740d54a0442039403105c1c066102c4491107000813910b0040c080400d80100b58074080c40c42a044c01100700c00868ad160740540c2054503000101600d40d40d1180d0f000c0310a502c4030020b44030f4090b041c0603c44e2140b0056015100034402e66001e80308905a0140740e200a0b02c04000842c2d01407071003c125140d80040141c041364166410029009031040021282c1d0100010042c5a01c81d4403140d16940c0352010b49410040024151809031070942d58140802c0080e00c1 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 958708093 1250 958706843 958706909
    0x3070903203d0e04020409050403022413080c10151d0604270503190305220227010e01050f030d05031e180c030a241e0504020307 57
    0x46910300c440949100711624510303c0b03465508603200250204904400c0d40105208a0107070702203403074a030640703034014940d54000380c854a4000746260115084048003c040e85005000d041e01a0070f00101c14801c40c00e10303031084250300b1040c0e0f5503000d1041c00281040031100500c000141610b10320f6040c0702038181410010859845555101c0160b1103117071036504451003040002200c59182000e07807405590326070010021084200d10850210708080c03190244912880c2404244510584862039046800c95613500407680082840800e901b4007a0550702c49101c03034010790004410354500002280740c260103802a1f8050382c507203821224180c130009410920103140d032801c90b44e20742d141170022580d058a200010601c60060f014801043c01c00400c201c00002000c00f59600da2400300300b00343c1d9600e0310003001401140c1da140c4e10000c10750042503020b0541c070008404182c0d841d40c440d1008108a900c5040070019a45400344010f5080820504c4003405407030f9441c40342100c01645000d00954468 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 958709343 1250 958708093 958708189
    0xd05030a050a14070201060816061409040204031401020d060b03130201080414010e0c0a05090108060f04060f0207051b0604051c060b191508060d03050307090320 71
    0x4408262103120340da03c03001d03030f44040c2c040e850880d0600b100003d000c0d10281c407403580c4078403800800341000e00e1803c4425084410546810241c2c10114002100640002c03105a512507030070310001000c00c0e08100303901380502641c000145d03100310b840005001c84580350000107801e5028010010409411080d03645002d80900b420301082d03440b86080c2d41c842c01180b09048807542403001c0c1c203020700030001345003811795000c07078421983e5a1035009000b81c00000344a0001d150f40010007040c3d202d812064000d81250007998081030701100783c0d82d0402664444c42085500e580a8100204c1017440d09203420103140084900600d080c1c549000584040c1c3d0300c50301400d9002c92802408100002603009a040310000360210502c40d800f0b4840e1b2854280900c6880906001c0b00c54180c2e48910a14a0350700c1654003c10b501024100c0762070840386600001c126a0034048005404000305900d4040c0b076000c40140c403903044580c1c2c0c0703a01c1403000030805008498908600500000703003807180800c010360000148 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 958710593 1250 958709343 958709351
    0x6090f121407060315050904121b120504050102060a1505060f1905220806070c030c0f050d030c020118020111163002030a1101021f0507110d05030a 65
    0x40d0902109404445040e0072842c0301e090b100084440c1c158001c0018032191050202203640d43d50184820248210780041000750405515074013107024040e0400814290600301a40d000c4566400c4100108450488042900846d04010301e40c0c3c10080a6880406018140300d115903410390303140803100c580507a074403446011520300c0c02e00c0030b11401d840c5801d1860300c3d4901c1d4540c3c0c0c140041d105a2210458a507111203042c01d201c1e0304458604500700721660705005100c80d84e6020400c5941024550003102000464602c1c800815140c03411004003c0c0542c1c041c0500348a0328a000d8100d45440c0f004070296418106590802000d40d400110741a40a003000003540f1070144580c3e042032180d0325007141c040110140451103100d640d039000781c0c00700c0e01b50303400744d521240c464070b922881410a40203505600030b00302e00c000180f02c40c41e0024108010b0044038030b008200c010600318400005900020705555008102400e0390101da0383e42141c07c204040c09800c15058002015440000d181031401501d03 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 958711843 1250 958710593 958710629
    0xa08041e020904170d060f050103060b031009020d110a110d030b030717010e120403022418040e0d020c04050609010e0a050c0405330c031e090910080706090f 69
    0x484c1125200200900c040040c00d84400d080f0b001410700c0c0c040d071030011345000000300310181c086040fa40a9001e42c00111740c0140307842c0c0c9000117540100d640c0701d6541d40740c000c1032007205645009002d451085880c1d012020202c076400d9840c00c40540f495030201801c0020300720b80341c0c90105072001070750071560084000c074144070501400740c14162a4200613201d0110f400c40602c0c103c1021b403058a100700c803c84d2503540d00030240c000e081c0b0f104901c000e044038200090401c9002420901c420400080c001080d40890718244500f0400d20703816403800360300003c00180e202c2c60b241c4662580f00c201180c851800b541040c0c01300e0381c084070003490408642c2d901c2d00442c054001c248241d40040100502c1070700c00c030340c0840d00c1c0341c00c4044903c8081041c407810140c0102c043c01c50030a50781070904035070046007803002111312090411202c81c800022a141041900201c2d21100082440ac0600303110011302030f444c15804a10300401e540c1b040382004203240701402680c0c212200348049584529440100400c = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 958713093 1250 958711843 958711883
    0x1110a0b10080d0e090109020904090501020a0908190816061103040c06120515061c060b0a0206010e07020601030b07170406051005040e0607180b0a08041e020904 71
    0x1040940050222010498003411801d828000d60322880256685500c0c01c0c542510070002588005510104080040c0548040c035809407959640003440410703400840d8a6183c02c81e40310305224000640010010310040004120990342901c071146900d02c0000b1075125001c2038028140698008a02d111405060120540001391420351451001355203007040d103807481c1c4910080c1300d90310102e1407003940d07c3c09008151140c2ca01c10b11803494108180340020040206660044965000d00f05036142d2950302c2046510522024040c09860b00b40d44032403101000c0d1405405a00210280980070201301e0b105602043d0cca0440c0c2e80009180724a480310501956504440303c445016000c0240802083c0030703064000c1409900c0010101004079110000c0c0030a4490b12505d4407a958000008078030a248030740b400100080c0c0ea1f88020407240c0e12101c2d40812036000d50b816900080303580040c8024005241503841c2c0260350400c500303100e0304641d0b000c51005600200081c01e03514051400f555020 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 958714343 1250 958713093 958713103
    0x2030414030d05062110020307270306050603060103032111070302070905010b130b160507080102090901120f02041119022b0912020d020d0305030708090d0e0111 71
    0x5000e0181ca480302d603181c074400b00911040382c1003803107005105c1c1c804d58480302da10300310031082080201400c00006030b405404080e5002800240402c1004d01808100d00c1c00520748540340003010300c0d0b126900c0d19504162040e40c10180c10144071713400c100c00420000c0e803c10803443e815060120003031410700d2081003240040c2546080e903520580c4c009114010140c0c00714951051320f15542c3c0822069032504842203542c0a243c1414001c1c040c4502c0c03d01006080c1b5001e880040b4054010003040303192581d5180c2801516401040c003690081054102c0d0703c0c040c1c0341039003d041c070301c8015204140f8540350440c0112070508041e00451752034401035000e080080880d1035041c0b55607583c04021a00c0302d4029500c00c05250000d0320a098030203000c42c460500079607040b5110f450395951034003d0a03c08141526055418200d0703100000c00f0b448001a21440441a030050013515826100d01d00f8820292607181c0c01040188240c00050340c80092070b8214100e0b076100e030004e1034005400042c41040d64504 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 958715593 1250 958714343 958714373
    0x317030603030d2307120f0b0d150e03071211030711010309050a0215071707080a080c0c06040b0708061f030f0e1903020d032702010201240f0e04080d020304 69
    0x604c01403020005400e03041206490700d1249000104420003580039040c0840c1d646400c141d074028003059065004c035070621245c5404050424002862640140034a4559030011800b201e2412010038280d041c030f50480c0d400c0700860f0002000c0c0d0b2420340c5560f15440901018246581810350720b4500c5402d01100300030541c0c600d0341c0503014454111000303110355403d4111030340c102c0f10105140c004c0c0f084101c1c138070180e9030311550112000e41414840e80382030783c01c58001090340c1c40b01c94050200d42c85194003046914011070140b07454841c1811310b01d070300405003040148a6802086c0350365034103442640f100700400d6202800d1400080700e551680c0d505015004940104295115040c2050b03030748d14000350b0300b5910300e110f40c00311004000010000d800b03030343d84012010078201201c0070110300d09542030301c0018820300c14800040c0d8144043ca54680c10b08020388001d003612031034a01400310640007403940c8058440084607500503d855030b038100d03142c407400c0805a140ca40210200c4d04104170796000140c5 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 958716843 1250 958715593 958715651
    0xc1209140628020c0a05011805040209010215040309050f0913080c100e0105011d0108071202060c160501140c060c0a090302090a02030f060d150c110d05040317030603030d 75
    0x1002c404914029600c00c44910b1582c070404101d10009a91740c0503220361007441c814034605c85406460401000001d400c04503085042d0302482a4443da817484005829214922980350b1840303d41c10041400250301414160500560b1428140140b401000140c456001e610803a03440d41c843d0513081c2c01d0308100141c07040d00c04150509500340041903040d00b200b03040c2e03a00e140114401d0b00801c1a403000c00300e030030710170301c045078200300020300221040c070113421000c070300180c841c0b1702d4000d82106403445c0c065900407001d2641d1464106100d10342c0d002040c20000c140351186141040d6109004035155040581881190000041c80030032a5016000290046800801072016841c0003c400070183d4412100e07c03941c401c086001601da80b0344041d02070100c0307800042c0e14114036401800d5034001c021710941c00d401d014440c821018030030010422186046442d60340d5645031841c4d071404c114106212000340550b580f0a004120040e14000f00f40d4046010002c0082424092200e0f101103201c4480c0110403 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 958718093 1250 958716843 958716907
    0x1309020c152502063705040201020307081204020a051203040509060a0905010609080f0d09051c06065d1209081c08071404050a03030c12091406 63
    0x301d02a0003082651284840d602c00300242c24180c0d9601030381d81103180e00700c013805c0c6154003c81409145640104d51207803060040700c2c41c0c00e080352140d981a802c0000d45402080c0c1200402045082c4000c060340100400d40721407a00040d0300400e591240614080c03180150000400110542e6440390288020003400d902007000396100d40c0014030070901401801043c3c4520505000141d00c00150381040940981d03a050392142003100700940d0303903407030684c244101c409548210003164081c0320b44001000000c0c0d08980c248a0030b015806890380243c19420306130b44054a40b0750040c201406907051401000444002c0d4003075035040c1003400b0b2042c00251141980d420040303806504504c4070400e69062004660914050560000b04004160f8401000400401c040744409015200491b8000300409600d420117031920b01158514171264001d400045070343c80084140180401001c000f4a981d01e4015002400c2c011006905d001c2d40300d042d40110000542482414031034041c400104d03403103001c0c0348 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 958719343 1250 958718093 958718161
    0x60503132603011e060906140c0f100c0305010513111303060605090901050405070b13170a23191401051009111309020a0201090f06021309020c15 64
    0x100b90400d010b8102a2107211040d94001c0a0f900d83c0c1104032107450361050b0a407810541c0441790300e594002d20080302d480600c0f6031100704206204104403034660380003d00d01d0302c42044540c0b0950b00c10f8250002030501d46801801140c507a00c0b54651030341c041d280c001c540c0c0d128450300340e541b9108061070081a6070040c2d40100410009401c60012244100d4041e00309855140d500c1703080f603509603070091456200600c20002d01d8141405441d22004611a002d40c5550740e00c00100c45031594030540301c85070044110b0008000b410001e400784080c03a9682070f00041c002801c00341c2c6c1c2d01440a690802d900704021040100080302c0d140b20380d806070341802400103081c00e0f80e105081070034038040c1d815a90b040c00d507000340c002016400d881c03131941049900701d0202c2c5840140c000030350204810800315521816041d003c82e145100c2e0f80c90f014899000160b4039a40c400c6601d0300b080d019041a5511401040f500705020000a03c00d100c1901c4200c0b41d420383e80360741004211003002d2940c003c803651980041a = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 958720593 1250 958719343 958719413
    0xc0a02040c0c24270f020a23040c03020a09062d050705060a0e150c0d02160501060b16080c010f0c03022a0604030c0c180c031506050313 60
    0x4042c03651180030a01c58184080b410104220b03d05820004e040382d030041d4000441e0003161a00a0f45002800705040c0b5907c0301c0c0b0082e002280d40800ba642c0302030005012800d81054807403080015918a03046007050061034004000302e04500c104c408102c402d44c866003007000c035141c003224941d450b00514400c45801d03150150441d007040f142a00e8500490780010380c00c00307050140819a801520141c6444000c0c5001d00260040c0500003107403980083c00030030314101c41072004100720000400007008051252403c41d0a49846170460654104103100003401c01180c12011402070341d000400d681c83d026100412801041000b04605001e814540c1142c41c01d501075008141c400004001c0e108071081170840001540301180d824030660340080c0003d404240f00e0341d00f03090361600c104564405103584810841d00c081141c141c449640b5602d05800c03051a82610420032040d02440c02d100700300c1d18003c0050281e000052a200544d07030888402002c020000c0d01d9825142000400c130f02102001d000c0da = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 958721843 1250 958720593 958720643
    0x3070203040902070f060b180712020c0304060809071e060e120109060506011121091c050d110d020a02012307080414241e07030201090b07050c0a02040c0c 68
    0xc1510043d10307003078400e400750820f408c0720500070308484100f2599417110740040358160020b96007442625030a010b004075840c8140014402040a0f43d15030243c0e04001800d107040081c180d005504c0690308001e84c1c2d2036034186181140c2114682e041c015a40392400300070a02c1102c80c51141003e9509c0c0803001c00070050242c0c8200d00447c02a41d40e0f030240521308000e2a9038800882c200c040b42218410503181d41c1ca1001c00514011001608aa1880b120100412002c1404040844039030300400c90032205287d0181e005451459014014440540c103000041d494503100c840c040e04100d20002009454150741000a6090316600d2100d03948440700d0801d00080d812600603c0001c1c403007501c030b4004615181884c0b50314040a5946480c0100700c000181c00135a01c840d040351260410784084031f85c104003003405402154025000442c400419141030145100018241c200340441805400000e250000b011046103505507000107015201441c287c0e405c4003010710007000054041102e1040a0f82d03081 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 958723093 1250 958721843 958721873
    0x40e060339011b261e070204090b0a0c0e040209011b050f07170c1503130204090209090105071e0c02040e0f030a050a03050a0915090609141605030a0210050307020304090207 76
    0x1001e0404041003244030083c5100781c10851009507030445c64140344508400040500910092001400440a640b42d20070312030202c950501a0759640c0e014030529400c14021050508112400c6103810502400038040340c50f0324188003090006140e07800c0410908002850580c031000d01210f40140e130310461b0030350540306043d054031b00f406415401e00c0303103080c003800324086405085c410a0a594800c040d182031044c1c00c0200340e85c05034445a1400158603117102240c0118007040021840385081c41d006040c40c03081c3c002c1506620b00c88244034107100c1c3e21404d1169071550454010449100c444041490680e060060035179a0200107240c13501303d500900203050f42401514107001030350b502151002210b508802c041c0c414041ca02900398002d0541e400b102005104030700010b54484c03a62248103882070501c440c20410780c00607116062849200200000400e0300b00c1c01801c1281070740d40411000c4654070a5241805800f00210f400c1c3c60090081c2d03000342103c010119101d1341603080220106081705 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 958724343 1250 958723093 958723133
    0x206030420031b15070302061303020319050714060402090109020c1c200f0c040c0314070302040503070e061e0a08030a0207090c031802061e040e060339011b 69
    0x29100840c036130b5280c419101840d4040e0040e10403541c0c1c9040e03114200f600030804500b14007081200d01800068000c0b42450f6180a0765000d48038a00d6207000844200d13000308080d01540000701b0080180d480c1c130f1000d8155201014003503140d10301c0311643c51809080152005880740e10045e04008a580f0002041805061150341d140607000001e0382610b407029000c0d020080d4108441070800d0303003019048561004968980001c0100c12402e81c115a100207842c034800090f000141003106140c100500c02c05808240f0503082181072260001d20800c21103002a1000d205117082044156140075400009081c43c170140d0b5554032041d68000d403582003e00410101d14034080c00c0c00a40c500c81d100d04400d85254105006002c0c1c0f09808001c01600194a0000001d012002154070401218098001403608070113140703081c2070110400d03040c50081d9000140ca00000c03017180041075880c0303c503800080402845c10a14503038280c0100e0301c82c0d102c100c0310391107020201c510350200681000361422040e240 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 958725593 1250 958724343 958724359
    0x2b030b0d06051f1a030c07060e07050102010b0a0602030301030f020a1d2202010c0b0a02090d0f0606050102190f0510021801140c070b0f0d0c02030309060c070206030420031b 76
    0x481442a00c2d0310b03e80200c851491141c000315aa03015034100554018121800c0c0d1404c00e80c2580e94103060310800403c030215134002e2032003007100356024061442c40d5081158908017040c03d04d0700c029a240814030000d0811003000880505540f10500b4071000f40a14602d03980c00c01c96100408402074005a802e0301040140c0d084400100e0355105801a100798141d6a40c4221895a103d080c1100030142c00449150b40c02c00c040007681d82c90208810a1a20480003184803907030a060400840c0c071980d004a05641158890508015130f82603100702580d07008003220350031440340c140185040f40b8100c003085031520004030884008007600c400352040d842640ca410050030786c2002d62286028086c101c017440d62101c40288441c0a0040260001c0d00ca020135036411b0000c0102d03c01d00b03072400c428040d000b580001040c4050407006001c1c00760300164a41c005460704807a680407500c0d41c0701c0148050000705441000810000302a40600700800e002000c9540c4000c1205191900450807050203100f2030907 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 958726843 1250 958725593 958725631
    0x60e03070332040e04140601080a02031c0203040302100c02040f050a0c0c080d0903020f0316140604050c09190f1b0809030306040c2006010e07022b030b0d0605 70
    0x20008140040902d04030296081510b490901e503038809029204403541403610b6031804101208001d168004d00f1010000d1a00d40458010315080610b900c1c81007501ca0340011403e1001600041158100c0340e06035081074115048410441d03940da03d849000b54042e05051418400d04a290031181c0101e040400400c090b2071042016a591092040000c10303d103024440f1003091402a4825039002d80280107541d0140c0c1c0040c601030441d44850501c2140380268a8502d050103521025100541031050090000b030401d516031a940f28440e29590b48170360914000a4080c034840314040480d28030444041c8070082c0056003241c09414241071160a45200d124a4106984a5020306000d149004061031458a8103024080504a01310024083c49490b6540c5030310402d91180079003501156030007400c02075040031030300c095681019005004561000103c46e800b6820880c0042d610700b600a520740381c0c440700f000d081d0090071841e502ca960280c0500f60003420705c40359810052181080c0004070381c1c50b02c1 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 958728093 1250 958726843 958726907
    0xf0f0f130914010e0603070b0d05040309080609060c0f0c0f010e01050c0a0e09040206040509040c08190b4015090b01350a02030705042304060e030703 66
    0x24505a05241501020740100410610b1441d001d8000d60054247c0d2140e07502c900b10f010300c980c005840450442d50341c1080009044d4000751210260075824050880c070b05001802c03681d5002c01030080c01c9000c02c0015000e50b20105141141c021810003411b81c2c0d08059a0b031039450007005240e103482c001c1d5081900046c1f51115000448030f80c054180c40d100300b0000070300144248400001d10480c0c110501308008152070b9034209031244100d1150803003d900d681018074071070420003080b9003015a40044904c0e803000501c1e03010420751020303241400c40c04180a0b0038180d01000c40e070038000e500940218443c0140f81104038a07514299020744000c945410082c2941c000311003007410050f040d0140c8400510400c00c0383c3c007117084c06100001400c00022040c103004210340091501301080341e40400c41e02c034114201480a040100400c86082100c09103401500b070040040712150000a074140000904008041e40002c03c051600750861761646100e24000c0c0c902070300c000d590202098140040c1e14504 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 958729343 1250 958728093 958728101
    0xb0106111c0c06091a0f040c0518070c0f020a0b0a020c100203160321050103110f0a05190312050406090b210411030a0b01090b0a030f03050f0f0f1309 66
    0x20566070761400740c07000c0f42c460740020f00541004407003c08929480309684101081c0c0c081c081c2c903050701c4002c400d00b0180707400c26000352540d1103240507100d115400d000d02001003010561040c0c560030000c0003400d070381c90500103030302514500a50050304881c010030208584005410544140e8080307510311040c5004000344d00f02c49016180040c0d0042212a00c544403504050704030340d200f410260140e10100300c10302116020021581c45c0b4640d910010000d01004440b800860304043d6000c010141542c800702ea09131086015045c001c40d0400e00030f0342d0122070080e50f10001c41d08020481d031400b48406006003a640706200b0040001c204110215540c601642201c220100b07501509204104000d491180100300920981d08175498080f00c0486860030702009032502c1c4540206241c5604020840d42195241c216a0b4025400c000007480000c4d02d0a203001e680c5038160520a0300c0f01d401610500c82441540c2001607481c00c081140560440490058684044048208041036485a111004072 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 958730593 1250 958729343 958729393
    0x21201061119080d0908371803021207170d020606091003060b0d02100c032309040921080f0a05070e10020721110a0b1804090b010611 59
    0x10310810443c2000c1803e540101e00c611b100c0d0601c182000003d40c40380000009494160310482218604440d5140e010b01d942014802503042c075170844410705903a056200e02c9400028096610384803d254802c2003082040002c3c19102c1c24600c4c980c081035041394852190031045009031103160b0101d2410f20700100c0c414031804880d8403107140a0310350384030000034091072540e190b00207001036042009030b260310203400d0a006194942549907560f030310f0001c26074807840300d0022075070340750003640c40c80c09015038201d555030300c02101e001c201e455590402c620307190f40c0c0c2c0410074030084c1e51074224000c1e1500300c9855440386100c0303002450141d442042d0781c801c0d11400c464000000303081000c50708151a00c0d084450307001c1d44a2046500c1c041c2c075804542c900d4034070a1506014040c100e48000b08014280300722008003581598208041868600d80312150b01824001c2c11201c000c2410300c260031784a6130321130052140c0101c0510b900d941c1d5003c0160418044002600e00f50050714103641d82400310725144102 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 958731843 1250 958730593 958730603
    0x70f031b0302130b04110a03051014130911040204080f06071701172104080c03160501080c070b24041b05090303070b070302040519050f0103050406021201061119 71
    0x2c690f80700c4104500800e0b600802c142e0140c0d030303100600c00100221010700520b03405500c0010741070420080500320308085d0760100c801d00b503d4098090803510303806590010300140950106d0204013519201c07408003110b450850300180b000c10009800d02000403103125103200101541d14680b100c1c0ca0880b41100d03070694400400301d8940041101000c0307100c3c9900e1420600064842c03e00da820719020101482010f000f2001c0ba01082c1404281410700262600e904110010080d02c02c00d0307032980c81c159015115403414050958001480711800c0380403240c03031b29403209071040145044c40344490209050b9090782e2131194103102015403070500e441001217a000d000280000480b030681c088a2941c40b2040d02c80c0c0500084c800c0b180000c1c00e035047d850140300d45882c0540c0b25403c1405205156032803c0f903141100c034815500300190b440c2d08030410704940080c603022845596a051500184c440d401f01d200031210310384000203107580c0c0288400a018030760320503031344480c407031040c0860381c0c81c2908000340c4 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 958733093 1250 958731843 958731859
    0x6170303040b190f0c0305011d010e150307081002040609050f13020306010201020f0304140f160e07030209030f010b0f04091a0405191104060f1503110408070f031b0302 74
    0x4448180803200c0d10609100f01107a40c0310400c40e4a03054031040407800000c2a220001845862581529000b00112050b541c121350342c54408942584000076020101044610350b0149030b0761424000c24000d05005421545450a005d81800080d8480c0c82024002161244003250510b06003e206a18200c010030251b868400080d821000350b101910340f5055650070482d40c0e1084109001552003140031303d2800356003004010b005420450301482c1c070b84058118450301c0c0b07020b950745d802203400d66003070402841c0c00e9542c9480c207400a01c201e00c00d403035040c40f0300200c6084101c0b05402186106800b551403c50302c1c1c0c030072010711040c3c070646840140710000355500004a0180d60b65410f0b03000703000e0001c070356008880e804446409880c602c1c082d2100c4807012480a851706090042e040107107506400045100e00d0b000600d41d00e81c1149102c00101600c4151640c9200282400d0b60701803d403907016100f215644481c450701c0706c8241d00c0212032000100740541e0315036944034003600407030303030003400c202 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 958734343 1250 958733093 958733101
    0x108060f01090b0d02011107120c0e06040905030a0e0102070b0c0c0a08010614010513090203040506041b0e040f020406030b09071806060e150409020414031501082109090a06170303040b 81
    0x26a81d4400c2072800310141c415204005100760310003e270399003458043d458a101c00c83c101000c0b040d1010006019a000368103118a0380001007001044800b040c000c1d01e080700c0700c4c00320348004034103140381030b40030012906c4081381c2a5001040440c0c040515181110035403a160303030307900402e42615003a1144170b0091a02a64184c0d05501400080c000b03c010400001d01454441e1044402c030b800c02d50b030a64403a4441d500300010804450244500d01040b40280c250300d520b01506a1030710f100081008100104000d030000843d01c45030020005981d000d100103555140105030a45e032800346225813029105003001d10780c02250241f00f03002c00d8410980d20b0f0320a01c2e4a4405010803000e280661220b10403040200150300040d41c03016102502d1500d03110002da04001080618100c0c5604044500c0b40c011401008400700014004c411154600c0e0001090070003030b00100040d0240311130036500240548100310340060f0ba5030200e001d84000740028080c4040c0040429600d0008550061908061901103 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 958735593 1250 958734343 958734347
    0x93b1e040c060e01090f0603090b0f0f01060c050c0d0521132105010c030b010e041406010305100806040c0305120c0607030f39050a020618150108060f01090b0d0201 72
    0x10f82c0c2c0305030103040210a665840c6917450400100d80d02c03401c00656103080290402248940041d0000310010110500b4100120443e210f0341c418810030003441840110101042003d1099502c1c07454018951200d41c0301d581045912080e01c500703401901030042000e0341c01c3c05c11080aa0309d074138601d1040030701c10394285500c4042074243c0d810500c4055502d5401d07800000e800340501041180385a41c0494460003e80014100c40d0b8403410b054032079428840e0545483c40211100f0340d020100b403130040382c1c80c0c88600d0314900140f10380d0004429401058101310034400754942c1001160720030021206800d1802420789071501440c802c0740313442e40001c404603801e60700ca80c12000035000742c1c28002603881c20804590340740d40b444148104502c6508680303410b1102e50310104050000b5507003002480c20340d00040c000d4031580d0080102500b1003043c442103d43c2c89003000242006245c088c4000490f503159119644c0d82c910403605015001140d400100f0304d0310b0a03004210710b0000140001d90700500c25401 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 958736843 1250 958735593 958735607
    0x1020f03040b09070512010204090c09030201020316080d022718010e0603030d1b0201060f12060e07080304030f050132041a0a0605040501090507093b1e040c06 70
    0x1c20f203168851032a0200c0e0503602c0c1d0300b1440d000310b4410001a515407602c8114001d464000342c1d150203015011b5800c0002d0b0740c0200880348004165810880c2c540218036101c0024018503803400e400a1020805000d0306003081d42031000300c0301c203201c400e06080751881041000c05841d25016280c0c2c1c07404004010307105003000b0560300900c0040580f0700308001d10240f401291542c04805850002203076101440a80a12550300034000011011807440c1c1442c8a04101c410710100081529030b448050004155081c003c04000e006241c05403a83c50b680c81c2010300049801603c10790310755190102425220200030360b000d910203400c3c2d94850b0040c55500564910320300003002a1001c0003d0b0400f55042e03001c03044580d2048585800000f5014200070a00003243d030141c000c408550301e08010300a01c01d40184000085581801081032280340060344d04000125144000001c070758060842c40020005c400300e17174412003040102040102d401d081203104180161400391880c20304003401d000030361141203 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 958738093 1250 958736843 958736851
    0x10f080a12031e1a0103063605010b03040b0c0403030f05031503012a0206100b091309060504021005070b060f0a08100c020c010c0309210618060e01020f03040b 70
    0x200080c40d03111031012925500072070030059079444e50342c64113140302414810035040e20603028a81000f42e1404c010300084243c1441d000140411122003250030309a11040c40d850304000606003d0080c6e50b50f070001c0e5022a001601d04a60a980100c0000c0d0b0541a90040e281201c0e05940d480f454903508082c01c0d101036201030000a40402c41c1403100003030303403024005ea45400070411906040c400c0910b818090b417080c5191580e0854004030305121124048000050542e502440125620300c2c40c100081c0d210a83d50304030990300d40c10702c2136003000d101455110500c502e0007520119116111801e04480d0f034401d400005110345c03a810040390050170314107295002c0c1840501140710341500c8114503807a2500e4040942e042030748a011600d0150342c14400a61002028200080c3d0102141d0b00078204444501841d850449174a0001c0ca101c1c013903d01800c442900000c08006c0b86035500b20703211003282013031015a000c50421200c50a03018051080f1401442d14075020750868480d560b400c140600090 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 958739343 1250 958738093 958738097
    0x10e071103030606030717040b0105090907051f0216080a050d0e1309050c031e0c0907050d020d110a030e0c060f0d0509030d050f0106110715031829010f080a12 70
    0x5141c0070700c8405070401460150727001d455501d41d20361500b01000328076000141f0000d86078000080170405601d40c07503d503503c0d0386050076460f0019594888100d20304003900400c181408020b48001030700307a802182900d003190041e03007914440c0002031015524107621816068010104082d540f0700111281c1c070036000780e8404c105a0701d6080400c1d00007454282c1c5014900342c03a0f040500120045202000b21031001c83d415503222001e407401d4400501139008912148281540014054002250355405940514003c0e0340903502d59400c1e1100030000d02c80170b841b411540c441d0700006c490754a080d0094503142c0d003680d030403145401201035071407000e80009801c0c5603e9100134484500f2501d50342c01030600c12108549440c50a41c50044024210b9448140c1840c49e90403191080c08413001250003440c584046003004100a010041c1d41d0365010400740c009416100a00e43e86104a8484100080141010080244c150f601d60703107181d0b0a080349103c0d1041c03691200d4400300000300d6035407240c1c01c088418 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 958740593 1250 958739343 958739357
    0x607031202030a1103070504090b1005070b19061d180714042003040b150105030f04050a0f201e01032d02090a150c1b030c0806010e0711030306060307 66
    0x500135200b90000d898110103e0000b03e424400d604492140c04100441120742840754580400c0141c1544079402d4041e00d800c04c21000122100000040112900c42c5c58400704105070360b4468000c500540101001c60200b04400403ca207480301c0d800080c0d82c3c030403d6000d01040e07407501040207414450015074540164136103580200d00103121000842208240080320380d030340b07004c0c030b00000c901c607004201201d11400002c14200c84c1c1d03400030690740e124400d0034051066407503a05020b0b203003001a80c03000b000102c03810300071410000880e0710207103184118032480b0401b0791800104800200c2039059402a0801c01c501c82c04558480d410850b82ca0b4000340404070720780e0719030011042044100240c80c4200da00020a4019428800000d5004088035050000c0c0088a00720083c2950074082024003500070604400c25a1341d14840c0c00f070011a404600203556941c1c03140d009856840034869101e192005d1000920514080d003400e141c025500b402440c0f0317660300d00c010461140c0028100800f00154 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 958741843 1250 958740593 958740611
    0x8070807180b0c010203060f01021902060f04180e060a060303020a08180907090e070813060e0304170114150102120a021c0309120e06070204090f020301020a0903110607031202030a 79
    0x103000102040f03842007001690780d00d084420b2000a0341129540c504540c4047c03420f4110913681102c1500720b56040311160359607140e03003e0407070b041d004a80005003040c2c5032041c1c9482e03c2800350b00003030620100701d058030360641c0c51101c01001c40c1c005202c040d000d0380085005030002100d00e80204403101d204581421403031800c8000c602003020071282c0754007180b1040828440e5202024a040d400318892078010141d180c9030076400b40710042c2080c001e040b40c1d1039803d41f05600e68103100303540207402d1095070340841d110300310852406030544015010b0049005004121902242c514179001030106030003c141803e907a07601e4640d0341e40080117840460040440b023004000e07191000f00c41000d0035642c0859030414031b0900d010100c0000004409001c004040303445662510420f0754440c5404490005070980d9500749441b1032400c400c0001d6065100040340380c0b2035a003003500c0d0002c0e00d002d0b0b05102014520b9100384080e80c842c485014011600340c03004180082034580081d80e00107004a0049681c1c2e203 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 958743093 1250 958741843 958741859
    0x9011b0807140d080a1a010c051c17010f03082d0301092408100e030f070f21121a0d080405030c04020f03040602030606280f0807080718 60
    0x1102c000c603659140c02540c3c51034400c44d0321004981d00000c18240800060410801c500354148682d004941031140d041106c0c428483c00f400784c1c150901702c00c41400100e501c142001480c0c01540d046050140d1082000032581401a1001d0000d03a0340c0545500e107881e5401d822070024136842e0070114558454000c2d08064040040f014600038480684003040c1540d01068003118080b1809000551101003a805c200c14000001c0d00c01082415481c00183c400503200e40d2810340c4030b00c10070400c0132480010080100031003010801c090a0240520302c02448103141c001d0b049280c100907400004954100b042a0440c4503400088070107501c14049407024002000305043e030780c1d400d0b01a03840040c04602003016040620084081c0003088804500d030603641c0740f007180300f4007000d0406014141d02100082281d180c08044402c01d66046030200c0401c82401b103003c0103d00b180d41c28034002540701c407043c43ca182c043c0d800d0a0081c01c0f103803103520196440207011102c2111850050350004891780c13001400c82 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 958744343 1250 958743093 958743113
    0x60f070c0603020d1d060105150d051303030e0601032012060f01090b2e0302040f080622050c090406020d021b070e010806010e07090306020301120309050609011b0807 73
    0x200480c2ca0158603a40503a0344c0a0455443e607001e80c05119a01a0729100d100c1d0101350b00d410340d00211244441500700c00b414102c140240700340780c034180749000184074000c8010139000f180d0b180303c0d5400f406801004c050468480e0001c0c030004212408030030044080540d503008002c2d030210064052100c2d148102c0c0400e15204090b40c4030100140c4410061140b1200e9000d107800486007510750382d81440d44540c981d400401d40001c1104a0007494240c540201d10a4040310004d0046141d14100c0765240c1407515160241920006190402c00d9414880145041e24502807541c10002400d80039205605000131703e00d0041045401c0c603800c1101d1484aa100c1c400f03031100345840c0300504e2011101606c03040ca400071507000402912940c0004000000c400140799055408480d0641850749076441c080d145400f540d0001081c0b00d0011001249445603c100b40710400d01940d9001051907a890601c00c0b284125841d02e8005846084000c2e9000102c00340c41c8486031080207402d01d4021582c8075001701d0 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 958745593 1250 958744343 958744349
    0xc020a030b0f0a05010810202a0a0807020f01020a1415010e040507170a08030c09030d090f05010e010c0f0c08120406081504090507060e01090803090d02060f070c 71
    0x1c1401003840b81d0a1082c4001c554407039500141000254105805e0540d00c640c40c11002c04403540310300d415200d848148600480450400246c1c0d900d5582a80850740303d03c2c0100e0070740c60680c0301d1880444d809000040c00110450700910001e01e441c1684e000c2c0004510b4002078141503208104445000540355104107505503124805014003000030a50640078103010707480104808902018000402c001088a80440b40307090f00ca9601842b2001459041c103a42a0018011590220401c0708020040740246000d5000700d0540790450103521b001e46102555000d80303280c05800c04024006940614a082006081410304140401007669a05801c140b0040200c40451000004100050040203c5941078092840c100d0415081060040c151a0004c1c000c5180034062100e0b10780e0768850b03038840c1030141d41110640d45625100c0d04080d00713200e90102014009421b0280000b6082c002006580d1070300d03001071041d01440c11580030800103400440300115000001c00508000580c14500e040003 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 958746843 1250 958745593 958745603
    0x20607030f110609011d03041d042109031e0b0106110102070203120a2a030f110d0e0307050a03240e1603020a0e0c030a0f1506090e070921030c020a03 66
    0x5080c20822083d001c55100406d516080d81c41408140103003028900000c91020002c00c403025103540702d050403c40c41c4001c4a5100c1020000705e621901070380d10a4980381924021504042c2c0c110b21b610712000c0501c5010805041d43c4445401880181e10030f03a40b8401c035500c0c400c005030408030701390002420700001034035144503690000313849603150340c00988100e0680c8070400060781c00e0048011040f2081c2c802c050040c200240d90b00403e40c018025814082ca54404030100c2e01c05609045018044110910400f4032031b10500c5000281c2d0b15140c100712007502d50055488010244a40030765640461154032091020b4440d081100152001c03c5054403038071240c0c5940341e0380d920314014404004203a4203c0340402c1d05850400200d44d074180e084030b42150f02c00380c0004801c07000350740c410003c04e040165403102c91316070200010250740c4198101c0984030003000583c070343d03290840c0603140c106aa104210185044682d01da1103c100e070741c0484840c074000d08200705c92600b03503800502c160b000368008440b = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 958748093 1250 958746843 958746851
    0xf0201020f1e060c0f0d050601090e0c0702030c04020316110c04020a08071d010509091008030f0405040e030301120f0501020f0409060305010e0f03090f030109050a0302010b1c020607030f11060901 86
    0x314102d420042c05030042c80c40c14110b86030085107034110702c1030b02c200d0001120054840c0041480d40c1d2107801800e0080009015540040c101214402d01941c400710090b840391184047c101181d16081c400c0f01d016803272820160120740d075501c1080d614141410001c00e1a4090102c14a20700d0721180000e140081c034641d80c1004034540741c50050100d4202d04010007001c90140e000005d942d800c1412245d0352901100c84400e40d0313032002600c00b4801c0351900251048d00020030b0342a10003185001410942c2c004480a015170010705c078031181d076408240318100d0b21482980240d40030921060600c20210300500016143c1740d4050ba5103102580315038407810409541d0b00003082405000e209002920f03005101a007a00d006040e61550340740140360b00d0b1031150184484850709954258818105075270f1200607a8030088072410080c0c001c00b45150841d0044c0180240201c810b28004909200300b03034010000f500b4842d05032400c8500d20b400e8207404c420b0000c1d844182044000070080d1911030f0210900101e = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 958749343 1250 958748093 958748143
    0xe040c0f02060702060f0408091306030b070e010509030a02010305091507020a02010e04020a17060102071205030a08060a060512060d061518020906071e151b0f08040f0201020f 77
    0x910300100240100f00f107411907420701c000c9458411400760030036040726507203171902c40d8040007907800940c8901d18100d4501d495400070070000b58580322481000d80d82c4540307c800380d05000545031486107131310456040d003244024034010b600130f80c881030308241000211148651018604407150380162042000340e40103d411004540c0d001c1d84034054481709840550420141c1440900102e418075003042103240200d002603002c2e48200014002001201140c1980070002c1c10502d450f81d01c4556840001090320000800c0c0b4284400c0000c02c0321711503a90f5528014024221581d2900007615a0394040012280340c00400c0140c05142c92100301c0b8816620710914003c40c20722222001440010324500501c00c061072581e03048140e85140760441e4840310219150700c1c08000c0c2a0080c08020507058402c02000500b5075140d00110010241d001207602001c06150700307440c070441341080307000064403c83c0043d00203100165400030b507078410b0044980c21480408001c1c200192058081820900360001c4 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 958750593 1250 958749343 958749347
    0x702062b020c0d081f06091e050a060311041503050906060429040204030b0c1b071a180603090c03010b0a030506131e110f0307180c0e040c0f 62
    0x41a650320000d10214504141c01c0811a210b80740c4100c220300740511400012121450f425000c03102098101c0e080c50410786030a000740c80b0200a002d04940c0f1540640194014240107540d103041d0307040144000020b5103012012009062514050701ca11041800300051070515201d01206070b43c095180496140303421900c0c949003410051080380300e20b080481c407034403069944031000f114048050201ca115148030010030040d10880e40010800c400400801008248079409085140540c600e0480f54040c20001d1640d5401103002e030803000050600040c522030007003001030507403018043c0d10030b24140103040001c132150800c07034210505400004c081205d0740340a00c180b0106840440383d80c1e00d0700703055440e00f51752200000e0200a031110344217081c03814050072510a42d0524102d0a100280c080700d03140006400fa0074881d02402100c000c3e40002c214a0040768190030b07a546540b90000c12044484206c0c041c00907071410740e042c058408170801c003e446038041c00860048a032980030448101d0040 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 958751843 1250 958750593 958750657
    0x2070302041b021b090c0703030b1305090d0302030c0f0a031d010501061403040b01050d030507050a0f0308010602030909070e1306030b15011704020402090103060e0f1803040f050d0602070206 84
    0x120b40d1300100303400b54240c1d00c3c0d66401d40d07150000413070000c903525071100b450103400030305120780b14940c002c00d80b03030441c504143c00e40c01c694880e4400c0300940703404904818098003640026510260100400d021205041ca00140901544c50306454003107440c00c06000c0000007561649042c2480d41d441d400184800d980000c0d1400740781c07a50f000e05514600e05a2103400c0d0603e0103010b080e104030728404140c410b061244007505d0311141c00400381c4042000502e044441c0c08024401200491551400051642d00100c2640c100c51000303401c01c00d40c1c1e910b9030000c890340800001c5681c1e21445c0c003841c1d000d0101c458440c14010b18418020507080d81800c003030601030111000c040604010301d460000c000c413061f10385a960026415100581c580722220700513006440e40b0782201060130200002c01c9500c441e2004110300a50002481035104c1e00c0d0440c10940701d02c20341c000d00f9414802c20408008904064001d030901d50f000700301c01030074003040382d00003245680010108041000c901500700d018142c4056 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 958753093 1250 958751843 958751863
    0x907060c021807170112110d032a0204110322141506031203060303040e091005040f1412070b09100606020304060905010f0c060e070824010e04020a0e0702070302041b02 74
    0x14080120191a94440440d940608009801108d401e149502058041e0000300d80201035810100710800120a4a0071014011b20003607125900385030007141c10000b9078003281d0295800812540f014009910a209448064103045503031003014603070914010428801c010306801c800d810140e1a013400305c109840c0901a86042d06200820000c0c07100a03500001280c2c200c511641c184035071503903032510540c100906a9440c610721402e107010001084103000c14101214443c90a00c4580402420600c0da1012000040a2005001c018040202c0c03282d643d40f075030200c40c000c215100024450200e00680b90140d0096000d03900104080c0203064001520401619080c07a01c01c0c81c403a1024402005120700c034902400743c540d107080c0a00e08070024800c00002d051740e43c0446011440c9107034910080c03540d828800b01900f05410011840714000b04840340900c2d00102300e55a075a062500f04011014090151070030340c45031030000801600c07180901c4007041c000b85070107400d0140001c0f0103410400100 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 958754343 1250 958753093 958753109
    0x105010f0e09061026030a03020706050f06150d06090e15180a060209040207020910080d14030f0601090f0603200a090e060411030f06030f03030907060c0218071701 72
    0x201048440a600104132084801c0180145100b12000b017812210516040050702e46020000324858881c0d0035800800000d40b0600c0100200e80d94081d1401c3c1c402000d03544680d200c2d00d01c02d40811611012000341204c2000c1c4600021119038030064242111440000c0a101303401900d1440b000354030030f811642c0d02085403500311074500704032003e00307440f401000c4005043d0341e03003c41d600d0000d841340d41c1a10061071b0f01914212207030905c520310300014041803142e00e280344035011400500394422300040c1c15001e14810502d040d42c84051810401110042040c0d040115040700040c000200c03150701e6005200c0e684000800909216400c00d4080d010b1074442e0145404200c007240701540b00740f01740211500c00002c4c07840c0ea06c0c5c02c4000790180050841e1802102ca0100038000c071107101c0c61101d030203060100d0895500311283c8a16580340c4c001282c1120082c1c000490400c44a030107031100d001000e00c001c280c09440c03050342008044405050301d45000050608280b0201c26101021280c090030b140 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 958755593 1250 958754343 958754353
    0x90f03190618120f17101502010c0e120a0206030c070203011802090f360f060105011215090513050d0e031b0a2c010b040509040609050f0105010f0e09 66
    0x152103800340142503c03110b07010490f41032031030b00c8603a2040c01c0310f600300c0070012032102407428003860303d4030403840a020300b6030b540390390090402840e401441002c0020f020ba4941c11704480d540420058a583d06280501d40380c068074005c60010780c0c41500451140085251032a02c901d4640181400c442550708000c0c203145a11039548056564400342503803100c18041d8408044e030341c003022042028201280c050345a0070405058040710705580343c8540e907120040c100c48000300008000c42c2e8440c0203101e510f001c1400c1b90700101d00c4203140c1d001802102ea0714520b1120081d52050b0010840740129581c4203c0503900d4904010044140641d182040851900b039450700c0340e0000103511404403416003c03800c2419940220075844154405004001d10020300120245615260402c48444a020709081e00e0700c600108207855400c00391019180d0151003980160348075664940105070b5074005030344c140301d000d81c4500b030040d09024013800b0700841980a5845807501d8003042c80b12001405e09196034000e = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 958756843 1250 958755593 958755641
    0x40c0b030c0315060a090311030f120c120405010509010507032a061b1b0201020705030d03051b0a020a030804020f0405010915090b1e0d0c06030b0a05031f02090f031906 74
    0x6c00703840003040d00e82056410a134620290002498600c44000128180c02425560862902004003401d5605202019100343c61003009003d04d507840f81e40281808a041032101e0340c015449513005d000d20310700c40e00345404804c0d014102c0484100070082041e41d00b209034220300080102d03c9c001c000007000000030001400b0203000c1e01034107065072021894480c004903000310041d07a108110542c000c11000e010b4840c1c850589a005001d0a01111f8008000d402144040c00c40e44500c0120b0b004001142c0c050401042f03280d4040741d0502c8050401d07a805201144c0e004081d56461040600912800500280541c0500d02c40200c409081e030080142618020800c4806d03120300c04800b409013028103000404100e4a000900c20242c0d02c00301404689580d0390102d1582c0e010b501c040a4540c040350500100c96840040507950944030058180c1a520041c0b0080280800c0d0080c184440008000a491150550103e03140c150001c2a90b6100a510410041400740500c540c50030444500c0c55031044070340e = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 958758093 1250 958756843 958756847
    0x190c020309030624150a09121203051e18100621170309010b0a1a07060b04180b1603050405060f04030e040c030507020609031e03040c0b030c0315060a 66
    0x1401005928054401455a4113041d03204005441448004149481c80464000b000560f9040003007501e020071190303000460611010b03080a95002ea21401100c00303006001b000710043d00b0042c083d040e81000d044d0180040d100704003c080d124102509d07074505020b101c1d4284030301d440f41c0840c001d1080c0e49405014004489203810001c0014201d21207000300382c01d181360201c04c424244401100100011003032014085064102111b010001c4840030100c542300c0e100115101c40002041013030743d004000ca0000245150890884800c00038400211643c603d030a25840740152442200d00b202d23340c0421607018030b9060110200c55035440d080100b842d0698407196540000340c250b015624190b400074080522655110b0300c0400058000c1c00050752030b00e40503001e40301c1540d0103005406604006040c4070310010071745400c402040ca07502202c050110b4854002c1d0310241c000d4030700442e00c081c080740142ca0fa00c000d6010b2201c4406580d40d038501407400811901c1c0040ca4a407084204100400d1980e03 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 958759343 1250 958758093 958758103
    0x1a07031e021e0f0301030c0b0f030a0b03162715051311190e100e1e0904050d02070801060b2b0e030a030b0a08191a190c02030903 57
    0x411010030060382d0b1036412811420103802d800c44006038040004180c00c411030880042c50403244610040701c680c644a041402c0607014186401d01400702c1400004c41c00002074100300551000a01a1031765903c500056030b00c5900c3c01c0d003180b0307915080107400100b4864010a80c64101c05441410094455056110002a01d451046a114038111010081c2501b0b0b1940b11000c02c0030710304501952420725908100642d04a840c01e034010440129000b00107003410440300c0782c4094141d40da408440b00c000300304034500705940c09801c404500d0b00c9190074992100949140030754012402880b4103610403030020300d401599000000310342d0610404003d0340b0450800c1d12071b102004889542c1c0c0c05c000942c101d52414080341e0f0034501d00c1c2130111381c90b0000c002000611200d5840d9030207000300c84541051018803411032080341d1080c0e00090b2403800d000101680808080c0c0b0030361000103495403040780c45040620540e0049a0f107c0410080c07131b4501018400c0c84070584850001c0d5081007001c5000030b40351 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 958760593 1250 958759343 958759391
    0x1a040e070308030c0d05070909050601050a0c0611070501090c0e01050316062a0c03020102010b12031e12010e06130515040b061603180909020d03030f021201031a0703 73
    0xc2d080100200743c1800d410010b0703450125018000b000b00e842d090340024441c51a0341700d0340d907030315241c0300c0800c00a510920480308c403000d00b0348400e1102c034004d64408000380511120011140c00902c8000000361080c0144c0003542c0c00343e00130031105070400725170032105441a40054441c1d404128110a801c4551100d1011107060b03081184201c038070000410042e5007540c5903912046455003040e402c0000341c00451094034000c2c4d0081040040d03410602105081d280800303c06a4014400007007211410b800c0c000b0761a074084ca20605210aa200602030507800780c0010101130b0030a000c0013084d0030490800d20340b01c4110b0398140540c0c10020a0b0250011044510754002c58480d0322205c0181c8800086403880c540c0702d00c11071072032401070a0051046000c11a60107242d800548001001807281c002d000d042078004041700c100d0300c403540e0190002d0814010000c641902070160008400c407500285000310b009881c0c84030100f4902102666001d0002c3c1004145894455400a4251010249903007 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 958761843 1250 958760593 958760603
    0x1617010b1302090409020d050a0303060f080a080904020d02030112260405011d1f140702030613060b0418050136020a08100b01020706050c0a0b180d031a040e0703 71
    0x50f030310200010a01500301250003030b40215010540c0c508119002500c3c0000078000d036420400192210400424039803207100e06851640201d41c40004548000300420045d00c00500c010301d011030801c04242640c0003644100c5a59100da14503c052000c4a0103011110040c066065040414100108a580110300501c0d042046240da0811340300c0c40c282e1214600d0070020705100000403010000480c2805011a8130005103078a04030004103041c44043d5440140c0c0100500065980c1100042046070324000c00ea505a450b003460000c0c07600c891003818000701c2520a102c030114500c4c2031841c01d49005610002865030b1803083c0700c18448080400300040102c0b0340f95813603010070500014849581e070750010000b074055004420314800d0560304c1000704e001d080e000d45000325501c0307409465034010300100d0070a580140702c081001070315180e1a5680660b403034071107214010449100c00c0c6006a801212030100e42c2e500b8003458918084250922524021a020b000903160040f9494543c5035074400208 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 958763093 1250 958761843 958761847
    0x182103180b0f0c0f0109061a1504140a0b0a03020403020a0618090e0307020a1d070c0b060907260f060a05030c090403090510020d0909020f1b0c031617010b1302 70
    0x20105009108a0380b0744d044001c024445030703120341010001481503e044030340c0001140d060500f503060080c80c160041e0140794140b0f0400d45481e41e400446a044d10106511805c6c0f240701103000b1040e00040c114401c0c051b40c0c01a11281184144154501c058000d242888100c80c0c00004001d8a0340c2c0c80002d480000b0404102c04412264061079406040700095011180710f0020a0542404031100100081c3c103039010420f0320f90039130075240010410006086541075000140e030609004801c69040850f500e0000500d1400b540304005c0c1d604403c0400000341007440030f0140e88800c00c544142c1207002240e50b400601d03c1c0c07800007513980000490305030042d0307021000101894003c140c56001800007034000c580384500408025224072000503401d010601c4041c022070100138600c2034660850342990346503d00045203050540355600c55601c80d10f0340c440d0400c8802d89480521108078100d0300c1c508421801402c00060344540d0b4a08084421180e1400040718101e594454102d103805070195001a = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 958764343 1250 958763093 958763107
    0xd0e060d0f15030b1b0703120903210c02072103080411060403050703030314070e0d0528230c090c040306090809011704030807182103180b0f 62
    0x402600c030300b003918602a1030400002051101e05280f070381c810626601c4a4021122061106043c0e00030302002400141c00035030b050400804a50250305241d000e070504030090789844404001d4046082c403900c0c0180c0d00d030122201942d804001c003001820140030004414500821800420419914043c0400203030a0100301805030388055540b46c0b22002d861a83d4468a0b420320a6494107584000c80c0083e103028041c0403402841c480f61801b0300255980c2102e50240d00b030412800c100405800e032594065000c1d241101d41c2190b0700744c0a407054110b00841c9174046818008180c1445464550b40100300c80072182c540c0e100825442c00000d41182c50941585501d07130307980d016006130380000301440e2628041c44d0a211400c0090482020f090366004c542c03191300341041812803029a4001c1c04035020401081d0800c1c090704480700e5011303a04202e1401c2d255100726550804404808a0015107540c55403803091651010108440c1880608401d5807a0f15050610500d4420b5400c01c031564400880c0f08 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 958765593 1250 958764343 958764371
    0x10903080f13170f0714132c060624030601051b0102031e0c0909010302010f02030702041104030501110412110d0803041401150803120709170604050d0e060d 69
    0x800040c0100b82180940d4503c00354400b66030740d0f50036030b035a4041d1051800001d110840c601d1241300341d010241402d590701c0d00c4e04103100b000d070240d0098019140307002a4041040144181ca49003070714035410007041541451428440c140e12009280e5a01444107a198125154000c0403070b90405420311317085030b540700b80f286038101881400c82a8500b80d4000818071124540684080310b4100c0300d003c002e030050710703015592409032156852158126110000401c007540c016984900c03418150300584e4585002a40028212001402c40041c0b17070728046002c1c82486024030600201800f040380d03480c1340038140400213041e4540c150005112070301040400c1e096844e030010035079422780c1c000e40203503c0703040030310745040f03003d1040b00c203940690b00c0d160205c0700818803a40c06000f1580c0301070207540f404010109001c5074400c000c0405040c41407600002517070824426882000580c01f20261246041c91302d4190f0600040c020000100841d50407410f4265840000303c034840065102d000840054490b60307 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 958766843 1250 958765593 958765627
    0x507020c2805090901021206041b140c010204120515130f051203090a02040c05090f01051602090106082a0901210c030903030b0406061b081e0414010903080f 69
    0x100e40d82103c000800e20054083c150042d081503c42c45030041c8141c2d480000f4001290701603400f856550302081e00b03150700c090041980f220321400801c0d80354507020300190b0341403da81c0954403110501c079402c008081484000d20482c542000d209008135918108070b0032155074002d0142000c0c00f9550741008100422000f080020005c013940079416843c3c5c60080d6542c0c2d00e40000242c00c1c1d0180742001c42040703040e071150040321725003080108402420180d403c011a03803a04600207e140c25060740e018000581da0780d282c1c85000740101c1d80d0384d01031498212280043e0f800e1660307603020100d21686001c0c4422030a031003500c2c00800f0a29051420700c00343c08120144103514411801e1003481e060b0548034641d410b820800c2140d01984092011004c40350602c070451346903100d2180051000251420b58030042c1c20440c40c098013550010381041c560a400d401102044100320204150001c3c0c02c00540d4105540c072301514609080034080c42e4910784a100c002d100301c0e11141401e44001484240403031007101 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 958768093 1250 958766843 958766849
    0x60918140c09041a0901090b012304090c030c0e090709090203010f050f01170f0a0f021f09050a2313150b070519030f0806060405040f09060507020c28 66
    0xc9a5550415042c04080c0110f800c0d00d508101400070b0000303038810414060ba440103640310b00302101c0c4c0c2e0300c0d10825a14003900784800f480f40c407012801e400e600f8bd6a40c084c8030b00c1c050040c445c0d03980311459440c1984001d0001d611440490003d8020005a0140841d94404580d504140407a44241c0c1e403001030700424550040e040540d2030320090101070b510403081c00e81a1003200080b410196181a082d0f541d5841850119215502c850000c070000380c0e201c82d00008a1303102401c1b0440c400000307002244c10320f4003000014001516400100070928085890f003000f800c100940c0c4c0070a000096042510040805a05000701036400786280d000c0303180c0e4000c801c94241100024032a68660440c1640c50b400312781d0698a0340316014001c803203881d0341c846400c0035a925440f41c008151400d00c05607000b0400400007030f4414000c2c0000a081d840c1c501800c0c22a1030003200000740314038035141020494002038070040440d405030040d0b0b909900c4d0864031021795451200f82c1c0c041414032239009031651010303030 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 958769343 1250 958768093 958768099
    0x509240709091e0c0905240712050706060f0b0901030e070902040b0304060f060e01180b060309010e0706050414090406090f03110c01050f03040b0a0e010204150201060918140c 77
    0x1c66122103110700304000001610101000c0c4005130b121001110b520649010310740d0310501c2100911030f8038070342c000009903100660301041e0600860340c65802c3e050121181c6800422800122141041240e1080b900500303a80c0f00d8000d905400c044c101207681c00340102a6060550b6000c150f4125007003000340100400c44980306541d01e076107503010001e6680054070100c602c0ca00f410070703104144025005a40a4440c01000586142e182010b10011410509004c0024640c0c511340401541c407014000c500c10307000d16001003604941711702500d203003070004d03844041000b00500052105400041b1034140f2080d00b110f10f9041a2a603081800041c0740301a0003c0010103058260000c02da081480c44003034a04100035078050458a5005464a1140590b00c96040c00e08200003000192401200382e0821010ba00004a00000384151422613000d6001101500111180c80e10019424040d40000c0c20702c0900c2030151488940807407030310032600480100046000c01b2424400d5400301b1401c0e111184c01 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 958770593 1250 958769343 958769351
    0x6090527091c0906030f0e0303070c0f020d0c03020108070e0303030711070f120515011a1803061f060e0d03050c150a050a0e06071706030c041a04050924070909 70
    0x2855003d41050380601c1420040b07410000001088080da12880d40940b02c2000a54a1565466012914811115012500040302d400500b004d61120403000c2180e0780300d068201b030140e065000160603501d0043c104d00800100001c0603240e62801710660f500301020f4102426070741a40c5008500784003c58000410030001c500740001c42100296983d20200d01071400e40c1c80c8000e510003820742001c02400f07020f01c140d6070241c0a40e05100300c02d00401c09046c4c14040300090401b07160029041c400192001740307102807402a03000302c1442e00c0e1b400e4802080c0a080084040c3c903401c1c040341c150100ca010207014441c0114580c0200d100c24000906281595000901346180c20010440104015603010400340d00d800408070040000041290080455489080c1d03c4800503a10208240700201620741602804010403490b03141e501031501d45402d584954860b900300401408101c1d00000e01c9814a80c2c445c84e210040c07030030700031000c40041c00c00d24440980e07640ca9842c240c5008000354822488a490 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 958771843 1250 958770593 958770643
    0xf3f040504060b16030c0627020405132a0b13080105070318022202120114030d0801092c03031504061505090d05030408070609052709 59
    0x1411005106640003201c042081d1a03d0301040700d468080c145500c0c1408040c500c01c1008203000e40e10703802c00c6901ca1140428095805001c40d80f00340c021030034281417048041c0c0c0f91021843d0a0250329841220181c88070079420440c1c643e85680310040d00420003a04200c981045026402d0719190003400d000082c0030b07a10300c030604c86407045001500c5600b100303500c1d02d408100391a11900801102c81c6605c441104030154540070480c001d1b0809024030340003807000d84d00c440045098000340041c4041c01e100c910041d850020210841d440302000240f1a411260311040b480f03070028036881c10765504140010755001500d4140e840c415046410441c401c07003501c01803030b000000100441c0300b0340880c80046900742a84083c081907078a40d0041d6814a81100b20381c039603140c81900034210882004000782040c0d01262103860456029401506054004a00921550390001a490020801070380c400c0a4080891010107480c00d030485031503205030025010540d20a001c00884020342d44814503004d00c8a0 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 958773093 1250 958771843 958771963
    0xf0705010815031504170a050f36191508041403120a0b0a21021314010509010b090307091802030d050c0c010c02100825050304140f 58
    0x40200c0f006c035504242c02590b0601c16203043c2c1654000080c1ea140c45040c07244c01e014170b041b55040520f500060590907019411950002100c0001000c040e407503550000758010180300da103516441018a1101003000208004012412a50450141403030325031100d489514203910445800c40d0b100d51203210100e806231502c1c0a0a400324045e01240004005a0b08c411050006114580c8544d014400c14070100c409400b519812020425100520891320600d00d0308864003203c241e42e10001c3c2142c44000140810f0424480043c0544440301101c0c0c10170f140440001e0381d408483c00790f84401a10b424628941111115079405443d0b401401d6811aa000c090000e00755005030350704290758402c000c0b59040b5035000d0180c203400b2640140a03041540e000000640d020302001d03100c05104030741c6d41a500f09007036005104000301c0c000f940e40c080e40ea05040c140703441c0e00300b11502c10f00e20a800820081800000c0080c4580845011800c0c030115510303034071a2203c0f0380e003070418030120000c00002c42c810140 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 958774343 1250 958773093 958773133
    0x1b080c0309010e18010314070806090c03010c09180f02090907020d1e021e0a12080405070617060f060f0711090a06151101020927090f070501081503 65
    0x4001c0c3d895111100c802010400481c07040703840c0c040513a00c241e0051004c90410300190400c814071000307d40f1516960040946440f10403201a502508020f001d0a0035203000c4c0102c140f22040f130300d861303281c0a0404041d42d000d1809060200f1829940300d071100041d11603034040c4d450910000b4003c0c5402d00d8210800b83d01c40220b82158800901c0c540d600c03003402c100410400c4031307502c0c0c1c0c0e034000c03e070500401ca00a01e9074107200344951910b1203901c05100028002d200b0446900d500c66a44805d20709041c5044c0f8640007640c0c009000384400340b9803122011030010022a80b1035400c450041031504244003244841c803404080081400c0300194840174880c007100b843e106100143d404202c555aa8a452400c030740e100d0103030140010308081645e14451080c1034036081c08110000040c07411803c000021a0100c545020300242d07844c8076080320419083c0c0e410564028035900103484050051040c0e40c1d01d030140c50140505210f070f0680070401d0040c031244076551140d0050200c0399004c010344412164a = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 958775593 1250 958774343 958774357
    0x10181a040207060f0c022802150708040602011b0f0507020a1707140315061009090f0c020105162c030a030525030e0d05010912030c11010203010e01061b080c03 70
    0x11400d05c00e520060910000e803104400d40300c85402400f09102201846510500043c1640d20400709200024260404802000b203548950034840da80c42c41c294020b801d45208006100c1c1a0711160000ea0708241c1140b1032440708140d500e400e40da2404144006041e942081e0802400c54200307420b041c000d40c1c2c00082c40000c2d24100300005800c01d0822040681e90460400000d207504410070118005041c41c4600d01c05800c0c980c200b0001a0b91649065002c60720345242004540303840e8a20a0b000c641c082c03090541103a05850300304141c5c54405001344c011440b000707140982d0456480350211124868800c501442e40050907500c9031410360a0003000c5800100201c08020300b001c1002c036080080031004603641d5415111410328100d540c04110212091000c10350b01035407100803000004a807480c4070b01544011b0b40b00001d8101031403c0062440000401441050384100018000e0020b030176002c50465486140001070301c0c034104020300c80a00d81c600001e04008001c1800741080b6404006000b02e = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 958776843 1250 958775593 958775621
    0x102040810050606040509071101050412080f090604110103060803070b070906053a0c17010b040311040c11030301030f06140705070f02010e150c0610181a04020706 72
    0x990703481004078070211242a121642c2c440002c0100b0401800c00b01d015540c048004e050a03c250000800214251072041714101c2da02105030000000450300500c0c0c5603040540b40c25505001d140c400c2c070340c59545c000501301070280300d05412115034983c46070700303c0000f41c960350f000e4948a08042c600003a1041c020b0790f9032404202c3c42c180c00700c0d0051040c0280c3d15200034000660303d00c1c1c0c070f6500c501404031524030301c891035541c2c0c003e5541c0e400040320702414803945080d540e0b08440301c0c0038811007045c043c03068001300c0500d18204000c001185050ae45100c0f154400c9800040d20380800c0070550b1103150b01c599402d481d010200001060020080c490380c0b80f68000d41d014000650310001702d104818007100c456000c200e0030b01c40b01c0045003403604208815032040c10004c0c0591216400143d612540e840034580840001449401e115000d005640d085070300d04000150305810f140c007014a240004941482c002c0d0380d1440c0d0001070021540c21000f10102900440d40d45403e0b003050005403031802d2008507 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 958778093 1250 958776843 958776853
    0x6030603050c040b060d020919270c0e01080c07020907080106030b010c0305030c0717040807051f0e060c030f18031905060a15172503080304020d0305190201020408 72
    0xb65802c0c0380c01360b030101040003065a031030306148025040003900030180c05d45d08074804401e12621038140400c008040c00c0790450000b040b540d140d030641c030209001c170800391180f070070700c4140003940b40c01078000c1070078200900305403400b0b40d83d07005039070401d004840000e984814074100344403d00341c0006904e4140c8501d88e50038814011500c0056900542a800050004204000164059400c440608150703407042d410071078a60000104180c0b113400580100249030001c0d0010802844d040000032045500c1c541c600d89035210342600548945208001c503405200c0006e4034502c0341c481407040b58103c118000d5401d455642020213600b4031029148030b03d0092003660340c1c001c0c0700a00070303c04410381c0340e12174002c08940e030b652154080540140b103150500024140b03808070322a4059100d2503242c8134101c00904c081e10500d40c0300c00300703030380904d402c0310781a0301c200400d00225001e0b1007280d85c0f1980654002c5440959840d044406d446202c0030549040e0001c0b103c250003e6041d001001180c81c0041250 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 958779343 1250 958778093 958778113
    0x7170c0405060a03050601030e010e1006090b0f010c0807050a030201090b0a022a1203011d0105120c0603180610030323040312021204060503011a09031905010b0a0603060305 76
    0x481584180e0046690000050100d200310903c82d40140358462410714001c942105c1164000c0d09540401071380380b8044d04584501038450001d4414007009140a1001b40000e0b80603c02240d100d00039103c695040241c40361000c0c007480084002c940c603060740f0900f02c0307103a44140d0078000d00034050510215041c0601e500490004030290013526000810314544d00d400a601c03031441000101c10b00c04080d401d000304142441810303180f002850003001c00010b04411280c4c10001c00c5a5a901600420302c180c000d20880d0600c1c810008880403156800e940721960307601d900c464221782c0f18082c10710f6283c41c800d41080083c1c3d0010802002c044238402d40303800c10104104068103403d040c1c003411100602c80180010000f050790844d070442e40312110b006480c800140110052030640c82a0001004520300000411010317000d61385459442c1c7c3c0f80424281442c0c0c1d40f100194548021600035a607000392070041c002445020360150403c808000e24088200c1d60f5004090050005440305440a0080f00d00d22 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 958780593 1250 958779343 958779361
    0x215040305100b030c04090c0b04080c09010b070b0c090f0406081507080112110a0803120106090602030a0f050711061801030e060609040201120f020f3112080705060717 74
    0xc90240e4801400f508000e503d085c20320009240c03545041d15001c105800001d990801c120003000501004400b40c1030061401d014400c10000690180b0b841e14001c000010102d0101147c05800c040100a900c0e59601901d00243c10229440041503000c0e2410100140c20440080e60801c80c0000201643c120741c4c8886c010b45552100340b2442106051160550b070000b036030007015000f0000010428114103880365005403468000041c81e81690b07440100501c03800d60480f142c1d0004180e2480158600f0940e400028101605103440e0001e02c48041080ca08020440c2000d031120400a0020341c0c4400781003184181e02c400241143d4046442c00f00c00750301151004c9502c6205010142c54111030361500d50045542c3ca12030142001110385d02c0c2c90408603003905000500081d000c08240030b0711404858001d0b08480e840da4041d00001c0700004003960743d80000d80010003110001010b0480f45c0c00203080007401403040700c800400c240034000402c144076402051403101c1d84030301c90100388a5902c0c0313861 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 958781843 1250 958780593 958780601
    0x20406030b0f0f0f0d060603060c17041a1510020309191a0a02070906032306090c06300411010f0e0603251d0406051e010c021504030510 60
    0x44150000810300c405280d0741000b001c00130805902402486022a0b43d032541030840d0b4540d00125400c1e80c440c0500804a64004070000e88520400c001c2d483d10305047e80c6451003005884d94070f40340810803500096108000024000340c0b00c00140520030801c0c180a8020b4996001c0f0403110310030410f03440540b803a0341000b4109019601d10200b5038022054010003c02140c00c1f01d0340c810214400c0c52008500380f40c0b14081c400095214800c1922070b421494240041804c0d01500322425612250410101d05400503240201d0001541c08507510440130b110321a1b180c24011800340246211744484035010410742d5400d00c1903000e409000591200c80004568001c040d81c60070000500369003450485d46001401182c0043c000e03044201c191030350f01040200602c0d42511540440d080500e0708100c501b100746202c80030711040b5000c00606082c1000210030452042c9201129416450301100b0350b4000c5203501e4540b174005224200f040e0004880314080d500c00d0104031114020035401144204407801 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 958783093 1250 958781843 958781869
    0x6040b07082a09040e07170c0108060f09190c05070507050103021207030f060f0b0a1211041205151017030708040b0d060302090a0905060c160b09030d0609020406030b 73
    0x5101c0201940c41c0e240c002d19420904849622903625501c0b60b400a008200d000c0c0203000090b60b01c109507038031f00062410500e00803a40d90500505000f008840d5489400c4910002c6c4221101002521645081c00c0b82152094a9001c11490003c0b803003a0b1581000140c0103007031082080302c0c10300f03480d6401141a0f02a903601c50320541d40001c0800c0245000c0e404c01640d40c2d404140018455903100f082440c0b035000b079800800c000c1d000144074060107500200480c240d1446002c18003418110391000100c1f84500e102d6a03144605202c0000200001481400181c100c00c44031403109080c503124210003045140b050f1645641a944541091342c0301006031082140c02002036400e2520b40004480349601011882c100c465890001200603a038143c20309028284420000440a050303140007072400c803010300400f003044800d2040020b072a0301816500c2d00c8950110084050380c440e01e9049145025118203440e009042060108036000c0a60103003040b101070365070030300c180e012500c1070040c100c1c0101 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 958784343 1250 958783093 958783141
    0x6040e03040e0a0f380108011e03020901031b0911040308071b170709091106092106070905040c0905041104051908070e15040507090806040b0708 64
    0x44820403804814040c05580322500400102d00c1c0c9507420510800c6496901700603519442c0c580c1145c2c3d26503a21542031920001c09070f032082c10b540010002070604601442480c9416001076082d096041c0e8400303440000f1503014190179201e584a151215424080841003003441000510000c1c5220f02d900a007040a0022802030385081c0c215100c00c2c0c81da0780803807020760309030b0400c2c0c04110403074214035071400081840000c0404002102c0440a080441a80c40303950450305000c621008a8400700d000001d5540440b14249d6640d02d9002140c00c01130140e00300b21101e03046000091101d640810a035209600b03594a102140e91598100422200350100b11030015194038810b02c1181007641c4084052600c40b4070079820165174000003105001c841848043c50405500d0410481134100050000380ca9201221451868004182c490228206403c14406c0d40c4442c0030942050050a0a44c05420703428242c2c1c07481d1501d8104102d4025080c2d9010000480000014641020003901d08260100751 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 958785593 1250 958784343 958784347
    0x2a0c2f030604111512070801050a06020304031505130b04050c0f1e040c0306050d0302370f150c0f17010b0d2a02100507090e22120c050606040e03 64
    0xd40709014404d00c800c807031040020003c0088041054400c0c41c4c207440f420380c0d561008015810b04082c08003c11040e8005401d552050006100040303075041015000010320500040e240e4a02c0240000302070030703100161181848600740014400041005905554281c0e20580760107139031401e111602062410704d2001c0b40728058000580d282c00d070084d54000c480c1d4034021401ca901c0c0d000045c02c50050384270883c0940e00c18898803040c5144030070750840d10828145051084081c80c070700842d180c00820340041c03c103243c04000300d080200e82c001d220681c00303a07030104022035210b0a0014045074415030380b800214000101a403a0140681182030584803401c242d20300305501c000089028021940c80800443c100c0c10501c000040e00104890400c030440e4001c00782c01c0341040300300048900292001c0c042100c1d000081c0003141e003140c401900168902030441e200c0c0031103050700c8002d0f802400014000c407542c03082c0410b610703885145200da19020344151590f54550700c2c200411202d2500e4100025001 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 958786843 1250 958785593 958785623
    0x50406110316051605180a05040507051c0b0c0a080112060f02032e2601110a051b0a08072012030d110c060f09121c0f2a0c2f030604 58
    0x11a23001240c0142c46041155506915800061031080e0500d501c031003250143c40c2d1a00502c9900101c4a0f001180544023038980341140c10000e00000e014040c89105c580b280c5150300401085501156412000500440d100e06056a004549000380c2101c074000d0510404203514801c2c0000210044410300c1980311803000b101c0200101c0e00940840b12402c0b03541c0c811003980010415001080304030350366681c00340c0c4c0d010065500080c08100f49410401680703d8801c500000b10048110b520054000c40d2407410384940558203200300c002c06d60242d401201ca20300441100e030300000501195008118103018290f2519100d41c1c0a02a103c1d50003034503401103000c6020039041c250f030a6000080d202c05d840d0410b26808408410354003250f0700442260060502d050200c14a110309012011403940c2405900650501142824525006984408290200701d8030580c000c41d40031010f554444c082c443c0003ca01152180719014042d81c0b0140814400b001c09241e16000c80d81c075201e50351129143e402500303 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 958788093 1250 958786843 958786861
    0x507180501051f0c0b06131b020d020609101109130b03070504020f040302040902041b2d05120a15060309170c030726120402030d02070605040611031605160518 70
    0xc1e298079041f201481c0c8154800449010702040201c1201100c20510500350000703103401c044082510864005406201c3c61107008207100088105007040030981c1c14000c40a291940b254540d2640e002810401070515421950014411090110252546aa502c0742400207030b205141c848400400100310a00042c50268080c810340c07800030b030000a0720344c442d40e00f02d900234920210140c0802c080b40c800c0a443c0c04642d04030800aa034802d421988001d5038a000f6010b4091003c04c0700040391100f00141c45144254442071007248440303011084d080e5103200c00f0b07009040303141060341c3c40400c0c0810909040004011108559088402103140a8143d11610402d040164403005060520b40317910400f00003450140203030300c0c0480417110391130403d03104061621245036044402e5401030362041040c20f802c4026201100c0541c1481c00c009110810002c3c11407080003090300911071145141018007000080040f440741e2040c40c03140c40f294035082005010702801c241e04491441540000d4502e00d = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 958789343 1250 958788093 958788113
    0xc13061803050601030c14100c02130b062101080303010f051c0b0c0903100b1c050c10030507090b0403080904110c0a08180a031e0507180501051f0c 65
    0x5200c00d114200015200c1e82d0346800d2640a90044c0c03041d007035603d0103100c142c001c1040d601c06840d00300c070311800d07044841d20007400c0d00c038203034901070b01c03a080d184041d260f8100603421141f09058014900d07030380c44952034400400080c118105458402c0b220002048030360700002160b05a5030407511000c810307403410007000094991020005d461310318250032b84000450810300540110310100350151221080d90038107241c0740708020400304c2141402c3c403040071615100c6010200965800d408400a480b034200746107060718482c46160800382142c205c0e0000d1b03034164002c0c1c0c00340c510f640d500403885540e50070340d810310b0203170b404003620080041080b07510b0b51030294800080b2002120070315090101c03105815040c10b002990030f488081c4005108482142c040150842c0d14030304490384281705065440782c099048040307004d400356440381600c4c0780c02d1000c01c02004009003029240601103108036000040645000c1c4119401214002e00045d0858090b5140c81c100c400d090395004000e62071078440240e12 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 958790593 1250 958789343 958789367
    0x105011518180e15010326091f03140c04090e0d093c03060b150702271003050705040501080c010e011202040906030c0b0f031518041a0c1306 62
    0xa1013582c411403c410301c1c0e00c0d0098025070258114001001490b011804c0140d500030542c0c6a0200800c00c0d031800d90b07580006494804410045203040c541c28000503002041580c580410ac0800c0d1020040c1840d41000100180e0300d0042c014041c816074125030b140e907240b10740480030100c0d40003803082c0141e10741d07060071040130540e00c4020b42e50b50515408092002c4020300d001c0707200450169040c02440303580d0003624041601583d464928003689169025103015441c4000e125505504c4080380b10f00b1294110724072110040490850307810030840c10b40e0003c10718801140c09000e5140d001030f003468030344a884d04a50901f405001440500401190050035100580307040c481589841d504004907440644003600046100086c03040c2541854403440c0a06e038854460230004001110301c000364081565003241a0301010b178180111080004e100e16080741144a000165004100a001844c0304002650500040b4058192071b02000741c1d41d684940340da1101080700e42c4c8010050140300341140d64070 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 958791843 1250 958790593 958790621
    0x607031b020607050a05010e030c03040506220f0609080a02011b0212060c0d060f05060403030c06020c030304060b04150303020601140a080106060309030f03151202060c010501151818 80
    0x120200950002c0da1a400c07940d01941c081c2e000c1e083c0c5504000d400d105000040716414011070404000390070140c1d403840b0390301801e03010b80307800b04070b4070724507040041c03c920b04100600e280c4884c5515252044881c500c284030744800154441c500007058071b0042400d046854040e5a003030b00300040d030294150721034500c0d4801c98004e4810700c3e1400d0907840030701078903004140e4501026510000c541c15241503d04a03040341000340c4180302d0810050f070300e0a0460b0202d0b581030402c8000710a80e41841c40090060381c0300c00f440f5000020421007040180e0380a0107008008803020010f104c25840c13401301d15409400000c0259000074014003041c03031307000490303100e441001f40350000301034480e051182075840c15440140071036210103041c0109608545c0c04110328103645001c221000ca000700208601c0c0300c030f01c0f41502c00e40e0360040000940d200d51003121411451034000340500c0d6900c910000d00158140314040c0000c00c0311a1a5060305c100c0c005180844810381c160480313070308031040090024491400c8401e5 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 958793093 1250 958791843 958791887
    0x70f080714010614060f0706050c040305070b040510030b0a0e06040b12070503120304120c02060705030c070504050901020403200a12030806010327030e0f0301060e0402030d020c060703 81
    0x26680092212030101c15400800d0651520100b0480750b44101c0d2854030903007040c403a004048101070180e85645400400c00b26003501c40c00c9403008180b1075504080d085014410000c6401c0b07a42d40005c000f154401c0d1074403940b52042c02d008500301e80c00444419409901e9030b008105018629942c02d8104070020400601e0102600006454905803241808140c2240740100410f2805104000340543c40070f1815140d4507155039072a1107207040101d40c03c244844030012505548541041d10040c6510404503a503400d00d440c3c500b59198100e1003020b10a070309100001310081018003d403400c03280d21100528030040f01c038280076040039040140b030f50028180c1c2400208461000031a44015000303894441090601ca40010195003402ca000f0201c0114200511005050b00c1001041d4a80620741012144110341c0008d91a035081d5600d83c0c0e0541c200800400c00e4907484010702d01540c802c031300320303080c9511400c0242d80b06d0701c103505520f501c407d0a100b4900404e01400344041c4c03110320440580 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 958794343 1250 958793093 958793107
    0x120506180402011809060314280314030702031305012303180115181a0105130e16020708060708040b1008010c17060102060c0f1c050a090516050105070f08 68
    0x5000d244c1e0940c0a00e2505454080c01c0092140c8001e2a16000d820003000e401c00300c0350055081c400324862004803c0c0c1c10540089181858030a44400d100205e610203a55036a08100c0c01c02503507a01300c0000b03000c1c10f11a4410000e829030040d04a80428802080b10303461402d200a458501d9401c01050303242020308900301c0b11130548080c400c460401c020081454240303810181059008020606440c039034900d403080c900e0162082902c1e10034405401d28200d5514544030003c800f01c5142d90380300c0c0301c1c8050a00c06010107442c102440160390703085a422540880d03921211169030f282c05071200c1e80131a040102180110360484040c0341c1c08030b816004140b082d65104041421102c500e202c6c2800240c21058068165002e500c040c1d8100800744000d080508054009190714810036200184040000800240234182c22000414100c8110710402107071130304d482c1501c00f07800700c2c000c2120640071b040f0409814007001c00f0090141c5030181d48403030501400340c1d00c1003000c60540d0f02c152096581030100c0 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 958795593 1250 958794343 958794377
    0xa02011b141b010f020a021e0604170712020c1014030708060109121a06030a0b06060c0a05061e07090e07030911030307240e06060913080a0f12050618040201 69
    0x1301d10707220000d00594401146c0002424508480700b070b20328418080b1048072040c1800100c86400580105900425003002c1020b03504500c00c00714020203030000040a0981180c0100b84d0710110304054034601d05e01030364440d00311184d0554040341d03850b0300014004154520700c11a10700e40c1c0454103041c03042007a84c50781d48003195500000412074904805c003001076240d103107480c0d005070050760640c014004101d66070b4401201c1c807801040700d4001c48000c42e170707000003040400440d80c0300358010043e6000760402e001002c2e000c28140013a40c60560800010407880340c41000c1040071241100b107411010349840204602a08100034203071a440c42d01a200c50aa40c2d0603c000c0a44911840b0310005034101d080d500658011040072851941c3e140ca000101501000f2800e40e60001044a082c400c695583e20301d4500580c190b100900400c5000c00c551007019044048099035a0094031b07941c84100104803c2015940b0480301c040e00189003000c0e280710410300c0d030a641c1e0854814146820402c5028202e = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 958796843 1250 958795593 958795601
    0x50408100e10060602060703050703110a020601081225020109031e0201200717030c03120a0515130e1f0c091415030424020a02011b141b01 61
    0x1950661a40ea5211195001e0080080c1000301e035030064244031140c41c0c80c030080e443d000020318440505032208000f071400c600c80d6008083c25448800c1c01526401001002903131891700f4010900c084c8110204c02455816080c20b991466034603448029810441721482c94180050000407418001c100b80e0101c0040d10300d00302c1e414101c41680441c1080d6845000061862185e03420380c04140c1504020513280d034602043c0d0a0035121160700344180f1142010b4045c3c035600c5030030048142070201050450700144110380450154032200424003130f039210341880000c040a480d10031648500b0a10360b0803c0402580c101100240011090320803078030348400c1d013040d03880103d158061003e948615492100c2e42041c00c0c074028051848807c2001c0c03d900d40403407039a07208110303a0074a000c40440013400700044c0f0450084c030440c1e0148a0040c41c6e2a011810001c1c3d04945504800b40d401d106d03942c0400c1c80c05200c884e008051550b0303903551a10442d030b0380b19000d501103840100018947c85500c0e64040b03090203 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 958798093 1250 958796843 958796863
    0x1207050c160303080613060e1b0403060c0503010f1a03070f020a0f030f20120c030c0a08121311060d0b19140306091515040510090b0111100b01050408 66
    0xc5404052030038500308408121b0000009540310b03d0524140240803a0207401075200c0c11500c00007460b4140d00032602894002d0b030380010100c909094840410a90090245048031280780c1c80391300107903c80c82c503405811004083c041d25410180009048144541d080507100039441c01038501c0da04043e100c4000300c2842403416004198103411000c00241e101d02c2031981542d0300004102c2501440d258143c60b0050b0f00784d903090284002c10034108401080c0200ca5241d1180320488a80c41c00900e0720009a4201d4001d4546035001000020030104c540c3d02505c45c1c850f445640740c0381c0607411000f08010f40d00202e0700d040d426592801501c241c0d4507203050f5160541e255144041c1d0309450250035020400401003124004d40041c0c080c09620369000600a000303001800300000c042d5a50801300311301009414071550300c141418103020411051618000030b0f2480500f00b8440020034100540b0444c5039101c69011903403108114080c4640d90750b01080e10b0401c1450414a4650b65015a51801103010 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 958799343 1250 958798093 958798097
    0x1b19120c06020a02070302090a1505300706121b0c1b0305010203040507050d030503010b0d0f0903110601080111181309080d0b09160f140a090f09021207050c160303 72
    0x17140c03c0c41546044050306a00010341300341031000c5228000c42c0d1014605501c500c42c080c94001301ca142039110642c0c00d1551600c1182e4050740070f001c0c1c10887c0ba580da82c1511401d00841c04044481c642c12206c1e00848c1d03045460f61a10034030103c56164200c6860f07848030f5043d83d00d1302da09250340c180b00c12112642c1e4015030088001503120308082c05c0c11400e20304ca9504c2207109000907100303000002d41000a50b81101e071188652500da41c1a0700455010b40301070a28400e4007880c01c00d03040308050704410560303150703103403002181c40c0c13680c0300c2a4190032101020000042c0780e40038000070071003850325584070082e150040d10241c000392800d5881c000784c4000c101e00706c44404000c00e00d405a600c10303100300045981e08403129009814100c22a07034046903107006260800c041021400c21243c0540009800300d002c0e80381e559554440c1000c003c10b00e05107030085e48000e9920f403400203508206402994a0300f0f02c1d503e4682d01c16100e016066500b507100c141001c019005800061352808070514400300103500036 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 958800593 1250 958799343 958799353
    0xc06020307020c0f04090f0b040309031e03080703050f0a0f1e14071e081f06051c0908040608220605040308180a030e0303090607081b19120c06020a02 66
    0x140701081032101c0d20301c1300640603030f14207a51100414a058908000c25400482c00d0f2070351745a43c1012110400036402c00307004a08201d6046159914440301201244d000e42e490b50055203406808a040d95000e58812805060b401d0102c0d4102c6120b52000340d1114545400091060340000481080c1d003848450f00c8000b65101404c0540072402c0b074001e64400725a02c2d01030303410403015901d000e01a0410003510200b1940c9400101e401d03440521901e406561a0300e4200354030750350300000300668040e4141d00c6010303070b144810510001ca00c1c001c0445c003039880710b141800c19042002c22103a4000080c440c0e210050140340840071008919461610306008880c0842c0e80e18060402515107040a02001c0580504141d00d05803180c0103c0c50040c400c0c8c5c10b1600c0d003003e203e03003c0040d255009003180c040c1d01c008000303030940400c54101c000f800480e11424001d6240183c0303956407a00c5e22001d401c103401c0f401c00f050a5100145030000c40c0740c090419814641140010782e00d0b91300403608030188800150f402 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 958801843 1250 958800593 958800613
    0x705031e19060e0408031f050909060402030d0c0f020907090f030c0f050f060d050a0b060a0c1709090a0e03131503110f090f03030903191403190e010c0602030702 71
    0x11400b07810007401e02c8100360801401c00e5a07810460b480700500081c2c0c4821002190250072102c1180940104001009140c550800f0000301c2c0c2c0340c0c2c5042d10202d200f81710b805410f1418902600c085034010b90019402c0c101d4401640070b00500c000010080700c1000380715a80131034041030a5142101840c00f501e0002c02050502a403610b00010701d0708110b21406c101d50003115240d0b5400216600e0301c0c4c1111020805480d4041d1020240260718a9154465800b00366066250380c851056250f05024032441d00d400442074904030001e2151442d001d0f0010021000a040c120054110920041c801c4e011a80707021110901140140c019420407410108000c2c21802010b40c1405452300c00301c0900d070b0151031700c03100150320700c0540300d0528680d00850f480500c03902c450381d0030320658140d114043c0c03d031b4002c919015014041480903a0382142d070742e0a07a100040114800005440c410782c1004c0450860303140d0301105039500107010541e14100b00310800440005000d40c00a50302610781500200300c4007034 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 958803093 1250 958801843 958801891
    0x4090f060f02091c2f030105011d1f0e070c14010608030405010c080f1602120f073605010501090512071208040e090a0221060705031e 59
    0x7060001d240280b40140701041d03880c0d6035200580000c000380f06040020b0002490003031158003031809404140043c45000b05000452030001e03240400e41200200960f070b0702c0ba9054282e54215188040d040b18886000400c003c0180c0414841d00c1404410240c60681d04c581041240d24111080000aa188440582001241e03040714606c0c80c0e03075100a025050400780c4060740e902542c401d1504000c52120031406211802c0100e5a4001e0312000060740d4070b614103020354400c180c440080340603081d0b40380700003201030011803100d01034481c003000380c28064034001c003101580c510304006000c2e5450a03d2000014a003400d424140b01c241d128002c52158544400540039401c2c0e98400781c024801c0c0c4105020b8000045203030000e9039880d1900380071030b00c80c0d030420401901581d0003034846d5500d2040be001c031030740001600e104514400c5801c00c0c0c2900155125418008032442c000d0090352080005c0754900d80210099070380b020500d40700381d4170f200c503018000320340640581d007a1410300001c1c1c407107808400d = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 958804343 1250 958803093 958803101
    0x813020f15160c060809101d0a112704120909020d0608010506060906070b0c0c0706020f07330311071109060d051221070224090a060908070204090f06 66
    0x10031810800d0891510003c0503490340c0104886160a035502c81802600d91080c0c0c8c0814145600d40044419240d502e107000c407881e1a00502c1e5502c1a5040b0780080c1900c88103030794aa560324141540880d06440d81d80e1900800008090b401c000d0021410380400c042c41284041c014084600401140b000d2030804803500719000900414012482080a0407072611000111a54a03034401026032007a40c9049001115001300e201c01380c01c90003150000a6842d60001d40300000c5a4604240c421050703503a05000c0888441e945090f403040001414094040001240f510b0340348103078100031074000620183d800c03869000c01030440d160800030203100214104840d4803680f105056458501003026034941e150b442c403091642d01010038002030041003800c0c41600c0c000340302044c1c1420b5051800c1c912400fa440b1021410001c6902c2d12440c81618401c80303500e43c40380124120f60141102d006d0382c0d112000901561542075640b902d0412100d001030b2143e2152065140c01445159000d01c0180317804000d907 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 958805593 1250 958804343 958804349
    0x22d0906100c0305130b0310090c0c021f0c020a080d030b0301020a091a0903010f0c1b030912080c0303010b040305240708091f1b0813020f15160c 64
    0x41081209000c07229070840c07500707800da6805040403515484c03446040d00e00d010098104190f0405c1c04414002100059a0010103072680c40400307007c0081c400c038080f12000180c080182d4440500c400700320100015096040951001d89000050000710340c0119915080a07804035a4560007641c4000010f6450300c034501e41001c089000303518140c07488000500d4128140129880e00d59021701c1e00803410281c2c000c070b6104844c050300174049010b1114610005003120844040820200d4900a00075800c50031400b951541c0360300e500004608062001d62000c04c0020100c41d41902046405880b00c801c0010718001d0034803400065683c0d0031840d1084c2040003c62600c03440b106200051821034080300d00f1903901440501d010103071030b0750303400180345002c0f00703122540414022114948051042904518331404002901070b0b010000d80780c00b01d038440d000302c40920090207041c0280005180c0b4900c19070a0382001070070f00305035144180c00000680d01c8200c5d00808505882c418800300540f080c0c0d40001 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 958806843 1250 958805593 958805599
    0x14010308190513151209050c0108010e24030106050406120c0b03090a0609080d0f060302010806120c240408060403030b06040308032e0602070302030717030d09022d0906 74
    0x100100e1080742c5992500740e0150480801d0300000407801306114030b5005407504145541803107141254205240c440d200c50105500080d003600c00801c0040965201314080e031101003601d40e007500030040c103208005440d505151b041d526420005240d0342c1350300510000d0b085034200d00704056070f90324003d60001c20507801600c0c07003403042c400c0010010300403540d0910796070000400700c0e2540342880c0c80074140c0b150481c2050100d2500e9040d02c07c007940d59002805891007a00d502030a504c9410070091944200031003811281d000d10054030403801c0c00d518410403012400b0741c004803001000c4440615802c1500102c405034021030030401810b03418060785504403400e554991405048d5102d1859a200003000300071074080864a5041c84094a1101d078040e030000100070000940300d5800079211151440164032078440c500e00400e400d48210303466a00070411100541ca40720b40b01000c04043d10b480c5809a82c00461103c403c500b02400d0503080351602c000750700303044440d1810000c2000203607000d424980 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 958808093 1250 958806843 958806847
    0x706020d0f0501032a0306060b1b1204120203030d09080a021b0907030914010c020309031c0c0b0a0e37050303062b1a010611030f0a03140103081905 65
    0x8503803868110b0680c90b0341101d16141d0f980445c15521060082580000c0c42940f405100242030180c1d000076100b1481c0d814803402d0180c21803441d1990b1500152482c440b54801008104210f250002405c030100c1c0c4044c059a040240b000025821200310403025540080c1c001940c0100542c14403800008003031082c2ea406211028001048220300010508010302d0f580f000844181710b803071a580b490f04000200244110f00909400a4a0741c0003118118000d209480c41d900703910405d600074041d02c880541e500541040c1680f592001c1c0c50010300340482841c0d84104021054105210210b003449607280c0142000d00d4000c40e01105160586e0030441c00155039500b10009100801129044802115030a82503a01d00030b0702c0d00d4050421a030814501c03c03440141c010001c001c1002c00c0b20040b1605149800d0b81d84010641d03100386042d80900c0c02d90000c006016000b0b42800c06030807200b04030b180c00104c0a80c119020b4120319000e0f00180c441080108002c0c820003c001181c00c107504491030030074 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 958809343 1250 958808093 958808099
    0x7091d010b1206491a1315060626010b0307020c031f0b100504090f0b042a0e210307080a080f07030506010507060f0b060706020d0f0501 60
    0x40440c01040100740c50140c0c1e400c0454800e1313a4580c1c02180c1016042d0340c0031402d40940c118142680d90504010040900128480840c200180b95411425410141d51090b0002c8400300f107125503801080c3d071802001045014002ca0341c651034461003c00c002c00c0c0000d165081030300181089000d02008081101020a80c501015031180014111b5502012960b01d0361111202a0f082c605080400e54051149048001045610603181e040d402c80250081180c00100424008840c684a120001141082004100050241e80920000d0a88002c0010368440f110001400d48400d002a0380410b0000c50b05546a80c0c0c000d54401c03525035050034104c0c1500c03000004203a0700c41d1002c009000d00d000f180c2c01d01002c0542842114403107903012104541e108281080903202d1582941ea400044030841c0000341180e029100f080d005030416112207050180c2503031032902902c085907044d6902a144c0c62000c040d51115009400c066200c0c0e2070140e110001300003907001311000268001c0074141860010 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 958810593 1250 958809343 958809359
    0x6020c0304180c020c0f011b15021c0b030a0f0f020612010312030e0c0a030b270a06060506030c090603090715020d11061e04050115060c02030118080f091807091d01 72
    0xc960711041c2041103502c11401c504008110740c09403c27040031018000034508250084182c030400c800f980c40042000030b00d801109043d0758294024000300307054101d0380180302144520240c5078805100422a074a0b14105150f03200540c03c003a44129490780001013500c11950b0580942c490060001c00148034054a001c00918070f411544005014184e04c4404504000414580945070a50040801001c0b181c009900c6179500012002650303524580b20f808503c0f072074960122800744111181c598100890001088840e42c4062b21101e581c1c410505d00040000ca404407800007074500f60064403814180348d80c0604020303100805010981c2003401080015514400d80424448049001900c941e1f12460b00714010001240007000b09005040700041d0590700042c1181720300d1080d0002d010764084a11441c1064a00080041075144184a0401103445800c00307042032a9000b0700a1145114002d210b0041c042c05441c841d0000300c01c05000e010b05041c50300702da900079010080b030f106a58544184 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 958811843 1250 958810593 958810607
    0xa0c0804021c020d0c030f0218010609170309030f061b0306100e120a05031902010b090a0b04140109020403140d12021612020a110609010c06020c0304180c020c0f01 72
    0x800102c0040c0e580e004029500d4020307071406a00d620040d040b1059450b800c1c6100c04c041c030050100c3c4106290b6010800a040c20344106040741c400d5180c4070503603802e0008801980308085040d41551206000d045070300c0e501003124005102c90200508a5030820400b5460000c002d10a888485941041441020384510402c000081810729010016104400010702c030300300c415aa43c81307188030300090001482004401402600461800c4125000c442d0a080c2c0c281ea01a0001640c0442c405000403801c060b5030b001000442c03402403000500502180c20305200d5002170f040420141c0d40401d0030300c2005800603244601142500c02000550001c20000748a80d2404041c120740c0c0d9000b00306201441048a04824500e501510203082450901c0c5d000b5592a08007206403002c1061404850035424440c3c2104c801600607510701039406220384030f41c006075125156a10707240c0b0082000090f5a0384405100416503200714010402c0c106010340245050300130300c82c282c8104480104c05c0c4040ea00044 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 958812949 1106 958811843 958811869
    0x608060d03020607080604020d24050402040b0313020d02040e030c0d030c1b0c0806010303050c2811040603050f010b030f030a0f051c020a080a0c080402 67
    0x10800c00191540c150180160b0003c0011800d560b1090b004503a1045000e40098504961500c0f542d040361180124242000e086e07503928080c43c1c3c841c0c081c00c001001c0894056050500303080581442d40310103803212035404584e011680c119120300b0120390240c2e070014800c001480984501507202d51142280c0904c0780111440c0509041c024032a12607000c00343c0d500c06182c200c0c0c4000420030102511415a4600220b000004403080b00b001018060340c401d6070790580760034010344c1080ca4885580180c408101e04080d40705104410400000c04254000341e10b4040031800d031000c01d004091980001d000707400b0381c0300414a0990f05400c13000c81c15405a0844130303611114500c4944a00400d0203103000141d10725040c0040e6403290014285940a0552240060840710400310417640810f40c0b42c030101e41d414040142c035200a202d4800207040e1401c046030f0f14603141e80001c0084000035 = true := by decide +kernel

theorem cover : BRFrame.Cov 958633093 958812949 := by
  have h0 := BRFrame.cov_init 958633093
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958633093 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958633093 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958633093 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958633093 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958633093 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958633093 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958633093 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958633093 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958633093 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958633093 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958633093 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958633093 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958633093 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958633093 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958633093 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958633093 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958633093 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958633093 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958633093 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958633093 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958633093 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958633093 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958633093 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958633093 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958633093 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958633093 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958633093 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958633093 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958633093 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958633093 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958633093 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958633093 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958633093 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958633093 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958633093 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958633093 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958633093 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958633093 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958633093 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958633093 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958633093 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958633093 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958633093 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958633093 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958633093 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958633093 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958633093 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958633093 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958633093 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958633093 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958633093 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958633093 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958633093 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958633093 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958633093 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958633093 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958633093 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958633093 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958633093 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958633093 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958633093 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958633093 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958633093 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958633093 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958633093 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958633093 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958633093 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958633093 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958633093 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958633093 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958633093 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958633093 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958633093 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958633093 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958633093 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958633093 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958633093 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958633093 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958633093 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958633093 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958633093 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958633093 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958633093 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958633093 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958633093 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958633093 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958633093 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958633093 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958633093 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958633093 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958633093 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958633093 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958633093 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958633093 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958633093 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958633093 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958633093 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958633093 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958633093 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958633093 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958633093 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958633093 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958633093 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958633093 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958633093 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958633093 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958633093 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958633093 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958633093 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958633093 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958633093 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958633093 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958633093 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958633093 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958633093 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958633093 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958633093 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958633093 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958633093 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958633093 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958633093 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958633093 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958633093 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958633093 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958633093 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958633093 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958633093 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958633093 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958633093 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958633093 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958633093 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958633093 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958633093 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958633093 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958633093 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958633093 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958633093 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958633093 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958633093 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958633093 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958633093 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958633093 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958633093 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958633093 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 958633093 ≤ n) (h2 : n < 958812949) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
