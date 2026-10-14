-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3698
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T10:24:59.472422+00:00
-- url     : https://prove2.me/submissions/0f1f5103-0d61-419f-8950-f621f585b83c

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 664928057 ≤ n < 665107913 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 664929307 1250 664928057 664928059
    0xc021504080904381e0d0609150c0305060405041e02031908030402010f030504020306010909080c070303020708010c0e1c03090803041203080c0a080c0f310812090f150a03050402 78
    0x22815a49190b1030025125003054516a002c0c00040e0f140c5c41c1440710401000105641990780c130302102c4041401c0b0910316016590001c0d0000e401c40004c54003500316078000e001c05004614110400c80018065800d01103860142c4041445c0040b82d4400285040141c00b40700c144070815080f00070800400801a600441c0f01740c84007642d509070240100e0131100c08907070103541070788894010880003445da8004030116008019032464012184c07101441c1005070740c03044006900211003005584428411034800da01d071403030010901c42c0760b00000707042e550202410100b880302034101c5d241018080d003401d00042c241081520f031640c1d5104c41d0450178807070803e0181c0100d02c451001030070300c00124048a50642d020f84a03662035440b40c0f0f600003101d400c0f06c0200c40c0383d07a6007004021015401070901140d01c1800154942c010b2022000402c82c440540d8040d2159601c9105001c4098003000b0540b16085400e03600003c4003040c1200017040c401440e8a05400c1003800100c040450323038540c00030b41c0700e140 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 664930557 1250 664929307 664929401
    0x2205010c091e0b0d090203030c1605010c02060f0306030307121e030203091507111902150a0210020a0504030204090f0201030e061608040606030215030702010c021504080904 76
    0x15403008559000b8806107407120320704201d05814054100c841000c1c0c20f807004081000a40c1038841d50100b0b145900c810540e10301c0d03502000a0200810406038114094038003841d00070030a600f50b6000ca8100d000341070001200340c10100014000e9102042030790700b0b880d041404030740a40e9141e413020b004e8130040000c001c40d208080400417142402402181e02602c0c00c1c0b8000c01616140c4121007101e4240a0001410072038070044040780c0b080b00b08452003003005100403404c0030442c070b44100303c000d9225400c840d1000f0424801010150313004070781020aa00300040260380c0704006003049606224940000350302618001d61002440705841e07008050794400e0300c3c10409024120a5a40d4401c81116070054014005020b5a0713014855a55240c009114140201c0d50075240d0340050540a081c616800890034003104100c1c115070f090040c1041c06101e400a01040ca00c606c1c40389502480007840544804030001d10140a5161580000d03640d41544845100102030000d4290f42d24240e54000b00a000c = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 664931807 1250 664930557 664930559
    0x1030b0c030705040b07111207090501050d26070b3d06030902060708071a0f010f03020f03030d15090b06180405040830070e01090501082205010c09 65
    0x40394040c201d0740550050784030107080c40d04e4199649981d0744598030803108800404410703801038036450900f0106c600d154000c3c10484c0d052429440c1100c10590000c0e00c50548503640e41c02003900059060000500c1c0260010303002020040d503003603840380341c0e0000c0c0050303511020840b2000b59158051040001c01c480b601010b032002c501d5500c44112081c41c10030301c0c0c159040412280d4026444007110708e10182c04181407803210786882217141c00c9040241c40310240c50324650200d00342c42c454a6032029800092052039410941140d100b98440e01000f80910403444103070a0716501001500c2c0c001d58407090501c4180c0c0505c0040361000114410550302c103084c808c24480616080065821114442001d50207658494041001500010b4400d8401203410013880d80811110302060000c0d040700603c04400b1481c50a460342d011000804c050104140072041048036030f0f000601a048032000d28003100c00761942a010003500e802000c7c0100d0315040a04117104200f41034105000206550712450802 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 664933057 1250 664931807 664931821
    0x51b010306170d120603060216020a0b0304080904020a0c02040c030608330403090b0a0302030106080c09031911030a0302101406010801090f0213090b040e120702040518031201030b 79
    0x41c034142c502c00081c54100d250394195292041c003400141c0300358180042002541c94443c1d8007242d1100603a0355010003600c0e400340940c100198074a0082502c600c29510350700d0b1584800c1c50f280034040d8040d2281d0b03000602c64000620541000ea41503400510030098951110001b400a0110340305104107070040c0e982e04401c0c0308507070748241420b04c0106100030340c40f10445800d84682c0e00c020401c800303221300101c000c12400044405445080d0702030320010380d00d504045e00a8050000140f40c5100c0080400090440d900c0c040b52000c1c2503410864401610303045850048071043c0300300f0107550144545c169110605074009401c848c04800c0310020052000390407070403984e080702281c08901152510340100030682b0140e22a0b40000040700c8010b00345050710007035440b80010b99010110322500d40d1440031aa183c9032180f001c892400b003000340801c2d00e4150905c1c1c010300480b54064800e43e0b4503000120140d120001d076820100301c07401a82d5490900c0050400081021f00003036400c01c50070b40c0020305c0 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 664934307 1250 664933057 664933079
    0x50a0b03070905120d111c020d02070504112d031e0f06030d0f0c051005190b091807030203070801240803070209150406030c14010e150304050a051b010306 68
    0x44c0c409181c060403040705490700c144e03000c2d40c00000420042c861b0200c0411031040f17012000e041043c3c40c3d4007500c202100050300074a010304e5030700200c0c462484c20300f07120400c401035802c40301c844000d1000468621424221101c50500003240050148070020802c01d9800502c100700091400110084480d6104d403410341d40311030422070700b41d0740540c0302d8005040518080c0c510040703a114a403a09100d00803035a03941c5402c00f00207013510180702d503e450504c100c2c1c0b0207100c601c0000c0001984100041d884c1e0400203850090042c0460400001014240311644c41c24001d0b80065500501104c460942d62030b1018001c003108a0804546940c1030076001c02e2f404400c55640807030b4400e0000310f0521019030204896914040c080704800b2540030310b001007586582c041c102c01140289000301c6041d18000d400c502e551545811a41044141844c03481070f030751180a011406c00c0c4000d030480d100c1d900c61402918001c1103001c06840c61041d0a804502c0e1104a12400c4180384280d82c02e01800d40d4484403204 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 664935557 1250 664934307 664934329
    0x30a2f1b1e0901050103091407140109121520030108070e060a0608190f09030215010b0a05030a1a031218040207050d0f020c0a0f030501050c0403050d03020310050a0b03070905 77
    0x250240b41d81d40100882d40c0320383c21011100340994221080c154001584a1a0411680c01405c00fa06c050f100000c4642c0c002c081c20004022071048444440035a5441c041041c001c20512600980e98121031075116010b4010b09a0f41c00d4120145541d0796110110341d41c0c0c1e07801c42c0c0705900b6900d0304400019900d0602c03035545800c0b13480d592034581c8541c540800224004100506985c0816960381b4841c03420007660090344540390080c0c010741890740b40c0e032844443c8400141c1114001030b1003006072608c5240d020080301d5001949807800207000c16003004a501e80c00741d2181c21a0300d031240c813100c65206030f003900c01002c1b614002c000d600000326040052206902a480300034006801011500204c3c82c016048010041650300c1610b840e20403201c0010350341a490b030007121018001070303130510411000b4410680c200e11941d0741d80d0300345880c55480aa580e8158000d0a040540210104022030007039500785001d040300805010b0682c0d12211410941d41088407200001040301000040754141500c800d5 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 664936807 1250 664935557 664935559
    0x30203030f1909030e100f020c130f060e180a0308040f02032b02060a090f15020408011d011a0f0d0206090402030702030417030a2f1b1e 60
    0x10308541e1084160080020028001c14041d000c0c51140c1221640d64807614002a10a84416010001031018064280c10410f840c1c0d0510001001c2101d40640015482c5080002295680c0b0103502c081c036010040c10080b03061072125824a400840c4940100591a100d903030090b2907030403d40c4201407001d60f140d2050a014022500180110380801c00000350000c5990010342100c4100e0b001080846503000b0302c42440100518101200c4000d903410703c626504070486040500404640e600d80f06020190200d00804130315076003140e022412095016070b8020040d080080010704810000d00355003091111903801ca5500e011104410010f45211150809030042c044010084400080c8019005110340c140d90105050100302040c4c0e07958002184a1a00356000d16181ca203001d0601861041c4680c2641460b0018803008940b00e034483c244848091602c6200d04084c1034468401c0440440c07603030784852a01403a400b4107888580407041a16000041e1080c44082c510800c124003211461041703a = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 664938057 1250 664936807 664936813
    0x120201020f040b0d1d0c0a120510020c100911091609060e0103020418020c010605090f06041a2110180f02010219050109151109040c23031609030302 65
    0xc1c8080a94070f000b80003000070054002a881d17031014460348645501c0c203c5151942d00c80401c1c0303489800c1004c441001008219061002a50035a60b02c5441e00044105150382503804502d02c01c008000b00004c0001c0d014403c0304000000c01c0b4240380400c1800f0a446038000e84000001c42e50116031340c0070144955115585d0203064505040d01107416110001505041540034000400d40a0854801c100c0222a10b54010307901c1e682c0022450035542558003440c4079811b07403410007035401e003001400c603846002140c0000e401d83c081ca04460140c0c1207000000c0e040007203181411078084581c03510440c0d0441c840c00710b400304180f01da9846c056540083c071030b0100658a541400000b046500c581c020a841401980c04000c0c511070004105c9001c0641514141c1d10b42c0003000610414480f8104550303451282844411040c03201c6000078424a1001da01035940c505400d0350760b52107921240030320102c1e948000c04ca50b11800c225050b0360010340e0000c566090922600010324001c00401086903490340227 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 664939307 1250 664938057 664938059
    0x91b0b09150901170405070b16050c03030705060a020706090606120515010b090d11060307020307110105030106080c072a1d010f030312110f070302011503210c0c060c120201020f04 79
    0x10b104c130400781046805218048010130300d1070001010306014010a81c84106441031420001d00d40b50102d20360b140281c104000007808240040307001580000c85001c05a60741483d4648031000b0403000e4400381c1880e20b030820115111000c1e500c2501400d000b10200c90b07070f00e0660703161409020400c1c400e585a641c0d081020280c181454641480340502442841d11094149408182c041d4011550b034001038000140e44010030240d5001801600720a01e405421907041c0600580010703005404520000382c040b80100c200030990300c4940103892203400041c1c1c4803444aa440315440420b008003900260320f1100c4260307000420ba81d00303040700c0b60304803040e0200c0d1950f10242ca4100005d000d401c441526000340c02071440e140e200800140607180d0f10383d582e5000e0f80c14000e084807074400c1d001100c507044540410104202c1078a0640844416884c0034039a90307480d00640b4980403401e0020040080d07141c00103035494124a511013400d010707a00340b511541400c04124202d1240c0c40b00c00c0d000302d01c1404 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 664940557 1250 664939307 664939337
    0xb120a050123040207211106010609091a1905030118120e01020f0f060115180501030b0103090b0a0c14190f0905090901050a0c031509091b0b09150901 66
    0x3030300b6448010041d00040c034040050311080001c03141c500b218200240341c2c44840c0680c0c0c1c3c0c00382c4048040c0711010050485541490b100810880f03552141040f210b498801880b403945000e3304c07240d0f4404c8018480714400d25610500c10398045603109041c800d518095050034104a03503002c820840e80e02013241c0f001601c94040c1501c001c441003440c03a045102d603d040802201040110f41171152a240080402c0c0d8502a0400841c52500d549001002060058002035088842109040d43d03401d00340820400700303a1004800416052102405c101c0101050128448449e0300c0755003190102d58540c00b18402d49103000d00588120700c80f06815002620b84412510b1148050424510441c034007219480c0e0b072b43d800541040d205a44481e0181d40d2072081c401000b0b000d00c144c0000422070b08041c0b04a061000f0800314000304c9115125100707881d42c408500f0002584000c40440d11070040c40c03280c2c19240c459000083d08082c454a00609041d614010144080d80c1510340c5002c0503135419180e000b00507 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 664941807 1250 664940557 664940609
    0x90c05060f070b01080a230606090408090d032003040501080c0c03120903032e091805010c080406290d030309050106080c15070b0c030405070f0b120a0501 68
    0x1c000990241c0c0c0074403000e40010300d4114003900803c81383c0b000740300185842c1040f90344090120250141104108281c00d0390103000724050307910080031a0f00407160307520b60900101c644100d0300810b03070048200540c0420550844504200032030256041c0d032810a0903500140d0300c1c81240611400325010a001901000340c2d10000d0220302c103120203480c100b209032581000c00c2c6d00c0a403031a280301d82020042050f15a07200c8070280b000c07884030141100001c800c0c40d04100f4a00b85001e600b8101c0d860305206500ca201c82c121442c01d03558800000c101e9680408001448031200340d078100c43e12414404034000c007034000118606454100c1c005d00080c0c5e1070004c00c004e81c290100784100d06243d11b03000e0072008990b0a102d06402483c643d8050306c8404040c0d000c005a05c1d55040000810b420280304c19000700d41d40c11165030b030004a00740030542c0c03900d0f02e003002481d0103d03a0f803143c401082241804035095280340c001e096442000200c0b0251a1140d801e1901030703482c24041c00d60a0704942d0414141c0e80640 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 664943057 1250 664941807 664941817
    0x803030912180306011d09070b0307030b0f030303070201140109091203090f0c1401030b0319021012060b090a050d0b06092e060212160f0201030204210510090c0506 72
    0x74000c0450b1000003000440e040078002d130b01c0001d0800303019403100001e600d032440c21507200a1100280c00001c0c21b142651003640405000041056611039213100c0d5601c0e43c0040d038001a10050890307481c0e1408180084c040c040c903001e886078500d41800001042d0200340211000385a0080c0300041022030260210002d00d403401003911b61040b440390703800201c2c5202e031560002d4016401c0d910100030b80000054103171070442038498003a504c04e00000351301e11036000c440b010b030a40c1194100d101c038403080b50884054000652400b1510f1801600203103c44050300100075260060716085005540c5800304030646405280203804444507400041d000d103040d94149610a4400407441c22100301041c0c0311484041507690103c1c0d01c1224031081c803a40350100100314402446045d854a01a071003281004003c0030b001c0300034200309002c60380100f16030080d011b89002c0d0442c0504030315641c00a060562100d0a0786106440700c1c040d000f0190f03132220035401180301064006001505041c6010280041c55204c = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 664944307 1250 664943057 664943077
    0xf0a0915080a2f09070c05010b030a03080105210d0201060515030403080f220506060301062103120902060c0c010f02030c070512030d050106081b0403030c02091515130803030912 78
    0x90066003943e64202c5214017698403540c1da04c04000f010318021342102c40d00c10707120348a039200041a50009a00c441d4841c1581d105a4038461004070180207400901200d6460014a0080c414882e14185c3d05602c070000311801100c1341c00201001c0320300001d461009480180c005203c000024000c5680440c030710341c01107100d00251440068010b4000c50000c0b11003000c40e038071b410900034028949002d019a070040c1c9980a0300c070f2617245200c1c500d072081840301c000013030500918005d0442a14004e070700042074141c02404003503541c00d21a01d00d54035921700ba0740c001d004c1a50005400441ca10001c2640e00d081292030041c00e00d20304060030081d5041d40326079281345610040200b4009041d150207030500900305c64541c0861414281500000b6035886000e500d03a070001444208086a408100128180d030181c2d003c0c41c998035400c108403010803034a240b450b00a070009010b000aa0280d82c02412100c0c4481c006401c004e48580b002e98032440183c400603410b038428541c039400103c07070703800401c1a0b09c5 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 664945557 1250 664944307 664944383
    0xf152003042a030506010b0406021905190606030212060702101505062d130605030a140c0903100e12030601050d06091b03090507030305090f0a0915080a 67
    0x1100400045042d020b481c024000304202190800c20440101700c4140500312500c02c00d424507003040802036030703065443d002002a0707541c00003917014003c050200c1e02c040351003443e01c5043c041550404002030211440308070f0081e150381039180d14140002c80e02500941090740035158001c103e00c4840c1c0a40361403010036120b140b08410000d501c1c0d8603000100488a00f01080025410140c0c1501001c2441d110b64003081c954104000403841180c1180070080e40e009042031505c0b80c9896100758010b044000800740300701c1810082c80200d83d03103030b00a0004100100d04941c044d15240d000c0106403401042ca045c07181c0d02400d0815201c64203034029560156040c94140d0034240021100019203a06520916507640d40380e0700b101158841c130f01502c84002e02801d0a1200c1c01c00e5503142c0f940d03409070384805003c0000102d130b03020255032401c000200d138203801451100050345070070310040100b110381d849012191ba00344000130046400b1498034103480d04550040021646c0c400c1200310701d109842049070010b = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 664946807 1250 664945557 664945583
    0x1415010e0306090d090509040804030308070504080f070f05010e1305070e1e100309050d080c09040f0203060f1203120703021e03240d03110313030f15200304 69
    0x5101003052a22032007003d0001e00348001440c40c0a44803900e2038005500980c5900100000314041e03004450803a40c0c5498580c4980c3e4521000b12200e01981c2c103e080b2a00406021290303e490004500c002c3e50294108144003a6648006540d9440e07650241500041d001e50401c0380090194000c40d4130101c00d01300404020b40b02d60010300702d90281403d140c14000540040c0b10f82d81480002c51114507110b050401c008440c6480d89540c54608806420400c9250030000350080001020384800d684040c1c01440820032000111006e0f4200b154903030701a9082c0a00184e082c034100a942095025042c003842c40c00034180d06030030714040014149414503800300800042640d040500c4040816206405500c03030030150030014405d01c2203000f010020404820303044103030351078900040c0c0f140da00d418008088403104d203d0601754041c01115002c483c0312490004144140c1c2148903103443e2007010781c4c202c2c80680d00c660008554041c115100030724480042c40d00c1980c48140195040343c0640340c0700e1040 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 664948057 1250 664946807 664946809
    0xb040605280e0c120c0906090d0314030106020f100b0d080d0b0303030f0a0c170106180819050f060f060f040209040e0d0906030b0303070305071401020c03070c091415010e 75
    0x1c1c0e00d00760f8000c0d00b1044009001410241a0350f001500300c604851050302c3c019625000861a00034250b20350302c00c500405500301018050941d094044c00312400664496a65000182d1140c0040c04044d070a4003d541c450050590309218503101a40020a0101c5200c46526181d1843c0c104014080c130455480c40350034038a42e41080954400d05915100b861a46828003202090b24540c0c540ca41c280302c0550f65103400300000c0e0f02c0c0709040d45c07694a480410340810340c0303520300500b855500042c100d00070f1240220100401d5588080e96500880403506c01c4040303403c565981e12411074145040303202800118074145024200400448001040507040a400100240c1103541603090108160b00011441481f41e41008007000100b841d070900300008650300d00803030b44912505c600107040150019640c402c0002400500c2095542c9000864503075841e1162603a4a5001210664800100c5100020203507200c0c0038003113005c3c0c4046c103c8401a110b1080c0d01c1c4000701c034a50124144544e44041040da = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 664949307 1250 664948057 664948079
    0x20010801120b090a1e060605042d090f06060e0c070b010902070804030b07020c04050a020a05030f0a02040f030804090f06050d06150b1324170601021507030e010b04060528 75
    0x44101c45e5000c080c0040074a0088212240c65212600890404603011001d070b40c00c200102898040b002800020103491942d50004d15200e50f00402e0b41d400c0783d1200741030101c99440a02640c0001c0c15041d440c0e240d07294012400d0003240c5000740000c02c040018487d04020b50040c1180c5842511010300705038076075844807201d40003200d400006a10100781c1700c10500d002d0051f42d4004030910380441c94207408040051451000402c1248107280020200b0303d40001d03981100c00a280f66074028030700c5604d034500310358903510920548031a10b0812059440d010080c0c07156000311100145407041c0c0c1496030307603840050100315054161040000c0030003e00c80550900401c50280703009042240d91f8200a8505c0c440e20b50b002e83c017150740c102248515102c5030410102d030101c0c171484400b50038941d207820040749405144c40417200400c11420a00616a07015084505482d038208000c0c451a1000410311003103031614890650b0103401d83c0003404248681c202c5548501090059040b00c2e15281d126102c2 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 664950557 1250 664949307 664949333
    0x613170a050c0706030e0a0611070501050f0f1e041515090207150c3204061205150609040f14040309060f020a0809060901120920010801120b090a 64
    0x30100d0000078082410880078000b01d4003815090038108042c01d041c5030381507030b1501484002400a0f40c0c0e4080c2e41c050102c450180d0354240d51050080c031541c40c0481328030030904000c1d104403105400e80d60106500d90085203042d4401601c1c80c425681c20390301c0d904c42d0306180c8003a80400310030951303911211b00149000080e01c40070f05032203031016039140c0c46441c0c80c0c03000e14514007a00803528602140380f2031142c1d0180003942e90344a648180008004074984160803a0b4112590014400c40000c000680315004802c141000140a000b0410380e42c800944c440003003403010040c0e41c01003041043e800d0519080e80805200d23003154500041441c0c004030090f2031a00305030307010f6021400b0000204056503202c0500e0001042e50b201500c0f00f00d90540ea40742c4140500310039184074540203e40c250a5034450704484150b40d010703010520003c0c116040580403c90701590784581d034484042004100d50090480d141200e000c50005682c64406807030300001000c010306000a14080c1ca4403a03000301d079100501c1c2c0 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 664951807 1250 664950557 664950577
    0x271501051605011b05040308030a050c1c14130b011806121a071706060901030b060a0c12020304080c09040c08060c04080c01030c0c0201030b150f0d0c020f061317 71
    0x50030803203410b1800006150500301138100302d010442480005c22250669070045680070002c40d054403000031401190089611030451000c42c1200c40b08900c00304d07004402d421900c4078800d807045d00ca2503c00c0e42c001145c40340103070014040600401030300c40c03000c1d01c11444c030203041c0300083e42136200c001e44100000d03048001d44031b200d21100800d501201510440c1d4108007181080c070701021816415032085200200702c02e208a03808100d42c07449034040d4000014541e4000e250380e9072114400fa000d08401004001500c1c0300d50030358203032418a800001101d055604a000030603c00c0d07502401c000880d04003d1048400c881c0e80880011241001c20049006040b5082082c0d1603034103204100b0724011941c020941013504246140120380d411030b08400a19030280703008a1001c00c0c1c01c1c007103001a1450900c00c80700710307000079901c02404003000240801c9141d0030001c1c0585510b41000701da95a8641075082e103140c000801203210340d0404440d00441c0340c80b1f140c40c800c003841d0703044204405412500c009 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 664953057 1250 664951807 664951811
    0x1818090203010c1112032a0a090b0901140706020c0d120509071404020c070f09020c0115050603180703060c090806061f23040801060527150105160501 66
    0x4085103800c0c01099103c0d180ca16100c1904000e0284039036403559482014100c8200005c00b0030068410f04526840200c0d1a50f2002a0054a0880c080707030780d8040319400002030f00712000030911100c08002c0301c08205052351424030261215501b082aa4041030086525507401c000881d1400010b0041840e0941d00b6290104041c045d00c10f030b0340c01d8400c002c000d11410b03003000e0000c2c031409081c1d48208040c901c0035240140c8a084080081d840e14a803500810840c01d0203035070026442d0f18503001811000e000b00000d0001455420080342800740c5401070984c1300c101440043c012040f100c0c03a81845074020421200e403199a41c8414040390102440e41000a4800200707011a4070100079580e0026415200e41c25806000814020411840c841820400c00c8487c24185020110300005121440c0d20210550b2540c0d0b664030b443c001c0800340300f441d01841c2e805071000f03030070025034004051045603184429190790702c01240e05000308268040c5414031800303210300f990551074108504002440b480c00 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 664954307 1250 664953057 664953071
    0x80919030c0906030b2203120b150a4112071706031c0503281b02060c070602070204020f0d090606080c01020709150305100b1e010c02011818 62
    0x220500d0f9600801d06d0110300300541d4040c03000b0056001c8480d40307641500e081441c0c1c8130381c059161302070078420b105294070588041d0340e610211544d000a0400000c2e6484c1d5000074002c007006890300100c04c4050b6010606d007280e40110400c0112261201c0c200d0f142c0381c1e14900382208228520035030b000e81d5910300080711a0803600454244454458020350100c00410040503488070700095403050696400c20030001102085668001c03461540c9000c065200e07020561700f445400d06c0042182c030b02c02c4035192840007101d003c42d0380041210ba0251170f005466600d0700030303983c8030b101c06548241c030200e8002d0780c00c01c20421082c1d0500050100d003070726858041030405040c1442c0023500c009270001c448a4102c440d510061340c1e0009103180407108551800300d5481c1c03c03d15161001d030381c5a80050500d00800e40c15200c849080e0380068030340001210841402e500a26a40d44580d940003041400b00302c1e038600c00c001540c0648001c070000034a00c503611544c15144c490b00e03100f1682c2e0420314007000b40c80d40300c = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 664955557 1250 664954307 664954313
    0x1201020c15190902060a120b10050c010513080a180b0304060b0109092d0b060c0a0318050a091a060a0e011d060f18030a0c080d0903080919030c090603 66
    0x1241412081075160a000104168000841714844c640010f01441154040c10741e2103509604000000f25000b40040c1440303d10719006055580a0070001080f54a0320b03000403c0c200100340d84204803034001855030306040300c0b0242911701c40300700c80002030403282030b100010340940b46900440c8a14899100418600c0041e000900708190680103902d0060500200380343c01c89910304851300070072205d80c0702100c1d028a0340801000700802899242c0000300003404d2280030000281c0409518460382d200500321000030005c506951450207450340c030402c80c40e400c00114069801c03800b07403003198501d840d00500350540080c001d0f0748009030f104041001803036020541c1d81c0001055000c02c4020001e044507052400c00a0410312600700e8003010305030b01040050403c024141c02c040c02c141e01600300d522606c02428130307061a480d144a10506032040c841d00032122445a4a11406c50380e01051441c1040c4042d0100000404801c4641c807450018601c0040440c55404c1000d00801202c41d00250840c1182 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 664956807 1250 664955557 664955581
    0x100f060e010305070906230d06170706090503150414060a05010609211e150b1c20060c060a0b01030b010f0903201201060527061201020c15 61
    0x51466042c05000341041146c0745c6c0001298010143c614074500c400007000011007214010360790f5900c0154603040c00815081140140601092080c0e000c0310b411550300c0408070f525669600071a078150700b000e032410211140710203d264205108607409507446540c1d100e001c0c030b4110100d508060aa8035080100805034100d040500a03041552003480c041000050011280c9442700380200400c240c4010141141650702c025001564803100e2070703c194900c1c03c101000340003403c0c06280310381c60300703c0f0740105148600481d910295012003a8029003101c8155240d000b920b00440c540c0001c010080200c80002c1071017001d11503098144006a0850313104001012106046540b5041c00b65502107807407400d402c04101000c5a600c10303110342503051902c04e070b411148190b141e01604000c209046007a00101074100d607060710f4040d603031018201400b9009148000b502c0c0800070392079488201058980c10699000f00072031601ca00054a842901964140ba10245030b10240307007010b00c8024080544203035 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 664958057 1250 664956807 664956811
    0x20d182111030106030f080c01320c04030f11030c030f01050f0c0a08010e0a0b060703050c12091302030603011107030c0302121317011b090e0606030907030209100f060e010305 77
    0x280c00030005682180d61b0511324041c02d0381c0150182e20042040c005019094002046a040940035a110075101d901c544c0300200f5220103101a030604180050010000c1e207059130101e9412440b901844190354544a00d2801c02d090310716014060044170040342c1c3c40030000808035500d0b64000280600e015542c008800078060a4041900c00810591078a60b500680c00380c1520407804902c549512141401c0740280040c98102d900900c01082c208103168100707010341a18070038102558001001e20702c8590a030f1091201e540d6000729400d051910048040c1e002d10f0344020003900010b100500010b00c1c0740540c10403481100003840032103036202015414040003d2801410325481d041440b000720b0001807050900400050650010307042d407084000f50402614135090342c1c1e528460081700f05005100c2a04d50040c0d50b03031054200042004d50407c90110f07403181e441d00300940380850550307080001c072003800307043c08402092042d03011910a241091010040c200303606e605114002d0304e0b0003d0161100 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 664959307 1250 664958057 664958059
    0x705060703050919030507060c050d02010c1b0204060306020708091c0c03060905160303200f03040509130b190c0206040506041b030b0f09010b030607020d182111 71
    0x1030000100003030b000003c0c0c41c200b22003118111050042078035015940364a690019041d8864038070b001a040703800103a400c1700d0070700880a40d82c0810302c07410141e003038412070524880010b01d240c41c0000700040c00800821602e1000b400801c41d10f9507519044280d0f0003002042e41c2e500c4000941780410b28010344102881e424424440018101544510340390304114400030f441c840e01c5601410810500b0320407001c01d1030b0584801d29000d6180c0c14010f00815420000c03000032001c5010110070322400040110b100c001440c02945450b04260611242180103070040640040c10a5058005042d54052520800108480c4001400d42e940140161810002c80310159080401400007085000c6002c07548603420a0b09481d0f054445140c21100c94507680c030180c0074413a624240264640041e0059014813408002401051460b004064840e8002e8030b0700400f580c8030700c00150304140103540201e003034025504e018000b00c0d5507590003004005c2c4160a4201089800b8442040051007582c40c049124 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 664960557 1250 664959307 664959319
    0xf03090a30080613201b071e0b030402280501030e16140f03030415080f16030c0e030d09030b0a05190b0a030f030203071505071b02030708070b0a02010f1b3e0705 71
    0x3e44d1b8209084004009d00a904034014004005400c0d0b40381d0707050b11045103088007c001c010003001c4415040c0f0318424000c1500003818020480005500095400c510307602680e04240c110707150058200c000201083c1d21a0030001d90340c030184850b9030074800340004000c619840800c80c485400001d1600400818001c2030201403818461b1051107000c004208100b00e04002808116001c020b590600110314800c0c0d162250b00f4500c1c0f115940495640c007140e100301ca1040e8151a655111002da0b80100d501d00c100d41d802902c17500c0703030b01d40c280c2201e200e105018001c900c10649075114003c41440b02c41d4141e01607440040c07500c0407c40c90019041070410850420003c0b030601080040018101380d00f400f074110010b0100100b9507800303011100c02000c21804448910b9540c5042d912103401102600f40903510b05a48003007804241e010b20108204900400302201907003e2090f1341d88802c0d0021181d5550030a010070814075890100390600c100a1070100202145404015140150940003d4010307a = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 664961807 1250 664960557 664960589
    0x102010219030f0b041805010b06030c03070f050403020604090203180a050d03090804091404050d0201020901021c033309060305030f03090a30080613201b07 69
    0x7400e100c26403481e0011440c000c103404070341c031040c3c01c007618410510300d034000c2c039001d00090720b04400901e500c601c500c00c0c1c00078092605450300f00190b5010480c0e04001000b0b00b040091100b612415020042308010f0901504081c6c490300445d0843d0496084a15107607400000d00c0351050741b0719101d185070541da00040000c2a82540c0d1340e42c46404a0000205064840300000104000711050340c0142c55043c0d810414003011018503070410405541c02c1d00c4030b0098007100b69180b4811f008403002e10704107800a0400b214003071043c0198010300c1c0c59060400d60703101d860158604400b00b07520948210440c400300c401d00020210156490103034000d44402c0c0c81c20f01d0070000204040155581c2b0201140c0c102c0d160382c0c0d07915a407030a10001980c01001c4054074168604080844058000c80c03421094014400002c1c040d010b60310320030107079900755004da0301c9054481c0040d01070304071510150000d460810b030f21400f41d004420f1500480b503e100702d661344003025041381c9010441d2030300804400791904514 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 664963057 1250 664961807 664961827
    0x3061c06050c1e0313080913020f04030204060f0b03070e01050d0c02010605310504030903120206150411071205041511150601051c09080d05180105011a090a0b0a020f01060501020102 80
    0x2401001004001d208040307030b20920740c3c8d2070b600c0e19045403c40708025513403082c81c02c1c0c242d40190b1007404128820340c038000000c201d56010f00d1060040d1244280303101d28680364180306031000d99180ca400307410892f040050302c4040e60140140070b1150029000840d07407900341410031001c0702100c004c2000f03052501158520511240381200c274080101d03c400138054985050480703115945130800b0f001100d03004441005694005a40c91141c0502c030b080305006602e940c01c000c280c401500382c40400c4074062142c04042802c004030290116020b0418900e4103944040300440300d07540340c0c0303084041800c000044690b00018031814260000303410821660346802c0c1c0020b0103600580d04c400c9014600e01511001d24089540140000744d08844807645801c99200c94130003806040341c0d4000d0010900520006c44181405036a05a40c0e0040006280c00c0c0b101000071065040082d5103680403002080006849040c0c030000e05031140c8a034042c2c00080c004481280c02c0d10035076840503046a104014075119 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 664964307 1250 664963057 664963081
    0x30201051b04030f0203070518100902090907050d0f05100e0901020304050a2306010905010302030d08010f05150f070b0609151815030d02030a0201060f0b03061c06050c1e03 76
    0x65a13440f413000c0c65035004e40c0c00030074070307009068000a4111003c04200110b8028204841d8490710004c4084154140c8840c10201031b030144030001030308100c031503021034803450080c0d02070072001d82c0b03a000000342d40182d9200e8006803101a81c012005118202c41407016040281e16250300c51b086034001d41c90b5041c240d680350340d034501922014000044a4568008000000b6032055507150b100080352071a5131250719010050500384401c078864444c0c4410640c566006171141412103d4a00440c0a8145000b081c010803522400141c031020f141044090403200c8100040c0111034058408101d843c0303400c1080c00500301000c0d12905880601c0c5050884030b59410140301c5da881072031080c646060315942a4030030701e1a05802d0860749070150460140382c2c0c1e035000014100940040d8028488240e035425144e04e040b800e8082c9403c1c030301c400c000054040c180304c02403e04182581c0d011084c81c0e9815181e0900311281954048503947c80045d0000070000c1c0c0d01404c0c001d0400203d1400c1c0745013440a00016 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 664965557 1250 664964307 664964309
    0x10020301050a050f011806080114032e090f05030702011419050a170910052809050307172212140f25080127050304050a030f030201051b04 61
    0x4070904c240c0c0e8020945034400c030625102045c500507444510740c0c4484014119030800d0017402202c1d0a0100040c031f05150009400241e0809149400e52400300e1200c40c0010a500c0c51101c82c0280d20b4442c16000101e1b030004454031030b4003643c00746403140464030006008004a003040c46124200b40821006090451600c01d08184541041643c80001e41d00507100010000d0203042842003007820000174a1001c5241030003e581c0b12020001d03580e07005105000d0030070003076000702c4203030007800310188000181c2d00402d403150085007180d051a180f55034492a5801d0041581558240401c0c0040ca0300e4030901002c0703500b51410403d00849042c222420842c0000f407001801001c0c42110301824520140103450203868032005440740706011202410300204450343c02c0301700002c0d4588c0019161010b00c00c00c00c40c1c41d04018141c95040c0d0715007404180d20054401903526003c10040012030340c3d6010f0207180103511032803904500400344c0c2800f030708507a4024040caa583d40c20040405041541c18210b43c = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 664966807 1250 664965557 664965559
    0x60305030d0b011803030e01080c0a0e06030a060b03010605070c05010302040e07030f20070201020f07050609011d2706090103080f0703050405030f0102190e030d0818010f0b0310020301050a05 84
    0x707000c0c4a1840100c131016484203244e0912031141d90b0120505500c038071203000021083c0c036444440e496010a0046510440c00003030f000642c0d00d40d20407942c0c50010011078000d01c2014002c1001500c8070300b0012a5131083e40302034049000000c10200300070003070000e1001082c0074201141418500326804e0041c14006250b84101559480c42001210460b8080281d459040c1c800319010300302c2d80c12920541d804240164054410f0300f0400120b03060014418041d510042c1031182001628801529840b1a8520351606240280d00302c00b065220009681c60582002d04040000050321003464200d09000d043d05029003115801840450300c1c4070101d4120b02d030384200d0581d4801a60400f2101c034000c035040150325000e08007003a04d01c6001500a171480740615071a000c020301441d1400c3c2c400b2121520b0440c1c05401240c8002c40c598003c400c8981e0162840c40407010420b041402182140c1e460b03a041e0002c1c0b691240560640d0408101108030410000c508507e1541403000188020716144540d07 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 664968057 1250 664966807 664966811
    0x1060b0301180e0a15062903220b0105040c022a03010207060204170d02030424110a030815010e150307031503080729060d110307031a010504060305030d 67
    0x21102c0d051207a008500c0c03810303010140c65840d4841d01c0c010000000e44000641e01ca82800c00c0400d40002d400b1404c0d8116600303240618201050585221040c0c1006000701c104007860401d0f441c0380d00411441800f0580300d19040d054035810001000100c507a00e05c0b504003158459010481d481d840200001d46c0304013040940188030643ca4002400f911070f808000b4221030001c940064040104c01200c1c0002116405648160b00c1044089940340568850080050f50640486808075018008041e0761442071500d000c90700500d061003860614006001c40015911008100c2c40040c4003668143c5084246041d060346105880014503111134a49625100c280c0000410b00c540d00075800503c0e080010445014172035903d007041038064115079001d44540d19002511603409107482c0c05c40100644c01d030754520517521b80000b40058207082e15411182c055544111403172558080052000a511600b5070060f41084418816440300042c3e0000d030095081c10414000160044242c80300c1042034400 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 664969307 1250 664968057 664968089
    0x1204120b090709020f090a1a180d08030f061e21030d0606020a15090f0605070c140c120705030607050a050d02040609060e090c0d1109030f010e0f01060b0301 69
    0x703050400c00141e00038102c0314400100c0a0103021900081d110640080301c00e51003050756240c8075034044202140000b9484c108004d000d5280341c07031201d2812001c0e00a85924089115a50340d0300d004d40c4260750740c0c108400424100b00d458a040740101802d40c51507a44c24181c441228045905c54200c40b5444080100c1c09030a800001020802d4421012901400307003c0540d640130080d40318880316006469012855000c0901c208450080343e2a55074891400103048a50351100f000509000d0122402c1086000c5040302064000030106901001c8802801c0440985010410384042c082490407140e0880c00003044107540106a0960100321420701075503500c180c10003121103100b84041c24142c10300c04540441d055502021090a603140d40e00d800065207013141c10854454000c560a50700031000b000700c40c01c4000d072078102407201d80c0140940c5061484060000e401d2800d400303c040996956149801c1104c0010414840c01244940081050794105500310030107110500504a1103900c402c0 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 664970557 1250 664969307 664969321
    0x4030c0231020d1b050c07091a0d2f100201050105100e1503010308030a18052e0e031218071a040504020c07052803020f01180e091204120b 61
    0x1c013042405940c4904802d50108420140c0103070400030030500507104403500810840c04521500214144a9038100d00d00e40b0004d0400c00c2e003246160044840c9402203008a103d510900400818510580d50301c08034003903c201481f0900702d4070300206085a0620004100980354011408400c50840c03400800b21351813100418040900c080c1c8804901100100002c144031401000d90f00448030204240451701ca4410144696a081f410260480c0c000b14051015030744403109a407900b022540074446107140b05020242216480804803030203800000d54121482045815103034891040c12600805140c040c100e02d54492403801140d11a003170124101110750544001d0350000c000041040d5520b0032001030715034407250325100301030080d812140c0c1043c00a405c000303485d05c41880846460781d506d14503000c101c0540d8182005c0b40c180040c0045010012807503913201d00181c1900f103030b0001d807070811024041c541a6091000300a1485c144000e0213100e40340000c02c4e83ca5a0400000700c41e58564030 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 664971807 1250 664970557 664970561
    0x109020f0906040b100e190b0904050403120911040e01020a0819060302130e010e03091008100b04030f1203051b030a0f0c030c0e100917031204030c0231020d 69
    0x800580d4030903146a461105184d000c10f8014a006c1c0c150b5441e0983c0b144001945856400e6010f0502c2e4031005100c040980c1c00d19070b104030ba0160080c40d140b81e40300d005c00c1e1300004507200c00c1c0c03050703c90041c0215070070f0303050500e401844014982e50340214604040d40400510130312001c0d090710740f006515403c05130000b2072a00944041c5800801220300c2d0000d01400c20001e28030062445150350805400eaa010803000c000e56100c05000340203507042d0114180c04a814600051a469881101c2003004c00d07887c3c03904000d0000f841c800c90709001038030614140000600b03c000c0c600c40805081900b001208040e1480300c1d441c240119441e19200d0b19440590f10103481440e6192140a1070000f00300403165240c1c020100050131600c0c1c9240049180003448200d03e144000da41c04912181c404000c4103c410988040c4005644292820091034114504041034103a40607400560051581029860803c04040c880c034400070b1180c0381f03461101003440042d50b1907100d00c92602da0124190229480d41c1d = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 664973057 1250 664971807 664971821
    0xb0a0c08070c091d060a05010501020d0c03180608070809030f0405060702130905010606091706010608090a0803280c0c0303110903030d050f061c021306080607030c110109020f090604 80
    0x1c44810b00001c4c890054031464480903000000d880d1041d003010070622009480b0b198161041070b40070b0050050f40a20a544294107a07034101c1c00c11007410751051404030510300380000b5150954410b801070918810090000c50042c016400d560401c01600e03100c412413104036000c584042d507042e40c5030b03400f0b4000030380106404030b0800f40070b60030280e408081110642c4441e0958150b9165100510745420320600d21024000500d0170903441180148041e5000744e40c280d50010381d0313008480041c0020b0303803400b0403900259040510101a051030300c18803640310140159507440c0b100308000c4140c2181005204070003c11016080c503a607080c00c1000c800155084078016a4080c040325940c08140198078010101140c103c40e03801414004148140340140c01c5504000040c0181c800118a41e000c208588041c05203000c2e05e0380d901c01000801501c1406030902c9904192400194488042c01c0a010f92110080c81401030349003001401c010f944024000d10300250030787e10080e080d640d0070042001003000c = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 664974307 1250 664973057 664973069
    0x1020f160306050403110d030c2a02040209031207140706050c150601020c040c080a14010f060516020418051615050c030d05100618031106090d0210180b0a0c08070c 72
    0x3800491f00310303040e0907802003548006507a80d01114030b001d00c2086803800454003001d03d0040c1d02c21800402610389030f0044e0001030320003000d459460b40805510482c6501c4040111178a00d51601c0e5580864001c1c4032541c020030050510a180a0b120082151a9550198014607101804002c030320030364420070043d03462402c0035008002c080d05a01e4040c103990811517102c0c060354106295103249000d040c9540c2e0407178450b03401c003050141c02d0041c20f42c1c070741d0080401c21190307800109248015a44601400345a0035041c0c00303400e035281042c10428107100c2a40e400c4031440c140c82d401080b08150b0003881079211107082c070303103d500c1e8408200e100d030031440740402c41d6255a082c442070100300303105440c5100886003241c4410411100c03002400280020b1403002038440044010451081c1c14032000800c5020002000b0307513512002035001070105850300305032100207014402c0d003030381e51142600c1080240480a80250401b03260f05802440c40001c0740c00202009800700f807180c02c0101e0030b82200c0217428 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 664975557 1250 664974307 664974313
    0x604090c0b03090a0b180304060c0503161103010c080c1b160605090108100602120d020c0703060c033b03070605160e1e060315030609030901020f16030605040311 71
    0x425094a5070b40d04c482050559001c504000415092502100400a00c090341006541020f03c1d201058845644100e070980f2207000401154612040e030307202e51a54180709540f210741c0d4a420005160031520003884c1002442120824006541d000700c041da8030000150300d24140540b20303100081d003410002c00d0b06144012800d040400c229030050042c090300c20003030b6540742480c1e8136503143e01c16039006032007408056040046089003015041000f400750305070f03c040252500303010a11013440c010803640180e0710561303554020400746030f146c09010010f0360030b6006006400407464502d03001298009038099084442c400c0016015000e00030364481581204080090345040c81d603100d94403a0400900001903054400400300d464440c9140070480c0e4141c08c040c46000e450801d124080d44082d00075105601300d40d04515840d542040700307512400f2004099a1a86100d1001914009140403166055000102240302ca98064100c00341141d8014201041c0754a440c02c050340c02034004600401c0c940 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 664976807 1250 664975557 664975561
    0x2060d0e0a050601080c0603040312111603030605190305070509071803030c02030d0507081602011101090804050a08010903021911100e13020f0d11041e1505120604090c0b03 76
    0x10001080e103074122a0b41e5401c0e6050030006c681040042c0c4000c84000380441c40c42c4c5080e40000400b030b03002a032061107201c42140b600d000c081445849400c070807001c0300000d480e02800e110780d007031201d907070305104442d003100b03903140d43c02d554a042c1c50f00460f00603107018006520009443c0361050103410302d503035400c3c000450074649070b09005020b07204520b02680240f00c2d0154994402d803190003140c401e9604034a1041c108284a81c03808200c10030080b06070304120341c5068500308003400384112640540b107204041d0703035140303441d041c0020210310761300c917113904d07490007400c0008290040348081000864a44c0c020042c0303111f141c5400441c49040200303410020108403185800c4e00b1501200049174101d40074886046001d01e43d1059118000c4a01880b050a0107070086451460300b10000d0310703007100c24503824541c488503146180e10000c00b02804d2319440000410620069010320151400ba61034042e142210045a00c001400c02400071801503940e241070ba800e000c1c1580d0403002800442000f55924 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 664978057 1250 664976807 664976813
    0x30e030711181608131e11030f010f0b042a091806030204050a0e070611031b03030718050102070e0402062a0c041401030615090e070f060c0b0402060d0e0a 68
    0x40f200102d0074a01143c92080401c1c905440c0ea554110415848074130500d8100f134030b945a0400e1081808212150301444241111540e800d001c850b00c550424400041d0398003ca04c0c030034007941d040d0454540240d240c4442110841a01480354596454044166507192011107086030a004030342c3c480010b01c01088680340340080150044001c81c1e008881c02c0c8002d03202d03140b03194111001d5a41000d1207500c032680400070a8055400840e100c4820010f89003000c028441014001013086011846500001304000405410040c494503844c9030303414191409060900103580c8507428040d10003a003400c000000c0841d030711039084030141c500c0c0c0181c20040c50228000140c0d0703601300440104850046a040c003155050911131044899000074948423664a1619480014a0003a611400040300800041005890760003017002c166161401481418035110700100d415819070400700401c5a007030500808544007010721604150116407a6075640401c0d44044020b0003000d035982418001c80124000b4 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 664979307 1250 664978057 664978081
    0x1a0f1212090d141011180f030309041508060907060203030f13080a030b0a082a030a0b01061e08090303041218030f20130b010e2e030e03071118 63
    0x3007400002e060118040394510f20503c0e0140380d0640c6c0c0c1c0d80b80c981083c034210385450385015840442c0502540d18050324034004c10207889070720349a80c0b0304103080b210420000c0010026603a1144503c07000d402c005080c0742d0f0081d120b10003d484080c0305007055001c1090310008040c1c1c0501d06500c40070b410303030340c28050380098042c083b1150076502c100c0403011b001801440101c2c0119040d080130341c0703404040700c101c0100b0000d20701d09010950140b01c1c200c01800090365844449001e01102e8030740703031900c041559400020401040b5040100002e9405104180303000100784c80c0c22a034412820488050601d02c101c07441c2c03011000c80581d0b5644001c0000c24003094000500b42a030050020514000309540d581074800c171440801500009a0790810300749648540c0880c80c80d060503d4410501c02c0c0b80d40010709003608502d00034010020340050115041585001d0725602d00300c0d030a0a2021081c03403550b554a0f0f005040c0c2c060400680c2400055040d6125414100c0855441c1c0d200d1100d41004244800 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 664980557 1250 664979307 664979323
    0x510171506041e020d060503070f0e0a02090a1202030a050303161103040f05120106050a0303030507031a0603161403090f0f0604170a020307061a0f1212090d14 70
    0x1100590800400c0d018245402855003400104880724403003480d105260700254403900c00e59081d01c6d52600013181c5550f040c440342c00101012883c00121500b80071104811000247c2400191441004001c4840d11821450700841c3e4014100014950040c004a07040580c060b4000f40640800000c0024150165812003d460003540d10007094991400132180e4078820307402054940051498100103c2c5031002c0340c075040710200c45c004920710384d654010601268240e007089011075100e20800200e0b5915100d070014205100700e0328152504003002141641c40050f0154610003149490711984601643c0c0300740200e10707030100056480c500304494540303800d81c002c0310708a28080c0041e502074111001074000d00403074103c901406100c10000355041103034002100c96055020a00c810808145c0520410740d80740c0b03a01c40c4851940d1001d00400912010352029280703e00321213044140d02e170b840080c2c0b50310724010746804d01d991109418006446e84030003100040071003d080792186032100010402071 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 664981807 1250 664980557 664980583
    0x3042111160f052b230a020a1406130f0801150b03010b1608121009020f09060a020c0d03020304080c0a14190906030506010315090206030a051017 64
    0x50140202511a058803411481802e9014203a9401804985098030503c1c10403002403900194814452000030614460002c040da40d44181411310401400e80307114045980ba640000381c041103500782e000807151560390084100000610780c40441586500080f210810984840341810365941c104170407803540e0900922113207500b001c480c02e20000040840405840011041a0440e800e080c40189103800041c483d00000c10440c40c1000840c0c1c450005002d107182200d0070f06558540051508880542580448c000d00e10412403074a01c0100c401c169035145004440259440c88001030480c5481d075620500355101c0203442030700f001c143e0004020000c44151038140c550313405001040100d004003a103c3c49851a076698544c2c1c4551a01e2000c030220303182802c4402c001251210000380c11030301e0f01d4004031081d6200c94014418000b265066000d50717090081d09115484141d40460260300000d891012000d480e04042071403014180780300005040c021800d03401060311102d07040d507600760b551000 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 664983057 1250 664981807 664981813
    0x2091c06020c1e0f030403020d0b100e010803070314090f1c080f13270f0e031b0c0d11120c1c06050709080616020705120c09010e0f040803042111 64
    0x4102094021003946d0450f0b0300107040d0407040e09a52140c01d030381d0320010000104030781203c001295134546041107a0103003c0100c01551104007500d0050b089400c81040c015016805100c2500c09540c0d90340b50082419081d550344c14207071080380704914940300e41003000306105408244010440c4950000c0c10107402100c20781a006a80c4405581c0c810b03541c04046036640e0b01030b4600c6580703149242c03c0000381c006030020000d812103202c0c00342030454004119035140102120784001030700408000b142412001264010010090b41e92000306140c450015140075090725186060300c4c4105100c11400548043c081c994051110851501c0003041e401c000c4498910746004150000e1041500c2425106248000c0030305403600d0303540c11054401a0592800c5105075500442ca617100c641d0605800c103c000024000704120b23030f041008040d01600031600d039101c0b110400c00503070300c03e0380460b42094100c407003140da80d20345050010a10200b902c2c41c07582250707074200000500703621030301441a0700c600c6025 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 664984307 1250 664983057 664983073
    0x3010b04050c03071e050301033807090f080607030e070f0609150e01081f0503030c031b061506070606030f050d03050c0a1e0905031b03070902091c06020c1e 69
    0x1110140c0d1720480c00c0c000010014801440000e200ea40604508440c600301c1d140c9507001e500c003040d84a220009454400340b0740000b8460b0f800e8026a40c01c015201d1000c81c0e41a0300e0408bd0b00e29615a40100080101a01c0d070f44116900101405440007500e00010a0388003140c582d6006820ba120034451070000c042e08420506105125035181e8240b0101607554915580700d4080b24804440341010300f4540103c00c40c00041e456404000404290035a000a541c9448031821060b4440c07016110454061304450100010a410600c55041031502124015100c0c052403c04200500040e00002c01807030720007911205005c000591a89070b40042c4d41c0034442962544081d4680d4029a001031000c035900c00200429000c02190900d110151440d00340c085a644500003880e05c52040d0b000010754902903889059070a051000c5809040041c0055250905180c080740c9016030030803038212a07006092060041042d6030b0121000405c290701240d080e900600006c3c5103511880001d84050b10540358 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 664985557 1250 664984307 664984337
    0x20105041a0f060f060921010612050a03050a030f0509030d0c0e18061230030106050d020c01060b0c0f0709060b030606070f061415010801140d0203010b04050c0307 72
    0x181c0300c2d0100792001c0c4010748401c0c0601c80c500c450b401e84640e0016060000c40ca840e01c2e2420b40014640340040c041042e208007006083c2182c1d82504000a81ca190b44181c00104000042d1141c0fa1039040c81d0059a4040c034003000c0b0001c0205100c002442424001848080c2c08001702400002030600305c2045040c20b40c50064504e6851a240b49810010700040d02c180084440000c2d42d100c03001800086110f0341088034a0306184001d40d41d1501100d070500c40f101d1036508c0e4440b00c0348500490702e809141d5414404080c0c03541c010300c0842c0c120070f80c001645142c0c03642c0a403c00b6000700300008003140c1385c1d191141d071180c648194211504082c441c0010004140e01c00f4007402044035019484945551140d03414844141d00c0520103403508076070714051300000340191141c14603441d00308403901b07880d06200444008507900749603d2410010b0800050000503186520031400c00c10442d00a40640c80307600c0424050300c170791105150b01c030b0b290070100440c05a41d0002944100560394800346180d020b50 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 664986807 1250 664985557 664985603
    0xd0206060a05010f0c02060403031716050316030b030703060615020102070206040302010e060403080d02071208060f010f0c02060d0b150708071104020409020307020c040e0c0d121e02010504 83
    0x4403040d6000e11040420011035005588450254031186040d404821440c2c000c1a456803040e0310490000e04104c07902c04511006183d50f80e041020002c40464501c4c03110802882400050003000c13158840202e00d1500318003d0b4010701d4104409816550029030382e06011005080b00d220341f024a08070711039a284154418400c99402d290700400150409045400448148542664540d04900c0400010022500060207020000c40300c1300c1c0507039584c10b02e103008131000c000040080144040348003800680c0d076404400e01800c02080c40c014001d6000e13900e0031542c600c5500c1d0044d400c00300000b4141c4c00c114058000640c68002900c074001a03004c0c10480024a04c5a84005028240184440b40c0060900d0300f119295040060003d030070152120305c084126070040d100200503038080c003512109820903000e558904042c0401270448540f03040c02241c0703c40c035980002003039196602d03921080d4901440d00700c2c10000c00d02e0040780c808446036201134001d0005850030303200703e0080840402d40b407901d0 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 664988057 1250 664986807 664986811
    0x80405010b04140109020c0c150c0d0314040b0a0f020d061521020306210102090901050a14040504050312162c010f030e2a040902010509280b0403050d0206 68
    0x60790f01041c05030f00c1d02d40380300000e400444401703410740070707034020b801c1d8654910b608078101340340642515640320340540300e02e80382461044811040c5403e106540d00311008140c480c55000b50480b440f0000303aa20384d84c0030390081c00c000c4c02c1c00c040c96201207460600140d2135800041030743c2c5040d041c1c031300405500c0c2c1d05071034007d1840103000c80a40010216004841e182e0091a00034901501242c5006100010b0b091040300882f81521507070341c08a281c569a18004e4404d80c014441619210500303401c1c960034401190301d00c04030074000c98507440410200402041201c04860891014264030b003400c0c045501a8402149034200103007001650201041805100b00e07041e80a4002039800da4003824015907500880c0325615003459074622040145950038850340c0c200842503040c440d112407486642000b00500c1d8200c5902075850440c1c0040140d03040300c22140060f0080b2000a840000750b903484000c1b015040c2c1080c01106200320004000d82000c0c00b9105880c031403030545051040c0c2c0786049036170310f0f42 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 664989307 1250 664988057 664988081
    0x1103030c040f050901081c020a08030f09011b020c1e060304081e1603030b120703081e04050d240608030307081f0e09101b02011d030307030209060405030d080405010b04 74
    0x310203041c5107686105101f8004455a6006076a5040400d4540c581203420844101c40d074006e8410030813071028000e00c511101a5800d94485503000680740340255202c811411117800350203503034540d200c10180155038040310700005080e0f81d81c0b440d05140120094004199503107408000101f246103006000c03065a81180d42c424502032400f002d514201d002e000d043c0c0036540c20960358400d0054180061000c900030714040e890050b621003540400e107420f910108100b09a040c4107010501c20b079903c5840c1c2100d030541196110281c0310001a001042c140c44a02081600b07103050b02c00200341c5004800303580b103090181c6841c94076581d400220f13903405001901924400c0c442d610107102c1010040d884603040421042200e501c8880500803408843d4558100600507022004a00842d030342406001c441450614440d1075004102110640d240005001d490505030040303a548603036150402070700c0c02048001e086400b02540c41c5000b4000d030b0001e45060382c0550900f0003030480760805000d89004c40c0f40b = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 664990557 1250 664989307 664989313
    0x5011a0d080d32040c060926010b060a120c03110714030f07060603020f060c0619021c02070c1a041e151101050702010b0a03121103030c040f05090108 66
    0x720b8610b60002050080c200001c0d01c3c0b0a241554480404582004580303d41501d5000c0300e802c1c103044c0001e444090764000403c01c490560280311100000710460410601c0c4501d0007121080c80c48210b0240001c12a604d801030004241c00c80d015600400e164004444120304110105030400c0441c2a10411031248284503000c102901c0007070308003800121a199030303009a071306240e0207500695090340140000d540d0304d0344490703043c0217620300f01990700f80c40902105d00520309900c407111140c54000c001d001034402038403240b038894180010340450f142c1131800302104140c80c03120000c0c40c3c000e40183c1d03000e54005a0458000c61079035000c81c4244030000042d01541d043ca8604044040038142a254505030503410b80f400180184001d411030301c001c01c4649461004192a280c900e003100e00040c2002c045a04141481c0080d4075210421002e0780e400c40345412445640d04c3c1c02b03036443c110708000c905d1036210000800224001880c00380c01a00c00b443ca000c03006075035070000c00070000001e003c0c01d90103030 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 664991807 1250 664990557 664990567
    0x80a080a05070f0605100306050a05060906090903070606031401240b0904090c080a0318030308010b0924041a09090a0b030a05010921030c020c2106010305011a0d08 72
    0x940900094001c00f0711660320001003404580d0340509a800640700d000042c400100f080c000c2258034002c1560202980c4420070080c5401e000003910444003401e8103001300304e00c1020030307503c030814801c903188180c22900c103120803681c0349880317028880d00c2d1080e01025445c1c0702c0030b0b094400d0800d02c0c40340a07400c80710038513490500708800ca4200f46d0040c0042c0394069980d03580d0034005002c8240d800010701e1020040c0102926a0078040d00861110f942c00001c01c6540100b480003d801001441c195010391080c1c0341c9a007213040100741240f000c842d20616000342250098507040c5c0000040069401400c2038007550000e00000c070b840c500415811903402150707a80043d015417242d5101d807288001c01002c0300c5800d203040e1141407c54070211003da60342d0752070004903e0545c07182004051040280c0c5810040c440b0556002515100b0f070300c403c0c9200e04c240958559082d01c80c01c0b114144d130600700d41510b140396502e28029000301304551200384101c00012140c40b582c5400144540c68980113854a4501 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 664993057 1250 664991807 664991827
    0x50906090a0c02010612050c010e090c0403030302031305150402010e4c090e0112120809340e011809020117011701060e07051b2410080a08 61
    0x140c451105802c04540d80d80d000060030360800c0500060313590141000d40055200200010003c4446400050040402c0f006128002000c00101c80869401d03190041c0c407620344002140000110300340192840c072030010103d00600020702074034082c2d8401d880303c41c000400001806628607080766010411058060070560b40c0e5804200100c40340c4c003400002c4154a100f20140d241c03051390700d0007480001d281880034082d01034141c140c5405001f06640c43c040c5204250b40ea02051011a00f440003000315183c0401e0100070100000401006c1010240746200116000f4001e0740c2e407c81e9035000c1d44480030400103010404444a60f05030748121b418991040e5562028102a0cc090f41d0202d0400c22004040742541e00325048840c060488805ca4a44030102c100340c503070a442c01c0350004c40307062185009125030340d5040811281101c11400f14102030404210780d25003011a4003202da0b0403018040c2e101417185e003405012601c140c040002001d0803540f121116662038036070780d20042110b00100800130300 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 664994307 1250 664993057 664993061
    0x170901031409250911030f01050a0b0d02090a3f0b060108071202030c0903011a130b0a080a050105040b0708010b0f0c01020903160602070503030310030f0302100203070e0a050906090a 80
    0x9a0503c1c41040312400e582c804140301100c05415070044100070100074407800f51100034105004000841e12100030300d040408020030361044c8008a03275000d50020310310030142c54001c41d44000304051039011030828a0b41001c00c030019041145031290f191988000c00f40c2002004000c0707640c43c0c000345904003580e41c40b0010b45050101900300f0003402101c000c03420760f4400d980002c46c0b00351a12190203440c0c4018800307160030b5404070041c0b0903d951000000300c8041d22000c0390b00c0500c040240022a0410510010810101c026009000103000e42c42c051420b11805403c0380d4082d83c85040d050031681d4031814100c40480c001c2c000d43c0d07082d100411231013034010088000b40603030700345113000185481c409a0001340741c45511501040700300344445007003207080e0301801840000c1c07070160003540c40e628090b40c04c1c4000b88901e000041c00c902004d480c44003407510030400c18803040d10b4440704540c0ca040c01100030f0481b102c031804003072041e00c05c0d400c08101801c041e02000e0241030003802c08940303900c8095101d40 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 664995557 1250 664994307 664994353
    0xe0709052208070602041e0b0c150601200631111c050a030908030405090a021308060a15090b0603041103160308071208040c21170901031409 62
    0x1a2001c414003103c1d001ca1018030080000b000b04421159000301101118171903007982e0390019407011010b1201046504000c148a0410240120122019500c0c000165103480402107200e00440007041c200405e00c9000079568000c0596003480c1c164645541c2120000c1c6204280070568002c02c2038800380041c0074000c1c02c7e65216401402c0d500c000600d10701400340d82074401c10680b0240d00c0540c0407014160040c100c60050000280510b15150501c40842c200140c00340000000b2a40002c0101c407654039074103070342e01503c000810355500341000c803d038401900c1c1c070700c0361403646405c0014006419801c5105203407242c0c40140c825400d681d41c039210011b8000b070340c80070a5058004c2007070340b0007030702d58040c480b0000c3c521803080280c6605090038549007041281c03403108180014001808046142c031645407040300c04003c2003210181e41c05c40f1600c90a100312034010600d40c0c410424256a111110161032005000c2c2d80820000d1100380300725054820503100e5007860307004805024030005548640e02 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 664996807 1250 664995557 664995563
    0x1050f100609030f0317270303091203041412041d07090b07060608190b0a180f050304120c03020306090601051f0e060f03010303080906250c020307090e07090522 71
    0x28051b00144001c100a40c0c1c0c21542ca003881407181c807203124004c00c0c1c90252018200010000c50540c5030140c6803607610b220f103002400b80303a10f02000003001c04c04c8113020081100055410f5071440c44940e580f13541d03290080e004030b0182c44174403500405252800c040051040616684288216141813004c0b08198000358080d1000d0361104000725880000300f1201c0c1d00919a14070b003c0c1e030840d0500f040351070f00344094040700d03095040501c00b1003580ca0401495007a16000138080b001c203509450602c0c55440390b94803924400c0c2824005505100b04000f030303070007201d00a40985a41c0e91302e0b24001a00c42c0d409004556200c1c1c444000304003074040066105982e4051400e10000c0c9080746000903005401450301c280c14400c1c00001402015481401150480c2507600200442e00b0312240b903026151408964251198444104d903e0b02c0c1d00c0b4040d00002140c0103000e0b40c100c00c0e00c0c0c1505101800401000c403046200340000014140d4184c85030078481d900d0010003008242c10f48403007800d0f00b42030100039 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 664998057 1250 664996807 664996817
    0xc0209072a1a0c030613090809010513030b043009090c1209060518120901121b020f0708030405030c040902010221031e0708060d0510020c01050f100609030f03 70
    0x102c5103180e26a8030903000e2007900262030b44a00d8103004000c104a800e6008140042c18861007000042d141016500251803d080194844890f43c3e10102d025195034405001c00c0c0348082031005010901308448c041c52164181e40610079443c0c15103127100349000c80c540e00040c2034090f04029a02c020f030310003541c3d04114030f000b58001e070000c1c488106a808008003a01d000e80d0f2181400210015110010942e65604002c0c242d2200103c125104500070306039841e041c4121a2000c00c111480e5620145602d00340d174504032590010650000e503030340700c08040300c1524415104089401200002644d0403220014000c1808280510601c00078218464049056208011103000101004500c18100c1004005034036228074201d412a0040583e4218410030014140284040c5540c0515059440304003540d800301003113141c0c035100c1d14007040121071500d8684041081348480d081904141c0c00707082c058210840c10740b10460b0411881a40d8462140816019602040002c1c1c1703400308540110b000f0b00344 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 664999307 1250 664998057 664998083
    0xc2701030e010f0e010b0405190902031609020705060708191109330a12200c010f1d060106080703110a08090d03060302030309150d0204060c0209072a 66
    0x42107007035900c107250450000c1e131a503904602d103400922034070110300d07412142848507051484404100c40c0084000c8034480d5242ea2103401992810044240851440151107040c1551031000300025045054110341a0156402081801c1d1081c42c900c0c5c0608444004d00c080b002030706203154020b0610a0100c0107014091003944059552030640304481c00351044095041545940700c0c40c01c12526800001090400b4410003071140d034440151a03001201080c0000c40c5040c0c0b0300b4204984491400040082000181c58041c003941900440c00e500035629003407201c41480c0507131a410391040c0c158180e07183e00401c0100011072040780002d03001300060078005002d01642c07960799010346c00f00b0300c080c0c0414161410300c000e9010801c403440c020f030f480d86020440c00d402d40c0d00013a2248241003180744100f0f8090840e0f82008501002c4440840c81001c04642d030300d943e010094454071003018164031825014000074413660103000512085144506074680189450f2510084010540020354181d030754915 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 665000557 1250 664999307 664999331
    0x10b090a05030f0d0f020d08010303141204030509120a0f0303051b0f040e0a0b012705090906040302150408041211040c030b121219170a02040e0c270103 67
    0x3c01925040e0402024050041640c40054445240c0d04800d2003154003448510b0107403a801080d05064075410b00d4040140f92000210300003034003030003e0b480b0f280100d44052004150b0414010290703004151030704c3c1c141080c4160303500d407901c424503405044100c081c5c1d07a59000900c81d41c800380d40600050380f50000070324940070124854100c8a0080c4000c50001820310524240782103991b8000c040745018001d0301c40c903100090051031040c82402000c0c942078000415034a0185448004d440090000e5400345403854070746541b001c0507581a400350141c833188405420b0403104080c030868000e84102d00d42850920501100c9024841c15252104110002485036589021300c0d2001d100d02da401050520000c0100548110174550800b03441e4000029041c066580318182e600d680b0885415000c0100301101c1990122010f511102c03800603a001004610503059000c0e03c140c520b480251265551134040c242007a1040c02c1003001a5442400031140d0f17110748020850400f403040c940803481d200c60760 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 665001807 1250 665000557 665000563
    0x11517120a03020306041a010e090a0b03010e07150503240a0306020a02010504050706020d2109050304030f03021209060306120f1606023a050c030310030b0901090209010b090a0503 79
    0x10070580000d0b000400d000b0907151500481031075804104441e40701c098031200103402211556a043d024040602c0020030f4240964020103c114000d0028012364201c01c007401c0d00e071a464011681181c0d003c13244181124405c2041c2d900c504819a04c000079802c080c0c0740c1225100c1c1d08102280e02140c032143c04400a40300780081c1034400346030380003c100c605091505c10b080c1701003600040c003154084c400c01074405501442c07480c00d0116424520311070b0321000301c5020241011301c0003e40540300012300002041800941c0e16181c50180d4241d608282212072061307081c2c492003018036407204051001c502d052405004e00f081150810044441c0c440d0000750040c24484290001c2c00603c019080c104000380d0140031400029020081c640070120101a103031080d8080c14256010500c5415542410705024101b101d446041071001c4a0301c0e8600451107400c1303048503000840c1c0400900e00410450305050140746442a4000c02424841e801c052b01d240c100e41004018940c05101d002e00050251002c0c = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 665003057 1250 665001807 665001817
    0x607170f0a09030506090f06070c11060a020a1506151116030c0f050306040b01210506040c15031503060513060e01020403021f02120d0219020d0f0201151712 69
    0x56100c102d151469820804e09180c002088401560442d00450381c5c00032000c15081c0d4840b08038140003462881505100c00710184c52103001d900200b0000e40100d01640000f184900c1c603206580c50402400d400c103508042c1d400901c140740c8401610440915482c1c020048400e00644100440b0180800710064200300030496005440f404a01c010611040800b5040070300541400e50003000d031803d05a943e0042d580051160a401c030b1203101611300c800c1c2244070000700c070300e400070200c070100d00741401c02150320415445005240c045580400d50031300d00900a50ba14407a0301c0d50784040302441c2d41c48050141a0043c0511500360501c0c000c900041c2c8548241d20003079803400d0005840b1b600303502c1400107640390300b000303d030721007111004000d8004e038000380a0780c10070f0030900c91a84a41c09a400d041c00790185104400390080c8444141d0407441d800190402d2100e0140c0e01c1ca10001101c0001b0f908949400403030701030140c04e0000034410789480805403020460584103c441110000700d04121507006 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 665004307 1250 665003057 665003077
    0xe0718021c021809060109240e090a2903060414010b0423130b011202011e032a0516140a0c18021206010f020f0601060f1206050607170f 60
    0x1103c4480d204504003054841d50156003800e1101d130103410940c0140441090741300e4a1349614988800e203014078031400d65601e400f2000342150100341459010100500074042c5c480c200d800c076041415807841030208201c4407104014016100720346507034031060307000b44118031000c60540d04c0d0549000c1c1234840d48183d00c20b450801494800504121302070302d010141c0601841c1c50044440403880120f0002400c040c11102e0803a1602820005880161a402d40b044000c0032100408030035144070315050b801c9200b0b502c075181d00207408547c0460b40014018540c40018001a2050102540d034009003d070343c00544e409000751a00841254010030306c1d00c495010104c481200a400811642d060001d10251000581da001d5041800030038080700400340043c806030402401040340120507009001018100a07000e00b560131940e10389401601c60101d040c001e800090030507045c2ca9120000f88182c0c0103440006041a2800e0815240d0812440c010382d00700c60002400c110881203050f03d40002c0a080318 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 665005557 1250 665004307 665004337
    0x50f01090b0f04030f050307170a020c0c010c0c05010c0206070b0114010f020106050f0d060902040f05070e06120c07080c1f060b09030c0402180d150e0718021c02 71
    0x3050300d0407505100001d016042d5585a8400f0f12000036004a207080302541249049512591041001c48125032010010401d45404a0038412411815002001400c1c2d000003198110510040110341c1c0c0700c1d048502620704451041c0034000c56104083d29000c80e40002c000c1420181d1a46484030410741c20b034420081c0b000c0c40d006010071075030000d00b801c03100c09144c0002c100c55031418012070706d0070240e0345d035503441144100081010401d40340e0103102c00c690003400800500302ca460303104005081c20340e00c0e000400e01012150055141c00760031240129076545441c0000c0c2c4806501304e80c141c00138003080311840030500c04451404020442c10048040c06a48042038202d501000c9040390b01c10b4205210a0904000c040440c3d24005803640015a050302c00603500c91080c0d10b0340c180c482440d441c955002ca50345440c201446036040d09044100d48035502000131802c003603101540c41d20603119681c0000450000c01446e0022503000d00f5494410000e0560800e040503a0103080fa4080c00510000031 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 665006807 1250 665005557 665005571
    0x170102040812070c080d05040312030f090f0605010f031502030a0e100504031b0b06010804050f070b0d0516140304050a0c06230c1b0a050a120605090304030f02060c0a050f01 76
    0x414204c1d0b8000c00e00301010300301c180c01c1000c0c001e12500c16800080c0c04400b001c64107102c400d100b81d010300000107081c0d004001780d10300c074a450560381303810740000e41d0400c4c00d060002c96200d002825000843c2e52140401c1d4040544940160285d00000c01c0340001c1c650b602034040510b002030154582c8220500d02c0000c0170701c6c15150140c0540d440c0e04880401294656440e80051003045090f03030484424200200141d40e2407a2103450001c80d96000c0c40309001300c0c00c000550380341c0c14002c2d00c1c0303a100c41142804030360381e8400c03000003041c03951000701d00140304c080000e0301e828030200095401c40d01902c1564040101d680760081c8020380d65002c0b00009030039086041103010307010b410140069140802d80c1c45c051555160907642c1203082442451b200c03402105001f0343e581c91103090020400a00060082995103002404520b100701c000c0d45c00710b0610b00043c80c00c8001004aa00b5030341e00845441589455400f1b1040c0c640281e090307514144035000b00319001c6013040000d1740c2c130703101260f002103250 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 665008057 1250 665006807 665006813
    0x12030706200d0902121f060b0c0a02011d0a06050d0c0804120e060c011b09060e060406050d020d06091b031803030527010b0906091017010204081207 65
    0x2140c1d030401d928000c03207200082012072512802114102400b4120110302494140009076004002d020459400d00c2001000d0446943c240d2011011040202e0100450356580d07111001c24800c006c0045641d40040e490f010046d030041d010f00d05088427010f602e1640707408a901240d9240095009540410008500240c1c40c05180c0903e003102a0f0a240203001e0341400d80d035800302284180d45403420b1041040040300b00380c4031902603c00c803280c03000083c0700b0038400c03009203116600394503481400511034403003300302e8a004135840307199504054034075454940741280c200c0e016008090000d412036004c002d900c035484c03440d018420203000c1c0807400152483d124150101c10850544001c402d150401880162100c584660003000740d415043c0461b907540c520a0150b0444401003106c1b4280b08001001703089140f05600000d0404419180c848054407046d0422000442c02c54a4540c0c841e40d8080c1400054812103d00720412507281c0013500303090300d5071011800e200394840540c0c45260702003561418 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 665009307 1250 665008057 665008061
    0x130804061e0c02030c0f030a0605010306051e0106080106030c2718060503030414010203040806010f060f0e0d11360a020408330c0d0f0501050a1a0912030706 69
    0xd41c00749802c0c1010700c07404030b9000c00d46170480c1c18803607445143c00a040e000f0b65102480482889a0300c100304112960b180e2522000a042c142c6000e2410544522203941603032442710710506070340494039100e466078a0404220301920f400400c40b8100101941c4101900c07140e001c4a450048401c180e200345503040c0f20b098402e80c064103d40e0310409041c00d004000d1520040100d80035074200801d04050f084003040143d26502ca00e41c0038001130300c1002d00010715565142e014409a031503680c0e410b10110280c1c6408c0b204894080a12039010000a0201c00000c550300c0000255450207821800e2540d850200040301010602e0752465510740001d8610025008061050303003d2124501107003020700b85401141d940d109804690741e9501c500880c0a4500298103450145002400c1101c2d002d02d00f2199a0700c440c0c100b102c0c031030307070b058203100d11880c200e103540c06528140c0c0e0b805071068500d1031610000381002510440d030492882c40801c00e6a8603a1189048a111107590790029696400b140c98040300f = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 665010557 1250 665009307 665009357
    0x2060613020a050906130803030403080a0e010501030215030603012007020414150616020901060512060907051c0608010f140702010903093003020127020603010e13080406 75
    0x80c18900c104640001c0030b4001c01616000e401c181c69607900c40005d4441c0b80035540d145c0e0013405061101104001c20542d20024442c4079028440d4140107203c05100954240c03003081c00f009500090031801c01801207540000340d540442c0013800071402422a1040d980034213048110b03030001c9080015440158101400340c0500c10341000420480c03840c085e045001246040f07000640301e104009501d0040c0303a0101401d280d0250010007487d45565180b0b000ba200d030340650f070041c0544881c0000070340d0790300c1c04c5d121441c4900c0b103a4880904c0c0210200881c00b8407070003101c0c3e101c011b90b512140411030107400d20810285500b040f1000031a45650580e0a04d00d01008103040c0442e070400c50a9400250b00c800c02408940041c0c0000d2815843c44600001d071030302c0d5059202d450b04690303402200f030541c150000c52091214000607409100c2000c0d00c00100050050003a4002104000402c072001c412194107034440b44c200780004005034199203603185940a80e11440000c3c0000040304585521003201e00 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 665011807 1250 665010557 665010589
    0xf0609051617070c0f0b15010815010c08090127050a08030406050f0a0309020414041202011802090a0b060706140a05060d030836150705030a0c1b03020606 68
    0x10b445010444500040d02e000140316004001c41e0b8004102000091801060712541c000c015140d103181c54900210032045412005002840003404207200380d401c0c40106281c8001030307540c00d0848501c2d07255802141d2000314a9410460388600406070350060b0400381c0400419280012191481e01c003c110fa2076020b5085150b180c7c00401c0100103543d0048211003d081440030016114162484142c3c0100346401010703400030306050301450310302005805180300703030300c903503103040b1a03503400c000032400c88100f00e001c1d00ca43c5007030140380c502516011200d941c0c8040240408a0030031882d2002c03541e250040c14040701c00a4170707482041013414102141591003860b0303a104000381d180180001707088d051700310006401c1c02040008110211140d001a5a4424078401c0e03800700140600350850b41c0b103a0341c6c41c3c01c1030117000d1032020004020a1a10507401610359985041c299115003000500a141e41c000306004d104100440c4204982410600c80009002e500030701382910340101404043c2441c0e07101f40e = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 665013057 1250 665011807 665011817
    0x140105040501081f03080d090c090b0d03030e01110f07030809060601091701060816081b0114031015030e160b030106110703170c120301050a180f06090516 68
    0xd01c5940d034440c0c40c007035101c0a81894952041203034800314a0500ea160800f401400b000038a42c00111042c2e0000e0480a00c00d8654038401e9a0714800e075070480700c0b0303c06503a03405103101103507401007440394101e81c5a42c2c206800004034901001d4215101d54080043c0b02c2610030040b411000303240c3c1051031150f0100350100509100e20b0408002400455103011ba510a5030700e250186412003000d601180141011310219148030084210002d9151014850208240b040e14030401401d4001030380c0054812041e140d95004210b0105400a290401000030584072012400081c3c0d149050a02140558040d2030000d42982c110407030381e00b0b1212000502006000c4d41e0010084401b52004030b80c110b8000d480c1c03105000104843c030b9400d100003a4400341a0702c90041244005000c4840141606103407442200c110390b140d211441c01740d00091190fa0f43c4401c04c24410400315400050b0f0906900d0511000101c0344905804a070480380700b500455021650b500c01c0004c004440c0d0700040601c1450700344 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 665014307 1250 665013057 665013059
    0x40806151311041725151403060f180c0310060c1110021203010320120a06020d110316080619050f01020c0a0b0d0b0d050a022206030c14010504 63
    0x10003140c410f0784140704440360407080c000c020070740c01e000f0310303084110703c80030503800c54042c80710181d46480c280128614001b0344013802504a0241200c01601081101c0c0c2604507031b590700c2001000081d90702255040f069848010030807040c4020014483c4050390320300343c0c1300e0405000c032580c507100c40d40001c02400703411802080400c0c00ba441d00c24000034200e84c0582c011041400072410440110401c07001a54040004010452100b41030309042401e91410441400c040042019015038103025400ca034008c2c0085101103030aa40044c460302c2044640450b0344080241039846541c02100c007400209180e020f00300c0340d1030707100d400c25070410812200d20301d0b140c0101d81412503480d032911070f107441180502603045030742e40280100002144000c0c80309003850365488002c5143e9110031018840f491801d10050360340d1070170700e03a00040241c0003c000c01c64004194244250b562501c80441e48041f040d01c0300341c510701100e00805c0d0140d84551070b09003106140130313030160010030904540e606010007488 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 665015557 1250 665014307 665014331
    0x1020d14040b0f0c04120f140106030312090501150602030d06050f0f0d17070803070f0f092919090909050319030b090a05041109010e01050103110408061513 69
    0xd141900f1000a420050b2503844200106184e44103e40c403c5045c0c50b080c1002006006103841c0d950002e501902081c80040198580d140c04c0340c4030741c00000d02240720070b8900c202a410f66809520903074800c0d8000600721141400101400d0202d501100050348002450303a0310b00c4042c0140c40c007e24041d640082402c00d074400041c0500c00d00100e0714003c1403801c101c0030038048028079a80f0050040780340750b070769034505040c020a50340c01203808038013140440d080d02e50803521815040c229040c2564406d5409800c2004041505403d802c402d25520076942da520b081e42d03c0c0000904400c2c01140007030007205100c00c4041d001d01c000d9409801c4051400e04054003184010040300ea03025020080820b800c00c400d0415402020000440790300052108200803d400d460350181d4059402042c21032016503190f000c04c48a11003d00807007000b000c000004200d00d50017508502c11a100b6405410b05140d01c61a000d481c040d0101c4035030075101e90107915214a8242022107840e89054a00244084c0c0c00b842c0c = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 665016807 1250 665015557 665015573
    0x80108070614040905180d050c0a0f11130606030f061a0c070f1e1e060f050903060c0d0615020606010c1a0406050906180a0f210201020d1404 62
    0x11203554140000c0340b04100307000880b002182c020b0540c2e004100700d50b08043d00000302ca03d03081181c61000b84140030b00300c0000b602903c1036907000d15403e8001e011039401c1f6954010304000ca130400700c0d400c40141007084941e5441c44e0060400c41140e64001421501c0c0541c020107031808654601040d62403d6000c0c0540d0790005001018008040744095661106400392444c1541e40c0d40400c20300c041f410404220341c414040e0154802c62045001034120342c5071401d0f80781d250141d2900203543d00c0700a0040080764054018a00e054007982441c5080003071000200f070600d075044032248824000090728085550423481800c001c1c204140050085518141020b0b640f50005021103041c050b000461408000c000d030460b642c9520984640461800c0c24035000c0c010301401c1d80e0640b11805404006275000384440210f007032511712140100340e184125152020a01d286803010380c1c10f01c0000c7c04210301811102d0401d400c030102c075400180d5602031202c1c48001c0b83c41c0070301d064140c01081c41c10300010905030 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 665018057 1250 665016807 665016809
    0x20c0c1e060702090702070b040306021e0a0c20030f010b180c07060506041e0e01050a0203063f07030b0903180402090d0605010801020403020f0307050a121401090b01080d08010807 79
    0x141c2d81324800b0b4944d6041a8940701d850382c8a41c621040014010042003619000b9005480c0c01d48103403c0b038885001c1503481207010b01d070460030004050074400400f080c51851020341d8900c410346800c04890151003c0707420104070070b6a03200a41c1d141d14400005090200700b1422301c014007505000503040000800d81c0d00e105500c006807020f501c1390301052203592147e100250101c0003a900ca03070341c0498544c03010040d116036121803449502c1c00c000500c0e403d006000f268071600c0002d10b40008032a07a0107010100700e0013641c0000950300940309070120180c04500e201ca1007180d00000386805451807914000c02d050003031207054036130001e104221001140c3e4441e00301c90107045402580b00c0003008085540700400403409000385042800000b480c140c19070082c81030340e0081e01c00b00e030840d070306030305040c0d5039422886241c0e0450141c9508114030b03901e00001c83d01d140d22a40d6880c100d801082c07521030070b5541d80c140a951070080080108000c040802ca0b1081c000d03030a007060740480d8900800c0545403400c03 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 665019307 1250 665018057 665018059
    0x60c03090115030f03020609160504090606030204090b0402100e060409180f140129040518010e07050405070c020306010611030f0c030a030605090f060d15020c0c1e060702 75
    0x880410050390302900b1450010b80308002810701543c0d2810100741a031290181900540640c20120708031074004a06542e00c440d01243c1e110605140c641844001d060029060310200e5640501200584c0c80d801490f81203030103a50b000c001d906090040102c0314030703010301c10000d01100c2c0d03c0b040f42c96200d4070140d8048850501d40060b0b64621860640c01805c2003440040210700803040003010071184009464286400400030801640740c01302c1d0402d402e505000c80b445640401200c6401481e290b0030103a8001a1a4210031000c1c0031251414255040c0c007410030b00d640c110200900c01d5060511440d40d00c00c4551400c4920040160040f90306c40c0c406001d00320411120400b07040c0340210400c119400022440115a80d801840c1d1400303071283c11441d40c0d400068140940001c491600240c124021448100d0b0b00c40c044e1244410030814141c12581118441c130400001d00490006201034804007815601500c03100341084c040040000801c0064041d03542401000d181a0300d0300707020381d442c1340d40c = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 665020557 1250 665019307 665019331
    0xd0b0105060d0905030c0708120c0601150c050a060507022107200a030b0402120319180e01030803060123040e0a0b040e0703120305070e060d061814090304030506 71
    0x2c00021000f03400038000c00340c0244030024010702c40040000f01c00c012aa070450a545c2c0031030950030541e00c644145a000d040300d5000000620003802d128100001c2c83e11503042606070a0038a0342c900b418800200829079003299103104110700181c050042200703841070240d031300a4214192010411600640e030010b0f244141005a100c00e000c1080b002032030303805c0001c0c0381c03c050540d81c0c5410001c0c010101c1d8100c0c05034064104c903101101c0000b090b16064207640d503a400440307440620482d0003402d6101415a42002200d0001d00c0040006140c0e010398041d880d901c0d50303803030241c002402641810080441d081013840c070401e00781440000b601c1c10751745618545540c603140d451a40010b80700007000c00e5030040c40d041d59000c841d100060550112803003445c4542e0118030007036043c1c0440701c04403000300103c1d0303503040086900d1408030700500700040040400210140c4a41e64030300f1024003815202010f030380e514003240f2220307040e00005600010f845c00440c501421541c50903100c00e0b020301100c00c042 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 665021807 1250 665020557 665020567
    0x51903051206130e010902040b0603090703121710090507111f15291809060415060e040e030c0706031e0504050d1706150d020c03040305100b0d0b010506 67
    0x2958039204800403003140d00f400d00180900060031030003420f41d201c2c106c1c4654a8411500a50f08159007079a00c107060f100d01400c4124595100c0c0c00400d01125409410020404001c8100c0000608440d02074024500304240290404481c0c0c2e040700c80c060019002e11a092401c4ac031303000d0000030131044001003200700f50034540400c031100014020020801c20650f00840012403590400104150721445002c1c0b20401c0c003600005014051040b83d03514185459450b692682c0c50030000c440c96000030010b000011301c04210742c198202c9440719041040003d00b0000c040b03c0601e4a806048920258000510b281140e030300c050582e00c840b148030f020b051586800380008003142007503598006240154051060b031a06180c0591a01610013840d000b0402041014040e49070305c4c02c03158480c03100603103004009000007022010307603003040b048449195000c108007403903076200744003410003140304030000d2854004040481e019a43c101c60021700561160300c0c6800401c920b100c14904442050343c15942d03035 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 665023057 1250 665021807 665021809
    0xa1e03170c0106032a0305060c25060e0d03140f070e0d03180b0c0d0827070305060c0c0a15060e1e0907140f0a170a051903051206 57
    0x9014207401448594608070000045c001c007074007a1010303545500f88064100042d040c2c0360a400e5260f020281503030340144001100301c400c002c010080700c1e0641b038690640b00c01051002005800c2c06808070354198541480c8006000300308144410040d043c101031000c4800040c1d1107020140060010100244013404601c40381d000b0141440c1c401c0b8050300000c411542410003034140c8810142c01060110300c5d91000403401c00c90030035240d0a511080c01342c1101a01a001150080c0c00075002d40301040ea1ba024580c01e000801407040014103090000e800860700d181400c505004000784410500b0004024140041d2008900c40512550181502140c803190402d801c00a0640d41c201940c01c281d000d080c0059411900f07901e039110484100c181c002da980301034146032903000303074460505280f0800310103540600d02408103c4075242c024099690300c81c1e603511800394100c0403040598041d04021039000502c04280109104c2010f131034240354400e0035541c1d0040461045004c035419841c2c2c014007141217 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 665024307 1250 665023057 665023103
    0xd0309021206160905030c0109140f060a0c020f091b0a090e0106031a030d0e06070204090204050406021309090b01031203241404060f050904140607020c0a1e03 70
    0xc0880d220302241c8140c90483d02481c6081010b00b900c101181c0015030020360361800150f42c0340903d2060f03480c4c90032185080c60a4140d420301d5500d0641c0506441c60901e0b080c1c07240c40c0600021b00869541207031140c03250040c8041c24184060003801280b0740020480107181200d418207421003882202c41c0c1d01c02040c0300440c1c040b0ba264000484804401c0000120998181c12a921341c1110687c9203c5981c0e0280030103035152502007550010801d02211101e15180000140c0343c03250016001141c4000c9640c005421140b00710b404a40169001c00c0a04544030700c1d148600280a04000c1000308035055128035008000520004040704402e40c0382202d058400d07040034aa9401d10700b42c1c01424042e0b0380741c1844204003406840d4030f0140c1c08441141c580b5140c000e040442e00300340c84c1d0415090030081401b0701c0782c00040054446090700840540e40d15010000c2d1480f8503007944c0500344442170481040701896003a4001c90101903022201e1090125a0b20308804980c0c2c4610203a000c0c003883d52441d15 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 665025557 1250 665024307 665024329
    0x623060a15020f01060602070e06030114060909070503150f0619050409020604171c0f140c0a0b04060504020307140f0f0312040b04031a04170703020705060409020a090503030c0d030902 81
    0xf26039404c01c0000200d29800007030703002c00e5a580100e4240c880d40c442040c58220360703280c010303a40c4004241c408a0110b00345a1289500242050141c7c2c800350b40341d00100386400d11078138240f1500c569080821081713600082003290070a0080b9008017158800c05440000d05081c1d00070280704139929440902107581e10000c035001003ca504075602488000c2c0c061a072544c0381c4019030144541142d02c07800d922445100e81c5504242d083e19070101c08040003440d41fa06070481e01c0c1c84081c910401d1500000300721a003196910951040381e003c512440c0c01e106042c10490558040c0111440818080003940d445494008110105a91629410304010700007840c0140c00303d81e080903d9000540810604c400300020000c0d01d00901e08103071000340258611814000c03c40e40640300a4a40241b0b0b0b07401e450300801824040d001c1d00c11a1001c50701d07040043c0240c1d0090f030060704200c1d8002420141d003600316810710010441100654108084000f00ca91a452528581402c042c0c6e105014000c540c0e41100602c = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 665026807 1250 665025557 665025583
    0x6060301111c02131805060f030d080402190806010f06021b06030a14070f08150d0f060b03010204060c12020109020906150d0903050408070f29090d0623060a1502 71
    0xd0304d040d607030818600004400c04050344803c2c2080d00250b02c9003040007055000103130150081032200c00340801100d2491018004a074041e81155074142d0030302010710050081d1207610090012549050300c0384c83d100d50107a0004082d034000c00606801c42d00000489540681c0a0721200d66991798080000c00405428241020301e0301600c1c2841074060f0b00c0050480c1c00c0b07200b52038100c03440c0c03140ea21800c680304284080311b0303206503441c000f60001009400b05204051040002013414a0005e002034203903081504000d000814461910307040c01800140000196100e0000b000180c13440d8001c100d401900030947ca000b4140b04100b0868091802c0440e140007442082c20030013400e0300d29005046038040d200d50a094481c01d41d011070040c3c41540501d00315a01381400d540008401c80c03820381d420300c070340b030f1403480810040c04043d01a803203550000c2c800c0ca210380d600240048a641c80d81c540f90150300c0c078110300c07801c612040010700d845d025012000d6400088600080640c1900c00300d00c0c10700001e6400b = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 665028057 1250 665026807 665026837
    0xf070206090901081011040302030d031112070203210708061c0206070602031b0406020a06090c0815010e0702161202030718020304021e0609091801090506010806060301111c02 77
    0x134150703002040044100b00d190070b060042110f0301d40300341c0341406035000295068109e005a500c3d224025440600168501006541044815400d54a212404403400c002681001030348540754190307048034002000124241251608000d031008140b408000c0203140a003d15515906001404001540300950b008101a640300214a0250040c2d0401e4a8600c030304148047e0740030b01b6040d0101560141d800760750041c2089072240e22110060842c10b4400c1c0c502400500740403401080034007403216001209451079081c0c0d4541400014100c2c0000c0c9128110b40000c20140c02c3e440f03892402800300d680c43c10f024022070081340002410250b40c0e9110717013014030100b41c11500740041c58000d140b080b40202e440d000c42c071600c2c1c0c1440a8240c080b011480c1d00c0b040c201f00d1356050740f80400c107880e0060100d403416124850310020707060845119100a407000c0d400b620042003000e0040151560102080d0000e0143d41145a50384445000740300c60308180c1c440194440c140008141d0607160255000418 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 665029307 1250 665028057 665028059
    0x302070b280f1d0a020616020a03020a150f020607020a030309060621050d03060f0306021309020c070305070f1208161a01050f010c0507060311090d030e0112060602030f070206090901 80
    0x3410040c4006094243c2e041884020344a15200110300c140c0c10030b4000d41034510302400c1d0303c44560040390000c400c907404940c0c1e40c00400541c42d4000d1400250190410b41c0c45009201503020740484031b840310781d0003194081d604200c007056002c00d031100d801c0d505042c046601c026615000c2d000d40680e42298240e1110411007642e49600c80783e040d1001c42c0141d0913214030482400c411410f0b20b40318001d6440100220104000185083c0c2c018417100000707800e07000700c08e911100034409903402629014203e900c258818800c0c4141440880010320b0600100c0310f40307514012a03080c140c0c14542c0050700040c80170864100318104020342c01c05c8143c0c00703d01c0c0519207010306840454040c013030040c0c0e40107280f03022481d2403a500409030410aa038104d1300414038980790200c22000341450b007881c0c0d00290300c2403000f060251510100103903803902c2130702e881c3c00e40c000f01c800050002c424508266246420301404004568001c411030b02c0c011140000903075582054004100a449003180441d081221100 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 665030557 1250 665029307 665029331
    0x8451203010f0915060c03020a0b041b060e0d03081008070f170109050a1101120e1b06070c0e0c09090403020c0f011d2e110d0302070b28 60
    0x2103041e2291a00841441d0352a0b0280c00c0413140c0080e68291001c0342078100380100390182440719101d51183c0304075907101000e6503a640703d03454142c030708889520040c0141040701020300250000f80070103280c44d038418a0030100207084112001c4002c3d00380b1504002140c4080358641601001d880804201d076401696417141340800c02c001c0c230640320380c43c0000940144501040c003070003c0080e045401088107007010b85500b022100c0c3c0d092500e050000400f01151400c01070b0080c00c451080d89405400701800c80d001d69100b26001e4400180b158008000b440e0006024818500950b000f003500903210390b44d03540a1014a1040250581d40000c8070300800080580c006100c440d510025a50014440c80e410010b4a6001c4034101303200c00741b0301c0400007424506081343c84054011402c20b0310400fa0216001102c412180c1c40c1c04500060980d0710400b1000400308150a10811103180441c902595602e52145c2413601030001c0ca0070b01080c01d840d5010190200025600000e02c140420404503d0f01d = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 665031807 1250 665030557 665030593
    0x50306040f05010f050403020307063804060602062229060a0b09060a08060a0f1d1b070f03020f01060807030311030a32040902040302010845 62
    0x2074102c1d1190308003850030310050a94051140105d60540045040c0341c102d569600192941312104c207a080411841d07842c4c13148920082800303485901c41d5402e4564a460244400c0e02e00d43e421203030955000b48184218200304050340c2c0380511108100c803c043c065807030644005107601e41c20110f0f00c0652495400c0941c8c1043c402c60081c1d0701180c1c2e8100d8159a06400c1c1d080e80214246140e1201043c4411080b0600544d60740c3d80c042c50003064205d01d5911444010151071207600580920914195007980302c00c0640350385a00004043d40400301440c496110402c00d10520200070407004940c805e030310406000300102080c2c0c0011400a1103010307121000c60303a50b810f041c8401e5000546424004140c8107011040781d4080710705030ba410307031001920541c010b0801a295880c0810340c1d00400b0b0011034251030005040035240c891005031381c0754a940001071003050003800907041d040d983c0300d50000c49040310003499601d9119150320700426485a450410905c1d415080c1200780c00382580b0751f04044484 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 665033057 1250 665031807 665031833
    0xd051b07030c181b030c0c05060c031f2313050906070201061e0509040f120306090b0f10030f06030503071505090f0604030e06071a0108011a010903020609060405030604 74
    0x24102d00f0981210a1481d10684020a0844520044600081d00403502c2900f00c04c5024946060101d260445a510325141c4002128560340b98113003c4240140f00c015032050300325141441d0540c030b4240c0e043c0b19105064042030300c580c5000006007529010395880d0030541c225800d00c0860100414a01034000d80d071a0b140444130100154600b5070003042034542800e9440001305203e4040301c0c01802d040500031002c3d80035006846098030300c01e985c00001c22044080da903050103580d011403034074680001001035403400e201c014071402052038008030035114551002e41c0c1949602d804510440c0c2c6003022030092040d40c00280060000084803000d22240000021012078003e108005c00c0c0d0700c2041450320380341440c0c002c0005401010114010034412201750f060054024a014a460242e542c2d01002138ac1480c4820740209074400108284034007031080308259602c2c16103000d03280d01101c0c0001d00300405800000c1c412500401d80c58203a03150081643c001d804054200c0e44a4141420316070406500 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 665034307 1250 665033057 665033069
    0x20703060e010618110c03030a020901180632040e010e0a050c03040b06010e100e150a020312090708060126030405090c1b1222080d051b07030c 63
    0x1c014050803998814402c100481c0d0405800350150400301e080c0c070014103d1038000c0c0078030060600130002d01c618280000c41c0541c035480c0006035281020000503115078615400c641d660654804100807407500700044c1c01f00890140d050303600009032a04e040d81d619001552a18884c5030100f804661403a8052445058500e28140d03020f01d0307a95508440c064800460384604102c4082c4081400217603c1c03a00d1035042941410714a0300402000086076241000201e0040060314183c009902c0d403e040141c00c40750082d005116241091104001e56680300e21008411a9021100040c2c203000e400d000d0240038000c41c8090350342c256540d160742c05032040c0750611107041421003150b981e205800007040340c0403154003810072445540c0e13503102070089030400710350100700001071802c0d01d500d64828030981c01d0300d1008202e03032a00e401a0000b4007029240c41207000100080c501c00500840300006031289200641745402543d40510f80e4080040200b541c020800c20712485c00c0c04000c0015283d43c180070303540 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 665035557 1250 665034307 665034311
    0x1502120712320f040c1e0504020f0306120d050a1107180209090c040303081506070f050f12030411300c181005120a0c080d08100b0a05030a060b03040302070306 70
    0x3c0301c1060200300401607900410514951400308240c40750f05a603d035415910300c10f5a11b40d140d03540041002d03a80203011070140d12034004100019454a00d41d0190040c1d004c80c0280320701900c600d8050081d10441c0c0280c018010403c09070b0812140c00c12007400038003924201c1e1508402400c0e1188065001076500d45c0c460496000060a40201c0c0e009560469800da03480041c00c0e2101d4128000c20880d60b44000d8104c0c200f0020b5001045100281d2a00f8502c00e20050900c2c4407480d51060815007001c10410302d000f41002800085212508800003e120441e11001d1102180318406000c4803014410b01c0545102207030024403083c01700d52000b01400a48140080c03604e20706002660341e034110344041d0100850712090000f400c00d401c1080c1101000003c0b19040d1b03109884052401503582e0060409903c228994209258024a02a0030803846001d4070649401c0c1002200745014500c02e103405c01501000080701c10500b2303041000140b1002c1c080d01c0d0340c1c1c01c080c10000d4aa4000d804286c0b090b86c = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 665036807 1250 665035557 665035561
    0x60207110105070309090c030f020c0c0108180604020f03010b190e01060c03020d120204051909110403030801090513060c1101050c09061605101503150212071232 71
    0x1d4003a0046a6100340e260350b03400b5059080104a00c01880900e00d0030080580d42c101c070000030240340c40180000c91a001c01400281e108100050840f00e00400003450256542038902c40c6050015140d07802540c1240d822201c041c107500030034010101c101d189035006141d480d1003443e1111980c1842d0540300504641e000c141e88900341038541a40c0c440c4024016031110051b6480544290119028074220745405450309a485000600f680c542030f00a07408440800c2d800c0045651512540340001c02040207903040a10b9624050200c2e44144220882207450303000244442c0031000a038401c15901000c00c020301d002800c3c008000015041c0d84481940ca442c0114070346141170810746c4c9003000001c141c11310388610f410103804500c982c5141160a0f10840f561021920381500420741b000301c4013000b0b0781035076280d820104902c07991510500d5400344100110303140f41243d04030080d40607106007010b40c89031290b80541700080c00c41554101180400d4401c01c503007558580c3c2c5c3c0203a03454030019011055 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 665038057 1250 665036807 665036809
    0x1b020d080f0406050603151006090911120c0f04060306153002070c14100507030c0f0f050d0f1d09070c1e0501150b09090103021306050d06020711 64
    0x4000196841c400d0389203844001800100290030095006101409440b0440c50000300601015000c1c0d411802080020b1814460301c1d45c0803ca0030010310010b0028030400081c20341c0254140300e006d00b01e82c112049480060400d9482c141101d04105140c5001d0750f841355100c400070000c000900451001041e0303100c03032212041c854000b50071418a03080d0034071651100e020100403400c8280400100c4590240101400b09910f01c11a00c003c0104201103103180010704204410b850442c001882841000d000c18000309901c10051101640d212201490601160901d12408402034100070003902c2400400c541c000e43c0003020022030b0b480c684580480300020010480414031030800980c1020744100080c010700d00c66003011100e039015404804414000c043d041c850300f040c007401904e96039180c031084004409109048802083c100355194100340142001420400061002a102e103c10a2a1691444444e441007009140080924081c00007515041029401c0400c2c02d451a01c182c014103081 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 665039307 1250 665038057 665038067
    0xb0f0d0b19060305090a05100912020a030e090604110d0c0e15090402070606050307031208010e0f06040908251109040803070c38010503030c0705040b060d1b020d 71
    0x2202208600020301814082e040340180300092907800584100c040000205206012018100d07000010108843c1c000341081210154800058000c42d4000020100442c2c0c6c801d240100c81d10040328007840e036444007c00100502552810b401079003000040307000d407140b0158494004102d298603400000d07811502081101a6500d880d000200300400000170b151500d6401000c0161084000003500ca0311000400c0c6401031940085548a500b50104e1510b81c1e00013285030b0051501942c06a4140703480c510b40301940318080c164030301950711058904100b00810741587c1c0c4e2a401c00070000140310444610841d076a00411003076891900382903104d072950824115413842250080403903459512110811a413501e0081416503980e00c0724054041041d858545c200c2c2d0458544558110714035240d0070400b0032400680c0a5486a8800c0102908411000c5030b041d00700c0d20b04540c00a02c3c42d00303000200d901c51003183c501000340c5280c50710b107130813554401008004041040e400c03151180c0509000760350b = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 665040557 1250 665039307 665039329
    0xc010e0102241801151406070309060f0309050129040e030f160c0b0a030b0f0109060f020f03040b0a08010e04020901031205070506040c050114090a030602130b0f0d0b 73
    0x8003460003000036402d202c000c0381e00035420540c103407a0010907806581d40c0c14211640c4050420b290038642808001c6a007071514591403a40044071621310b000c1d555540607002400c1d5204c1c2d141800400000001454040e51102148940200090007143d47d203921000314203e000d0250180d19540e4800030406050131700c6032000000c5000c0c011450040804081c4810b80c12030303141c100c188000f910444001610b207103c0308005010882c1025101d16846601800b518100c0d01780b580510ba00f40c480d540c050fa801b081001c120703101810101100c07810800102c0c1002d85c050280302582c8000900005d40780070440040203e00c515948074402030341c0743c2b040707403201c08015140607510415450042c03003c2280b802c5030307400075100c1c0d0908902d001950364845050190448054950f2400f4210802055030442c580020307a90455440d0303460500ba68000501c4003842d03000140c445507010a20706001042101064081c2c00c4418403a0340301c0250420002d46a441030b80700710740c050f06040035001d20b410310f104503031 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 665041807 1250 665040557 665040583
    0x6020705150304050d05090a17010f11030402100806060904180302120f030114040e0115080d090315090303090f060501090b0429010e19080706080603070e091e0c010e0102 75
    0x110489485c040300300c0e03c0b6041001d0140d8441031600c80064011451850b04440040203000400d40103071096a0500b20791100111540c440c070104100070051341ca02001010b030a44500b08074440340c9410700403c04a020f400c0603180c0262030300081c1d540c0b8030708441100304558032079421924602820b565004190048180c00703030001d0010320040c840b64000c15200c2070388100180c0001031220000c1071a60a44011714a841145402c0c0b41060012600900ca0414a421a41000b0981c24550399804100d4801c400028200c15543c0d10a241054800d422140025400034208103540d00c0d18100000141420701c42c0c1c000d800c0ca005140c124034149401464060390b0080e40b404500d2494081c200c04108010f0101410800039515154256580402882e00c1000a00500309000c0c200100546008030a4111009005d400c004110305580e00085c2002603a13441d20303850915440754860149003510401500903101d021a59007089150006091003616101762b95000c0c10a901c03000598488004400c48 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 665043057 1250 665041807 665041813
    0x1008010e0609011a0a15031407050703110f030706020c07050a060f022401060809101506090b0702060f0c03042606071e050903030c01020c0f06150904030f0c020a0602070515030405 79
    0x4204003e1040004103400d4042c3c1008101c80388011200502c0441c221200008110045a243c090503400320100565604370340080022a40c2a124250740703001c0c0e500d00401b1590000380007002d4480c1400024024400941800081503e40340080c20017821011580c0051298211100b1845014180301310160880b050084c0642d0074840304483c03540004080c140707148581f811401000c5114810045c2c0083c15210000c0000d041c0710000f4804402075008140100d400e1110740050707600d100c101e44050104a03201d036540c01c5452040c81c154016903201042400700d4001a40a00400c10301d9032451100f0141520802e64441c0c400f038840d5203d40019010b600300b08014105640e020f90014550301c04001c04503070901d22800101800c2e64021255003d007038000383c41d00c1c1c15203002000980e8005280510030b103144c0b80b100c0301180010340c0061000c0c041010305040c0e0010940200e01c40d056058000e0040d0400d203441c0d18010b9603408841c41940d00800b00307000e01c280b000c80f04405481c010b40d07005000e = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 665044307 1250 665043057 665043059
    0x3180406030c0906180c2f0714040c08010e01090209120703060203191b1211070c0602060f090a080702060d050f0106140a050301050d0302030f0301091407090b121008010e0609011a0a 80
    0x551170050050f01c440c0e05450301003460260f1558005c100718001000340b134274100b2410b1600300902050380e1130010141c0a02030b502006003c1001c1c5080307614150b60b00000c0058a07821410001007444a8a840b01c0c541d9014091b4048144000c3d60002c5200b0038003810900c2d40010b038144c0a208070f0b45000c1d03406660000b1003050b03946041c81523000c288a0746840c08081b800e03008450016209601100c0101c40d5400201f200b0040d094042c003140c0d170720034002000d580d41480c0440380e03241c0750940c500008114100c001040001c5545030800d0315980142d0442c204403614121080001a100a0043d00f0200e8040088441c102c985007085900d41e5040e90b0f034071030469207440c00b445190320307031008110290701061000320b603074003402400396000340280740010492012151002d01d05c064081c112740100001d0803003c3c45600380301011a01081d00512a0b00165a038418051f0746010041c1c000003001e500301694040034200016105000382e98490080000d20380c01000c61030140178120440d500001c0d8a10 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 665045557 1250 665044307 665044337
    0x18030f111507261b0a051e0c03041211040501030c06030c05040e130308060f010512130b04030503010306150608071b06020a020a03020c0d020906090405120318100c0203180406030c0906180c 83
    0x81c0c0001c144e03500415923820704000600355401c5800c81e030002c5814009031404002800703100c0b903c8009221080c2c40401040d410341e1a0040d4800c03150140000341a1108234030141241300d00103c60040c1035844901e00182003e10400442005065050b40000d4403800402d215103042140c1041036a8140c4a1500d0030200c20300c10b0030008002481c8035098041030484c131021421030010b0511442c465a40d240d80c0e036040d864240100c980c11191707421400750305802805007603000480b60f03400082c1c50800d211850208255564035204051b0018181400482c4850300340e5000211941424444d40950b4100f041da0710074041100d07542035010350301440641c0030a00d80e05007850780310341141c060000c0d14610b021004407103296500c1580e042c5041c103512464a6000340003480350900c0204020824020481600d500a5880c012200d8442c1000340101c0c50310f049680d0307907003c5002143c1c003c484460307680d990b502200091602e4403405185140350080ea114182040c401c1c000340090640368a81c075844141 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 665046807 1250 665045557 665045587
    0x10b0f0f0307231206011401030f0b030703050319020c0d061113030f0c060c0f030f09050a0b030702010501121e03090918030f111507261b0a05 63
    0x24001d4150186100100e4003c000d400c08041d00f5000102030040754548400b80844245011078412040e0021001480f13485c00c1c07009120300c0c0700d10918001c9034042518808900400d2809100c40c0d2602c5515800410080084040c00c010902956880c40c41c22002606a13124000c99201580c8002007240d41000902c003540030310340c3c2800c1710502a0400800f507002c030f0245052500241d0340d090800280c0c1c03041101030700f08900980360503e410000b4000c030b540d40052050460100070103000700c010612901600c5018060001c110040180d544d165599522103110f0380199490401035084c9070005ca1110000c11068406a90041c003014582041d4180310180349400c0400310108140c1c070f000004c1e0440d031030107018176a50300500c0607c00d45003685409000000d03099480c100f44080941c1c0c4440418020900c6030303407240750a10040316a55210011552100c01d004148000444e1035601040300410040703451084800f505904c50138180e4801040c0f503801405000000070701e0400868240788284 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 665048057 1250 665046807 665046829
    0xc080c060a0e01050106231b240c040506181f030209030c03031315030209100302091905031018050106500a0e09031e0301050109060507140d20010b0f 66
    0x103000c400c0c14000c8c80c44c41d28100030203038000d422000500550b1000c0c50240c8000d007a0006024600c02e840c1c140780001040480c0a0116202c0201c4a03030301301e40c130494885403036229482102c1d0410040104844d20050029040203020074001c3c03091031401000c070f0800100f00c44010300c0c1c44509070002443c0090469807411058082410160288020741d455143c14101d40c20b05015510050707101c0180f4424411201c3c0312006503008450802800c016944020441504480c4c0c8403001154103402c40b583d442284045010041c61036107080d9000600805e90460000c0341418010401144490701000e1041101d00910b40210701d0302c0c07489440844610980305808008c030207000485e4480d40c07042c1c44200004201d80031a12a0400200c2d850089c00000113462501c110500c101d0947d41040c0000341024001e02880080c080700041240502424181d044203072000e070030889080c0248850300400c41035620050812080c0c0024420a4070b03d010b0085140517400036011001b007904284c10002880d0342 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 665049307 1250 665048057 665048077
    0x11b0302010e0703060507110703081b12040801050618091e1c02010c0f0306030c03020f0a0e150f120a0206031902040e090c0109030f02010c080c060a0e0105010623 72
    0xb850304566200b510501c0220000c40c00351000050615180c400540364100d04510f4892541145100303000150001040d41e05100c2140d080b1b040400c5941007070b5240000c1280640d8445001041c002800d090540200c2e10030303030003616210100104140d00b00c40911069942001d0741d0030802c040030f00d5483c0c00708501005420301c021141d1040380243c40ba800d000c2c1c00d114403c0181d44428644258680100e0f103554006098941000b80038615150b01e0603507881404001c1c4a40112451000240c0c0c5007090240600040075801c1054241510a5210f484440d00e041c4e002d40811903004646241040c0c1d2248a400c6880140c82e8103c416400c02c0821380c0001d2210f60804400750b42c50084030210300c044c2000d442140803442050038400e044900d0101203c90041c104540d4003000c0c0b0018050300000080c450782801d101020703103814540301c1d0300350244510b41440c40c8245800c1050140098010300c82d0506801d000300300990321450222480c581020201301280d0308000c054410806034001450b0441e4 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 665050557 1250 665049307 665049311
    0x1210c030902180a0b010c0f060e0a1b0603060b030c0a0c020111190b0604060815060612041211010203090a02010c0c03020306040803011e050a17010e0d030623011b030201 75
    0xc0c0941c001812100700221800f880c000c000100720600401744644c1e0801a800d007012529010a59902d5105801075400104180e46401c10718140d880c040000c0d48485038000c0560004041c40140c4000320f40241c491500060306010002408e180100110f07030250401d03400c101c0c94407220034820380f030310b0440440890400c500d00804a400c50001c1c8100e82d040703c0c400110815440300390908500208010f012a40703ea407403c40108841003002918120010742e04880c00e840356555030008056000e0103821700d190007503110400040002c150418041d0100c0340c0c42d0112152405400c85080b40030841d100000e9070700c1144460301643c00303620000540d511650302c10405070346a5020a080c50360681c0c04a172802004001400080c1020901e800704005084910050030301c5d000c000754220b02a03218404031204200c5515500000a41281d14001c0007038044800254444200600400440c031402804004003618900362038007410702c500b482c2c0300503500c81d180e282c0c44c040b610300301400202c0103c01307640d = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 665051807 1250 665050557 665050571
    0x80904150b041202041406010c030828020405010318022808102a080c03041a0106021b06070b0a051f081b040c0f030519050c1801210c03 60
    0x902980c01800901155091240300005902c107000c240e0b4003000e09807820015240c108001c5980c000c206045c080d41518040542d62103450b984c0304403802c80c1c420f1030ce008400d002d00701c100004c4c035002401224000c0c2e0741048080c0c2200c0c002d0b00c3e40203d1003c000e60000c4500c44420714034400700726040c2001d5181100c403040c15a19100c25141104070551191003a844000c03004000002c886c0c02200b0129584074040e114070a10700080184c40700400780000d0b10808804142489414001096410551242d881c0e01e540c4415020b5a101c0300c02c2110355051801e1100c410b01400e200050b80e5815900520080150311141e203c403002d007100800500746820031007031006503115026106401000d00b880a05004190011100340c54421652140d0049040000c6d5103c540e900c1360445051110a14000841e030302c03442c0c1c015070040500c40c01e5a030854145401c1c40031404501c03000f04840490790090700c065a803a1001552420603c0000070800802c08481204078403168000c4228900700d45030024105d = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 665053057 1250 665051807 665051819
    0x90207030f27180b040e340b0a030b060c010e1002070803011716030803041118060904021c11030f01140403050c070902030f09010605240903070e01060503150405010308090415 77
    0x1c0d10354070f00f004650351041e800c040c138070000050712004004c1700380c000380450101051642c910140030720401265041c009040c4a040d40700352f02080c8c000308000c02c200c1d43c41d403c61182c0e0380070308201c1410728054050f1080014265043d4070032650710310b030f1215416003075a2030a507101104c122540081840740c0100c08003031400c07403500382c0d1190140d44954202500c03410719041c5800485100000325004a082c42c004c0181d40c0001000f590f803001040b03c09601555803480420b034a50780c155207079000d8034000748000b800c102090001e20307880d00040e4120384020003034620300ca081e1144400313004901c85500005c036000c60311074001882c00c415100b0031103950036030382e01c403a50490740100d134180a100701100500c90100c400303010b21030081508895040d0000384e61080404410b81e207200340e6100f81e0001446140076101400380100034144414041a19a901e070000b401640c13085914000c10b5400b201c8000c194500346c403905041c1c9401c1180e84d4205070042041c40700034a400d0120206040380c1c07150004503 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 665054307 1250 665053057 665053061
    0xc0a0219080f060708011e05041e020d06061d0f01080c04150c020102241302040609020304030e090a15090c031d07060e0301090807060b0a090207030f27180b04 70
    0x2540142d100106030341e20301000d00505400c0183c00c01414001a00d56089805a6a005100030350b20112000514061204400030842d000c000c0c0c50f07100c0c1400424221100034096100f00e00701c605644503100780824203060340f28024004601582e00c6500803095008ca544103005444d800011568407901d00340e12008038402c050740314200400011000c0e5080170442d6418400207201c0c04984903881300c90f0300b003041211000307030740180400164140c404c1548250f54403a000300b0f000748140c803c2150350382041d080040a072109958082e000f2f40d030601c08980c1804503031045400b01c0351486040c3c40904e00342001d0001512485407404101a110f864200c010f040c0183c10300480d0014500a0420614001028201c0030307000443c14480d0b4940300000010034602c4040703c003034070307804003000031219007a80c00118070401039080114001d2000c01c0d00000c16401072801c400003000e50312025540da40042d952802c0420b0000f03030140d900107560080101c0d008280c140e40350f40340c40f040046588031340c900c08141 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 665055557 1250 665054307 665054323
    0x1412030403050a1208041a0a061a1e0403050705010807200f07080d0e0d0314040605030f06060403081206150703020102071b03021f03090b01080a0c08030c0a021908 72
    0xc0c40c3e00080101c104128901c03020504480e000e0610503000d10741030700c8040c01c51a6001920700902c00840c0000c01110b4154010350103070113200072203451400c3d03060210405801c00070002444032825180310602060b50030683e402ca80d4001c0050240f503003448011184600c01406d11010700c07000c021608800754103840d50074103900c41a00140800c0d000081c08514140980d03015195070341004030880c8989601102c000c0c03040f50141c50302c1041e1682444c0440314210500ba17a0f04042c00b02080101e00746034420000c6002d4051940302c08401d1707e400c0108505072050340701c0104566400c10000840c081400d080c80c0d40401c00401404d032425041c44510b11980c04401c040300103035030000c5c05200308092103140e08010000d80c2c00c260070590031540440c2c038035920ad840e1507800074007040150514900c03981009080d564054410f0944d96901d10b8040c2d43c0d0009140100c1c0d9041014402003070707409001003501d2903005003600a0405c4c2020381c0901c8400f0716444d1110000012800001c80d002d04200322900c = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 665056807 1250 665055557 665055563
    0x207060b040c03050901050705030601020d0e0307090e0615030c010e0f04151413050402010c081b0703080d0c0f051e0d050408270121020d0606080604060515041412030403 75
    0xc50030340b805001680c2100c40c0100788c041400024800d11004d80d900041070040500c19040030720300140103900184c50603610390311070f0498504082240c41030420200b8000d010710703440480e180801d813546d010540c485e042c0e078810500040315002600d08a280c84249980841c1c0060300c0004c06818041c65100c100c1d4a6812001e0b0702c0b4008110003183d0306108100c02c600c3d075505502006241420360000313000c0c55546001a048082c042804803480214154403064203190404079498641c1c3d0b07150281041d0003900000c840d0310301d840300d03900740c85001d21030003620015181d54040c5441072150703900c948001e924003180d600b50001c0c0202c02c040103151040700c2c0540d000390303802a00c62042e6845048441040400d41031b4500040c1c410b00b0499030415005840110210400c48013803151040400003806948005c1c181542824400100b00350070030251400784100303540a0140c59190070903c0002d80f4042c81100440034104820020400480701e1008900030003007c02200d00c42c1070b07010a10310741240d0026 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 665058057 1250 665056807 665056811
    0x5100c050d1521050a06023006090c03070903120504030209242d1813060b010c0c0509060d0c03051c0e1305061c0c050310020c030d0207060b040c03 65
    0x5000e100070385070711268042520422460006055910303913884884003440108080d40219500481c9519101c02250820541c4e000608c00840d0f4999003e61400503101540603540e40303004286494030704802c036485041207031520040f1924680d2014215900900f0302c030204030042c040440142da400c0700d024024641386a5160004100d00d544629050409102ea80b1800000c11086540b01e00c444d40c0c0800d0244000001a5030001e5030007280c50f41445d84544644103060760100541c1c0540c10302c40c3e925141c000c000410800340200d0042d90120346110020f4000b04c10048100700318078101c0ca000b64450000381200100340d040da91042c401d04440d4104403103035000b03290b03882c2900d881d1009070031010380309141c00c401040030032000c5030007039040c0c41c07602c0c400c0e5440d040000d02c00d4030f803107500701090104015071804000c00c1c0c0c104020607241c40c1c01510722a01030b1702500e098022440c02907c403421140000b031032808410401c114000d61180d002155655200c500d03c240c07a030340d140314812551a040e240 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 665059307 1250 665058057 665058059
    0x304020a0b0a0f050f1201030605040506060103060609031416030c1503090b01090510050909010f0e0303060307060813080a171e010b0a0c0b010f15050705100c050d15 73
    0x10000280d50942000030615024060040315a038400e1194014141ca82007181d950180c20088465500c41c00f00e140108080d03e0000004200c1c0682c0400d1042e805041921080c0c0ca42c0b100443c107841d618403601c400a800c4083c28400702d884604403042e5074900340c086640b204014804805030510b1580162080707400d0301410414031580541d80c0c050004540750400c1072000654840001e0201030044034a1140c2d0b81c0c000030007484800500c8070140400134482929850022840f0380a008901800c408241c104001c0102d40c00d00042501d005441c000c0140808605180045403803c130b0041854103409002100c5401003400034004020030403480d0303030721721a0900c014092040420040c0c028090204580c4800c191721a0b4031481305d0645404801482c3e071260800300c2115030300240807010f00041041800000c001c4a05401d250459050704502034040d80007070b20a485500401c240501a5040b404101031450340d40e900044050f2543d0030300c0c1d810021030b000e0782012140d0711491003100001c40343c0 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 665060557 1250 665059307 665059309
    0x260a0b01030510020a021c0c05070905090127062304060f05010602160e07051b010501050a150e0f060d0e1b060a0516080c0a11090a0e0c09270102030402 67
    0x122100f90000906815407400361112002562401d000c02c1241501c1a0321100b64805071160f040d0141c4550804200c400d51a226048000240701c00e503116082e541c6001c048003240c14000c2e140309202c4181c03800080424580d501c60001a10700d5180801b40068025036410109104403056401180181c60004803183c03480c0b030764000c0b0703035060b0003441c00d5612040c0030706a115014042c610564103158003444080d140c1c590195106e00602440c4000d0b062803002107402c0440540c4824100c0e00704a558010059407021841c1c0301620f001e501d840003581c2c401500c0601d08281013034020042c80900101d02d4564403c40100131100701088641c5540c1080f9049101d410f07040d120002c0040044414618121208001408521800e030300300540c1000740c45448140b02d0b1403c00e407960580220162034141400e4076290007080300d50100700c1d00c903d4440c40030a1755802c0300d01c100f2001201c400028004500c182e81000016030000f0303c003001404003002c000c3d51091030f14006041030407200c0300150f00d130f080ad84 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 665061807 1250 665060557 665060563
    0x3050306030c18061908011107152c07051e1203042303030f21011a03070c02120d0908070e090715020a060c05091801050a260a0b010305 60
    0x2c0c0d80d80344601c0d0750307600e03088410b4200c0080c19004181218544119a20081038030000c418903032203c1c10759460481c40d80120b1002d10005c0140e1407041d41d0841c0d046000800f6541103602e1f051484000c200d0701c902c40038005180d0180c440c010038408080f500390b03543e00d00003e207115218030045034001d08004106589403d00308100c3d5040078103072001d50b040c5420400d959102059054007000c40000600c2d082c5140d4406004680c020018003a282e5650310483d0400c5140d403904007075413610b00c81c00000024001c8031810101d01540d81c0e03081c842e4603546483c1401c031440c044240381660b1243d8030001c80c6501c82c80030000325036465169102c03198841e01d04180c140c2400c005d5030024082c8180c200c108050120041010000c1d40c00e502d003044004c0c03038403d00c01c034540000c1c40e000070215032808079454549600b11010301000d40c0c045a600208000404c9050782d050020b104042d04440b80040500c030201c001040200310b10881d101520b244100105202d1600b130014000365840c22161005009002080c = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 665063057 1250 665061807 665061823
    0x204051b091e0a0e01150c02010507060b130e0f15040b0103060c050d150e0109090201170c2107020d0512040809041b020105150109060e090c070f0305030603 69
    0x8030003000310031640201500d0300c10818207500c1407503030040350008408600c1100d031039104082c203074000003500d4840b40040e481d802c0c0680403a01081c92551054240301d2900c00f4140c5a060351054240603c542c0c42c44054902408181d600c002c0c50044003a824000d031003000e400c03c02c0300c0b0040c24032a460145160602c09506c0020614413034010801010508038091141181e501c460000790301101d0807002c0307405010b075030013803203090b42040c441400f0018466030290954460f030383c3d001c0103642d07910b8000c4100d4030001030007400300701e640041c1001c001e5000426580294542110380c50410750003002c03c9500b40f01c003a00c0042c4440702040c840e520364100f01410080e412418a00d107030081c440b41900c40c440c002080103040c4280024800b0301d54882c0e41001041c06031000d22050600d9105002a004e41411a41001d102d00781c40013040703142d03100c0c0c10040c0c201d494585551100e00740110510203044001050402100c5040020710001a017600a5034401402942c815840381081d604140c01e040b45 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 665064307 1250 665063057 665063071
    0x20d020a030c031a0a0b09030a02090703060503070b0702090f061c060f0b0a23010e060313031e0e04050c090a03030206180a1505070c051b040e010e03030105210613020405 75
    0x1480f41c0100c84c9840c0ca05da0b003825942d081880940743c00040d00042c0c540300720b126000350070450703513400d21041580540010051380c804400751442292918201080760203201d4001c0e500402d05000316022800c58029590018006491343c4981046015502003601d01720000b1148640c0d00c001584010949206500034a2000c40300a000d8602d498941d810f65203003100c00d05030b441c0f228101f00b84568040c00140010000182059841b031409503c1c4071201d8940400550110352a210046016020350011b488100300949174050441c2d8107405000003487d009051441017181042820a282e80310550340700114404e0b40102100d142c1405e103a455020904489425a400907042400044120703203c030700440c0e000c5000040c03950359074404640d101c031400070250490090152074011131400000944941c101600c0501095216190480c00c0351104c0a4945150b0414070042c41103189c86400140843c4e0b82e070f4060703c02141c10b20462414502c0645200b52014800e030025000c43c1804c2c0203460b80814 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 665065557 1250 665064307 665064341
    0x60e01050130090606080d17011203022b020d1412130b0c030114010509030a020d0f08031003030f050307080609091516020610030503040302090406020d020a030c03 72
    0x1241000190804075a408400d5090303000401d03200035804804079410081d6010b80c400d020206180c2020b02c01050103000f84c5100c3e000c0c404603d030410740500c00c040740000700c002c51400b150f031915501030280340c06032008400314028008420030381340790301011009080c1c0c02e615003050240c8208001e07251002c0c001c031040510803408583c00d041e15001082e00e03c0b08204c5150040f56550b020302011040c01c1001d0010103043e00ca03030500c007903400311802440c1a10880301030401e03840d60142c0107591500903850056450f9100018072001420441082c04032503201e4000700d0150340c403c4d074840074140c05c1114111015581e0741000c2040c1a40000b8000d08110941040d81ca581032a00004280c5000145201e00900e008400304891500402c00c0e1503258681240280e018100003c2c1043c03140c208a143c279006104a4000c60002c01c2c0c054424000c503076100e00250724040c60f41c0e09011103040700403c2501d500d6400d010b0710f01d20f50b281340003c181c0ca919a940000b00180400c4c2c000e0200c0e011424000d400b91 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 665066807 1250 665065557 665065559
    0xd08250506071e090e1012050a0b0a0e030d0b180a0c0816020d0305091606030209090603010e0307060f0f060e06040c030c0c080d0f15180212071808031b01060e01 71
    0x9070b04180c0d460252500034207445d10940c1d5501e5940d200c001385900110040b8075812100e000d002000c03401803000d910031140d18007191203003035108050f99081c1914007101e030820021611023003a140d1011000c43e00c06042038a0a10480840e0399040600304d0b04d440345240c694580d00c0c0c0c1283e2003076550368001c048007409080070400041c001c5da21a0211650700601d540e4001042c1051000c009071529000102c01d04601e4680382c150040103500945103480c021a400710200301c6c41d01e010f0141c850071145140085003403947d581c4800001d41205400103440c00d690b0007d00d070021200707015030030140c14550104007281c01c12100780021120f0750700c00a000c00d07103050504480c050f4003181461303846410601c901e45800c9800b00f10b100920322034945000c401c0c035040d01540c44028102d0b4540840b5581c45045100e40d58491207402684141105104144001c1d80003d134494054030309410000240c40c004136140da02c40c0700040c9964010b4141e10361101c1c502d81058100a0709004440c06005140000c01140d = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 665068057 1250 665066807 665066867
    0x604090b04030809070503030f09030c040e190804081e0c01322203030f0509030c010c0615180c0207031a2203030903120b0d0825050607 60
    0x1110001d0001001c0102c40400303d05a50340800428014200c01000c2d03d07900c814804c20741c506030b0700c6a81d907180030b0700914150540501d02407044850640c6c00d88003900c2111081003014400c910421001c4440312014440803410390310410102441110341c03815250a00c5a05118903e050100002e05040040000c4114140c500c48885540d00368984200d8a0700e011070100f4115503402104882182d2005144810111150100c40c0c003003168060744070250f070002d02200484862084282c0076030158842010507000b94410b040b45c04d202c60007212300013a50040c003410050801d04580c01824604645200810040a1881030807958425400201103d030314503a03510400318015040400456589000910390160582410010340741e0754507000d074000101e03d07029005107000d5070103400141c0012040c42a035401d41c03084404501e0014414090140144e9440b1a6075000075540c1c415038501e9100c00289030701c1801c01110b0a0b1190001d041203182502e801049510b00240e12a03003000044101110 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 665069307 1250 665068057 665068073
    0xf0b06090a090215160609050a0b0606030c19090503030307090f05040c0824030a08030f0705180d0203030c01060b030105040b040203040f1101020c0a0602030c0d03020c0c0405130f1505060409 84
    0xa500e4020704c1a40e103500665000c20303900503000c0d8000d080785040440328401c114001c144103e41600c11940d0102179103c01e024400140030441e41c51000c04800c120720400c040880c0500105022903151040c49c80382c540022904580050b1100070106561980a01900d505070007500c0c0a0301e01682c0810100c04880c0b802402c0d100302070040003100c82e900580b40001c103018014841c0404000d012a0751245407494203400310303030048903014a0588a9408140c52500c12000c58014040866840044003590010030030320360705100c01241d151004110141c2c091800b8040c1000034110114089d44944c0740209110954110046161146104204000001d40703104025174605420006c59800ca000000050303180c05450240300c3c1e44802c0508002079a141d000004240700c410070002c0d0796283c482840c0503001d0b03001d0808440255089142500c4480c20140e0202c0d5104001a60f650300c9950380b5282c844a0314034200068402069400300f00841e042035001e65904000d041d03d04010140850701c682030 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 665070557 1250 665069307 665069329
    0x6040c090e04060f0c020307030305070503100302010f17100302120705060f0f0708120711010b22020d090c0602060906010605040512010b180a1401260304030f0b06090a0902 76
    0xc1c00d5120480030805000c0c0551280c002543d80070401c105c1251782c442d006c0e41e82c1c0c024103011000070b41084000f0700c1541c400c00c150380c0501c2c1e0009003941e47e54216401074661080d40e41c02c0f60100a4541d02104003060a070b0140b90180104004900c206401e40c010f00228540604002401d680280b400300b2490b00c54030304640581c0c0c0c42038a5030f82c640030602c2860303030148161803003c0d010580c00b203410b02d82c10900410303ca000340c3c80e684909485026010515081c3d907420686a07520890001d8100b1418a0080c50f5203020100c08100518110010001c0811915100b8054640c05d4241070148041501080030580105214004110961520500a0540c41107024141c0030b482d03a224004690f10b002d401c11800001d004100343e007440f0b40354410860000c0300f1101c8503265400c004048640c5502c80a0580c183c582c0700159603d008600406200420704800400915100400000001c070743c914102c0504580300d10400050781c1017031010000b41140203800740180785e00c0c05100b4001030340c0c0e05500c21 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 665071807 1250 665070557 665070569
    0x60f07020c03011407210e03030105120c130209120a05070f08070b0a0e0411070f0b0606070503030f0717010612050105011d040f060f080a050708150106030e0a140309040506040c09 79
    0x401303140300d906c00c1010f00712412200d00381c414181000407010340d101001440c1130301e40986102e21211804005030795240c1d084e801c940d4001040100c0f45014000e42d400030600c11f100600740410307030b000e81d022980c0b8054904005079400c0d00002810712144901c0c0404400a092a000403d542401d1042042291003410a00c070b00340710031541341120a880b40d070407000030110034000954403a201401c002403c0c00e00314508495400d0040c000504901d0120b00b07a803001c0d50040d0042d415580e48242002e41400094058800e12145044855040042c2c2032440e020700782076610f4034840070074051824290741c01a04030364103000f02003141c1204900d1580c0540050389048034046035441003414200300814032a00308424040b079075140840c041c0b2000550340c10a0f4440d008482503260780c0c5c080c42340c590a80c013103030344040000b08004018041c03198106240e40b0b00d0800507034031103289541d03c0c503444484410303141090342c20214100300c0500d058400c15600003030648091120202c07811006200d9400741c0148 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 665073057 1250 665071807 665071817
    0x912090e0f0403090e0f090d0504080705010528021c090308032a030115090b030601170a0b0301091a0f0f0c0a09050a03061b09030209070e060c060f07020c03011407 72
    0xc06041c4100300110045c040f50b0351030030550801d6011007880260449812041d84500411000c145102e20100c504407842c10300504a018205001168a940011000303514104031007826010341d81ca06100c140e401c00b658000340552400ca8840254488801985505110712101c0410216880c602240e80c0025007045500c09100c1c1d12520100101a00900c3c031158040400003040340300180403034800d001c0d49522480d4006541c2d10021030284012143c060001d90001024041d1840041689810000303407400881d081510f030020078215100c002e01620085489000f1010105001803d103401520a410b40d031414034054140c069a070070302070300446002500103905d880d01403240e840d01c400b5010003030914404030f035281041000782070100b80024442800002c5516410b0062411808696001e48078840654510070190f50000603d07410341d4200100300107412503000c0911040c0d20501c81c4405034665030405040c024585221030300380b9400b0b0b80c54030300d0b0f016215141c0503100c0d40c808054034107 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 665074307 1250 665073057 665073061
    0xf160905040c021501060810090204050609360411010215060118030b10150203040f0302060711210f0c01020a060c020708030307020d08071b0f0c05030706030912090e0f 74
    0xc00ca240025030942c84e0b40c01d190b1140042070031a481142036001d217480c3c02d0111015070702c030300703c4508034413a501c155644540100300203089400d103905a4858000300d05034000304150000b0000d4140107200122130110364402e41004100445000c0324112103400b17200809103081c221016900141000d82801d06111160002c0d000320244001414003856022001800505103d9603500d12041d035401206000e001101d40c1c9450f662000054400b01e8000100e05840280341d43c0030f208590f070298006981d0380a408040341455140e030030016004a0300c01d014a00f1000c1980b41107030a06c1404c40f425201500310044401d056030380020707104102500101c0005800c0784110040e0300c1e101281d13015824600000c0204400c00b6000b181c0108a10a240c990407a9a035030b914045515120400c2004400358024500c00003041e42c41e031040d8030507445440700801c89515040024901b9070183e1008c80001d07121000481044046610030910300a6030820300c40c02818900d080c0060300340104010582d43e08040 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 665075557 1250 665074307 665074331
    0x5030a09020a1502100606171b04170a050d300603020d03021b01140414040b1e011715010c050c09040c06170903090d0611040e0f16090504 61
    0x7180402880c07040c00c0c4100f640b40700301010f0344585c19036075200b10280c0b9103440050b80d6030180c945401c800990400b402d0300e959a49003024920315800c3c90910b0b10500500010621030250858200c00d051030384001c01c0e04030b00300e117003161609054102c003100b00b04807111a40c90402041062440207544002d0000100e0025400c0301d004124030744c006540b0110300d141407000d06030049114010225440800c41d4804034110041d6411030900e0303c585180c00c8100800c1216089042169074014801880070501810603800140102403281e88170215070908109a0115a085200403035640320701944420a880d000f010003a20501d10f140305030601c08034100400400100380140404000010a091041d080c00e081004003200382d4010213012403904a0407904080718210503510581d01100254038001c40481070003d0b60840010440e070042e16003461801c41d10750031010700007070002418001d245140c83c00080d8000311014009007812404098480104d80d130094040c4c080c0c420581340402c0d0741641c80 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 665076807 1250 665075557 665075569
    0x405010c050a020411030f130302120c19050607110601080c28090c08070305100311060706050a050a0605060c03040e070c060c02061b090d0f0203150907210305030a0902 74
    0x1002540117240c05094003601c12000c0c007540c09417080c03040702c44442c2c1d0351944003003003410001c2c009070240e441300c4d06034140030310180014002c0c509602c0a445c03141240091074008411030984c11901500b0442c1003110303490703006105075460150400107100d40c0d4542401d041e107462181e22000e000b010b014081043c800c488450b07205e0900308000a0300c43c640d545030f4840c030040c0034103000301001400500204039414401c7c05811702641054000c50203051455448043d149024441c668000c0310520106000c02c185104083c404d500740000400c2d50310300400000202d409a0b00b116204010600c0085075800d000802ea82c15601541810101511108002c0e246645043c80041c070403410940500b040940c041116801440c10281005c000c0c03030351600f01c10050103108295034029250041c0c074004500301303a442d001460b0010302601c1001e40d00c00060101c1c480d007118004c132207500c00c8000b04a0744503090888400700344820054648098144d030014007610000d4850703003800c0e45854211003555100 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 665078057 1250 665076807 665076823
    0x231008030a09031b052112120105040b030d05070b09073b010803180f0901030b0702250b03190609140105030a0210080c0c071212140405010c05 63
    0x89048a807106038080c1c0052690310607000880300b0304803141c049480a40d000d0711120a45030010212203038901c424001c0e0304440a45042e100b214860302c900c0c10942131819005126a0180306c0c0c0c0c1002075810081070001741e400b4001305a000c1d41c011803036100501c0e406019241550b6221035444003039200c04108a00d0728407113400016500507820382ca80c160f080c6483d1101a20550004070100601405440c1d648900e024440c06120f60410840007110120200d10740401490003060103013151450800b0480c0114242c10403150640740c041071081c4950108040740314008402d9001c2c185200b009550b103140d41e010b00c01d000003d0008000b2480090f1045c00044604800d04010005aa0b0724002c00001e4040d8036080000a91514004900d41c10045020b490303958001e0b10b0740c1945210384004840c2450000c0081500d584140480c3d54010814894000105861403084004006508002118004c0b0266401c10300c000081c4804001480c030b4103940444009007804101400c090070b2541c100440 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 665079307 1250 665078057 665078069
    0x703030e03040f03120f020d0c05010f0e0f0712380a15080f0304050f210a020111150403081e190b1504030204050c04030b04060c122310 60
    0x804100443e480740c00c401c16808480c0035084c0700c248010000c2080d2207848101001c5801138124070f203070410b2540181000000c0300e1103840000703109980d0b00f05460854000064024540e0402498001d83c1d010070400c410140c102e00d00790340300001e402e42d039400c05030390040c21000c40803a58800c456240780060b0b400062a1001c00790966451400494100081040404000319002c40b07032004125a01d00184942c5980300440040d45014184800c00480301c1e032410300540d01080c080844110b00811601824042000c81c00400516195200140c080221040c595002d0340c03218404611300381c88039001c1c9401030740505204502e901c0b0500c9042902030440d4949201003048020303c00c1c07061500e50500c1d1070002440c3c4c100916070070207040010034407440942e041c0c9103406010030f1025144c00d901071600030080e02040c600d801e980b9a00d041101904440542c0d41550350755084907095080503040c010000003000030000080c0032498800d4200780850f04e640300458400015070320301040b80c608405010 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 665080557 1250 665079307 665079313
    0x130203040308041b080a20120c0301060b180904030e0a0f051014040e1906121401180818040e030406121109101202040609030c0b0703080402060703030e 67
    0x140504010784180403c2c2c408030707210001546840e4405403075103004010b48164402400c4006042e40302e401c0119502e002c612160901032072181210340d07902d510340ca4400d400307901402c8540d4210040500f120050303407021515a40030031154542002c114022400f40030211a1900d03213440c0c1d410121101c00882c2c901c1600036842d40310100d840c0c0320000398401211001c541c01d5800010149041b1070901004030a420101020300042c40850b840d8071220754400304000704104640c1c1d4010304034007542d80d01c0e0300240703512407013200d010244001d0200383d60140445030000e200c40c1d03422424451080b0002c01003d4601000452a072487d14600d59159101210040c010701c8009032151046490b54490b00c9814042114401145e4140c0385034001d68207480641800740e41072800c0e00060240200381441e001c0c0800801040310244900d1502c0030700003074016991425111815072500c140414910f4100c0c1c46c62400030f2105d01d0000ea80314100301d600c03030fa0607140e00361181c09618003078020b803100100405d0540 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 665081807 1250 665080557 665080561
    0x70b030a0207111c0314210609060a03030212091903062403030e060c030c0706050a020f03160201030902030a150c0f171f0b0705160b0423130203 64
    0x8100ca40281a1140c05184400d03104803c480401100c1560507150300c4080c2000740012020038080c4091107204074102134502d141410754103241c02c039070f00e10011224100881406028460034100003141c0d01403020b551407202241152001f032f5035142951003c24101c0c3e400102c098150701d0b100e490703400c51410100c05801d03460700c1e494001d01800c0d00c1310002d44c0d03c0e0006a52030205107040740001c81200e4064680d110380e070404500b4411a54452100fa001902c0200a00c040c6030800b04500c200500700d980d44c00d03454422065000b400d00c00c104c0a5500c40c0e90050102d24922411074090480d40b076424200040c040d40d0b1440071030b041141140000c1c04001103003076002601d40403608a61303000d0000340d494200010090f00103a440b1080710464404440610000400c0ad04030307208480007040e02c10b00e514030781c0c035613856801c995076001a40488442d001004030040c075040c0c0788141c07006401c10080c1142054202090700303280101003504411a6100c0501d4104503407504103407200f01403900d80c0103658138 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 665083057 1250 665081807 665081821
    0x20f010e0a05010c080112020906010302210402090703020a0e060702040e03030703090b0105041116110411120705040b0d020d1404060b3a0c0e090f1b0f06030702070b03 74
    0x6400a620540b955401c0500071a1524881d80703a8070f040e41c101d9040d840801300d1680070310103550402440c25050680c06c00500d8200d612580c1d8902e4214041e0014201504e4180b040c051400301c081d113041c06260041c02181003158112003200d10402c000d4405d20344540d010700004018024100607800c03280400010b0081460385501300b1980d4a02480003148582da030f60003400110b869102c040742030f00c40140160364a401408101e005181e004603a000301d254407420020f812201034412000302c26400050729403052020013821940300d0a9410181d061614140e0400e020b4820010400310441d80007a8110b10100709a100203010080c08040e40c0c001c3c07415140c2000140f03848040940305203446150038001d4081201c41c024030300d50000c02080141024108040302c00c40c1c148013228001d6240d040070500407400c0440380d00c144c0e000c400622105044918140c14507a00c00c00c0c3d0144504000c02c521003c1d00c036201d555543d01000d0300d40c0e03a43e030390700c00104034140001a04100c2c0c20000000510000b = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 665084307 1250 665083057 665083063
    0x509130c06090f06050a090501030203070315060306140a0305190507030b07031e06030305040603020c03092812020a0b1b1c020f0105012d0e0f0117150a020a020f010e 73
    0x3951141e0f564036050a44a0300292090f004d5520364600003601c0c00700504c020b508c280c0156410135454200070402950b041c01441da000c0c501c1d081100020740e9134001700302c11203050303070a0380241d0401c0e5114541941113445182e1160404480d9050200c0b840361030b1000c11004001c41401507410902542042c2802d001c02400b9028401c0d0104004007411074449400409200302e60449500d61240c47c03409143c5042074002e5000745280800c0f0340010302203514580c89040e40d000700b40317110007102090a983c1c1101440b03041c5c000d41100d4060310941c00c20308010b85500e00c075901502c182c09022900c4000c5001d0600700245c05c00c694130054000da105514120843c020711081c42e08890b026070b640e4460034901c03036080390024858492104640d040c2c1c40200c1e400d81031071040092030300c0c01c00c4010b52380341d0400c810b56140a0700d920324100104801005202406401e0818110304c0c000581008026140110030740340001d49180c40066000504003600c5000b00f012841c4542030308028002005507d4050361 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 665085557 1250 665084307 665084309
    0x20c07060e060f040920190809010e10051f080309060706061511070b0901020a0602090f030d08040c0b0f030402130b10021b010903170306010203070b01080d110609070509130c0609 79
    0x40d1440001c3d01b01d10a03034111005456168900c5204d8003c1d0810003801160300c0a005444180c255507520301c448501d039424056094854041b40020440c0d00f0b02000d6030280110342400f0001e4030380c080c0420311000c00048122101110210381c01a1541520b04000c401417510781c3c0192400021500a4000c10303400a120031000040300b01582c7c11541d035680f01c0352640c81440300242c010303000540301c100043e1040d8054402d080c8007401814030f000d242004a8500b2000000e040082503826080004000768140806c0c0548100d410b6107007410b000d0580035009000c040c00081c8030345152001d005d02c0c0511544484040300004205009034090814080e407103000690b0311100d0604c045075840903e500a40c032200440f07a01651081c0d00c08441c6c105038840350000341c50b0a0450104102540c0410150120180a01005000340030306840e070a001500140ca0503008641039000441000000303080440d0001c11102c054800500540c1d40075600e80480c0100540203010280b0402c01182035603001c0e903020 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 665086807 1250 665085557 665085581
    0x90201170c0909250906090608040501090c06120606171503010b1e01031a010203030612010b03163210030e030c01090201080714030a020a0302090a080c1003020c07060e060f0409 78
    0x4450320041d500b080f6030110450060b1b102040060f4000c00c546e034418010258441d0042000003041c103001c0d070716441c08103c00e0f4443c40000e105500e1900203200d84e8800e2000809860a02200c8402011442c043c45d40c00109520206905050340c641c0700c0d10290070035085504014000070f000f200d0021400c044002289040f170000e85880701700c0001c81c09062030020a41c42c142c00460840d0340702c4080003102040420700c001d081d5200c07800661b25417810000c002d81c410701401210703005414000461070300c0c1500c001406d038217940d114103901c00002e4007403211520300c8103030741040512100314015006003802c4031141c20140300005e44100595419403000810600c00d0303071a1310440d12001003c5903203260804045150400410110782e01404035801402540c505040160034141001c2c0002c402c03020030361104140f03070089407080e00c00d850031010400601506040c11030412800400e000d03540d010900820782488588600120310741d9480b4140e410b07000b0440622070740e49458007041005425040d20513 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 665088057 1250 665086807 665086861
    0xb0c03010914130f020d06060b0405091e060105090a0e10030b090609030904020d0b22060603060f0e070c0f05030c1209100c021f020c0a0801090201170c0909 69
    0xa0082a60b454203901580580f00d40d41210502500c1d0225052070303035481281e01c0054000c3d844005012070040500520146642546440c507000500c5203807a802031510350b001a0003d9010300c003031100c070001074110f03100381381150311102c113540403500c0e0300d80c3d80d044180003131510010050411211046001030328800d0300c4072003060315000e41c455036820090b584201c05400030310171104541041e9000e0142782c003d0000202c2ca0b09030f1341c0b02040713141000c64004041000d144010ba4819055401108000d01032490700b040654035100d24101034400314014500204030300000b19824612403500b202d8900e411040f40300d0702c0395051403e1540c1e40c4c480350b400d4800b40240c4046402d8884d400050741c540b518040c201e00c2600c00c03003c0e8120b613000070919003241d10489101c130305030819034001c2d02c00c03c01c0d0000c0d40081400040001c108009160070b40d0044039240c0c1448000e10060740e004005c801e031704041f242e522000d500c034950b40d03540a01404a480307400003040002c000762040c203024401c0080100c1585 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 665089307 1250 665088057 665088071
    0x12030807093204020906030103031202041710050609060a06031e11070c090c0e0f0a090f0f050c0a140c0a05030a09050126161206031109070305010821070b0c030109 72
    0x610044c1e024444441c2e900500600041010a0195501240101034018018a4a42ca501a41c0030381d012050500510f980300342c081d50030a40e064414103401090840e0200780929080340000d0b4034075102c1c0112000c1648400b1a01056001c101c3c800903000c0c001482030040807245280e81c0d0b010b400c1500d06440809010b00d002510785981c0c800e100800f081d654450014062078028443c141c0000001950410101000008c028205201e003148007124032001041413041c0100d82402d035035014141c0d0f9848241003049120141c1c01a0320001c0c61214407070340030f80f1210302510142c100301c0b030108090014040050520322855205181c201642c100340c890442480d41010401c0d26010414402d032a84098040800c40c9070140b044405507401c1189020702c0c5009444940c2e00c142c402c40e500840b08a0312030501000e0324508440d145521020614040101d985407000481e07940c0c401c01d00e030308000190811641842103801007280d2510f0740244d003e000600301250700d91441c0d4001d101d8004441d1929030 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 665090557 1250 665089307 665089309
    0x122a0108010608150d291f0b0d09030c080f07060e06090a03030e010f020d0501090b090f04030309031716020f01060f03020f0a050306040b150109120308070932 70
    0x2a600030350f5103034440301241d10180d00340402000c507a0030503034180c0d1900d400c0300c0c1084580101c00d404d0f9012186d900074241404207035051218440d40008007490a003040500009030210b05503074615a01d45000706446920341005c0d6050166080c000d840f11800150740803240222a000704122840b41c5410044402e07124459901c0f00b4054542c0304146e001411904003107403098001010701a2114000030708003002e0001441260f0003e100590280d0300d4400410041e00b45201d05215a4400d1359503820501c1d08590304000c0304c02c000c0c4000c09240e40c5201050a062065140322550041155848400c0c205040c85640c0306888000b000700502c01d65084145841040c0165421246c104040c0300300e450540d802c2200d241c02144e2203540110080d10009480c0d034007008014011405040c41c6030440c1031211088030044043c5941c030307040c044060b10801c01403440d00b40044280d40c00d403a011810707481e061030485865070994403074a085011a480c2529802c41001004a40b814010b5070300e5411207858 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 665091807 1250 665090557 665090567
    0x307050d080a06032102031605070305010c030b01090b0d0b040207080c0f0d0c03050306040f0603200d080405040c0e1017062e03150b12090703050705122a01080106 72
    0x1000080041800c2c1c14041c04517003c110316440b002c40d450061700e041802c0c100b0070420603085614161043ea101150030005d002e07080c4528098440e252030140492080340002910508143c407400c14480400075010505400d1a4003911500300d000308203554403029424660034581200a080341d20b0f01810004002107040083c1d035031a51046502c0e10f0450510503102550b25800c0188400c0c3c010b51500a0245118032600c01c15010354810f0845454440f048500e003440280100d40d968041e035080ca402601103032500080c1c50866070111004500150024070442c0c18401041b42241c000701c8560000324080d03000261100c4051003c80c3ea0400c56036007004000c07101c0c00172a4400c22205035481020110000e107910b0140311507590a011515046185500c05070114962008903a01c002141ca260407624a400e42c6421400b164000c0c100c80742581c030792503100e110b24890f80e40b082e600490b4000043d6402d00503501807645460f00803c86041c200c00c0c1c001241d03c0c0640040c0025091800800c0080c09a = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 665093057 1250 665091807 665091809
    0x90311011503111201090507290c0703060903020c1306090b0405041109090a05160f06020a170a120905030406020105060307060903021c120e030c060a2309030307050d080a06 76
    0x40f00031494680100244219000950080c0d080b0b0354843e1540c0f800f140080145038020800440d00d152802c103c20000504a2040b10006080403010041000443d40014060081c1d9821500c00102c075205494180e1402c0700c6050300c250440c102e003107001e54211880d840b03001140c0b1307190410300072020f2000030841140c0f012a40200700c42c20008140001d8100b0b083c0e600c1e0700c496040e0171116104565240c10349020306680441d00d985860032020301940d40294244401042240002d1813004800c0e51040c441c4460030842c20300c10303003003c01e50410143c441c0c12030320980f8580401c01c004d80d1105041c040e8480c0d1141c0160005503003041701245c2c640c100002e80004840840d039624081c41d0442d4208805503580d0314680d0400103803041c108001c240c0c5034028107030000b84e544071100088002d90a0506240744200d0b4907116080600c9407110380c0b90042c0d011541513040d10f0b450701d403160718101300c0c89060041c0e000f201e40521000c03030705c0001c00c04001000d005503102394407007240307540d01c00e2500d0042e2062 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 665094307 1250 665093057 665093063
    0xb0109080c0604031202070503031611010804050312061f08040c050a05061c091208160305090c190306020c0601090501090c050a030c09031b06030e0c0a1701020706090311011503 78
    0x410802000480d29840750003141c17540500c1642c81280e50f980010b450340c3c20105aa90105490400140c00c02c0300b0141d948600c8102820402018a0310351035440e228001c040a02c40785282c21000a10142c0d00d4000314807110140064400c05032801c1a001441050200c6003120b040140440208462810321030a004469009109030300c0c10b140503800c5400d4000550604903110b4862101d240081c249562100315481030356120724062401c0e51a56481c0e40d004800d14045c540f900c001d10510ba5400319511034254815901400808013a1508081d4600d40c0c3d0300c044c003010300c0401c00601e07142001c603060b41221407250f002e02c00342e6284d2080c84119204600c030000031803000c00801c480e250107600208925150390500d0b848880d40e91721032441c008050254440e503103e550800340882501803090b50414150600107102403208200440c150400b0781c054501d94a4502107021200701e025011107040c6a8444000d000360b01c4240fa0141504c4200d0111080075400d20f034031401916a882c010108480d0 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 665095557 1250 665094307 665094319
    0xf0b060f070602040b0d020304021c0c0510090302031c0f0f1d0619020606030d02010216021203130905060a0503010c0e010809030c0102180406060807020604171c0b0109080c 76
    0x440380e80060340315400322000315034280d001d1100041c4445660003a10400494043c00360f80d81c503247c41004141d160201c00c149088600d504100041081410080700307588060f5441403841500c20015500c40760168002036051107503c030b40403440b04c2c00c0d40c0400894400c54581602010b07030501c040c3ca61003810111800001c01c0c038848400c000d5145410545510f8010301024a0105003402c0300c8007400c5a2036440c0003582c001da0600205090400c05c00003400c416100850619140c55070000011a1800c0c020344207000b140305100403104180101c1300d4241c281940146d02c43e0f658001100500400c9609c135124003011b1500040d54201030240c03400d00000e80d40c41444480c0d8000040da00c8100103404015103200034005040315242c244002c0003114120709c201041c64182100300400e07506290410800c0046000910505039000200c06402941c406186040300e030044481c072050b409200401c00c0c4106a0340040317030b1080106e0740080031141081e40d0b0420134980740c444a0380d03181d100000e2550010 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 665096807 1250 665095557 665095567
    0xe030703030e0f030307030f3309091505061906110607090e1311060d05060a05030a020112050603010b090c03240120120703090f05030d080c07050f1608010f0b06 71
    0x43d109030701441140da00004000783d4049809e5503c8000072101c540302401e41c4aa030441e0020032200c040b80002041403207028043d550306c550310082d0642240c4184103403142c0311004256130b070b43ca2a03029800d000c170300c007079024290385d03220070003000d40b000003580e080d40b401045c001c03807070f001d115002e0401540d031144070301c0e00303d51100007089407442c85800040d039040d805001c0c004842c1d615040240f54101d18550b02149030700308182080f00c034031043e03405184a64015000c440050742c0004d10300552054211000982e82c1e40c00000ca8054602d9055013031380720599078204540c2407034500186000d5480c2c841b0f94001030460000b4410100440d81c105404034016000c4510000c104159040d50452480f0986d000c0c401c8032201e414040c0c1044504a010030950303d07003030012013401c410060050900310b004180d10b056110300904605001b51075880b403280001000b10030b00c04200800380183d1071010884003400346540b010400004103010f002610b5003001c60031110210640112800d00c0070041180b4981 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 665098057 1250 665096807 665096821
    0xb01062c010e06030a1409010b091306060b030f09061e0606160c0602010e0d031b0503091614011803080906130e1015051612020c040e030703030e0f0303 67
    0xc4240e08145410041c0e2240c0a1075161515000346000b070008050115040851010310708100e100100410100c0c2e1420040001c160307038900b10309400c03001100071803000e283c250a008014207202d82085d220b083d00007080c00541124021007612561030705080e107445880d848040355001d2140910300b0007220040340031541034542580100400c1000c2110483d030703e02a59070b401900e084d242d10400160f50340d0032111110f480284083c000070030b0540740401c00307035842075003031108559040708050801201000089526800300200318110b00e2101c101407200369125076440b0b080074040c082a00040c5503808070188500c00403514001c0d2603005694900b000c0c591418000742d03810100d10b51a03a2100074030300013003000e4003040150080064203540c00700c0c581000d060106040c0c2c074901e0349007008805c00500c44180280c030040000191310000c0e11600f003413107140032441d1680090b442d40d80503181c5403040010003000002490014444d46003409581d040c0c40301c80b500c0d8401c0c0f80700040d00c0d4000304001104 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 665099307 1250 665098057 665098127
    0xf011403070504020a03090209090a171c020708041d1b0a090902220308030f0f151207150e040605030111121b04030602071505060607030804060204030f050303040b0106 74
    0x80000a1b103070010700301e145900003c180c4a002c0d99043c805400070040c85060000b0202031070440482608410700d0020031511140c00041038040c4114039071350105200c8200410501110000c10140042c065100c0c0e0386040519a84021f603030840401700205001e860340200102130350b12004003500c07800d8440d843c120001020390b1052940035502d45000ba40b1034451000c6001d26030145004c3c03044c55031a4a403c41161302d6000001d440000c030701d06044108051070f07049000c3c1c1501c640c01547c03840281425101c846203000b080382c01489e150415907000b880500e5010085100e890402c980a03c16170390383c0d00602d4200c844c10740d107540340d4850420081c1c06080052091941212081c0013208041c3c00c05605001c0e60b8110f90403c84900b90005100011b104e070007003220200c4000040200002d0400400061140c410503000030148824880090103014080c6c0c113aa00440e00006241c0c85c3c0011392400a840e580106c80460315018804004940700f40304107000c80056510b08003500c0c004841305d0440300 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 665100557 1250 665099307 665099317
    0x6240a03051b070f0206040b03010e0702011a0d1103100c051e070c0302061b0d050703080f090607030c02030c0a050c01090909110f130f060504110705030a051e04030b0f01140307050402 81
    0x46c00c00310030400011011183c40055000302049140b004160400920081c203541c80c0c0507089200008804445105a0b078511a03600314681c01084004000e0701c8a001c01e007000c0a810005e0040b6161070f8102c00000d400c0401000d003841c00021621400c00c65100500c19801030705c002824640108a080c00142030442c0240100c00000e04050411515031580c1c034500003100c01070100080010482c2420960062151500444008204102d903d45113040c00d0f038804000b00f070350042540742c03500c01008034001d00450718419507202c1514100241800c081d139440400d011980e0006410401c00180e12703e541c4100c8402940c003513039110b682e4561800f00640d9154840c2c0d802e03405410302078007a03105070b8580b040802c015091000031860720f1a2034208001c075a00f006410050900c05c01412002440c048203c441d000c029040550700e030609400014103605411045041c08400060040140103003c036500384030300c03018101501142c1e01c51042e2000c20051120898140c0c0c400c4100b80b1052400c2d07000b1301 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 665101807 1250 665100557 665100559
    0x7080618070905040f0618050d05160204050f061008012d0503030703120f0c0806090a06080d081f06021c12290319030806240a03051b070f02 62
    0x42075191120b01e1030044500c2503e04a400c95183d844850400085001c2c1c12122501070f01090308040c0c403511401c0e150301011401c80d00b04180003518880c40e41007480c8054156401620030072003441c122082d084c860209565052160b0410514034046608c2010154142c1c1c506182d10342032207200381030a400c8460038080c3c040700c8090354180840c8a071010005001035500941c1ca4040002c0c5a25241d4104c40381491000c049e41d00740390180b09496080166190480c81c15600703030115070303915000e0390000c11070354001c800503000d40d800d010b50840d8400d21180c010803603c62502080b80c5002003922500072a88109000f43e0018041a0310032100000e42d1400f5001768100f0400f9100c040450f44112040c030500c00c0544032103603034082c803e14840410001034000c00d83c01480c00011070450700b04610340009004041152110000708aa01d03107058020280c1e103a03000001300305502901241c1c2d240c1011580400081c0b8000029059056484075040b0b81002009042c0c5081c0240e120302c030454200800036 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 665103057 1250 665101807 665101813
    0x71a030717090a060b0330070c030f0c0503061909060e07090204060e2e120c1d0a06080109151d060102070b0f1b1509010b030c0307080618 61
    0x20285039411207100360311501071072000e40300314202458800100c51710b082d5110b00940c014401f40c07680d0020102444107008100c0e01d01c031213814554103a4100792050400041c1040d0501d9000410007608003103032000140719800d56002d00d9215030a144e6225400c66504001e00130309451210004420350110442d18020580450505640b03203034180f4000c0c03513501a56090340d000608002a41d8454005074007010102c941c00c048060790b0000140405000101c00d0310b1420300918012914056603481c050401c080206200030181c5500161400b07903505040080b862010803114014a404c0260609440c0203807a0300c0c2d85a42000c408a00420300c4003002d1900001841d008030f01e00400c2c00c20b0a1850020b02080b03081c0380742c404002420b0043d00d80c4080744540b805e20a0a54000c0190159681c44c021100f404c0989000b01c280c00d0315007512040011441ca03141c02c10b1090003041074020000f500d0b42030302260b0050080784141541c0d11820310801000d038000b0000b0a110724281001c6021510f41d02c011 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 665104307 1250 665103057 665103077
    0xb12060906030a140d1710050609010c05070b030415020c100e0c0316091413030c02061b010b030c0102030909220b07020114010b0c030d09020105040b0f0301031103071a0307 76
    0x1034004884d42d80d04000046601c92110720a450303501521068841200503101c00660034002d04003007001d071190003598442c400100f80350045034442c2d0905414035410a00f1100798580d50300c0f400300c6c40c2c2c0c41a030303040d81d4402c049015200043c1442c0215820002402d0042c64aa00000b0041c0010300700340c25690b40d64050292051040e5400b001564003e4004500701440f00b890b100f0544101e4150000d0041000c02c084108605d4074450365509041d5a05410039601180c4a0f1001030b806106c0d0100601c11510101d0340c00000c00015440102c10030300540868045024210040ea900c0c0a084800d0741d02485520014200441c01c100c0042040300c2201c1c0414210711a030f468083c921001c98054006079500e04111400901c50748100380180085492180f5058040e4070350345c1c603842002c1d050705d00c0d0760311880000c2c1164800c1d01100e00070520700c0e80080d2a1440c90072010310561081c8030940d18a0b898414104107443d003c6030020450300b61005181c0a0001506090303a60740000301650140403007040 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 665105557 1250 665104307 665104313
    0x708040b130f030803072a200d03020a060e0c06041814010f09020702060405210706090b0f0a12020c0a05101104031e0f030309150504050d03150b0a0203040f0b12060906030a 76
    0x10f0101d01d0f14410740b090420511214030148c1403907540800c10f88142440381c404401f1940116000c0001604041d0226148509605851609091441590304400001b8002a00203200c500b017004041e0081000d001800c041050390b014a0401e006480d04254036020030000b2001d164001e00585101030034041c01c003655040028000c44050103c001011405d114041030a0800e03c0740c6c001a10543c1051a1071604000e40341c1d1503800703040e4626100c03040000704001d80b46c1c0695101607141c10061801c0d540e49140d14802c5072245540d1804444e188925210700c10503490318090311242649110b007050426185440e40d100134040070440e41d440900009922011a500f00169500385010344ca002c92440702510349840d201c24414505e954040c9801e007400000762002c40d00c480c40c0b1301a8500456000d0b518080350084100c19440100402d40010714001c4036138011002d481124006400d52104a6907120340d5442c034840c000c4004150308040d00020924035080750010303041040a800c49004064550b = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 665106807 1250 665105557 665105627
    0x4021e04030c05090a0207050a0f02120609070f0b04180b0613081e06070903061109060705010e0f070b0d050c0421060e010b01020a080c030708040b130f03080307 71
    0x240080c2d030404100740303040c8090304040c0741c0d4542003950110210301e42421525919201d56658500401d1603030701c01c0c62403096503512002518000c00d10030a4440c0b07800c2089005a03610344034480c041c0360032055080019090940b00c2500d0440d1384075804c2c80100007070100381200410076001420741c0136005000c030301c090300100b554590250051400924080c00d01001004c070013010031001c44c80716407000c020030803e0740c0d109088500f04caa0200c00410501052034800d14140204494241c00c00700110700081030210541080348288103c10030307182c0e01c65130581025181c0d1460300540865001c104600d9000c819298406544a042c50608034203050725461560450a1100b1840c45c03008a2440c003501401030034032481098200d000001c110404400c40041d4071195003220241902202003030100400380b051080365000c69205403000e58a540702c68080285400c000c4c0d00c0182014019008101100e03002d02032820b49800c01c1c4443d04543e0340b8407040703c010000040444031140041c1c40000290030300 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 665107913 1106 665106807 665106809
    0x311120418090c05040e01050a0e032b0204090c0f030c030522080d0905060103030f0302030c090d020a050919051e0c0a1e201b04021e04 60
    0x260401016401240e13000b9504107040c002c588055000662145102d00040d440401c91034900380300c2c6a60341d00888450390b0000b2071103070070002c01983c200e4030381d00d984034001009451325448a04080c1a00d50344074a440c0499007110b016500c1f944c15004000da684114a020003403403a1080e0058240301048224402e001802c56010041c40001c600312105405051014000c1d4500e603c3c10981d2030409120a41c0020030101800b8101c9100c2e000300c0b03020750f044425103070424a00c101040382100d407030a4202d0f404500c01c200054903495a03100180b1504034540408854104811001e05407540108940d05c00303d60104424100302d030041e42e160300303c000d0710b00460310b90a99003000d480304980d213001c20843d0118107410b40031099012038010071800000e55040482d1440944280d604c0c01e10508800303042d811110f01840c98141382e80074017506090000256043e80390585a002e01d5405 = true := by decide +kernel

theorem cover : BRFrame.Cov 664928057 665107913 := by
  have h0 := BRFrame.cov_init 664928057
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664928057 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664928057 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664928057 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664928057 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664928057 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664928057 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664928057 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664928057 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664928057 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664928057 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664928057 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664928057 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664928057 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664928057 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664928057 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664928057 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664928057 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664928057 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664928057 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664928057 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664928057 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664928057 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664928057 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664928057 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664928057 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664928057 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664928057 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664928057 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664928057 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664928057 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664928057 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664928057 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664928057 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664928057 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664928057 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664928057 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664928057 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664928057 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664928057 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664928057 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664928057 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664928057 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664928057 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664928057 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664928057 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664928057 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664928057 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664928057 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664928057 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664928057 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664928057 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664928057 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664928057 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664928057 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664928057 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664928057 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664928057 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664928057 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664928057 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664928057 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664928057 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664928057 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664928057 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664928057 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664928057 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664928057 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664928057 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664928057 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664928057 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664928057 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664928057 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664928057 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664928057 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664928057 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664928057 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664928057 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664928057 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664928057 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664928057 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664928057 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664928057 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664928057 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664928057 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664928057 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664928057 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664928057 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664928057 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664928057 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664928057 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664928057 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664928057 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664928057 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664928057 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664928057 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664928057 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664928057 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664928057 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664928057 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664928057 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664928057 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664928057 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664928057 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664928057 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664928057 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664928057 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664928057 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664928057 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664928057 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664928057 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664928057 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664928057 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664928057 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664928057 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664928057 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664928057 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664928057 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664928057 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664928057 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664928057 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664928057 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664928057 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664928057 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664928057 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664928057 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664928057 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664928057 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664928057 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664928057 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664928057 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664928057 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664928057 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664928057 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664928057 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664928057 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664928057 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664928057 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664928057 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664928057 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664928057 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664928057 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664928057 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664928057 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664928057 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664928057 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 664928057 ≤ n) (h2 : n < 665107913) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
