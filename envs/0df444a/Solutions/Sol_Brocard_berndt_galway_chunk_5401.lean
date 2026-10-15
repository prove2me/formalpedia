-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5401
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T15:44:51.653326+00:00
-- url     : https://prove2.me/submissions/532fcb5b-9371-428e-ac9e-57722b3075d4

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 971223021 ≤ n < 971402877 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 971224271 1250 971223021 971223023
    0x30f040312180302031b07050a063e0f030a051602011701060201140c1306080403050715020909070c030f0e030715030c02120406020a0f150c18081612 66
    0x180d5a08003440c5603030700802c0e0020300325010b5030045441341c0050104041c0440c203a003e1425940c05000c0402040e07585141c1081610b500345400845507034544940d41c9940804400c02e6000d08400701404020a0040d44012014104a08849069500c040015280e2040b20858400201c0400c42e00d4590011140e950002501c1803505134800c80c1546040d014001c001e13004480141d4482034a24005081d40440c142c00443d007a0f1002d00e000004042116051000d01c40d110034056104005014180502c0695208642029044600202d0810194025844060001d11480540d00072400b282c3c841c100400840341e043d02c5595904501100c282c4001c003000e0312466151040010102d4807021150701c1c0141d101d45074130086550f0085c14400390502880d100c1c16180c1050a0100300143c950015a1150841d000188042100c090341400c907409a003a8800191150403c3d07a1540c519510250700f540c1100824040707489240ca900745030f9203030060013401188080308500300380442802c01a65040f25 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 971225521 1250 971224271 971224307
    0x130602010207120f0e1c02030a050102030105100e0a0312020f0106030302060402090a092409021801060e1210020a09030f1b09141f03020306010e0601090e090d0e030f160f050303030f0403 82
    0x400047d80082d00e0400407031030441d0710340d4010004001a003400074154000072254102031403040355190118890901310311010344900303040040d40c4981c9009014101011002c00024000e05440e400e000e55a0401a64124011050080054034000c03062250701861944040c42c0394202d00c400c032000d05a14519040401001d81c1c40e14140700603510700070b000e5040e801108500e0010f41c0f411401a04003484e140c03000f03005200340c44003030b82440c0b40464802402210b00500584406050000b102d18162036000109a900090181010700007a91440719008521106147e001c41d1a081d005040d80c001c450340503a082c8482021800c40030b000500d05801c41d59a0144585041c0d0740d0700001d00d803100a03840382018240a009204103560307c07500c8240a440111100c810f103050801d1400d5941011034002c0e4100500c0400010307076654144400303000000c0c00e100b16110000540d440344512308191058403950142440001020704010040e1303446040e0318074840b050381e600e6407402d40b18001e003910b1012403 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 971226771 1250 971225521 971225569
    0xa09050616030e01260402040e06070503160207182a0203120c0706181101050a0c1104110406120e0705150d090512220e0a020f130602010207120f0e 65
    0x55440030580e01c2d0080085c0c2c200201c91030a02d401800100c1c0c000d002c1404164015208000c0c1c41600b00c4110ba402c0140e40b028200e0f0424241d800b03e080c8a002d420405055861000142c0f080d400d60b009004602a944c5516040b0303030080305c03c5601040c140715140c0c0540c00501444d0359803600744654aa0024814141519005090f52940101c2e17283c220b5840c108103035031420340e050102c540d00c01e8044031070a081442c60140c0401e005000713118001170040003104603024894050300d840d0448109103180c180034545890302c601d400713007060088241001406190101800540e000081c044040300c0018000000312122401420760b19404102c0e003090f415110b0300d100c40001e104100f400c2201c07120884c905d4440c1c3c03a958400401030ba4102d0540711b1800071000c14407820718040c1c912074114440b04801070303a03034030060385140c120b001d0340302102c100003c10040000e00503010340050542c80d10501014103440c2603c43c0c155994800e001c10400001c40501d440c1c12541085444201c50449075248294 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 971228021 1250 971226771 971226797
    0x2280305030c01021909140f040f0e010b12060f010b070318060203070c240302130e1911160215190c1106040810050a0b03120a09050616030e01 63
    0xc07035584042e0b00d2880381da60001d82c0198444120f1140b0221500c50f140002005240800c08040c41e07540311581c601c140308060045895640f1503108140c544481102801408603403224203000f0081650064003801c14600034219a44011400382d00c100c12050410084c1c0e420b001035a1000c1d009100c080b010b00030204071081d1008440f0628034005d0070300c0d42c01159035000c3c0b850a0240c000540c2e0043c1221122408100070b144039003601d464040e445850010703150606100c0340036110f82d103507114a0303609004006201401350020a68030759000c0b0444244456940c1030790b0007095126a036203c0001d00a0101c10784010300c1c00c0384802c2c690b07200c0066844d04080c00c40c041d20041e20025040c43c000702d50b001d0441c904100b848505a00341c0801100c826003050320b00a030994898140d42011003000d503580000079240350040d4842092a42e01504644d9440e00101c03a0384c001d5032000350001c000c242c20010004103842c1500440e191140d86034510042d008035580c080d0391694100d038045040c4038000351109 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 971229271 1250 971228021 971228023
    0x412080c070e060f0a0e0f0c0f0414120708060f1f180c091802031008070e04150c0f2d09030303050c091507030c06020d020a08100302280305 62
    0x700030b0a000d80e9224600c0c1065002c104015144d41e20b25406803901d41010049001c1103518240e1284800601d440140d952281d949042d00c10b44000d009a5440400e0110f840e40c5980007451205606407841030040c194004680d0780c80a05203e034440c10703844840000c0360390540040c520303001546200600b40301c5220848a6102e01c986822140b035031132014000444d000c820703005e030300c0050340d241c00d100d00c0c210b080c0100c00c5094001040789160080d00003000c50707032440313009007038a004100c2c410070f44401c0e82c1c64480c404508c1400741c8080d2807594811000c08014a00c0e03108600440c0c13180c0e205c0b40003000c8212002d441c001420000b4140c1001c045d00c0c08120a114142c2801d0304060680c1d46e00c117080e0440c5000350454078050580501c1400500a0f50700c90740380c0e00194552510700070b00d5681c5078000d030300d81256120703c2c2d83e10041c051400481d08095002c41c94014245030305554940006540d00c44800b00c81380b404620010354402112280c0c07010781144030b490707240d400c01810f441c1d10702c3d251680c80302c07 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 971230521 1250 971229271 971229283
    0x1110301060c02031509071406120403020106030c0b090a21020a0f05031203010b090409050f01060b1e1602060c010627061a091909050f07230412080c 66
    0x1031000324030310142600c03c500c2e0034444032401244640000d8580e0500011143d51900302e40101808a0050100402c46a440c58103480003007928203025000c903d06031400a000c1c00d1103201c01ca5500305850004240c185a0a060b10303030100c00942001081e61030810600441c02030382202aa000d0140405840503131107102d0400050061240c072502e4640c03406081c035103851054888600c2814003400184100e845a008039203840d00c08031008240b000d19403e1880c20240c003d1a9601c640d880c0140c000360201d2078801400d1105010010f100d111005041c01e485c040c440e0050316000701c0700c12803c0c0f800524066000e042c41001046c0002144c1d0346841400800708400200c589210100c1d0071850709000b210b0090f0006058131410702d02c079612003c0c40c0500140108076882e80b04400c01d0300c81c4403607060b24281d200010920b01c10140001d00b0702c1c072010f4000030016075209000a0014850a98000c011707140c00a81004100c0044e00d01403178a001d80c41d0b0b00b82d4143c0111181c200811491703a942c4420403175 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 971231771 1250 971230521 971230529
    0x1206150412240b0f0d050f030d051e040201052208010207140706030b0d1223090f010801050616140d0809010b030a0b070e010e1302040e1305030702060a0201110301 72
    0x5070030400d007804400700c401c46100641003103185003020146105515089051134022400755002c00310300c01d003031800c1406c140045055103824840400c0d0808000d070150401409042c0784c20b2a40510b5060001b04020700000315001380c08200e0400c012861000b41d92240d0300d44501c42003004001c2c980b00d81a85007640d2100c107050368403410407840500554800d021800c010a10303400d040000981c10408607415201003c00500400651070802502a0041540003a1803d09103501001c041c1c3d4280e00d0716150b004440ca01340181079012f00162194080d00000e410780c8c4e4000c0000e0b042140890401c3c01c1c7d044400780c11100140004141940844200114170b00c020507a00e416803185004607040742151007411a50344254003407484100401c4500c006540c03c0061841d108481000c0030005a96040000c48026000012001140721482580c1d01030410f842a40c46448055282d04440300ba05011050000d04290000c0058a00603d0088000c148404050002090720302c1c2d24500000e01760400d900c = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 971233021 1250 971231771 971231783
    0xa12090e06040b090601140904110304050607090b180a0308070809031627150303050318061519030618140a03080105040c020703020603100501090b1206150412 70
    0x200384440300001040c00d5201c0300c15a001c020400300040001c1c1d038608041c02550500c9a00000d21003420400c1c2d04540302e4a001500c240a10200c018440c0095801290256100c1c0103480210381050312940001c03048407034040c0c2c824102030100135419a15800032502c254040007500001000031070b0080a40020340c000c28401e0f49a55000043c142002c0e007038414251840301c4810180030070031a00a00032199202840c1c1300c0d10301300010800303000412402a18817403090030602d00000305070340032004603c10300ca0352103501606d00c2608001360703aa101c1580c450618914807010014a81481c1003d041d1502c03800803445407003650394031120211490300d0014440b4030501110103041c459128100005c100303d03e8020308190380780e034900400072401800b410f0301c0b80340c48040303405440c1d00c00c1140c0b9000e1900100002e56030308041e401d0b521224810306c0341c0b9012a06540c3d0002d818040c500541d18500c2c03c040c03062845640c7e0508000002e8401c84200980307402c24400030500030000c000c16070146110306 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 971234271 1250 971233021 971233037
    0xb0c0405030c030304080307150b060d0b1c0b04200a030c091506170a020d020f0301090e12071b150527030703020105160f230106060e0907020a12 64
    0x41c541410500094a40284c0c0200410040c1d55070000c00c6444098001c008544121444407404018000c5046002d5206d00040341c0441d001901e60f10003800c51104a4034031071111120800d8189558080340058000d403403480008000c00c00300740c403004006003480c85202408005100140006019030402c2e203d8000c2c1040c00d0101c004c00b4443c48400c02100324010b840e180c40c0c50b40003402ca1a260b04a014061803010105003a00d8440c0c055880d00d031080441513440d00e0300c08501c81d8441c0c00921034243c40608240c4001010400401d06403080d085000740c25182840607100c07c0450300f00010b9400d030f640c503600b90000b203908582ca17001e81001e0103580c526940d084602d5210301c07908220540341301ca08980d00c0c00200c030b541e4001200812a40c5c203003032254880e00c0340007090110042101c00035003c51303c85030000d01000a081c150704c5408010a8542d20521401c140f44c5089940d0360140c1c0010440d111020402c0d0302e4038214041e8002e1461045803140f02a50707540b240901c06041e20a004a0424 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 971235521 1250 971234271 971234279
    0xf061602160b0307030b0f0a140a0f0b0a0c0314030f15040c0516030203070f060e10090506070c020d02150a020d110a06090c0e0405060a0b04020a0f0f0c0b0c04 70
    0x140312160054a001001200746030900e00706060341c1c4006000b810515036030f425000059121035008a00f0208020449a03079165102c2d02100c2e00c1c0c0860201e14440c1c9240840840c6e2011415010002e50340013160142c284851503000340c490a101aa0a40500042d030110b06818501c03c0011031003098811811300306820010b200718400d03102c40ca8450b21550a10f2a1200260740c4181a110003104800b0500b1342240981810b0741140310300b0380068618801c440d85501841260781260060304078007000c5510301d811a620302da003120070055000f84641c1019000c83c070020301c07901180180d140010070070064034420343d00041040c8400306003010070201c0454403a070b0240e01402508030a0001c1c3c00c2c0240383c3c90414103942c5e01c440c4032660003030115980c0e04100080c01561007400020785010311585d4001c0c02c180c1081a540c180803030760142900c0c1090394000c4107003007a0080d1985094642c41d40380b01268100c105490500c628034240c410000312484250100c1c08100c0028003904801c00210307919820 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 971236771 1250 971235521 971235523
    0x120a17070605060f15130810060503060f101a12090a0b1501050d02030c0705100506040c050c0a11300c0103090c0902160c08100f0b130504050f061602 66
    0x5001d103120710120350070210251a503207013583c104241003001c01c1c2d81e00d046e50070f030740d5100f600da82216099105200a00c07505d503100ea8005d00564408a0071111107035503c5584551505044038458948484060200200701d01c0804441005035080340c19810034020094822080c401246d41207038543c4005004018841c203600f10030303000002e018500c1108172441300080c100b0310a8901d555031103940000001c841d0078044023a208020b80c00801d680c800441000640d01620098540603c00d9182403441c0b0b03030b231a005100315000700c014600074000c4080c050705d03481030501ca0154031f01d4000048003030701541500803242424407000347c00302c076989100b4100c4050b441c101c4040502d038141464844400c000c1810322480c4030840780060009603984c50160880785904c04007010040402203480301c0031558100104400c1a10b9142030030801004424855103170542c0c142c40c2d10260001042e03008420103504981140740e206000314101e1b942850030440c0586801000c407240326980054041040d04035034 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 971238021 1250 971236771 971236781
    0xc0d060f0c0206060102030a081015051201050a15031517030a170f06211209010e0a060906140705030a05070203061f050f031e010c021204030c05120a170706 69
    0x11902c01083c3d58548440081d55a01c10300c50207105201c1107400140c0d85000204000015000000c0010b940d8421440701600f1500403000400001a60f43c00102d15420815410030450b0030691414080c025003220640c0200b00030500d0380b07238480c45140301181480e00c0c1d0f0480d02a07850543c000750b60f942624a0010044400b1800e0034003d6500705d814010a420484442900500212100d8400c8180400f040d113080d042c44441e81c1c400e00411010566080c4050042c0440c024203880e0380c0c1c0c80012000400c1400503280c0107e0000c200303000c109111551003250071058071400444110310f410380580f50300c2d1071a044680c020380040d0b40020b40d1011030409209d0190800c0c0700c002c031600c2416603001c00e4404450203004550042c292030350740b0300550341c003084071083e41c00411860860600801c89294040d04c605464203001d44151036050400c1d407520301c111021603802a2500d030f101400d10080000807040b16084000601c124031000340030524801c240c880c03200e4490241c07607075035010785402c1003510 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 971239271 1250 971238021 971238041
    0x20d0e100b030109110418140309040e0303040f03050f1e04060906080c03191d0109030915021903031b0302030106031404110f030f0109050703020a0e090706030b01020c0d060f 77
    0xc3d060140c0b04000175400107040c036041400310750208050300c07031348044c01c503d002e003840c0588814048940110b6000001c0001c0034007800071354040c4158054040308030f03500c2c0f0081c5d030014051000c101d68480031070b104001500c402d04001001e903140a1141d405100d1100c903c2c000e544d0320310000141040016007040c00f040061250782404121450400c1c2036078001c1c00028105050f5079040200c06c2d496943d5640181901910209020700480c1c50028090080003822800c80c003050500d50041100584a80c2c004c40c4a81c03154000d00c15022081001121070701c01d244110181516401400180042840358401c2c5a8079980d0060f101c0d807500000609032140e03882501d02c03507203411042c840803480c840502c035141a0190303a0000c20661304404286004480900803440d540382070080d00030001e001c10780d682205e00848031b0405c4283c40e1008408245000c4d41e5400c2d02d544440400c01a1070302a0700400304800c0c050041d40c11000b03c2d81c0c040303021803101c1401100c13010303a10303044d20b4039010803131190b12112 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 971240521 1250 971239271 971239273
    0xe0f0d0503030108011407020307060b13050c1c3c050c130614030a05040c0f120501050c0901020c1009031a070219120c0c0807060806030d2102030a020d0e100b03 71
    0x91f0070701c440c01030344a21070030380050507881c2c42e48203000d00c5842e0014000002400c2c0e01080000d407401031031440d4103800a080303000301603841111550200c025401580171040f04c1c3c00c3c0034440341c42c080900e021145059801624840101501d041c83c03d0715610480344582d00d8400c041343c0d80c446407195041d502e213503508a0800c0c440300b2250003044102c0350059a90000e921540003a40c0d4503182000c0c401c14483e0350181d814000303450000301e10031840540f9080018444c800a00194441c10010160750003035408280c01a408841c51140c203240041d0484c818800500b440c1c030b4410b45030b0b1039201d8a402d42161951151000c0000d000d2600d034100402105540b0f4030041c1401000f0b5a61155488809401500c0801c403082c00780d61705110312a09060020f0900c10708a41000d995000701515940049440a1181c000c0c14841040e1500901c0c2c04104e2040341030025240100c1c0c0c5886400a41015001c0d016a030b6003031000134440502445a0350261802c4001000700c10489850001504c0032070045d2802 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 971241771 1250 971240521 971240561
    0x219140a02030f0a020c030d02070f06080c3a06030b010b0c0c0402090117010f0e0f041a15120709060920160510060e0601090b0a0e0f0d050303010801 66
    0x40d50110a4a500b03850303c900303041d07464101e60301c22464044251203003507250140d0310400242540014221084030003803800d80e1151a0388130016200142c04030748101805a08110000d0004031214051003012500c4003044000040c9440412554000303010040b010ba07600c1c2400d001380310000080c0780c010030442480341e14014840c18000c0d00c0e254150000b07805580c011400300350b507a00035010800d0900d0348040e071310040c1da5034140342c4560601034442c6051010802d404901c60741c0d810030307889107c1da400c000c075112210b02a003d1504481401422a030035040140c0390b80c40d041d039620400e40c480702000313002840d0450401d0106001c49001d5400014070a04c5c01030061060074055081c400207018100245450b0b0300300340d1084072500c12102008046002d80a00040581c80713036801141551400c1e685512642d0b2084010b50710096140100c048101c001c0c01a010f00b2807041c8030021341030070301030102e81c2c0703c40c0144042550741500b000e0448280c2c00100c01400240424405c942c02c0001401c00048 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 971243021 1250 971241771 971241787
    0x420e1c0c291308091e100504090f06030203060f0709050a06050d0e0106080c01230f03040c090204030305070f020a18230c07120e0603130203010b030c130c12021914 72
    0x401c2e104003a1594000e22007030f4140070a61aa02c508031030052806458840100d03540704c1d0003030159005010310f008003850840300700d050450314412f0703c040c0e9501030024100c54407032501e07080d841c0e40002c10035002c12082d40800709a03910b41956200090900b611201d440355025440e0f18107480c40c131306503104161f14190b4200520300f00055a41840d002c00e0030140b68290700d048120741134446090203001085000100702070840f07802c400443c4194059600c000045440300c914500303134441c511002d40090000c0c8001c10110740e013409a061032900c0107002c1440103603a42010b68040b8250809101180e0740d17000c41c041041c000c040c0140348180d0b50305040c0c2c060b19140c0c0d0000d045000c3c00e00090081205561481006400703505c10641c0a1802001c42e61607140034412003424100ca00d404900a50030409041d07014100026030213100000108000d5415640d02c0a00b402000310702d1900c81004629042111403803440d01c02011003031001d03c0034a00000040300081d02c0301d180c0c52031a948600c000c1000725 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 971244271 1250 971243021 971243033
    0x20c090411041a030625020304030506190209120102040f1220371d01090e03090603040602030402030705060304110103020304420e1c0c2913 62
    0x1c00800c1c800c940c00608216400031548940751580d4025405202d82003e001200d540035012840c1c203c441c03035820400f506220760407600d03030040340700c014000d030710040110303d20040f4806002c10300d242682005040c0a80c102c001901c1000341c1c07100c0344003654002014041c100c0c00c1d80402c0080d0a00642c1c840d01c10102e85d5403040c0811011411800091415420722070300c0e9600307100340100d9049044e26000a450610f412440c8219005002013030900f8454000380401d8404c440840710341687d20800821380c42c000c000d0014140d800d4200d2400d0008119140541c0d4034034002d1030143e402250010b880b8034261040c5440c001203500182e120b0102030040200240c2c454058100c0c00300286000b5880e0340f0f81e03140c60160521002045008102c40d808021b1640741c0008500342102100d0804a082d600d540324140111480c4440c0c010741d0760040c0240d108101c41e01070b0100c0c0d80c1205450508901c581c26210041ca20301d203e003140c8050721000f4203005881d00b902c070340303550880801c1121040204e01a5204 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 971245521 1250 971244271 971244293
    0x21050a150f05060f210c09130b010f0806060f121b03060a090e100c080a060f050a0314070b030103150605010504620601060f110c0a0e07020c0904 64
    0x1305022100010711100625140c00304081601c201082c031070140c0c1020492800729400c43c4140c00e018a408544521182d0f50902680380d44c0c40042e1100403460600c0102120b000900070201500034108001414501d98824003c24003458152100001410b0116800b03034601c410418155900405005002c015070b01c0d5000383c8110354494400180e025480c440c03044c04c4c170b612012a11403d61400c140080b03980d80040b1500d204070008403082001603103820304140303001c0090040310707081000454140700003085000f03624442c0400c1821194641d68031a604031099200f600308403060032286028010070b40756809400c020309800d0030014105030500e085030607080082030040ba418407400505642d00c18602286404802074401c010031102d0b1280b100030020448640d4141e020001c4090401482401007010b0b03050300c1c81a9a040b40d00380043c4001c0f50400c00200b5046250701078510202c5140e964685203800801222868402c680341050f00a82002040d80c4928040d56a04e81000000f074101542 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 971246771 1250 971245521 971245537
    0x7122631050c061303050d20010e10020a0e09010303050c0715081603020d090309080d030203090a02210a0c030b0609090d0f031122050316030321050a150f0506 70
    0x70a0384a030162213a4a01a0701154070240c00c60090080480015601100c00e600d1a05c542c0f90002ea08000f505a41d8202c07400c2c0201e10307001c0d81044104401e5001ea6070002c00c241d41003440c041e00f520569800095541034280e0003180483d174006441030303140c2820f120210040c078100d1155040030359410b60180c210350000308908510700b0000c43c0d003600303039000344c0c169440131f14541000c01044c8187c1c500542160f400340141e1205104001300d840c07880e0305c82d00840c1d10070400c100c0501842c2c20254240301ca001d1502c0c600b111900045040c14940704c0c000c100303600394070380500c400b80703d4107255082c916138200c4058005400389001c801000040e03640003428140f80020b600d000200d50300b052000f1001009040700000c0d440800141c003070803801c00c5004940c80440c042030144021035940c802c159544000612402e0740f9440f45030304101090042c080c800b0407081040c0c40701d603030034070072600001200d0080b40d44c02845a80d90750449030f10a600040200944241c1034500211420440040c00310301421345 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 971248021 1250 971246771 971246779
    0x1b18011403130321020c0106080705060406050412020a031703160912021311070c030b01060516080913020d0905060601020c03100b06091504030b0a0207122631050c 72
    0x86211034003240421142540d02510021502c906d4070701c5005001e460244212003da100d8542c02141d10300e804012035084401d55142c10345003030f24020701a007181c40d5014090360b001c000d004000000c5448214039060b98034038241065074a2034051018420440c88031000703802c1155510051100441007000170982c4c83d011100c81c0003404203e107001014040380c625200c03030001e011501c0d40802c1a1084990140d0703114034120112681c98410441d114003607c200d10348100640f204070008210520000c02030407502814050501c48400101416680003100c0c04000954803011036044c40070900400b5000f000910181c12841403a43c0000e80d641e482d1400843d13030a60350240802141d460104a4546010103402c10b0120160f0340704411560708644000c2d21003070f1203407000841d206000d00c21507d515601c482c484055181240c000c6a0b244110101d00c0013210108103045c40e00c02e820070000e4450010007105501c421905404248000c2c2503030302280383c7c84e54030402000052000705042c400080300f1b031 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 971249271 1250 971248021 971248037
    0x1141b03010f180e010c111e030415052a100b090a0b04060806040f03080f0c0a080403020a0c034b0302031209010c030c050c0a02091b180114031303 65
    0x4140340188031030706251006600c1d240707107040c030030340c2181c0c0c000000b003804401d0b88d041000d800c011003000d00c003078610140940c004210a01c02d106140c80000a00743d00e034600107007403903010011003041d1281c1c0700117080c0d14510800300701c2440c0c0d81044050a80752181c41e080c010050040003041016101500300048241c580329802403a44960384003100810b08403040316a18102810608554405c0d0300b0242c3c002454880000c03428a42c00e80303078601802c040c104580c034202045108442440700074008a00b103001da0b0200e41c2c0821a4080380101843c042d9a8180041c01c0039a051412132000640508602ca2030107054070700640415182c0701d120031000b080c050911010f24040342103100b82202605000840000d00950040541c098842c1c45000d850030452003102c00300c141c456000d01e001d0005294002248c500050401c1c601054101e0701072190155003070300030b6014040c1c5811000044a180301501802c007595a8000890f81005048440b210700d1410700407014080c0d540300c080017505020700d403 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 971250521 1250 971249271 971249309
    0xf0f05030603120d0507030501170c0613050d1109010801090c0b0d02120405010b04111216050c070303020a120e0904030320040e04020f010f1d030f01141b03010f 71
    0x60020155820f52064015654109014030700c006103800d59035200028a400008264178a03041c0d02042101e800300000c05000344080100000b5500c507641c044e48056858600007540e0b150042c00d8604640324070002c80c8580d4182051007000401640800e0040c1e040c40916004640c0c0380d0010350540300d1b070361215a0303624200b91200c0040e02c103040c0904503d1001c1002c11040c84010740c0005000da01c201c6091060006495003c603443c002c600003110a8810000842c24190141d00045046d2986052207800c0c03602ca0f038441820b04a0031b9206801580200c61000200544604641c203c3c85031802d1030200b6a0503640881e480501c014002018550b45840c0b4030388420f941000f092042c800c400c10155501c0d203401c680c00c00303c0d03020b69081f030007520a05070b0b01d001136018450b0124001559500d0ba00c0080f030441a4a481700d00d004aa9500350080e1080b001c0215002c0c051705918501050008140d0b081220a03007461006090a18110b80e60a1005000d4040540b0080045400c085108001a0f4175 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 971251771 1250 971250521 971250523
    0xf031903110702030d08040501060902030103020f0402340309120305091e0405010f0302120a020112090f0611040501080901090302030301090f0e06090718180b07140c0307060c0f0f05030603 83
    0x20390302019605101d0400301c05e0441d54400f2030340b0f00c260f1092009100240c0c0e80c5042c0d100360300081c00300950050f488130b00c098130780c1450307800303842498404000b006082c0003024991000c4248a030201022042c1040d511061503007010a610007020403084002008201d17890051980c001d03442024404c2203003414260010560b4034145500400c010700411441d41d41d10006440d40d10140b000324001c2907841000038480802082c01250b030354060315203161000e43c40c0c040100400c1c249004458000030059480003040c076500c42c040c0720a40403580c0560b954140b0300054401100201004c40c141c1c10100c5000000b07034040140c2c1d0450f04042400f2501c0807c002c0224054000c80402001c030b44201c40c2001085c40c000580c140c119041d40307107221826040d002d4544140c5100c400c0004a003440e07421040005981411601d500c202d42349004109100448590486540840c4400c500c83d4404030760507003800810700c10312802d10480c2c1007013040c64801c0343c009415207804e00805018003002100049158030 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 971253021 1250 971251771 971251777
    0x50709060602011a0105070b0103060b0420071704080d0810080a050c04051b07080702041107030c02010e010c03080f0c0d0f0f060e0615030403170115020f03190311 72
    0x85240034003000e41ca5120082c002c249159040038841640d116070302c1154054011a20b070180c004401e40da80360700b076844a50291400d94030b0260026610050210440810045001240c0c0c0c03c903007a42d81e510b07840c241a00307000d0150280b4600752078104800c010944000400000348241070070068913503034445401c1e6403128410b07403020b0414091002001e00708100420fa40c01d503140110390401403601c0f00ca404854040e00001e4480c680d00c0c04114000201b174240303010f011a24401840031440c28a95000380010303401c0b1076011800300700305104007000c6680014607501c1032902860711601c9640e40e5140240303854400782110ba02c1154040c00b14100304c84542c1207a10303e01c81e150052040c0c030b0700940404000d040c021012260245444008142807040000450207203c00030104403074955000382410803070b80007410807810b2100100c480074002c51000c20b00c03030003001c00d660780c40d42000c800c20b0040c2c1440c24280c00519250000c00c0000c03400b84011403542d003012424a00000c841c04038488402c0300348 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 971254271 1250 971253021 971253029
    0x5120105271207030c0507060801050609190b19030f0c0507031808010507021011040b030103150209030a080c0c01020f070b070f140303100e1608060414190b0a050a120507 75
    0x101c03000a0703c1080c1a00120500110f034460030848140a680d004116000d68003030150603440002048154918503010311301c00030308110a1006450240c0da24032010265200744225542d10f80d0050354803044503018800e110004850810510101000420041040c4142c40c002014012540100d042001e200e80702c900141000c00c00802003418040006951035004c0d801e802e54003414903084c10144c0c001001035a04484045e02d849066900359500c1901019030481030207030030340e800d00406199030f40800040561f01d0103001816036484003255210308194032154400e041d0b6011240c0340e05c0316403000445004440031819803603110080d40c40c00ca00740c04400030014251202646081c0d81e9200702100450041f00910700704c420040d5110310110000404845000100404000300d1b601e2a0003604410342c060700040000a0030391010344400200801030b50b40000f950248403041c6c1c8640680e1090a520b4079044604084062a2134006003140134a4041c0811560f010660070040004c2040b545000c3c0c = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 971255521 1250 971254271 971254303
    0x82203020102091207051e0904030311070807080a0305060f0a030b2206050f060306040305120c04030506150f03030705060a0f09140a02030706091503330512010527 72
    0x3071340b00155996640100340525403003482d6031203904100c003503c2038410702400c00140040920355039075141075000f032591011828802c0380030030030f40c000a03403040c0040c60400c2c272400d030f69502c40110600003400c40380000d00b803a0040a071141030040700e6444c000000100c079440001d0b4940d680d900c900300b0303100d007811041442c000d110f0b01c8160010032071550040e80c820400c039810090280d91f031000709562040203440103800724200b009848804a00c3c407861644c8060b1414002c0d140c6940c964846203880e03011640001901003032484110186003505802914401c110025818110b640d00d075682c64080241c1941c14050b5102d00d02090400203400c0240d40356040383c030203454003184220483e03c03455201e5080b40700e07000307106022403043d00524840e810b4520b02860070090701d81c0004140c2c02440c02c4e00d060b9242090f100c0d180e2030070500c0822840c2072007604100e0300c00c0ca145031205010014100711080049030741440c08000c2c04400c8018200702c000b19040c0800d100c2d80c074148405050580d040c80880803 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 971256771 1250 971255521 971255539
    0x9120c0a121206240f1d06070b0108060a061e050d1109040c0e0f040b01051c0b010605040f0b09060a140702030a0b0f0a0b091602010e0a06140708220302010209 70
    0x1c4c030300508141050368402e85040d80d028144420b0103d40c0d004010b10b041300801d0808000c4050b4407510a0030070820303c00039042a190600c2134545902448003648002255480403080100300301c0b0074001d03240207060803001e101c0400003c14000c0c5c0110a00d000d1305010b04400d0546105016030308881210040c0007500100c81030925080a10503030501d40201210741d100705000c00e09025284156070300c55034000301c040b003050b401c00c020070111016000741010501c00c031600d2440828100142180240199201c540d0341d5441c00c0e098100f02030035540407907101c0c14280603014040e16810100d400318842031915008545401c0e0030003109010b035402c069010710500c1d620f9402c002a616005018070f41c0206108240d58078a4080805d85081060090b0018a1800425002d5415021030041c2d80c22900010500c079601d0090b00d4038050350740d031044d5103181d25116280908020551001d801080034600b5010b13900d801d6081401128850103034040c81c40c0d01d203c0741c4050600c00e50542d904000f0040c11826 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 971258021 1250 971256771 971256779
    0xf0403050601031a090c09090f0d230c07050103050603070306060303210c021b03071a09190e061005070f0c030c05030106140909011503080309120c0a121206 69
    0x55600c500340811074180380001d0340341c0b01300001d00c06418803480c1d05d07100804080c2140401e12007041c10103001b44410307101e10214a0841d00741440108412800783d07540000f0901c5945045102c40032101103890303070b5081088200c00380940072800200341c07402824007103029190341001c00c1c07510106034005025580790007008010140d2003aa4840b03003914141070101100c2c0351441a504442403d00100c01581c410780f503a112102214a0384010505c00500b0745048996500c804403098100d805030924800c4001902c842514120403441490a144090b41d041c0c02e05281c0000000400030300280d10402c095408800e4480c49030044601c0c15500001c94075042056180c05100c40843e03010449964950220115090505100f084102d0340054908503a440281c0180030031900090b000843d19500c8049080940d1847d2034104021489070360520b0380c81c9400a0000c0c02e140303078404000c49502080100d8600a503000800325246608140e91044058003004143c4506407010f8a0b00c1c0c5582c18081c0c002 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 971259271 1250 971258021 971258023
    0xa0909030813050c030619051b070b25020601051905030601060c062a092106050c0403050d05120123100e090a06061103030c04031e0206130306150b041404020f040305 73
    0x88450707c40c0d400030300c15625041555114041410f4008a0030102808944041881c4895041e044103d1803003d141a40d00002c0840e45c000d40d00ca0518013507030254004101d82c0c2480e5080000ea0210044191107007400c00c0c0c0002c0c0c03181018411001048803034a92641480394650014900e0000400440718000d44000c2c0711281c490b0445401c8007188200c000040c070a50101c0d20742c07000c181d0010b0000341c40d403810382ea098010a0f02400b80407a80308188404030000c0c008019281020070a0346913141c60303040741c4901d03c41c500c00503004a010520740700b800042c203101205911520820845e020b042c0e420000404860511040480c20f0340b100101c401e100d158259688014203a03038195580b401101c0043c00141e5403440203a400c400c0706482000100007040401e00100f03000603801616041059054000031102d07000101c8503142825681d40030020408076110f0280010b6501840c00310031440c001c0c440d8054003651040c41821805445405204d0303449504407007120a07610070058441b40c03242401 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 971260521 1250 971259271 971259301
    0x804140a0b0702060a06030809010513081204050901120c182a030e1605010e0a121a07111c09030f0503070b0601050f04121703090109020a0909030813050c0306 70
    0x102c0058060100880c00c1a010360103007070140c035040390703080b407501010000444580d440009240101c500002c000320b45a80103201c120380743d00c2c5103000d042e104d90500040104202040e0304c51099a100d5078041400205100c498204540c84a141500b40c00804a142801780023940c02c0c9950424062107030380d4061003010340003d121595a9420000b170030031403c0803a070751900a050740c6078001e900300c4100f1040d8443e000302d055142029004007100c903a5880005440341d4a880215030b24004464101500542004810303844a8185011809040801d00e4142c40d40d2400f411a6002c4100700c02506c541030044107000000d6501c050582c1114080b820a280c8a420014044490042e00710103d03a00c1d40c41001550210075160644074030300792a101c14051820282e1002302c035000d0f01240d0072201f8034019009540308001480010424007468410000d03d55426001001c22900d40784241010940c0581800d0b48500c010411544051088c02c04520b8515030a640503414400c020401081242c0c2c0002 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 971261771 1250 971260521 971260531
    0x1b150905011107021807020304030c1512051608060a050607061e0603170a0210020309100f29040b030a08270904110f130204081603080a0804140a0b 65
    0x304600448a0b1500c40c1d40d01c1100740284d484520f001c0281101029007a40c60340110442c01140e00c0c02d5503c0d076070a020842542d000f09007800e141441c400a69800002c9071644000c450820841803400307606e40c4200c0750b03260114004100d001800600541c031920041806864014441925801203103068409001420030408080346584913000c01e04000c1d00580c001e89030f0065844500c40c51b100c0c80c903419034004d0345044085104034450041044e4052009501030400c1c2005030078404440c94441082d05c501114407091246448081c0c150070481d0030f000014000841440f540c841d02ca4800103000e80343c01c102076030345801068242d4003044109401000c14001404403044458101011612496055600c071364003d44400002400101d6000360071400074401818083c02c080110041216280310105003405660300003814072958804005014540a6031024448042d08554541107039006074403010080c04002c6020400f00120703500c01c1c40315030300030783c049909030000c0d420059280d11054030 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 971263021 1250 971261771 971261773
    0xc0c0c260c0109050105220b030a0509061005060706021e0309061005090c0a02011506080a06080a200307031401140f07091509090f0506040c0f020d1b150905 69
    0xc0d18a850080218401e00d4504050b12540d44a83c941001914141c0c450220010f20910000080506840700300d00117015092034107109450386418107610301219000361103204c45900c02010044500c8809904030f0985105131489511075100e4a0440c0281c06808400364600d0306501c0702d034a580340d0481c05144079124200480f105a06e6010b02014001c6135400b55542040b00e0b0000a103070b94060380000c10010660b071000060700c501030b0b0000008a61a60800070003c0c1040c0c06016110b00c96004039005400381c04040c02c0307034035110303500c012141c2c1c80003014416443d001c2e02c0380c24943d42e0a0000100a50300604440f9079950082c0003680200080e950a441414a40d004581c0540100c01858072440b1a910798800003403c185408107801001e100c0802001341d4001c02240f0301c00e150041150200001034003141504080041200355446074a5071030410010940c09000709600250a07805130f50390b400c00002c071030005002c0c0c040104044c42d0141020405544150908500d503100540f59400f41c4 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 971264271 1250 971263021 971263079
    0x905121e040806060103061203080f100902190f210c03020c030310051005090616050709140f06030d0c14010209150c060114030717030d0c0f020c150301090c0c0c 71
    0x3446230710100d100e0a001a0000381600009410400c2107010b02e0381003000c120600189940ea9061413040c1d90041c00351140e0002c601c40890300c200d41142d03041c109110319081044c420b4118859007002c94410352084850561901034a5850900a50449010304600c03c140da07a61f241082d04020b00440b00d1040ba8003072540204401140d43c03151040c0c1d10050300082011b032a00310032011b130780d00500c3c80c0201503c09010b503000c0011072a8951040200d40c0c08001c202d00f800e407501c50898420343d00010301c0180203401001500110580c4034621b00d030460741c0060810312618664620a00a014800c0c4041e041619000d60150050350000a0304c03c40240e00119405070303807503240444040200300c0480da05544618018021044129070069509001d5005c480c00d10750b141c2443c4003a200d024141c3c5002c07607000c1c28585c40096040c0030310041c080064a5a4960407040d501c001d034948814455240c03d2944d03080b604191074030440303210500c2604114048001d64444031405644410035000300c070150641 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 971265521 1250 971264271 971264279
    0x10807180b0a12060b09070c022d120f070f0320060d110918061503040c141807050a02010e07050901030b04020117190b040905121e04080606010306 65
    0x380c0180781c00d8400141686070100c0c9050410700d0741c0e08071003604884854440b00d0313103c01d940341c04482a2042620340e603140d02c0481e56006214580380e800320f002010300422200b510500c0800300300b1109641d41510709402c0131402100c007074100442c181440c041402035103400245440501aa101034a004200400b20a25000d00e900f114180c90205150000010300945a04511980c441007034640103040c26441c2000450000d10300e241441c4250038074040310010f101745c13820840586080e4002901040c2d10314101394850036418110f0303118a1030341030307142c0910f050399860300d4802651010103c1004180c84c103010380064075079080b211120340198078020032845044c1c4002111407c40d04040c102c4208ed1b421519102407008000b0001d078140300320380d2401e0540d02a0b030007210381304500600c100314028134402010000d407040700c201980b041d400c3c458400081080030460564403024010000c1e40c9041f524401884580445c00c45805c1580c003150014254101054081c4030341d0090768100320003034031 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 971266771 1250 971265521 971265569
    0x81201080c0901060f030b0a260607051204110414041b121401060f0f0302090601050c1f0e0f150c07081b120f0d06050603130204020f040806010807 65
    0x4400d0325142d00050403401089540d00501490040120034038001c03441d1040d100200e10002c0c141d038010545100644180d82000c81815003042007070240c0c030050169400c3c0024001d20b10b0082240314114142500041404c000c0d1005046441c090064014411100c00606001c4c81d15400c80d403e4988000206074202040f02c07410110080d5012080214400030464440c4070582c178000814508a40d41e81d400850260420600c55008007110f24240d030000d070441c414844c205901500060600c007090080d0860b501010132914511101c02094002c4000c03c00d80e20009044003568840c0c0034081c210b15403403100001308140c4010100701d25072209544507444044154410400007410100c003d00c024244000b0035803054040714041c20844040555850350300d222030b4810141c01c0d0500750000380081e000c145a004003170040004503000c03410b500d804d06e4035040030308104500901c0b595001814095443e41e440581d4090480f00044070314075130311136091954564444c0a0f808041144100c40c0d01c01c40b0f8 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 971268021 1250 971266771 971266783
    0x90612020a1514071a0906010906080d0f05030406060f080f01051b25020612150f03100f111b060f0105100c050a140106090c050702060306011b0b0408120108 69
    0x104a81e951180c1e41c411488014030fa03044014111200110a2030b210030b84058072502e640100300301001350446501d4400702c1030480d1015400818107400c504010201e154120380c1d220f209102c85c1c200280c0c3c9035a2072500c1c1c4010b0607135420500840d03e040c24041880340e4009039010203014050020006034a42609000c0401c01652200d80b01900c2044030980e5070301c0d500340424001e4031850040c501880c3c581d000580c10f821134422008043c085100b00000328a200701400169501900c1030180b1307502c80c02c00300b03494082d2811001044c5440d28038400e1483c60075070210f6104036105512a80701e2003079a9605c0303005400070352020058418400801d02c11034041c0c1025048610040030710208801c0713060706039544118500c00307407420b0050482c017001040844541802c04081800001980307070801c41c2e004112440e4294520401c20180070450041e00c0300030841e0340200d42400c00500f50810120800c0d04a42c0c2100c0003440342d084c59081c8000c00c00350300701030f00c41042a5034101005a80365150107940d80 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 971269271 1250 971268021 971268059
    0x41203230c25030f031106040f0b06012f03091e040c181811160302060a140f0411060c01020304060f1e0905030408070803040503251e090612020a 64
    0x2c410b002000050000b402c07a002d924401d0070b04041d00c900070612281840c40c212001d59145071030607007450800201540045d03000400742070061460740c0852051000340c0c80446503440d0b540d0180300c0030039030010400a980d00035000030b22900705000c1500c1c01030b016458080409001e01e052825802040b0302500c4403040403030f030b54601659a50310301241900c0002c8480b118031070180d518980819200056401032503080c0000d00c001401d542d00b07280007071500c8001005405400e1801c400741b03c440030380d16021508510003102254660326103081506118118001507507100d000001d03111348100064014602c511302800302001818803c0d40e0360000c0c0c2d07440700d11100381c102d048044441e100d2942ea00c04c0004a004400310b9080c540c035801030500d4030080350480c0e0601d51000c6410080740c60301304401488a42040010b00e05101c691708042400142c03405100a0100705082c08220812610030900c01000148400e10140382e480300d015119110741101640604454000860a120787d034074a20080 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 971270521 1250 971269271 971269333
    0x219080f1b03190b040602040b1803150903070b09070e0f0108010614060d0c0306080601121b0501090302240409270201020c1c0204020a0f110d05041203230c 69
    0xba038095920000744c000c1c024021286035500307020204151020348080d066a01e942d950222500f0182020103143c4580c4d03d4091960a25020802001c0c00c408001d0769400c43d0b100c4d412100740c3d11074a0205080522a8000c0c00f81e8042c10000c03c6000a5800042d50413616510001c204076078540d005034186075240b401540e0442c04c100140c40140306194009506002c2030310b00000c0041e1202081401d180c0280e000512a1540c0740c2180140685204129070541114069003000e40c54000060022030032444040e1161540802c555941b2002011071500010491003160350342e611480184000e00031069200314001d8607140c03040e8981d0204040100258050b0002c00300300e09050300f04011170041428100856200c0e10b00708005840310700185c02c0d10240c580315007040480f00100142a00c8941d0075440503a404104621065a048001c440a07107100840001441480e402c0030340710080c10034950304241102c001012090b081600180014180000645840d00b4210580030030090703e8484010725 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 971271771 1250 971270521 971270563
    0x62707030305030f18070927020a0e0c070c030303150b0a14031503010e1e0307150c030b370605041205010b091009060609120219080f1b03 61
    0x30134155580c8180c0c1c00085049407040d080c901091305420070b6455440448401d480304071001d8803055410302c20002110b60254001601800c0c0c00103001c422007842038441850000d008a00109505001ca841e143d800980c003208156403490010010319601011205240c481040812074100c0e0004031407950702c1c030382d583c070b400300c42010398554003580058842d41030804c122000582c40d48081c0030f5041400001d602030800c04000c000c8100070b0219070400c8010329001005071400040d0198101c548410500c00c00046002d1a140280c6c010726505841941c400c0703940b82d908800c5943c49911000f81c0c114806103c100d0007103000051910641d81c007441d004540288414441c00a10085a0320740c00d018500202d00c0b802a04040382d4900d00a0301c0e080070481c50a6014803042c65603000b604000c00303a130301c0c144a041d4582010040d010304501d030000e10800f5400c2c904502ca41c018140c7d40060404901510300311303002e0b5180700f6076a0b00910510b45014040138000101d0f403074041024081d800c100e642d0221 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 971273021 1250 971271771 971271781
    0x6041b050909060604082b05210709031e02120c010c1106040b0a0f091a0417100609090212010e0307030f0908071d161b0309030506270703030503 64
    0x6942d00c4028900c0303401c004203210000b136540c0200f18103407a03034844086c10440012481881e0310a2071184da12941071101c10002c0301c0c6d06034520402216150750501c03c14030a900c1d444011100007819500103000d140b15901409e204210a0210445092084526071190b08106d407015880c0c403411990301c4d020444c80c01c074003004103c1c5081d0100d028100107005c5ca1403d501c902100b5103903088001440000741019060b980c2243c1c02a0482c409001c0c6400c19200103200a0a40810307172069004054000000000c240c2c0385c0b0008105014100f1543d1209102103074440d04d40f01c00511000300300341e102c2c0c450309890b59404036040c4200300c04841c11001540c504081514103940701042c1700c10f40c0c010020483c2c1c0c0003840700e80074000e00300a4109040c00b00d00a6155611001c00035101401028003c20071070316212400f90840e01310300c24180c0c00511111a040b060406541c06a04d590024116006800070822159407074015241c1c40f1503841d0340810070703000f240300ba250b46410500005010840c200040381b = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 971274271 1250 971273021 971273029
    0xc0a12050c10050f15031f0605030d080c04050f03010902090403120b0f090c070c0f03030f0822061d0105101505041202060d1d060405280f0204021b030306041b0509 72
    0x41c5ca0703124003400726080c03007810038810802ca800c40c600c21078009595460a01603881c05006c0b0803102001c0d40340225050500e020350700c1d4103208a1007002d115128203e8202c10740e46003900310280c1d140d001002c0544500c0c0608014107000070340f110400d60689043c0310f00708140b1705811656080305000c0c091140325508c11b02040d219600481c2e06840000c800d410014003000504040d00196100341d0f6801041c803034501c0060b010780009861601489582e45000c0c10380310f10904680485504504c02160058010002089a200d40780d2800215400d01c0104040c00050160b0902110f401404c0840840d01c2c02c01d00322980d000724061082003800d42c440c4003004d4506000501070070400420000349248142019a5002c18042c045004603045101004184503050017074100f61148502c0c4951100000b5040d04e8014020080003000700039410603290564640340d050302c40b841515603d0079083c12075144400d550341c10803a4100e20581c100108038240c01d0b80d201446840c00e129885050401400f0300402c = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 971275521 1250 971274271 971274301
    0x30b010905060117151005160209101a070212010506010c0609150c020d110c061614030705150a11032403030f0a030509061b0c0a12050c10050f 63
    0x14100f000000190034010b800c102014051034001000261000c03071641071206e41b07a6800c90708014040180302610b503544030b030000c03140c2050b8102e030b0082007aa11100c0941141246800405801422a03030700c0f01030780103080c01420194001c40e8a003c4131541c110089081e13840c01c844683c00900c441110b000041c001da0400700800f4410242507001c000c10a0090003180c50454103500141d000300d47c04000c541d00f20180140004118014080b01003a5501082c0c2610444a5503001490b00d1100102480201300c02c1890520000054a60360080342c18480d541d05080f0807060703924000f15010810300b0b80c0c80e04c00d0421900c3c0c24082e1a04654074900307900000701c00c820169104000c42ea520f0310441d502030006180c12032507462255180c210001d801011501c0c014960301d600d60007003060141c0c0c00304031592300b20040c12244032195203c1000d09103a08182c400c0e0001800545402282158980c100c0e000d090103859450440b403140b581c4c0300c0c200041d40c40a40c1c1c03400701d10326024049900e500c911800 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 971276771 1250 971275521 971275531
    0x80d08090f100603031b0209011e03050f0a0c0915030f1a0f091e06061c1703190b0a05090a020f0d0905240f061c03081b04030b010905 59
    0x2a5084090030600c403038104540000c00400c081ea07030f24014001c050b00106410700340160300032868050205139006c24152501806460800c03401c00c1c0303805a0b00100c11004402a5a2003015a464180c0500c7c140f0781e1172110300c2085503601a402c001041c40308861160b401c00c0b40510035000c0915246884940d41c1410790038082c0c5605040c95505c0b11000f480024660040c0310b0322100c0f0a191a103840e1807414100740480c400741650144880c0911170b00c0014400e9041002144c001200d6601505d82d1081c08820542c001c08801c00c008007940c0001219020b148140c800e210310085034400709030383c0000c6681c0b0b010310aa22104414042c80503003082d0010742d5122000c007000501d13101c0308141080540c4c01800e40d13910700a07180c4e03420008001c01800741d10008107000c143d84141d51910003140212000040012058070b040308000f828584e244c401c035072511003030310700d50701d142000c281402400d48000701c03822141030310150041ca03131040f41c03d0120340851340c0041441041d80d0802c01508050540030300 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 971278021 1250 971276771 971276773
    0x310031e05030c061504020406081b0c0d0512010e0c07060515130219080105010507081303020d03170705090102030406031e0219020c0406050d0b092b0806030304080d0809 75
    0x4480340000d1040000300b100400b610014130b064603181d0012281c40301c064420364004c5006010420410350405003050704010584c945074400140d00d404000b660040c0150103039548074940290310300030341040003000041203081411180360b88a410000030b007601603d1904140e0030401000c0c001c24000d62281d078121071721a0301c640c0c40d5850070b07000807600003034030481d02ca0950303000421900c0320000c64442003001c0c0650030074191544c54140080c0c440c0c001d56202820202000402110386c00341003c41f0005117500030000750425000c0c2c18010300150000c19a1044210400d000c51400782c01101602c00c1782c01c1c160b005620b440d040c8541113015109500b20035042d02d000d014403070400c010714000340090703a060800381003108031103800091610808402d010f0007240b8005080c0101d4035843c4004c200d05402480305070103500c84881c6075161030400d101d042041c005001d8042c14000720741d8000302a440481d501c0c0d0700c06071245420551284964803070300701c0680c448a40601a40c0c003404c101075202c1d0342c1c0c030 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 971279271 1250 971278021 971278073
    0x50703020a06020f1e19060f061d0f0c03180106030206031f120203030708070213050c040503150f06040c050d1119020a0308041506120812060105031003 67
    0x40e02181c040500d907040000540c020041d4000c81d400100b2050700e82c4980304002a04031140884101e40b50580003034003c012800117043c02c01440703a140c10012582200032800c00c5142d83d14000300c1d03c0e855110840110540348032010413010004540302c54040c4021002e09071654070307403900020100410355900742c03141d501c964000015075aa040507601ca0170040d03100902c1c04540a400c9601700c441c6800c402c1e400302c8001000e50141e207002003034840b19907005000c56039440080c00095902d9129071098000705040104004603100c540b03010b042240d0b4181e040b20440800f100440e18405001c480c21000700c00180d0000300c1519081d08100070500c0c5a05102c2e2409900c03071010001c4c0d50640000505080d000510048407080803000c0c450402d035148080c0040d40420782d4021704100740038002904000d80328404040b507851540c130050082480f24404c00a540d440c0c81c006000d50005a90901801555000030b00254000d5040340c1c45003c03000c00c416807503802c544da0780c605443c00b40501c0307220342070070 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 971280521 1250 971279271 971279273
    0xf03021b0a050307060608070f150e040c110f010903080a0216081809071b06150518090c010306050913051f0e120406170a11040b071a06011704050703 66
    0x7400400449070090b0055a070f5000c55040c45d42c1960f503140e1217000d01d584283e104201c5000301112500075200165170200314160141000c817500024449000c0c0d11500e0306400c008642e802c42000d46841c0c03040c0e800d0342c1c11900c025061900f203035440e40300030f008030b00c1043c00140c41103026802400702c90300031807a2503a030104c0d903144c0700d0050f0042c0500c42020100340001e030813689000e120040c3d0000c902d00c2c1c10b0342080314044104008461a00c0010030490301c031b450340c2d40341500b103610030300241c0400740c00a401c010314045804012003080c1c801803000c1c01000d103e400c0c0e41d4424080c15045d0340015180582d29101ca0340740303582001c8005c4042c3c074140141c11152215034000c000f00e1103040002d00d4041680c1c42c080e100c0034244146c403500003581920400003005001e4000c004103031425000c1c1c4a43c00c41c1ea841e40820009007904a0b0000030b10f0303900040c0428a06640405083d006001c1c0d07a6860300034500e4100040060000c2c1da003503010440c0110010304c41030301c10100c0e550151081040d1040556a = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 971281771 1250 971280521 971280523
    0x8030a0c020a0f23100c060207020d0813030c0801020c03070b040515130317220804030501020408070810180f2f03010b033f0409090c0b03070f03021b 66
    0x1180e0021307159440c003030b5592a8000e01c081d015030950b54049031502d517141c240c01c0014002030f0286000920345500070401c003055503224503d00c200f01b5001035030540d4420440781000c2c0a5481e9000131521030002920100343c0306414401d881d920f44101e4002d41c03400c5e40c2521042206840244115000d10480410340100030581711854054804083d00019201c00c514005e41048882520b071900800e03841c04010180c001a51602110030510328994840d1010b810103808134481e6800141c00c946c000140001c4140b4000794000032514072000399064100032103a11015980340050001d08083c4900d01d810104210760862560580310315514142c034440040c0000401200700b0041d1024030a81040c89000d060a00904454074811000b4106c200d800303c05503181c03603580c41c5154040110252071202c4240d518041078a425042180180e02c9584d00c0c41c91102411580350304a500d100c040f000015015099170070740340581e40c15101e0102e0321405040031030007900401300310600d4040c1c0c62440440918 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 971283021 1250 971281771 971281799
    0x9210b2203090e091615050f030405030705010c140d0b060705100c020d03060302032a0d0506041a04080913060f090510080303040510020c0109021002060702060a020408030a0c020a 79
    0x101c00c0e00d44142d2540f41821000700307560021301c0200c041c2c201c10301d03c5481901003a141819604400741c00741c2c13a140c10080865003402011090211542c1c00418001800340c00070140c0f806502c598020b22011001b0b030b10450b060046040f01c0c107419102802011491940e41d008010f0610001d44140e0038002d082c0c9515142c05011139601100d150f07244820a0750f03550501c000c0302c00c0d00081c14144029491540070994540704140604c4030b080b40c081503c00c1c410040c80360b44124583c001c00d250b8011a050070202c0d00d0310307000d89003142c883d098814913041c0070501d410894405c075007100e080307400c08a0920601901040007142d5034100355990350040707841064a000000038144006c0006520315092901c1440c0342002d411103141903005000b04070002d5400100706050401d0f031040962105107181100d8050f00280c07000a601c2003108040f02003040c1d0000d260303446190f0320ba0807202c0640711132140c401248514020200c07030350400c1101d0308465000e0544031802c588040e00803070015945803003144000d8 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 971284271 1250 971283021 971283023
    0x70602070512130b0315090103151b0801030303200c0d03181e0f050a080a0e010305240111010c200609060613021309020a09210b22 58
    0x1540811940e0500c0300c01c0040304428503060300503c0c5491000007414003180030901c01c4240141001001035914000510000f400410181c1920380c01c0d6100d10300100140754085110654034501480611417804912401d5820451515000446d9085031000c07005041c0c040c0103056889411100305990314600e100034891000440c0152000c400711403802020743d080c001c0440f00c03013038244a40b80042050400d094290250342031034103e4002c0c82c1c1c0b03002d200012007910003a00b24001c5401d02e2040c0071a803c0140001030007550b56040802801c0019421101c2c240e95400c0040183c1c02c1c0314a1036003c140ea14004201305041130100b0101d540c41c6d5130301b0340740c0301c908400010302c3c1e88021260052030503940300400c00220002e08020310301030a9481d0344070b00c002e003c20f1103650300601110041c640369045030710303445108082c0150030307131a08002c10103036101120b140000b400107440069100c3c10211801e461224038424245020f03060740341c00c07402c100054000790501605024808201000b540001585 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 971285521 1250 971284271 971284283
    0x3050f03220c14150d0b030f10060501091e060e01050c1905070b0a0509090402120123090c091302030f071215050108031e1c05040b0105030109050d0302090f0607 71
    0x301d003003c0207400e00140c0b84100c0e50190708000060320814180c00180c5107603100181d000540c00d03001c2d4002034540498480b074007020340074001c0303124411400d03901b00c0015500d0071b803142c1540b0783e0b42e0480d0000d0f1002815525040707520004d020721500e84122050192002d051405c0da05010030311030072504116144070f095448410b0000e0300b4080241c281300d00c0c13006056040c0398a04100004002900900c202d181030f6108a00d035400141c00c540d281e0480d516a80d0031007000700110000c02009561aa10050b6507015003404076000907144400040c10b01001403015100260319241c9441700380782002066030482e458090714046000101d0100312400040100100b14890401a402c11042c9820780b0600004d5030f0b803c080050050580000440d900d14189045c064145100b4100f00305141c01192403c0c981e40444009101030a032150300322a0166020b86000025030341e8450405080f0382c1c4030742c00140103821000d403400f81c2c1400783c0d0107490320300006011007a02c0e081510000d001c50f48145011544 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 971286771 1250 971285521 971285543
    0x307031506271d0103020a0b120106030506130c02010b0306090c1005090d1a040b1e062205010602030c1504050a020909121b01180206030c0f1c0c1b03050f0322 70
    0x540c0780c10f014240c0140700445039540342c8516040c003081c07270351030501806040c19180d0000c181c494a6110355941e03404c5007480b040046210b1080024041c040364181e091092140383d002c80c40c00b0401141c0441000c0000b801800d80300702200054500d40c200e616000e6020300e030003803504081000580d2429003040620310403081e81c0f8051900900b5084040c00c40c10b805030700008905221400008801e4008204a0303a800c01040500030405820040d0900c621100e401c0c40000200300d81c0020140140f0160b40081ea06035a00343c8000504410046801806e69480050b06002500303049190980000c1c41d0800c0d44c0d0304c100c03100040000740d8400300b00b104a450701d02843d150102c4003846a0319104200e0791204807100400d4002480a00001d4a05070030314100040c0c0c0002199904225a60b54220b001c0d060702d1112500c40e510001d0003920010408108111134150004400c85400310000754151180c504000004400c1645074000402400c1480c1d8400303000060400c0069802c000244603005040c1 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 971288021 1250 971286771 971286773
    0x1203090209010b090306040605092a01020c041a010f02071203050a03060e100b03060d0501090f0c0b120a0207060b030a0606050f121506190b0307031506271d0103 71
    0x142810140c0c8100f1801d00d042c13042500d2650b002c9420350304035401441c00310b160b1703c1d0883e402c3d06121602c618030004141c02269040c0c2c1c802c0f03038803280800410903025103410402c0c4c0020312050380d25080c3c0194010481019056280d030040c001880621528030450390080e898501d0404500b0780040c0681c084bc0f00400d160507400c0e4503024100c06451003c40700403560800c4005000c600b01e0318010107285840c04800109030382c07912001c800c9803d40000085c03140350303501d050000c0d229980311b07010f8403018031502002c80c894416000f00c03101030403400303421511542c45803075400094005800403036020752628038001c01030303404200300c1d160140a0b00000442515200800c03003c8142440e1850040c00301c00c5030b49051843c04141c0700c8182102c913524540a0791500c0c00074500d4401210b0003021003041c0040862a4400da1000d903100304003d80301007003024480403030503c06505520030340e030014140301c00081c07001c14298610290320700c0001ca1030b6421615000596511403332070998880b00310503200100 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 971289271 1250 971288021 971288029
    0x1c031e11010f0e0d08041e08040905181c020a150510060306050d03110a0819080105030705060712170a090b0604020702092701090f120206062202040312030902 70
    0x30342c0c01d441c0003000c0101e5941111880d450384c9080d642c40050204480009040c88112054100c2c0d82450041140040d0440c3c5450070041d0040d01804603000d00d0f15000591062440b0a0b00f0140d283c40c2008208800e058031001841080b800f1001d011801035400c001e00007500c520307174122034020f1032074049982c0ca00610f0b01e05100b034590b03200c1c20816050050800c00c03621a21500300410780c02d403411400d1a8655007a161800050781001080703004001810501400600700303400d0320b0032055840075007030f0340e0318020103076607146034050554414800c024820000d1144c0d04481c0d5a61843d0801004400002c11824199041151320752a1a61903207030031020044a0b0350b8495024904440840c10082580c010a00390070008095440041040070041c07040e50f03260980e981c4014655000b40300105041c1b03081d50070408600d00c00c03504103070002e01d171541349030012500343c2c49140c0c09815070064851003ca14000c0441d05ca0a8044480c0d00304000300c04502c05950030300313100d041524013042800c15417040c0 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 971290521 1250 971289271 971289281
    0x30912100c0f0f020d1d040b0603012d030309060807020f070b030117060c0726032401111f090b0117150411010c020406051804020102010b0f1c031e1101 67
    0x410440d04a0700420701300f250403100c1b40806032001d00340c11520383d20041c04207000304403000000d40e020310040000039080780c954180c1460081d070b1001141b440104001090b05400490100902041c00e0b18028480b491040314069800180c3e03204a41401946080e0a400d041c000c1c2c100f1001440c000005102d40c030414141c12101000f004010045441c01e049038054500030400000c003030002500500528030340703a02c428076040a0340c9200a0384c9042000440c04424440e0b9140141c0c18100074601c00f196000c0c855022008400d14050024221482c0c07400d855108191104c14506c1d170740b0001080132811010030b071406402d481c0d4050050300c1e0792110700c500c4c1c06078a00312684402c405901b000009154083d986007044801c0c28054504016440000c0c050305098206503040f00d01c410030300b90800130540301d1600440c000c1c0c0080190f1003d0109000d034070400b0340c0501c0d8002e1210803080c0310304911400c4e03054103035000e0301c0c00407560303000c003c0c484900c110303042c0400000445c14101880741020a11075 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 971291771 1250 971290521 971290547
    0x61214120408070e090304030b01080a15090f030309081905031015090911040909050a0c0e070c020906040b19090e060403090314120a0203070b18030912100c0f 70
    0x10300382003500e0660015902e41c00b600400035201c000c0c0000c10007944003001560059948498526155078585507103030f51f10840c5240135106001480782c0ca114100700d91080040d00c0340c110161506440c034580703058018001c091800c41d041d6104020804040100411105858190369a40c9070359003051143d0381e60009840e08a41a11181450f045240d503402590380303012107190030f1001c241141003005000d498041c41d0f10400380e540c00d150301d500421502007040424103200d0b206030b2000c0c13600d80700e200b03051181c1152554081512a401c1201501c0c0030121141e02c507200a10100394003108801246404c02111501c80c070b8000089000e01520145014140c0208190030040c0010324141e24000c03c1021684409002c1d9400c080103004590424820591761180e0502166a2030180c0140255290300400c1c0684861130848086403080442c01e004942c0d0b0031f00c01c002141401141803c20000140c10001c0880b01c3c41480300010008a07540101d0b951140103465410b414940c003800a130850080d190 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 971293021 1250 971291771 971291803
    0x512160602100e2b0e151b0c01120f020c0307030c02090f0417090d02030a0b01060329010e03031b06010603060503010b012f011e18050a020f04061214 66
    0xc185980c5001c0313903414a41a0480a06541d001408460283c0392942500d10490308071142e4100f0084000802c0010911000c48080da82c000d500354124070344e19064030201050001d10a00d0045030700b4031603900420400e5020007801407411600040151840d40410411004107500031f00000c10b524003c02801d80c0700c203400c1901079041c07420756110700c180a081040c1c8100d82d42d0201d0203180700e40b20b103100b0603810390b8060200d42070b00d1453f00f044007044d4024403410b00028200b2011822550755442804d01c000300381a00d0307407404641c1d04015030b90f207920001615014442031164605810300c061a441c0748201070f07405040c0a5041c40d42c018191061703a0000c6000c1e07030428810300c0e25645d105064000e000d141031400700100342c2c01a01c00a003030030001d1201c4042e40c20007403540700c5046d000045c004034400502c030030803809400d1041440d40c50703140d1102819030f4000b8105440542824280c441c4c80090041c40002c0036601c50b02c0042c0d901440740d801b41ca04080c0000545580f6101304051601801160 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 971294271 1250 971293021 971293033
    0x14041209060503010b03150306090616020703080d0f14010303110c0a030822080102070813082e0912020309030111090a140301180b090d0503100512160602100e 70
    0x1402400912041c458001704a80010004040490317041c2008448a4000d068442c503040803503409642b40d5040c4d801f5078001c090140c03491a0386000154000c01c0701c1d0700c040405d0800d0000320069008081c0502c00390a040e40725100c43c0c0c4854100c0202c140a0b520913100c0404c600080e12190303141034003400c40701e40140340c0604217001003500c0c2011b03103d800b1002545100c3e4180800c0d01484c5909403940440310941c0049114020071103510080d04480d84003e201c0316001c2c0d5140841c0da41c45410b010800c00c1c1c450101c0c200716881d0740156541c0c5000e0142c110100d4003a41558503c501c3e80001e00c6c6620050700040346681c0203140a005800141c40041c4c3c101d410590410009600c0c43d500d44100c2038004003516019020382c90030340010002107008007400f41042c2c16818102511581160028004d001e102c4e000c2c0800e50181042e00d025400004408010030300300014452025201c025045081c0300fa12165a254501e0007001006031109902904000101109000a4a00b40d000042c42c6820031 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 971295521 1250 971294271 971294279
    0xb0a060e06090a1d03030c1c06300b1e1303050405040b0d020411030601090b0313060504031107170d020a0f170d0c03060302120c090f1914041209 64
    0x81140560440d540c02c800044e0b01c0d00d46803d00700b6031070100c00600c0080c000442000703e80002c10000e0080c8a004001d84001480712201c203c00700c0b081070082d403414103d031030360100c01d00200b009603064203000c0f18a94451075000d9100c44401c04000c40d50100c2900c0c05898001c1d0080212130340035008002c030401e0281f010741c07aa60140003806a030003181c4c0075a07603c60202c01c40b41d0310b61810541042d005803003084402d07102c0c120786e030942d0700c01c0310b91601040c0d00d0b120014611519074100c0e840342000c810400781e4003880356580c0000d4100600141c0030043c2d00302e03482c03446072014041070009008050788140c4d0000260610b03410048040303628410b64002400b01e90101d980340000410030f80e4000800c400d40c40710000011054003034101070f1306000b49040c1d21401902d030907a00080a1340d000300c40b070080d82c21401006556030924107070351503040320065003c250750744410680103030801c408102c0320071440000017404048408407100f801070078680c01b05210070b1040c4040d13035500c207240e1494030b00c18850034 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 971296771 1250 971295521 971295529
    0x60206070e090901111902011104060c0f1a10090e0c010210020d061a120a0207150b0f19030c0603062634080d091707120b0a060e06 58
    0xc03042540780200b04101c00907103448000c4d4040d2101744041074446449000d109046103503080741c041540b01543c41c11000350448880102602d040b994203588400b880342d095982c05031140104001101c1c1d4803034401d400311400340003807540c0d4070903c0c4401c0034140c02442c01c1c1d8101c00b41d031482c0400b00c2c120b13000b000c0340b41c1c540e036401704102c2d1100e0f04a040141c3d480501088420007080107503c80210802910510346980c4080d00060121032020040c030109500c40154a0040f40701300da500078042000c00c40d5402440c400e070380000200403c01000391017a101c010001c15031035180c480190500d040050070510400181c240e4100240079103240800405003400d5183c0c4851400d003440401c0300e40c0c40ca5500007100810000c144a055002d1030f0011a0084d45079280c8161442200300140049400303404140e0b072500081000c142640f5a807500100d9141c20000c9448017105580c0380c0c458045c495011a02c1010441c4920f02584282903044145c90208800400c4030502d8014002c40f012410501800f695 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 971298021 1250 971296771 971296787
    0x10614010c0327030c06030c0219020f0a03060509010c14030c090d0f0f111002121801120c0206060112050103020d080904020c1203060a0f081209060408031c0606020607 74
    0x35040c00d02424441d001d81000466005583d440c503d4941188008001c21140504a030100d81c29074809000c1414040400ea0f00c038607118155400f0001d4021188000d8a003006000c051312001904441100e500c0c1e845010540303104840100050f0f451f80420140c50b580301d0728026007a407000c90f40c0d03800e42c24041c00d04c07070082c42550b01d264811203101020301d05000000000c6030046a21000c0004410340c0b88c6025207200d13078460242e51044654078100d1174582d002141c244401c444004145182100c0c14413050210070003211418100007840440903450f04c024804c0d0f10040c1d00d140c00a060601d8040300060003413403a041d0b0345d81801e09007001080141c0310a95104481c0c0d82c400310f155212240440131400074024180d4160941c82030b400c2400e003005c8218021809180306480c1e03585100d1300e424a182509d43c2a2081d8909070388210040c0302043c1485018000c0808010542031501d84d98003420344c80c1d50820750141104a111202c4801b010f109882002c009003002c1c00504401d240c640400342c8404 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 971299271 1250 971298021 971298023
    0xc091502161e180614010c0c0e0a0e0a060b210607140f03040f0209060105070c050409051c0e01030b09040210030b0301230906090f0d050d09060617010614010c 70
    0x6009941207080b94640c1d00344240034021108205400303a14803d112006480705219861000c2054143c195155104002100107241c210051a00c0c96140141746d21250b500141200c80e11a903598241c0d0711f1b090144040168680200d0000c10000615400c121600300281c072401c8503010603c10545803030038081022640a902828000020120221800841e00c2581508169001c002082108107c03e9042008540340250b81d101042d0340e441d401541d45101d141005400d00c0c0c0301d01d404020501e880c1c0c11103d81c2510807000d482c90303030700c07000744005101c00300b0b01c5101c02140d03004404410959140c8505840303600201c1d003130300f000d0a05402142458882d03481200c10140c90b04250245900d00b5000f50170000e952034409020b03c24a405c080f050078a068812001c0e43c0581c001180b00680d00107981c0d80311040041c090044046014000d4585520201c407c00100d603c0f602040041001031082034010080c0700640d1590041032902142110f12541060740c0e000b14402d0340024503640803007599041 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 971300521 1250 971299271 971299289
    0x20c10090203101503060504080c010f050c0702210303070203031602010c05040312030b0907030b031b0307061b081603110106060818010905071203120b0f220c09150216 74
    0x14607405042001c49084c07940000d401039081c9018003003007000481c010410900090000c020040c260f02d46078040da1025a010f2075842402c1c0868070141c07824070170000048105905805540c80712420540c1190021030300c2c640560004000c2014141c2440741c0c19034041c82030700c000c000402c42c0070310141031400ba9000150011003140c05070758001d40642d20081840400400103005d910384800000c020780403013424140a80a440c1e0900302115120303030301c0c07580d200c1c0081c040c00003141090801c07550210081101d042a0801090b0780000c101408001c041d45d02c01550303021000da54506000c0c18940540801d1308850b8580342d0100038070340e804000713650058104900d00140e10103041410f809086a81000b03001800303441b1000422103c10001c0c1c06020703110342c4455a48200048040c0e04440b0b007041c0740c40e0030044c1c0c3e6251030304915000c0c241c1d140641482000031050010b211083d01200c2071200e040380402d0b0700c0c2c2c205008040281d260102c440d02203100074505074038180b81119006100f4881c103054 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 971301771 1250 971300521 971300531
    0x162a050d080313050a061a061606270b04022115071106093022030605090a020301150803040311030106120c051806100f0e060409020c1009020310 64
    0xa9020151240c0f4180c0002c1180c4600c202e070f0910000800400741c000800f120400c100d000d060030028240c0c0c000c19000c06240300541015154400541500c1925406810024090008120122085142041c0248201510346c030b0a0b1040c001d080c0100f00c03914207018007802610720070720000030703c01d041c01038651800790403500c0e403410a6a00066407542c04085004840c100040c1c0307600040d86445000c1002c4003055203400020808040244c0c00d00700742c00e0030004001d00110000440e0507151101c424014034568665a612082d007141c42c10f5a6000301e94000380c910101303616090080d0a42a00c006a241c0401c1d843d00000781d59038444c038032004081700f446c42007901362943c0c203502c808020701586012078140e031752519281d050400d0f80e000302442080c120b08071054240c01d00c403100d842000c02425103000722320504000d5039100010070014003041a40d003001e46007911094064801000903c101580310007202d6407030760802026900c001c4036a882d00d0369802c09070ba000555081c0b200502980020 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 971303021 1250 971301771 971301781
    0x2090c0f07060c0e10051804060f0608040f021c0203010b01030501140f1f0203130e0708190b060c01090c05030a0c0501080403090b0406050408010b03070f150203162a050d0803 77
    0x19110035001c2c1c1e105d900840394003c0701c407055004401040101e090003558244030404400700011a4098052407074044120602405564022216113401c42c0c0210003446200f810390340021003110b0b03003010104640010380030f4031045003401d0154004100007420b003030007150304141c4461600082c072105c840c8107080355051600c05444400c0041c58484c00851041040001c88801940d00d40c801042c0782c0c68110040000200311102150081c000c2000365100c2c0d200361142e800b21413442441903070012045a90f042c4509042d130790200200900110340c0004a98403006040400303403085164131560294001d2542c95000840c0c0040400554000f420039200a44560404503040d801c15081a80910400500070a80640002c0580100c4074004000c0c4000307a5034500b4140c440b01c082c8111f480881120b003080c0580c607549a540c0d03001c4c0d402441282c0c2000207000e810620312400d07460a40381d4130340c1d0840351030740400f0768030512890b544040c2e81407500c1c03030ad8003011511080e040940988884000b1021507 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 971304271 1250 971303021 971303027
    0x19120506241201030f0209010e040503040515090406091d0a1a0702150108101a09060411070605010e1b04030b0f040c0503061602070f060c1b0506040801060302090c0f07060c 76
    0x59100b41c0c0c0408540002d684924003502080110803080c0d21800351000005640845421001d106690001c003031400c00c2d1400d400c0c00502003060f00800304d5842c0c1803060440c030f501c03540304040040002940119503496240d95881412420f03210081035500200003050205034160700c2028504006003c80e01e0319a9007400403803c0a600d01e03e03c2c00d1480e40a030000414280001d150713100c04007005800c00080502c0d02e59101051568101d26400000c000000344003481d06a0055503081f0043d8071192810071aa43ca1608503102600000c28000c2000c09200002d00042c12034041180064112032606065407500004410020f1489c0c0c1040c500c0ca001074101f201c03030500d4900074040074048610314140594005d00e07094070a60303040010300c2140b000103020807106905004a03509a1a8001080c0d110380390903036805114045840303150441400020340e5100c0000900c01041a04000034126055104001c41c1140141100e0025202800392009600007102100d80640c0d20180010b4034006c112400c0d = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 971305521 1250 971304271 971304277
    0xa0c02130e0d02010b0312031e04021f020a0c050d0b041518080d050a110702121c02030a02060609070801141305100f0503150106050a050f1912050624 66
    0x255009000380b10044452a4054116584090044080e10021011000347c2100c3c0d01080340d5500d100b91403201400c24201481d00c0941d0030500140c0294448500300c6c4d19007101d04d0107410301e00010380c4420308800074003080c2c0803044003820003220085800c0c1d1040d280d0491410700500041c06088181c14000c41320041a840b0341a400c1440c075401580761a14105035816400010760944136a0911001458085961003984001880c010b0040d040038115001d0001e1820003010b40e0380c02d403183e142075102d0301c180844c140030f444110b03034000d41e0380f81c80705507000b4200722001d010a40a4a10f0205101c0c0075070f000076200c1d05481d064091345210552980004007014403525041d61442c0c41c1c90240840c041e0030f100c8020070b9429002750505425130314024140e41d0104042c010403902010030050015901c20001020450b00e0b038542103082980c8103e170b80d80e0703d40c014540c100c4240d0405890b8103045810040c4070315a034104e044100120f24200c40443c100f56900c00c890113900404c50720002610f00aa415 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 971306771 1250 971305521 971305541
    0x30705070b01090204090528020c101803120605090703090201021c08100503030f090105031b2109030c071a1213060e030a020a0b0c0d0c03050114060a0c0213 69
    0x35841c195949180302c000039130150060208013801d00000070743e00300c0304400e180c92104010420307500c071010008a15000390481200c2000e14003501c8084034074101d26000360903070381c0e0905095100f50364103458060320603511039080c1e00c50705003040341c1000b85658418600c4c1c0e10081c0b9046c080b40c00481440101d00704540025403045800c61000c0c0301200b075034060013161007007a40a0305001c807541c0f50360415950b4001d80203c3e18248404100404440d4030900155030400b5030348a903a0480b4403c5552036459402c040003c000d48010343c1d010b00c2280351030800454010030568080c62420038481c18041d00e03810341d4040c501c000000c055a00c50411160801c41e02d959400503004007003400c0689074110781003020201554145c0c203040620450000c01300440e010910720390002e000500300ca81e2022100c00340141207036200c136002d001c40407090b072890080d600c0810f4036a40c0080d981d8140034264082c0e056003000503005000a2020300d003416000844d6106a640454408509034003540c0498050241d00e50 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 971308021 1250 971306771 971306783
    0xf141f180905010f060303180506040504020705210903100603110d0c18020c01050108061e0403030605092e06141804020a050403060f0b060d0914030c0d110307051203070507 76
    0xc240b03007410255403003c0c1c11ba03032180d607451405080c0302c481000300050a005095103c00c0c00c00080100703160590090401911540c20f5802d05030709421404481c4070003030542030381500c00050b40ba03001e207024040e403010089a04001c01042781940c4911246400c15858039000c0c1019410320f4052000a5a030303400201a989401103e6000320038052001e0740058404200ca0341c2800008210b0002c0820441c3c40f400c42402444d02c4103141c502c40003107202e4064070650034540d9a00740402c081d241c0c5e40520b0b10401800c0203c450640402020b80800507c0008036030381d038a401031041c2700341e9078802040581c0c4c1c03231407003091a10740760154007100a002120b60702c0c991252001400642c3c080d0807101070700450b4003642d002c20600c4c0810414009444840340d116070721400c104165458040958000020355010303026400c011055005190314581c4000d900c1c4a070342c2d000503e0300c04507503171107170368668005a404080d5080403155a9900e981e00e000140780ea0050750080005407460b03100d4010344449a030440 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 971309271 1250 971308021 971308031
    0xf2c340e040f0929010f050105220e180c01020601030201020c0d0519030906140702010c2a14040624030b130c030f0e0307150f0f0f141f18090501 64
    0x100c0b000034032070f6400f10714503413404a8500002e000e02291a06a0880e00d06031261032400410b651034800d45114000e51403002200c1d800046609141000c00b03a02c55050586110709440141da030562400120043d01d034110760002c8010300042c0d034082003103203c0d0b5005a59205d0024050b1400300e08103a9a20030000c00800808804000d05600c43c1c100d604581d03007074070b466400e0740b081503a88a55115201010740468504071703e01001034054020b01901c100b071a00075121041c10745c0c400000c0b00045a104440c90310220450b201c2d1403609100f01f200420209915916211018000d82001d0402c621040d0501d55a080707a100790ba107a2500b21002e0345c03500321040058151100d805001021a650304000341c4d45054040c0b00c80000c000112440703182c024007204100f0713026210707601c054481586c01c05d95898035041c02c600c05641c03c2c000c01044059500000c11000f912840140001c1030040c41558001c040d0070481104030703c1e00c40110306540c04039542c40091000c485056024000e4101d00410035071911b = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 971310521 1250 971309271 971309303
    0xb03030c03030f0601091505180603090d121503140304030b090a06050106090308070b09030c0d1106070c0215070807021f0e06040f2c340e040f09 64
    0x8030003580b10750b82c400740e010303c61344900c00112440b42603070041540e01c4503a002c001e01d000340120040c1c0000800c058050f4407044880d00414070310340040c0c542c80019441207070000c3c501904034400352002400301000300144186443c00c1e8540c0d1240303110240005003401080902e80c0014401c90b0007668011903040413500b005c2c4005a0781d008000415103055140100118100d4491141041220303040b46d80c044c2000da45031038240c000c4402802d001c640e0300c01007010081041c000c0c442c9202c800183d46945200d0000020103e051080060a01d010001310048403001695540c1d2500350700301d0f45200081d15000c0e5841d040030b007486510000703984480400c502e808040715110071103114800664915403016003038014051940107a0045120034003a55809005045981586500e030401d40c096032142c10600c491462240b402c151088140c1e005010406036042a20b0318000300f0b104483e901c1e4841d6440702c040014001d421021100384110348070060b00180b49450b402000e04c00e900400301042c0d50501e = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 971311771 1250 971310521 971310523
    0x12030c071b06050904181e0519030c1b0e0f0115080c09010c0c12060b12150402010806190803180108041e14030d091e0c0b0d0b03030c 59
    0x100c01021035030400600411049019049400303402c441c03141c0c450500700b44492007048040c1c803642800101c40c1c82180c8941c1e0118020548450100c5801c44603401044c030203060640c140f1280c042d001e5003820f034101080340001c1d485075151200e2508000e07c2c400c00c943e1440e200d00d6203e01544801c00c1100b030503041c42252860203030325034103e880c04212030180090b16201036030080c400301e03116040c0b040d092004451550203103460041c0c0e68402da204c0c190030740c3c698043c3e003081110040700307441003076031400000c0482c1002d000d00c0080c034068034010416050f03802c483d80706070b4400420003410070041d10046401c0740c036200c400c00d000505400100005c0744d207035490141e41c2c1d04030000310000442000303440c07540f950251a0f01405243c01000710700300010410a52805044a05c00c12529a90303008000c3c0301070401031000d450170b40401100442d211400d070038103040e42c0d42030315620704503d10301c008414000399008000300202d640a2804d203895001800001e4003c0601d0400c081d018040000c9501c20400 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 971313021 1250 971311771 971311777
    0xf030403200d0209040803090723010f110d03020a140a0804050c19090e0c030f4e090307030f0b010801020307020a0f1b06080603060f2712030c 63
    0x180c481d0300ca00e50076122040001002005102a41100e035101c0401c0c04283d000c001598841401400c95403095030740d101040700b10000032209000d5168a003890203aa41e800400c58100d81981e01e007201c0307540c200344002900c40391901800340c00c1c10380c0020f04500440c00b8400340c1400c8004488059260101400e02902e0b04104407400c071202c1c0a507e6200010307152404013082c48101c902d04100c0307420304284810009040c4058480001e1041000d440515a0308200340710307a4106180c00340620740c0620740e502500741030058001c402032a906101c81c20640403a2031035210610f18801c0c0000d0050b60040c00c8090303208003180a9014065110040103009103148840311252045411414981e0781d601a00d01701d0105484680058011111010100300244050b48410b4051046205501e0700d0580c0c10100c072200c1d03171000001c00d0440d420444580342c1400170700c1d880600081031700b01754945401040303402c850003111003503450501c60a07002e240004102c82418048180f00103545c0341440380035545650 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 971314271 1250 971313021 971313053
    0x60302030412230309030f27030a1208071101051512031204080a05090a15030b03070509070c051c02011b0203090303030a0504020d2a05041806020c0f030403 69
    0x407400b1003982010742c440c0e032542940001d010305004400d41d181d5100903050340068002c80e0240b10a01001c680503d6550003000c136840403ca5043d50440d074548800b89004081150030321a400c4034003c1c002284046050904044091a05520a07a503200c07082c0d91628564603000090f40ca000f00700043c4c0301a4042d4042e10800844070410b1100c214010786560703104029542070550501c801140010344a40040c1156940031b0800c541414100008540009515403218484082d140082c0d400d05d0b4142c85898400d0f60103501502c0d2503800c140c042903041002409105c10411008410800d200040c1300001078076410645424003182ea42900a010b07001c9849107041c01c002400d19415031038000021610f45003000b0b00a18210741e600d05c01c810080000400680e001040700301058001101c12a10314101090000b080e001c40c04c948003805010304013900103038001e91800d88111043d00a8100b102103107584084007682da10729103044a8203008240c54882030714400850041304000402c24110854 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 971315521 1250 971314271 971314283
    0x91e0403021b060304170c0703060e0705010813020306010605030603120c01060509010608040b1902070503070605041502070203070509091501030b010929132309060703051b1e03010603020304 84
    0x4410900f0441d80d48000d85008104440c020441205100c49001070248201c41000b91902d2598176280d0600b034034006461003a0a410a40f010712156821a1040b038009492210924821415a020964801d01800380c90140403000c0002070403030340c041007038110103001e005013540c4510149507014040c101038050702d80300e190b4a82c00802e006220354205480b880c2c00005c1c003512610b900403c00ca00103141414440013a4003040745101061080005080b228403078031001440346841d05191089510b03007000d01c186d8500402a1402694000981c9400d58004682040d10303522484280b925205043c1c00d9040c100160b03030000800d0024501d90709040f10740c042021b200c0031450140c0c0a80191308007000072600d168007a901c1000b81480c1c415100d4904000500141c0880d0060f4040203004c46c1c1e5410351032074426142041200c65003800850307040701007418203200e00e04100442c10014818400b51485419001c581c042c2e146004074040d0000e24258070007541d4a507141c510080180d03108a07029540303 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 971316771 1250 971315521 971315563
    0xc09101a131502061803090d2019060311040503010c0c03020115030309060e0102010f0f0c270303051602041127150706020f0c0a03090f030b06091e040302 68
    0x400d240e030a003084101d40040d07000d80441d9503800400d1403030040000b52601702e44024080007000352202500031903490300818043c428524041010440322111148003406916002e99642541c101103010505444d42d600f404101400c816524001d00d024960245070b00d5070030244401c00142e013050520400900130741c000e004048004011200c190024840140003524410003046040c0c4214110440c0c1d400510020441e03802007003004080e035104200c01190035686515100a041e00301650741c0104824120030405806070400904070700c4018071010b42804000030700b60615405105e084c1580d954001c2040003c850b00c201400307030a4008520302d100c007040b240c00788100b00e26060500c60b0741c1580109120307940328401809800c41e400044040369055028000040c4c1ca03201c50014050b880c0e080801403074025101c2c00c00500e4154503900001c1525251401030000c00d14811140c1d034029002c0d0780c1d44115881c0c82d03c154000c42c540190300c50100e000c074800c2c4810107901165440302204014150750b0 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 971318021 1250 971316771 971316779
    0x50307110a170a080d18050c010e04060b03010e04150501060210050c0c0a0219172407023003130b1b0909040f0f05160b0403050c09101a13 61
    0x40141c00640c01401d0540c000c40800001a082c4c00040410751140203001ca058003000050248410020004039a07942204103842c645580c0a00c40d001500b04c00c480c14400c091404240c0f0070548418011040c640e0400341c0001c0c03d025480001e090301c903008100c10800c2e076945060080d21010303004d40c1c0e24032440c00d1001194050488a06a64141104801034a00b81406c1d81c20400070200746048021110780c6090005100400704641d290500d00f0300002d4240303000314050032401d9001c2300d40c03141540645401440035007a40002d40f401c810404c8052041c0180000e0051503040701880f1400000d8803001041000b890b20465180c0754061046030002c80580b01c15201101c005600700a0440b40c410601c000e031035500d00b0100584d0480d01407280000d13040700304d84800e200000c000c0400d03141c0313900441c1c28401e000d41d071121440080612001e49414030741503596039900c80c484050141d1045a80c2e03008101c41c5c1c2e000741c015000402c01e0740d82c60034003410703d0420000560807a00c56030324505100d010002d = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 971319271 1250 971318021 971318039
    0x204060e12030d2a020a12030213060c020d061b0f1b03080c0c06162703021908031b0c0f010503061e100306150c050d1b050307110a 58
    0x907a0385038454000e141840d00503902440100820b90060408030b50800110081d130702c502c104031009030141d0b8040c0c4148040c60800048030006c0d089000c0401d807041160400e0b9040ca40100020f851540c9030000c01040a4000100704081d80e01c0701600e040d1405000c03200005c0300003003007600003406484098058481100503241c404184038550902c052400c02d6000185c895400180d000040405075403c10014015162405c0c1e011106280a002d560030301140d000d1700402d0200004110700820445003076080480b480450517031000a0045507c80c1c0000c070309410b00c1c0051400f404008007280e03140c8000680a0b000d41c40c01394a111200d00420041c48041d051002e01c5051010041c3c50789881c40c2c42c2c0f10140030903c84108808044001c014400c665a0385c0d0b1403941050041c0c0701e80d40454914203010304440c5000528000005101805161030005600894000122003250402c0070b000008403038405015541c6202c010032a000000c1c042c403c102201500d0403e804003901d54a4030143c5498003a = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 971320521 1250 971319271 971319289
    0xc110d05070b1303080f09010801243f0f0b0603011a13030f02100201050910020a0306050306010801020a140c1902011b06051b0715090302120d0204060e 67
    0x36109400061040c000414008020b0020020b0f41c0c1c2e40b2a4031036070325110829590058002107414000020784c0040c50b6038400c90701c40c0584411080401803c081c07000c40001c49075001c0c200c00c1030107590704600342c030724201e01ca031940ca01050000d000c1800c0c4000558142b40720005818003002454900c200790002c42c584a440f003101e50281c01d603451039080c0b081c1070200400c02c0300b00c846101d2080080308848502c02c41e0392401944140b00010a5400720b10401c9403602c0151030000440e80f4000400c02c51030400103c0c4840b507010301c680183d803035000d0407084025240a0700b2845c0c1500c9003d00000300c0c2c080560050174032000c9503440821000c649004480d1724464090311880c2d5a220f03417000c80d101c404410b041c8207800d205040c11000d0b4900030180942210760705209588056846c0c0800a1002c0c41e24000005104a200b00a04e421031035038441d95045400403007940303060f58480c080010103008200c0703020141e550081c0309407035001000c4c1c042c010754454000d200000c2c5001c0b5214010781003018031 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 971321771 1250 971320521 971320523
    0xf070602070302210d0f020d080628090608031309050f1807050d0f17090112050a09061506090b030c0d02222d030209040b0c07060c0c110d 61
    0x1c0c00d009865a020400031055182000c85982c4412926607001e0f001084003424605154884103403080980300301a080246e04003218042c41110001c00c54075540316003070100ca0b028090768020380a880002e00e04110141c54204200441c544079021560701c4000018202c048803004164252076158520901580c102395019640d0240701c00c00310f80f4280d02d00c8000e20030009038100301c0d100580d441c4001920b05400d20410b035400211032604805101d10020500400320701c0e421500c1c45c0400303020000307180100740f10349040140d0f9998088ad8642240b60049072080f40c2164050120003c40300708003864210714450a004944040d01c0003440982107411740b403003819841c1803903080c20030b581c80349030280d40520138800b07040c203403a58520391560240d08008050301912403807640c01c0c4050a84030030907090903902016242c0d80000100016038848515991095021100341c450340c9a0304604110f41c004c0c5a0014059414185042c40f00c0790300c411121071040c01400b2211440340307280c043c80001c0944081c = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 971323021 1250 971321771 971321773
    0x7050a021302120a0606170a0213060807230306061315030e100603050c012601170d140d020a020703080403050615090405072903010801050f060111100c030603020607050105090f070602 81
    0x24010300000075082c40b5030003a06008c0c058580350800121b20b0070b030301458202d40081040780c000e015106612181001e03c01caa003081030618024030801c2c1141e240401002036100e09000a08100000ba900500b030005150f24820301c610440240c00c080c01800680c3c0007024244a240e291000b294528000d2800700e1ba0050041c124610b91040111031800c04030800c51414400b40e4000c1c841802004481802070100804010014403d03e40030381c00c10504460b26410804004001c0540304088012036000d03021040c0010398418a10400381d0911140d40e04c0642804008500081030290219481e4400c011035883d0701501c0d103140e81001401e5a055a001d069580f00020030b0083c200045041b140d10041c030005071102c48080644030a160b8801d801c42082c50351110140710318286c14144240e040f0b4000d091a03200c5015101c00030340c0e9140d18100341403000d03844a00c1c40390290300035403140c0003541c5c01500c0c8950710042814494080e20f0242c0b0019041d12550b81080284500441c84001750341c9198 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 971324271 1250 971323021 971323037
    0x5100606030b0312181f08060301050106020c030705210d050702091b1920010902100c05120306040906110c0706030b06041701021207090f0617010b07050a021302120a0606 75
    0x101e0f07110200b171450750400d41c10420f55071a5802c110040c11020034180200d603a21051842c0840c141801d440c5c044e4041810b40d8840c048640307141d034004c28001c2c1681e105641000460b51a0080d940c0c0203c0c0d0405410000d00131081d4022605601400600038a80203882c40d02d5541c48400004d1b40c1c42e518420f00d2a0102004d000302c64003c45071400d6418400b04c40e20740343e10700d00c10200ca0401211050030348c0a10f969501d070680800c5060202101388803045a00740f190800300d4ada01d825403210103400441900010010000c2c47c80c0e9501e40c030841c01207030001c0040183d8034038106038401d250300c0110800070520440d100004d0742c40c420f000b14601030401600c0c05003014a00b05000f039a8100da00c0071401695001d102142106400c00c01c0d05100300159980c0003c40d92518110a564000641121040001d07660b0500c002d488031000341c1e4119034824010036510320071400c00504118900d04025400070007402c803041c9800141d00540401c184005018500340c803210180d00880380b00b840750001180b240 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 971325521 1250 971324271 971324287
    0xc050a0e0d03020a08030a0f0e06160c3216080c15040e040b192307020c0a030b0105030d0203091005070c0918030e040c140f0705100606030b0312 64
    0x1008910518483d0040340c03a010582d5460390a5034104491302c0610300c0e511880c003100d40029001d203990a4210340060810f03030401c87c13009003601e104140e1038820321200c04410810815807100d880c241c55a4030043d20801030354070f1b0501020b15189240c001107441503003000c80703151218844040407901018014103404e52640180506a18038030101e03500d6090074040020303804401d03000700d0b01c103d1090b140401e00d4500302b40c1490b60721350000c44840c80740e031401e0811040103905a00b16104840341c0680300b5010f03901c0040c124584001f001c4500e4122114030000000c00462030304040c183d41c821070030380f403220380c0c081412a6a8002c2488060b8441d5100c2d014140c000e00481c02403402d2400b86100f1802c081c2c8418202c1c0c1500c07681c1460071114626010071505041c1e11800322452106c00300c4080c8100b015a0000410121440e00380400c14100040c04090300c403802d03411285103661080c196003640c0e46158251000380014440d020102c0e00b0251051154500440d4840b001000c03000104d04282c25 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 971326771 1250 971325521 971325529
    0x17130b040b040e091203630303011706010e0c1c06030203011406010e100c060c0c120e090a051314031b0106030b01080d05040e19020301030506042006040608061306080f010c050a0e 79
    0xe1f211111801c1e5408800119903014030040d80071b4071000090721003000d0b241c0d00c00c0c0c3c9401c40503481035200019031001c1c4000e0103003040480f0421303460070100e1030b1705e0b06401004c03000914003640001d40c95841c101d6800c3c4401d12921425126030401d0300e03180c50704040c0307206000c01491303c080303201d0015142c049407a001445551000c00691010f16118101d01d295a4440042c644901c841d1001b203944130b080c0200501d845046540d1118103d00140882c1c1000c045c0c1070410340d140d44004000c01641e000d442e01800c0104144c034001c00c8001d0101e00c2100e0441580d600820050100341d6000d605c2000101e0401d1000a140103c0711103a07440d989458030707000381111500381c068881d0380405030040b280320f2091030600203540a58003039000741c0598142881e021103c510000038001c424800400e40300070742e0f80c99500b0703541200c145041401c4143d56032000140480c0818600d02c0c1c0b10340c5400706c007003803007034000882c44e140b011008000c1000d0741c0000800d4401c0c1c00713144901400207016035444101420 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 971328021 1250 971326771 971326921
    0x3190f0b25051b060c040e0c0f04050d02130f0b0901051f0c1a01031a0a061a1b030a0c02010f02010207050c060c030717130b040b040e091203 62
    0x804018207040f1492201c3d0b04500384030058485031800c4101040510501c910380341010b40140c190062a417403c1540540c0064034003130342c801d040c400c05038260160155100c008140289280f107a0b0100440d02d00c103c2204014451550300d14054a0b108002080c01e0511406504201c11590750341c5088064020702116510203c14007156850a000f400a10404843c1d01c407a01841c03240000781d803803c40e50921000c001f1001420b220301c003400d0080401c20400b201c00380c0c214480f0300b040000e0351009214000300310f41c00c2c1c0d03160418a40c480068000c8009621001490103a0f100343d83d5064900780410049090340100480a400c3e50455800b008142c54440c0c01006141c80d04002c1e0703414003c6c15103400320341d2400552380003160000001c520128019414544002d400606402070510342840340611050142d80120090700200102003032008400704038000d105001c0d800701c507941c0e1414000140e45600a02d418088855013085094000032800022023800482d105030020f0401d805a1b000031044 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 971329271 1250 971328021 971328037
    0x90602070e28291008011a07140f0105130b1303122405011112030a0b090103030c11040207030813111801080609010e100b03190f0b2505 60
    0x80407151460000c01040d000f01112000010603801d4416072002c400f090407002400801e226111201d440b142c000c1d04054642d0550b4100c0c036401524002072aa881d402e4415408017400d912600c052030440c8140c0002c15207000c0300503038021700c2140c60b029a00c000c001443c2d4002410040ba2000003120700000d08400b030000381c02481c10001500858850808480145410301071740b45039204c24604403424030b400240107003020311b003481c1e078500348103051034a070411850400701001e8004007040006000e030300300111800c0000c0c402901135075a0318014205003c01c90302250782c00301c00300348070407940b0303052080d14a06505138440c21398a5a0780b01440003208008441215080026000d00b00240c56200c894042894030400031542175041c44101c9242c600001d0019030f5684c10028401e9801602080c110a806e00c04100400d401a235900001d007032081e1000c0038050f41e4004034611042c00041d2211300d4203540900d011040f10f0311780c1001083c01140e03070306150f44c0c40c01030180002e81142c882e000402d451 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 971330521 1250 971329271 971329321
    0x504060b1206090105090d0c03030b03120f030907050d1a0402040f020f120c03090a021002070810091202070f12050c09010306090308070c0203060a02030a1e0606090602070e 76
    0x202400100080d58011401c070609203503841201000710442c4244100d0340c0103101e0f4401070a5212210074000c200101401006007010b445005000894030b0070821855104c00c004100c80c3c41d4580d28103074401a400407a1545860b101700d070000181da0500b00d41ca001c03240c1c0c11011190000030041c01242c50710308090001c0307070020f40ea006001d1810501784090086014092003659a51820b4031005e090a84082c0c5500d580940400502c41c03058030004000c901d803681500d4000306a01015010780c1400c806500c12041402900d0340c20a145141d030b40840071144c0f051488004001804004030381c0c03a651030080c1403d07003416034414400c900d100c4151285140c403600450b10120003040c04030700910020f9008441860f1910201410550001d00095105c01e140c034040304102c455800003580c036400507100401642d80040418414203076034110800402c0191900a5451741d030703000c0c0300014003191140d031002640b89030010504a1011625408680082d400c0440b0fa403903109542650490f41c241610708 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 971331771 1250 971330521 971330531
    0x30209011214151516140105162c010e0604031401061415070f020402070f0c0f080309030303180f150402040605040e030a230f07050709060513050406 66
    0x18001040c0641d114144090b085200d003801c00390854200b0312002d02e815845503081c64400d000f0550000c064601045a01e01aa4a202c4044c10139451072404408021541d50034002041400001c0005c1d50b00307484003580d10075030084020f050740a00039002d64206c0080d6044140540042d612503500d100042c40b00412040c0f40039940d13940d81d00411443c0d40300035202d07511450100003000300b4403034064551000380c950740000c2141401c400d58920a11500030700059040c071444081d5100c03503050343c00b402d900c822142108046810709508c144518031035400c07521040e42c00800d0740c0d031000c81605c020010140003103003140c0713802d400c1100c00700d00100c00b0309283c42800360a00310008208103a940110038010061442e08083c0140410380303d0942029000d90f00340044a03030000000001c43d40120130926050302c2461100b01e034110800c00b0145009401040416176842c5031690400134110180702d202280e000b90b64400c140d800f80d80c058071449074400c014040414045005400050b4000d20880001817 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 971333021 1250 971331771 971331797
    0xc09080a0318120f0807030c021005220f06080a02071209080106090203040b070e0d32010b010801030828050705010e2e0b0301020a08040314041503020901 68
    0x4508840d2200c194001402e5103103a0040c40300300740328040581210903250603424243d03181c2d6892460100e034020010786000990005052060104280142c0c2c0108603010040f40804000c01c81e42005204540740c40c3c0404400030000d9804103000120340000100e6018546010000d548202c402027040084c0d079000c00c6a240051903902c2c2154900700340d910786510342420710500c0350854040742c0002c80741a1040040c000428008103025501180a24003d004401e608001c80c0b18001710a07c018161825995840106942c4110454014003c140d111200b00f000c540745034240c030604084035022030b2440c070051012031460f0004140506041495090104401080c04090f50038580c2500000d0f40128603401001700a0080000900c001e500400380071090800a80c100c001400c103d41400c1c00d603001c151090f9202d60448076400300010021074844201da04080c080101c00c0780c0490008400e032210701030480340705050360b080e40d0001d40340700452501c1c800250003e40c84840000d0501121481c00b130 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 971334271 1250 971333021 971333023
    0xa0b0f0f0102010f0603060509070807290903010603050705041811040b0303070f05060f150a06030b010c0618050d1b030f17090106061409010c0b060a1d040309090b090403030c0908 79
    0xc0103502c00d01c070004542c07601103032842c2450016005031a54ce00f0030601003104040810800b20800750100b400e00c02020641403201c070921a07070380066010350070514000184480440c0300421a10161010300082d50f09121200c485203080d04000c200c82d90003100a2810305060380100580c0c0d5001e01100d00e400740341e03210003415074403400003191030764048010491030800180c1020742080805911800c04011100015075441850064008240c1d0782d03000117000b40c1c407a0003010f150781d400c080300304080329040c8440303c11030100c0030054038148110400704000e541310300c200c503140401c0301401481311603490341d040744d100030f0307548814003001410380240c1403801403110240e02540b08031000003034031894008050880b07040c611966074102c01c140882d040790b1b42c12801d1016020392009951005986080000340c901100350090140d00c034403510070f42c4404000ad01c1440c0501d0081c0c554501e41d6641d6001036095414000020382c2001c00980801c001902a820480d80a10fa908115904a40b211401 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 971335521 1250 971334271 971334281
    0x501080c0328030905181b03010608071116090501050a0b090a09021806190906030509100e1203160e0409170309070e072319050a050705030d05010e0a0b0f0f0102010f 73
    0x6c003c00121050921295501c8030304241c007580800514517055600d004000741050300300030300b085c052200940032402c00c5841840903001060b103190004e44825200c1110310010103007402000c0c0102e001075808149400d146003501d0401900070101c0e0805400c1c6985400650071140200400c002d5070150b80e1050364640340940200101850070152800b00c1030801000d002d40c6911038400d0528180601156980c0441c00340c200c0f1039071180211b4048402c501c944d241c003a050304400018400401803089540004094222502441ea038803000b0420b500100401c950f80e2020090204030840f4200810110300c0c40035503404810340068800290781d40318618006001115400f0008805455031103000585803032503a144458025002d00309000340d10309110b0700604034080d5003031000c04503030387c1a40ca201d00100c41c43e09500c0802d0326101c04650344501c0240000380248290b420303504001481808044c800c075200124010103641e0749401f00d600b880140c1d6840d2444504554035140241c500c44824058 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 971336771 1250 971335521 971335549
    0x191503060b010e0f0307091d070b03091506210c15041a07020904260c0304060f020f0a110406030c260619050c1c0501080c0328030905 59
    0x81505040030000424900c43c02d46201c1c070550003910480c0d0180c80000b0380c40196100741740c00040c10b80301d0040c2e0408a170003440f46401306100c0c800c000b003010500e04001e1030049102a0480c2c84007000c022101c00503880c01c071142034110030400940300e21174000f61080030b1134070b51314000d80d000503c0d03c4010031403100002070f546140c8000020700300901484806025400c0e0041002d4074142141c5a002030124800130300b01600412020041d5120f0f2059041401e605402a41d485680d0703c0322103a83d592603030090312507100400d01c00115106030f07a00200b5083c1c4500403680280c45441d150340d84245100d03041c0f440581d0841e03911500440045c2c0f201e5140009001c0b1701d040c1d0300b800b0034689040d90b41c8100e0a03290b00010b4000780140030011014071400140340d816490003065903a101240d9001a01460300420000701406160003014034060384450705031201e5106840c524000b900505a0b1102c00c08003500816200d42d00c083c0c0c011038a61004c080701c610a240003214165548001050b200585107 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 971338021 1250 971336771 971336783
    0xf0604230114060f0715020909040605071704020d0b0711010f0204080c1008010b0f25030314130b090a080c03030a0b1e0622080c09060603010e191503 66
    0x501c010090032290014500c011a801844c052100c10f480215005440f00104000c2d020300d1000c0d6211a190180c1c3c0c0004009490070401c2e02c6c00f418a040a0300050300d01034042800039010030041c0035000145840703160007801c0310015046940d03480e000558018404410460100700d49100400c0a010b00d5041d00340950016072034074140360701c0c64209003558201c180b08040780d581c24084290804040350460303a11601030398464905030440303100352044141c0164680c180941401c12801c4131901440302d103000f5074003009402225480c0c03d44100003614240850ba52010b1404001100410100e070711942043c1556003019050742ca038100f5800c0700d5100b8603503400200400441400501c18a11a408c040382c1c4141d40040030404207141c06040202d05008080021b1403d2000c4100510f01e009466080b041016127981c5121302a240d03404d07510b41503c80e0b001e00001c951180f4100040d81d041c2c40d40d9410010071910350800c01600b0400c80030004c08059210001d040d00c0c0c402e400340000c0290f000300 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 971339271 1250 971338021 971338091
    0xe0a0b071502090901121406040c030b0f0108100903020c1201021902120d180b090105010f060206040b060d170c03190309050d05030c1b01060806070203120f0604 71
    0x854151076550070504901d150a2040c00300c0140381c3d4030070048504440c846000740c400e0704a0390070140105003c181041042d4030884050004201d5040b20761003c482c05a48a0f444c01d84400c0c03005001a01c0a108900041c1d01201218048400c16402282075501c03d0040f9801d44220300d01161408011303e0742240329941c086540184150b000250f9450035140e0300c054504800e44030b4405203580664101c0780500c0ea0f8030028891003000d81074021040d01d410090762489031824001140c0030f44424041d125224014210000c2c15600000e6040d0280343c2c440d20b041e0482e6141018040c00440d0000141c4244550124a616540420006141e00c0c0010006140d94118041204621903486079a1600700f510740b4030802c01003071022030020448903161a00c1590307511000011001c90042c4400501008526820000c0704901517001000311a82e2400362034280d0b6940707400342e03182d01801c0002c0c2e50f46a100380001e0513072a0076404507030340100e000700001000c0348600d01040c4140140900c1400754403c0c0 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 971340521 1250 971339271 971339273
    0x81c08070807090603110909091e030405010c02040b031e06090c10020d0f210204080706140301170a0c030506180f0316150c0c14010504110f010e0a0b07 67
    0x14a496a11200ca8100000d0505003150010300b40d4402d4031519041550300c200a01c995601c0c0c000b16680908014441c85960038a0001e0742d40ba460303144007542c3c0c10360700c1c401c1d60f5a030729101006460442d9016103900180308025028030016180004001d54107009091b07214540d2944c1e50b6440003a2180c200050140d880c1c5109450302d00038407444854400c4948007201d00100c3c0e13001461400c007072420b280401d181603403100d091301d007009103003203440400c0510800380300c01ca82c441c0d0244c0100c07694a03040f2160580d40d030400f605c581421141e007051009040006010a050020101040d6036420044603001e0b900341d11000074107400c2e5013088899070014010b05c000d08280d01d0010501020030005416481c407c20f5030350340d80784194201c02c07026103030021440d01070217420b00345090280e1090a09000b0340386120001002032055000480c0c00d0201124615003a81051040c18807581c2d0003020228440c0b460007c10051204181042d81001034480c0a041680c40b0304002d4802400032064064441640d = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 971341771 1250 971340521 971340527
    0x9050708011208090d080d0f0b0f010c020d050c040204030b0a0f0b010516140105070e15090a060c06200c0114041e08190807030c0c0b040615081c 64
    0x500600108002980180448010280300078001035100714075580c0d460712030340070900320503046030301801c0b4150126402e080324585411648207012080380400c040c590398010412156283c01040d80001c981d06040401810115035002103140900c0c11500460107140c001000d9030301c41d820498403d441e0350103110203801030303000303034246c5d84401744060242d603081d18002801c0c2e00422032444940303040307040d03680c041c0540c0c0008600600a024000c7c05240340c010f8014140b190036803021401010181351980b4911490801e9419040c801040240c2c50391401070100e40140e14a0340035600c0c00c0c1e85031703610016407041c1139a556105855035031050b1541c0788602180d003104c10340807600c0310302050072040000040d1040d200c0c0311a0040310411800041c003c2c24122080c0c0101c0100c00b10f1504914001c1c003440703800092603840350302079a50034009844000807c07200d1010440d0700514035821070010400003070071508403800030a45059522241595220303040e01d80006150000a4201400000c1c050340303074 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 971343021 1250 971341771 971341781
    0x20918101e021c200f0a180602300c0c01140906070204091109010e04120c080904090501020d060b120a0e060103110a15050c010c0801080a021203090306010f09 70
    0x4512a0840c14800020f1114020034082c0300c1c96100c10340c1c2c902d2001c1000c0f0f405001c20403010700c010040c03516564000c10641c0c1da648040210704c00302e4542104800c85078106520b08040e03400715030188c103607102910604458048114941440c03414030104410514144202403c0a10b0001c0010a0798142450024000c0300d07214890900001c01005607400e20b403150b0003100c084542c1640c0c000f61f045d00504118006090b1400c1d800d03440034001c0000110180c480140d0fa001d80d020300810324100041d040151110441302c080140398902c2400700c05034916040c0d2008903850b02407000946840c41c0d00d40000200d6a583d002000418004034400344040005035640303920468640041051a014180c83c035a03603001444010034842503944003a00715194000b8074001031001130800024840100e0000d05240c0003455009042e41c64160300080c814407401565040f01c8030480075240c07420060b002c4c0132075000c4c0c4201d120301600c001c01c081c555030784080000600900c3c80c00c68107802c040c00c00390f240050380d07 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 971344271 1250 971343021 971343071
    0xd030203030f01050a06050901052d0a11060f07032406120e01141f080118050c0a0e161e020609120f04051c0b010305160801060b040302091810 63
    0x24000b92001d01c00c86070031074108d4000740e00034208183c581d04071145041c1c00101054085107140d8481c01c2803e070016124000c1d0000c000c080e00e40c01d110003081051955121021262540e80102641c0840c02143c001c0c2c0c40224010102c205c1c030a03601701058040d01d500011540001c0c0003071301c19841203215400f21710031001c28400740d2009006a11a148912145940c09402001c2648800483c12441c100101c40b01e0000e0460100900c40703e01407076044400107500b4a000c0c2d40901440c1c00c04400391403d051240c06441d492000d403049a220f5462941c104030f00a2081d4041c082c440c40c60301060417404140f00c6c50038901c0d5008140c030340b4013002880d08203090b074a14000b513100144404000b030302079401510140d6109460740249811124800107603481c0407c406004100000000300034020080390404e8040c03c0a90341ca801d0580d9003030103500301d4155103d40325001d4030500041c0010f1411041880d004000c400c0300d01c4c2109030700c400840c1000300c1000c85090b0380d41d43d070300c9003512085d9500301c4079a41 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 971345521 1250 971344271 971344279
    0x90114040209070809070f0311010e2d03010e0303040b01151103030c1c09031706030a0312020c01060f0b031006050406080a110f0f0d060f2d03020d030203030f0105 72
    0x150034540e02144a122000d404007083c8407403040019009207040162000030300907c1c0f01140390983d24100320000c01c6c55284000d00086801c0142849424210305030344c0402e00c00d000c03032202d1040d0300318208000c5200485881d810f54030f076110720b07000d0841000070714000c5000700d802c20704951401d0141c40f04c1c034090040c2c45051045050044908403004426650300580d44645203a03103088034030101d00312041c0c9034280c04826180905202c00d248e4070004000340c4545000d00b00b15292985801c069480d032003a4001000150001c00308a480101500500344906031500042501902c801081145003101d4001505030600401041a0b003070b16404988014581410301500d01420044024180c1000038a0300941030349800c942046504954210f95080390001e1840d52900b07003c420084441d4000c0403019202d6081000c00705100513031b240300004a4a07600280b80c207243c00e0103c5029000b04440300d040061340c00540020142e100c0750840c91089100b540510360300e01e40106c02440f180e138107811013402 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 971346771 1250 971345521 971345561
    0x61014010206040b04030905130e0606030f120d09050607020d5003010f050a0905070819020c0307081b0a03120f0b120a05121611130e03030901 63
    0x2641c0101d80603030040d0f08206a81103981e0f6504080d1031140e50380d480960403541e05000d60448484503404078404281140030380d80c4907183e540c10140e4402c2d2018252031507801013406468103806003401011210b500d01008140c42d0080d4845d04d003000001c50398200980c00a010900d40140d205001007a449004221544003209412091000c8115035002c80c401c9490124500026602c9640c00f040c11913a8581c115a00d40c1c5400f6000083d00341445068040c03120400042980d01580c040d1511a604582d00c0311456600c00380c059010050115000808a50820031030388038410078001001c0050140d280d896070303128211030340016081126150620b40e040003c0c0c140002e0740c0132850f100d2101207410081400030441a00d080107050240c42c0b00c0d4000d03151100c2452030400420302d040d115000310309403450701e1340e11501c0c3c40052042e1680840038125510324240000c47d443c808000805003d4095400c410a07080312004a071140e84e0107800320703400030080180c181d0003409020364000040f00c0403d0 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 971348021 1250 971346771 971346809
    0x4030c0e0a05130206030403120f0b0a23060a05071b0512030a0e040203060604050d0b040501061a032706180601052b02030f1207050601050405011d071803050610 71
    0x2e4140031800003e225170fa000010800b41882500190083e040d040c1d000c008959020000d00d00400035a2a544d01a03a00405c001404040900d40b04e1403000d0044540706c15041c000040106661040c7c2070641881f030284690408503240968019520403090762101700301d401c0008003d624910030380c0780d08465000700204814694403d401c03103042c180c1610050385944400000038650f00640d002a9081035044a10006000801c4c8416002c2c9000354000c00255440781031001c5840c080c400802c2400f0170810104003402c501c0700c42e8203041040d500300ea040c07a841180f1540c1c14440309841c1c84008001074445010050010700100f801444110365020280d40c000740c01c202d4440c80c00d507140400016800420003551418442c160b1840e580f081502c0c050459490603044a401c0007005a0302407140c0d50000c5443d00382071280c903050700e000002212450a1440050340d12401c014070000400001c0c89032008402c1c0f010490724051441000503260b14585420f21220b85503496200020301d4038041c65140b = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 971349271 1250 971348021 971348041
    0x911090d150b04020f030604231801090c15020c03070501120e0309060a120522060203041103030f04180b0a0b070311030d0524210f0304030c0e0a05 65
    0x15034400e901a5814100c41510707501040106000500c5076005400020f60f1401c1420400c021417003014126030400440740d01902c074190f4800c0130125103c1c03201c07090000c202c0210084400480c4c1d245480f00126100c4125034400b070210400e58046485407050b541030407601e07901808980c1c407801c0300b41c0003022001d00d810700081002080d014203002e89a81d0340382c11007092005001311400000041c14031640d902802d10020810031408485800e610310300030200304109041400c0320105004008604100303035807500c507580207500107030003151681148010030546441c14005030424114008119031944d1400d203e01b00e440c507080c006080d917903281c00d10304c610959500c9440c0d01650b11000005444814500d01074401c50014010040a1301c80030032940c8002d01075400151040050860184200c40300c1924a04100850350305594010014002e69200c0300d07002c561a10300010004c00c4903240c440c18440030f0b0441d0f02c260010b0300c0603645000d0900c80c82140d104020341201300c1d00e40400c180e141040b404 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 971350521 1250 971349271 971349289
    0x1302010c111c022e0c0206040f0602030405180c03062211030613050c0f0912060c0d0c030c120c0e0d0f21050a050a0e120d08150a0311210106091109 65
    0x1400e008117076004070255145c0070140d4025002c01030003402403549400d00695070760050b02c6038610074200d0300e03581d000101da01d0380014015058a845507096850340002c03c4442c08041c941c400d0001800c1032601c8002140340240038024805280140d507908114060040c2c0c050076403840c030440c0f0300340800e210310204281c00715028500202c000e40e0325002c2030700c000b40f100321743c2c0300030340186100c1c410610100c88109001071005040c000c070b04002c00e080741c02c019802da40b65401401c0118003100b2411250175580d42050580c003099180001515003e0f0300003030700700445210142d509460740c0810104000080e410303210000e507404e82c0c030641c40a07115001031240c491a00c405080000c04034240300001e01480b10b800d00c0c03003c01001d035642602a640c4070b0f90384151666400c0009180b04000c031709641d13485240440c000c8009090310000c00d05588070380d1a001c0c03844607025040a444841d4117106c005c1c501c2e03140c0042c22102d0001c41e0b081d02e02446903059440300e1040541c0030360308001798007291340c548d000b07 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 971351771 1250 971350521 971350609
    0x51b070c0506030703113708060f1f020114060a0f090207050709090501020a021c0c0204110702040207050f0c01141c11040603060302090f1302010c111c02 68
    0x30070398980d04c01d5001c501400101300310700c0c02c001c0003090340d1071741900d101c022031421192800007661031400d0555801d00401c203080d02c00d01140703d06020035441e0401012411049030060a501c0e0020460040306408120041140c1c0c0142d56507811140d5230b0080700030743d90b002401141c04800103130030403640c000c5000461090808150340020050300b04002032203200001c01d003c200c10440c0850904040d4040c5d406115a0b8006004010068654002c0b101c03044c2104440c545d608010301100340c3c240b00c01030064898088400300c1c1800740d10010f994078001009944d200b5805040b140201500c000d2414100c802c1c010b06200c2c0300c103001941024100180c800c4a032001d100d000d05d50040e000c00c00c000f021013030f083d084034031800980403a125401d908008101c9200b41e59401b0190303105c2000141745001500c4000380301c81000c0020000d50310501135800d80794003500034466400c0c2a04006004041e40900c05041c001403050240300f503107010b03141031004440050840c0d14010311030071444510305120071 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 971353021 1250 971351771 971351779
    0x913020a091b200d1e080f1308040306231012060f0b03072304061a22091a0f0904021e03060103060b0f030d0e060a0e06030a051b070c05 60
    0x8024100700707000a0300c08560030800d0103136245401e40101c0280b0507181e0501c1c415007803203054075541031070340704203400c5214035242d01c044610354032341c21010307440c142581109880e0010b0a1002201045035803152101c0c1c0303c550341154100e007034400a1240355610050220006202c41181005030a83c18400d031074013254480d1000948082a440000051400d001a640c0510400c2e4003c609400d417840b10340f030903a50908034044028809010442034513114001c403044183c0403542d080c05800c0c07a0000e04217100700c120441c101781e4203540100120075019444108030903101e1020300c07440c208a0107010751420080d02c0c56844001107601041d04036070b0150000340145100c0301201903414589220780d000f0030005041d1146560340f401e00c00e01801d00301040c2c40c80f454000038004101c2c580001d5150710019941c0710410140c2000041140c11b8100d45005000d2100f10040c5400903aa12001940708100352030000905082c4002d103c807601040541032194580204105000325288404000499208071 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 971354271 1250 971353021 971353037
    0x9080312041a07080a29090a182d020d0b06011418090601090501020601091e0c020303070f1d0d0501182006120a02180913020a091b 58
    0x2c60403154611440c15010b500e800140184503070f10ba80104258000d000d16003060142c2c0c2c0c1801d0030040c00382d1018002c044268074182114035141009070307035190300c003000781b00000f202c511181e001401d0001c003d00403104070580104098041d900e1900341160603015980c9403100708010380c04900a00c0c040403002e010600400300007140d80e84288008280304400702c500740e4a800707034507000c03082e00c0c005142064030a908020008030294030402841c012104141d005010302e9280c0004640100016000842c01c07810074040d07154024200d00840c003088a159004558030301d070000000700000b41c2c20103501c0c20442c84d409071510100780c9084560f0140e4040301c4d1000c10048c1807601710300422000e4841d49141c40304244480500030003481420851401200106110310380c81c003004081e220700f40799024aa55040041207185446034098131000205003295030f0704800c05c800162200904481c1480c421001c10301c0001181401e02d080001030001020a12a501c14130004003840401403050704c0800c0b9000e = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 971355521 1250 971354271 971354273
    0x60504141912060501140906100c020307060504031b151202041214060705070507030303180b040503090112060305070302061303120801090b0f0a050909030c03030108030a0207060908031204 83
    0x100303050710075001c03a00071429685035120034100302500800320581d107081c40d04000040c40280290212032280c03008020f070f241e40c1d84400400c80400064051001000040d112030340051300c0070045a4060074454440589480c83c1d07103080848183c50890741c004d00702c6c0c00d040c10818111406090800c082181c03c2041e03141d482071440000a0242d03501081c0b100b600c8040e1003003401180a10139501407039a2055540c9036407480f809546074403a031400141164000c1404102191090b804132202c7c0f0105601c22003180521f0702c8660380080169170584007a08001803000896800c0840003110825803202800b100c1d00d540c98141c3c0b188554070000e80526000962001030081c0f60a818000e581c1c040d002d103c05480300b4030000c0c11403009000d140d100c1c900e400d60419041c80c0c01c8a00c10204240149401e031141e04000600400f0000038044520612040c455011100700600156003c2c1032500c00450725681c003013400a00c1d1070682e070b01c9034003403004c0090148080503000c4100c0300e50080600891031030b5122 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 971356771 1250 971355521 971355529
    0x90f06160219060f050108060f043807030b0a0b0403120c0515060a21030e060c0a05160b030c0f0901050403020603130c09050603070306090f0c0e010611030406050414 73
    0x51901007580640242540c04000081d40000d01307130300c20b20000f00981c0e130300e40308141d90b41d860980d02400e05800100000300020081913840200c1c1c1030507035610010010b0f20407070a6140441006030701183c100e213030805c0700095052044040c03c0e5400c4401151462070700107280d40074495400f012b04070180060100304039901405410402550140c12952a00400c0311100100001075440511440d5803060006e101492206102034000c600701c5404040303d202c1d6015142d40b00882c007190342003841400b000d001a00180704d24141107001e940508001f008010450101c40c441d40c0141c0c0c0c180c60180140034000d0021000c0d502144883e54100ba5141c001c940107031611701413503100135408407000042003200d2404403c140381a42c0300b010b00440d0a0307100d411410944d441116550b07007590086802300b01003403140d0070803d8040d004220003456840d42da210120041d005810059808040301d0040080a50142140c200303410302c140070314201820540014900c0c469442200c0c60308083e41294103403551 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 971358021 1250 971356771 971356783
    0x5060f0a1a0d0905030325020105060109050103020c120d09060506040c2c04060603021213032a0c080c1203090109031203140a20130506030c07060203010608060405090f061602 77
    0x1070018105c03501c0346014502401d68610380f54a40f80b40380d0100042410250050042500a0f00305031182240ea43c24640110025000018028030b180f16840e400700e0408030f03c0c4001d10841103040e07402700d0701602c181024401d545025060742c1c0aa0319024030749006542c03242c00e0001110742140c200a503802c4030001d40c040b0707181d500c410f154011301e440800200d9507010741c010541207514400482407695840040c80159000500180204050035484460301407c6941170f0380705021f0300705800420080b07454194240300d0b2600303d91381d1039001120540da946000c41c440c1c0c040d0b084d028015450481ca982c0024850704461200400b0812002c010858290080c0c00252400c04141d0031745e00c2515000291030068006c0102c9003081c400d21298945c5102c000e0822103030f85400341c98509030a00d1a0406111082c2d0001301600b110301c07018403111000034a82d000840c000c0000c0c0e034900c1304d075080c039038200004c907600503000c0e65290740410881d00c0b401d04041140b03030740007030340d107042c21a803940d03011007607007400 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 971359271 1250 971358021 971358023
    0x150409020a0305040b090a02030d110106172d0c040c120212250e15090303040b0a12020403151e06060512100e0a0906090c0905060f0a1a0d09 62
    0x2030012403590149541035018034407560183e54074841c1c81d21452109629101c0750f890117501500f0039490000780700c0c0200702c044019625103000144450352040c414040b0500200d2990840d044600c0100d01d407408069455800c540c8030145000c001040701d03410345d0303408541070168007554496104032410381c0500c2180703c0030740301d0220a6649095400e03010321104011103031310044048602044109108040c20010080c004c2e449040800e2000400c000c1c40d01850389920b9000c80081101040c1518184044c00003080640d0100b40c40e0803900e0f00c068a0300e00031074000b500c21481440304001103841d8425000002c107140300000781001d803e00141c408000c138071810605181c00c080c400a141c5602c00300411743c030172102200c0f45281d02c41800d4850440100e00c20751000c5018000420f41d2422580c2c0060445440b0b941700080c1400c40f6502c001120f455a4000045965500100725190901080002860f4011100c1d15080344c28800c6280c0c0100c0703400c0380c0f40c0b00c4510100303030054201003a83c040c240359 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 971360521 1250 971359271 971359289
    0x815060315071b0b070201050a02091e06070515070815300105070f11010b0102071e15031b090305061b0c1905070801140f071e02010e1b0904021504 65
    0x5940700d4141105412005d5070303000015803a00700002d00c501400e1090714200700000745940004e10080720110703103010b203030240d9651041c0200444030001c2c0e000c011103621440148040c0c41913140400e0040c01c0d002c001070003e4a00d681d101c25141850b80c8140480f0a07480d00160107800d91f0b6802900e400c1d61240c103000728040e0750300e03020900c02140d030403000181140f2025961550a250000c9a01c1c2c00c1c3c46500e00e0217400340e80705107024041c190201c501000718022080655040c940d58590941d400d56001c54036502003581d98044441500c030101c83c004c1041e03001d06004500714550b0761420340c1d402000702000d079481c1014000310800483c420032203a400200e00c00700c40807201510a050145800719808440c10b200ea240c000a442c00c06009030310000c7d032003a810002135a540c501e4000601c40043c1380c0001c018041d04201414050303d00703a04109a0326600000711140c0d4011110f103401c8050300e080002100540422401d0799030007d440e0b42c40750b41510713054034140500307030440f4540c01190000002 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 971361771 1250 971360521 971360567
    0xe0901020910120c05041208090d080304061b1805121e01022a061501091d100b131503061d040210050c03030a09031803030306081506031507 62
    0x2c0a58403c040c8200720780d00030700c00c000402d1140800d4855120301d02c00c4112003c001e000000c04160840041c2002a01c041d04030401700e00690764010f000d40c000c4401304c2d845c9580d19400040100d4804559000119904003110001c1000180d44070b200b81c4c5109580c81040b00007114075a0010030321008072008a2800e802045030300c0061464003030b42040b0710700c01c0800884640c840120104130101600e21480c04060400c646801410202414070411014144500072000180c031444030560170389580280f800400041c10b007035000d00c440700666400040341c42c2c01800641c003104800d20545082b200900007039109400b035004d0540203800703154000316401e01e8107200c10b00b0410201d0845880f40f03100f150000c042c5100340d00191024090100d110000d580140b000400703120070342d40048601070103030400c40c540b010540180e04203800d064004500290300c5500810001c80e0030801100b03135421000188072546049404641d49460401c0d0a5402c48501408942c1a5000d05034010380c00b0b10742440844 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 971363021 1250 971361771 971361799
    0x60f12071406070b01030605070311030103030c060c0e010906200f07090b061920030c010c110706210f090c050f04090818060d050a0917030606040e09010209 69
    0x40c403180288603224045010308806522840c01c0021201c12a501075188a010790031030312210024540102003c084c182e50321014141c03103004001960007580310399290308011000d450b1410a0b5850480c200d0188202004844001d83c1c020b4159410350302240f40088a54006000060300e40c8885140c2210078002c002e0711141b80c40c80840d05000b95100d0000074000c0f144802c09125071807085d50401614002c40c0d000f0f00441c00c2c420301841c01e140c2e00b001040e00da81421031500301c4c02c0d90f11510550046a54541c04025420b8001b2100d103480a0850064040c4525040c7c0c05000700341d40031048012840c41c80402800c5128540c0120045580500d00b000314513031600c3d050007030240c03d0086c680b28070344081005555141038003441d8007069100221600703101c8610940c004034100c02004a602c141c05114007001c0c1806445214410090b4110210b2100041d0511441048a00742030f0b03525100100108141500c03248100d4049694012181455659042406009004141d400e607400807040348c047c4 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 971364271 1250 971363021 971363023
    0x160e0907090602150106051b030c0106140103060b030906040b07092d0b0901020a02040c0207051504030b06011425140a0c05190902030402180a0e0c060c0303040b060f12 74
    0x310030b5510907000ca555200c01d20820a800d020b09110f4180042e900b000f4628034501403d850006140d04201102c1c1446624040300d07094552581109412610300c00c105170b12907900d0b000e1000140101c1380c1c00f91943c02c000054a40f03070180100007818200180c0c000c194024800d01d41c54000700780b11024130002030b0715040c091201c4402c61600e4581d2201c50400403410605100031200c0c0c4000580040800d075050b5030a1102802c3c12110440030f600a50f00700096075140c01c030b400b0856201a0703440f59900c0d4218a0b02d4960890050130550400c00d0714405181d140c2e6800b4100c03001300c05083c0007960391000d104080e86c01c0500c8a64010040259044040007180c0000f074060910b030b220300c204c10003403038448040c0104480101e8800300c10350b03220402009400c04581c02560000d0010f80645001e8041c10410b00c0805030503144110440c0e526040440b0301642070101445405040310500e24114030190400d0b501c2c04094806041c442c01100420003565400c030136092210f201a00403286189446285 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 971365521 1250 971364271 971364287
    0x60f04080a05101a010f12020f040f081e0a0305090a090903211a0402030a1d07030b06010305040201050906090a05031c02120301030210050d0902030a0605070e01030504020306160e0907 81
    0x80c40a090078041302000441c0802000c014440301a501c500c11b40890800031140c04048408501d0380c90790802041c4090841c440051000c0c01e07880002c400030070301d0102550700c1d00440c01104a0722a960b40b1492003000800b0420071071382d9405140007900da10100c00010207030500c65000d1400140b4111618040542001c030f08448003004200002540d20700650030400e82d4840d2a140302c004100a038000c0152520b03a01071034010410100000e0705a0000300039404080c8440c0b52000710b64040391081042280c40c003111035000d4002e00c0e003032145c0d0900d540041c180340a411551882040e000c210b03040e05882d1111007c00601006003250b880710740400340307030340403a80055030280107001c0c20a12490721050030085070b04031b030360141145086080b88202254a40c02250707010071015180c07103910780541d6040001211b483d00a110000da141031051019000c404241d507a0f038149400c140422000d07a801084055100d1010551090401541034040301c0401007101a00e920440302000c1c03150b4a9481880c1c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 971366771 1250 971365521 971365543
    0x60121050112020103150b220f080c10020c060405010e011707050306030d0801030f060903140a08221211160b040302120a0804030611091e042306060f04080a05 70
    0x810032641040201c48104181f800345160b100c10400c9065480303030b132610780c43d500329969440e03c03090152107403200079410441b90301600840d44858140d02c010f00d04541c0d840d641d16564002132001c1106000410100d000354404c09040c81500780034400c19902411610000500f10350031140b10740391024015201d070b00250f030701501903ca91540b80308114080c0d5006416a5001204401d480042da510340000e8030f2509800c07020000e41c1e00941c10040d6040001e48200f407910b490b00c81e000c1c54800348000303a002d14404407100340d100350450800407690080c0d00541d4803c3d01d2424004e1402034440c2203181c5480c07800c6410500b082c1c42c0002811104c0400a807040c0c905c2161950380c0c820405218956800500798040c1009104000400008180c0e40c0400748030524500c189080410781c00028800800c51466580012001078240003d40351610070100444101c111011030b15411001c85041da550007800d545c01110000b80002c40d840380c101c1030324006c258403c122007503820245000b50700c925000318 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 971368021 1250 971366771 971366777
    0x90a0b0402220e1023040b0a0204051309060f11090d0519081909180f06170303040c0503161e1a1e04031e06091b170f03030601210501120201 62
    0x400c01c5513520b05200c0001c0b81c03003046058005c2e20b848076200c0c411403c0300542454006542000006501c0d12030000f03414035010b950710002403220389800d0400aa50005284082031880c0c001000e00f1040f241c0c05031070b45030f181600c219070300420f68605945041054100b01070000d030116280001c01214500404009801921452500303030300070420340e0344401d1409141d580b24000b1460b00504802070380f10261164020a000c00d84965030102d587c002c81d140604108290000001c00c01441542c2c008a40280425802850000305070040310ac80001c15015955000101d458107111940f9120414006001a90801856031070f0910040c6600d600480004907010102020055407503141000c3d6012203030800ca4009013a0b00d980480c03840f40c42c51403000ca800c15550203004010072134001c6407446030b4064900e03480c0381a0401d8103a40b05404140d00400d90380e0b121411355068000044207494121030207003001c0a02c0c440340d540350b16010782d04021962986251600003c0c00c128100560801c0b64001e80f = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 971369271 1250 971368021 971368031
    0x1401090c260714120a06141f080309040b152206030612080a12061e080c0d0b04020d051006050406050d171b010e0303060405090a0b0402220e10 63
    0x105403180c035190648a00f40d503948401c000c41c1d040d810305201d40d9081409440541e69442e13915a81c2204484a010041d8003440c1000304005410f41164005602c0408600d40c0e425920300c0c0603201d41e501d21400700003d0141703490b06c0d2108220b448030001c4156007004003070b0031600d542d0b080200c1ca11022071f4201e00d0a2008840341c0c001030103400b80c032501059072000140c00010781e0b5643c460420036400b02040101304940040314240381c400d0b43c426400035040441e0301800d10366083c20405485440b940140c5960342010309a5511a0f07103c5d04000000b0383d112140302c07000d07a600d00000360740000c494000b501e14010b07206881d0111855501c031601340c0b001264208441e94650702442611224600024500d075890000180807512150251011038509181108202c41080c050b509542034603503400b186502c003005000d81e070b10305801140e80c44605003004084c1032000342c4541c0c1f003480000c0c00290203480c3d03181e81203545541480003145a0b5240340720601101c0e03518284c1590351030411001d034a000f4641 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 971370521 1250 971369271 971369339
    0x8030406060e0906270303090c030f01141302030a0209090d02011407051c020c01020711090606030c0a030e010f062c100509061219110901030b041401090c 68
    0xc102168081e0a03840e0040c8000d94031480c4440c41d0030307417844204140400d04c200c1340180c10001c000440c070404d102000340c03800f030440405140c0ba1071181d011505859040818046c1e0045001d003101d60700c083d00101d1241c0c1c460b160b001090070b00030140d10181d00001c58108000c8005000034103c1c080c04001da008005000e03c1c0d41514000300740c152420400910200710041101c00140d11185203841400801031510f81d025034081e089034801e0408030b402450511058696252580e0769075805001915020b2079403a06404495840c860a1030800c20306a48840740c500c1010300350f010845012108004002c130f030b5200c00c880c1001d6a41400c0d040c49515103072070949124021012010b001d1100001c200d080070707080c4810000e60503402419580c118800042081d803e24040000d014914400c10240b15581528244a4076860040e41d40c030b400385d00414010400281410103983e84590008a40c6440305054003d550140483c61b1020b484600380d8940401c4c0e124104601d001c0320404000c0010034507441c = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 971371771 1250 971370521 971370539
    0x180609060115080a0b2d04092402070b251e1b0507030803010509010b0702010e0103022506020d0c030b0307153b06030f0402040e0304050d0803040606 66
    0x9004050b6440b050b0240c4484041c0110403964001c3c901c800c0114401441d8800f00d06000102107154110032094500c2000441c0c00b0709921030390001c25101484000869181c601804403000903048100e408540c40303d02aa80c81c3e4143c4100d01d034000b14a0380b89080070078201a0003403101358071403440b142c141c5412440e60b002c1e05826008807000d00380e0703944c2c9407070b00f240594910090b1071004450b040d4031440100001c0d414047c02d0081d510810300b076500d039410203042c4407080300160481442030100f00031610260707030040e015500d100700900e801b580e1a04410f440e41c0c90602c0b001684180b1684030882c02c0304100c0c803078026051312580d0680030031035441c03981030840070385498942403034064101c10030034000c070700d10001079040c2c020079030514460510400e110310803044405c0c03a00702c070103050301401c0030704410f07038012407a0744210102eaa040c01c0d82444c1400d103924240140000381304595950240c402e001086c01641c000341001011100300360001d0800c000741c0c0c4c4c41280c0c00c9410918103600841e001203 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 971373021 1250 971371771 971371783
    0x110702011202070c0504110d021b0d020304030f060b0619110d031509050606120f01140103060b0d1d010c02070e060301060f03030f030b1e0a0b03070f0e0f0306180609 73
    0xd041080c0134003040c6030605010081003c0300400b005104200041c8400309164001032001c50252a000c50070950280f045604000800190714215041080200003298500750000c15440c0c0200001848010140c0010312030321450440c5280c0143c400007189809401520b66110050b4400540b00c4400c01c0032012803c5509103a03101440d00380160701803082d240715500c0903901000c091300c820b00d0b000c1da0380c0307158010310300880d1902c1ca6018a00010300007444144130302c0300c15072001e0030140103c1d03090140a81450081010710940a80e40d8040d1261754920030f003461086042c007000030000f098000c44004e48400340340c00b42500712200c0760302040715400d0511411040710322600c840389615045a40448040da001e2060904050710340a070560a50344042d040b06810bc844c008648040c03562a05001d69003d8580c0000342c484c41c203104104440b07401c1403000e0490000c5d450859901100400001c2011603000bc1d0305405110345020040b425022103003502c1c02080d0001140d120f81e031070203e51a6102 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 971374271 1250 971373021 971373023
    0x601020a030e2803060e16030b1e010f0509100b1e040f0f05040c0315170a08030f01030c1205030a110102090907050d0621081b0111070201120207 64
    0x40e02a205100129114280d050100500100030095012201a001920503051904203820704000f200030030070041184100d660080324000070b0440c0640b84910045111080c0c48040c0c1070300450307000190003681c0d807501198440620b20b07030380e005542c682c902d0481403811402024004c40c040c001158000c0b0100d07214104a506407903c89140400008410030180c95401c0411000d0a0520000c20860710620003a405031503614400034180740b41100b00410344900349141c500303040c030303116209a0000407160411f0594680c0d01c2052100e01c000100c4170b280034080c0700c025000c820b001c000d2203104081c1c44841d6040380d02900c0d2065a494070740100d0280b40d44144401041e60748104840c024490203551801415007038080010700701840000841c0c020082140c00b0b000058000510740310f00b600754440c4c0000f403d00036084145540d6042c00c2d520074040181e00c050641c07040403840c401c0303210592625154498000000384004141800081080d0704107640482c0400c0011903911000016072081d17880c2307a = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 971375521 1250 971374271 971374273
    0x40f05120303180a0c060215070c0c1401020a0c091b11030d09060207020619120b09131110081e090c1011070e06090a2c0705090a140906060102 63
    0x5600d401807040c4401d10b540d040d443c940d0058080c07440200d0a6561090000c01e03140d0061311069818103954421214002e00c2101070018109840c03002c15404400b070000c1d2000c2c52a010018141100180e2800000ea9001841440f403928040350707003451038008400015001007500e4031032600705400c3e01d0700103130101004816070082c01024100741054004501d1140a1440103141c800b1329000324170107a00c03a030051914004e40c0c1c2008025950302142800d03281d4400c1408200640144000031018080940803807542e000d000c0d0300c0380c02e1140514039501120740080c8a41d15511a806000d0300c0460215203040e80c001c20008102030b01c000910f1030510401e02030015210004407413040003c03032100d100d01802000ba450b510590a20410081c210280007240120700c06807801c0420007901d4400200010f01850034610000d042c0e5140030540e00d80300400e554401030789902d2115103031611070240e00071940000c0300c41c01d21000300a158020511a07080c4c01c4243d45a1703a48405450350394601395852401 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 971376771 1250 971375521 971375527
    0x20d02130f060c051c0c080406050a0908030a0c02010c0204020409060e01060e0a0608040f05070806090c270c181008060906010c030207060f091701020a02210d0e0a05060c040f051203 80
    0x510195080e42e00a00b400908041250941e07c0d140c86e0003540203a04000b0200e80002245803025400c40b0078040200348510041d0302c0c0028440c8001c1c2848502d000083c107001040301c0c4002150760300d4055501400c071061041107559601c01c1c064640800c28445c003404980b403295403202500701284400305407401ea4807010482c1d11503944120b1074165030135068a45000c2c00f100850a58024401c0c14003c00481004000e0460054108801c24100303900030209a09000701140040e68202c40c0194424003510038644c480d00105204041c2a80c004102a80b21068601c0c80152542000003640100016209000c01e035440100640f034030704103a00d000d00564010041000f480e441446040381e0301100b40ba020302c0880e0b079015840d40310002e03407000f103544c1e075004299207000560403c40c1d1251130780312174150205005090000304440c8a00d40f98050510344445031507c0f07a5030700b00120140d0750f5111040b10918602145809030542180c000d06030411025440001d031441c1c000300c090b50040ca10000b441c130f = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 971378021 1250 971376771 971376793
    0x1510030f0f150c02061603020711010e0d060203070c0b1e0c0d06090905151608010b0a090b030414011b021b040b0d0308010608060103020f0702010e04020d02130f060c05 74
    0x407405030450021500e00b41d400c0700c840c50303991840c081e281c00c0f0f0455400030145802c0c0000c22200b07000c0c0c808091400c040c818003d01010503484800081c081034207003004808040c100d00800c042c1035030004098103403030000040c418000d40c004081010240980304010580d00c40d12044002c2c0c981081c9003e03900454400801c0e0b088210b04020302c00c1041e41c1c600010200d90300c8048405483d60910700786c40e2030700a40c0080c1c40f80d05200c0e1880b07030f0000d1741220100b0420400c00c0060301345541030168803200304003c100e0344d00e002d0041c0e8080000c1c0140b912a81c0c1c81c0e207401c0c50300e242982c1c4001030b080055400c150703c511a520112101c502041000d0f0041d200200740d181c00025440c201c441c1140d405030300c90701104181e44510044400c082e00a03660540c03e5818088082c11654025124904041c0704214454141c00c0001c103607200c2541c2464030000c60f15110340040c01a00074900006c52030b502c0010608d0020014030400c9084401340026400440d81d42e050070741c1c1d0880c00303d101a003190845d1010070 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 971379271 1250 971378021 971378033
    0x50c01020709090f060506210a0b06010903030c0b0405031314010f050f040e060d170d050601090608010e180d03091704032102070b0307090602012018030705121510030f 74
    0x1580c4810054085188d12442d1820410201c071003007003400c91071700b216040b0b406010307080d900d69a2040d803e0078444071503840d680e402001100100b10240a158401001c01c0410109204507102c0c050402480d0003c1600c41f03200c507a100210305546800b06081d40f001c0c03903074903010704156045581007120840c181440d09003d548183e600810891f442031100c16402d0002d0720048840c9010450a40690340fa0100c1c02d41c080121480a001c40c2c1c1404100301c820400241d01040a905481c1030581503405070310b543c50350f050701181c038002e0000a0701400751840030082d4180d108801c143e015912001d01c1400d411101d0460384158000602604401c5024103202c0306043c88044040c403603441207601c1c02d6031318414224950015201240020303c0da8000300f0415909004042c809410700b2801040070390450500c19071131255100c503008011b0812513914041d1303410f002c17040081c1f5015150054141c3c0052816854a59908000c2e43d00c900f101d0100d10b6000d20152400181e9900c480585e012444a40f102c2d = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 971380521 1250 971379271 971379281
    0x5011b030f0320030a02041e0302100c020d2103140c0a0c03111020190f0e18180a151a040915060b0c0730050c01020709090f06 56
    0x740c1482441202d1040280c055000070740c030415443c0c000589803030a002189251031000c8c407501e00001051082071000d651001ca10000051036400d00c00145071a920100b81c080d005402d01a1600014000d2120900b12440004ca81110541d408120420b03244a500b03070200d43c10380d00307408251400c3c400400d038940100c1c40c840c1d0050081c1001a40b82c01040c01b45071800a00c2c0d034000004a46a841101900c80131400c07402800b8600f1400505082c20201b4141482c0741c842c61840412140b4a8461040c1d80103401c8a010018090401c1c8900306044540f264044010780b0506600101d00c0f04d0649000000300d84286226800322901c01c2240134001c91502400440103100d81080c211409000c003541e40d44180c1540d140700b01440044c2c0840fa8050800303d40d115800072040450070803812000c090013107a810246d0700886d03102003145110407961008449518007024a0341c0456159101788070b00011100c1040070241e089441464458400a00b40c911002c0002c1c07891040001d541d00040a81d000 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 971381771 1250 971380521 971380541
    0x807301b020a0b0a09140714150a03090c0f0801050411010801030c09050403020c220c021b04020711120f0c01090e0c03310b011a070b070c02030304060905011b030f03 73
    0x3000c14500f1054541b50207010030700341e0701030480c2d005080401c00c201e24600d0388030252100302c1d21648210100300109640c0e00c90303109400101036507082098100407224540d84041d2007103190401c032894031900214000c02050750195a402283c21420358158840d07c1030f14166541f05002109081c94190400040c10380504114298010004001000d884460041640b06200c8415900c44600c2d03891641c00c0300d0303030b0303005000454028075038400b400e6075002c600c01850031080c1c800607170300c6d1440e0620f0308203a01e51401d403c2e444004d1103022003503500f0000703c00804c1e44110081d14017035400b075001904d1841e428410490240c8441000400b003601c2040511360181556036028242c004650f08072101181074030181d515001c240101c1422b11009040c40c0c0c1c0036099080075070000300700d03c01711600b181c003c507540241075081240004650610500b440f0b194140d0140449890b55200e100241c84400640901c600254254603818040350402c400200c2664054990740040003032500100c0203445000f070 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 971383021 1250 971381771 971381791
    0x2060c010212070504051212090f031002040306091709010c0209040609020d0c06020f072d0317030f070f170606120405010506120f0d0807301b020a0b 66
    0x300c207806410810800c07078443d840641d0307102e546a04141c1080703240da2580210740691ba0000304680809441c00d421100c2007101280e07298a00d01e88500042d2034140c100c400020040c1c000728000003002290b400c41441a481205840d0201880440340ea0907402a031540600085078a03a42c0400340c10040d5905800ca40680400710b01103115801082d08882c2030941100c1010741c0301410400303250b062050107070003151240607000c0d4601c4d00d0100603011a41001200f51690004510600c03940f400d00b12100940d81f1151890718103010801808042c0c10448528820b90b0660f0002040c60340300308805551140d15032104469a0340030891565203c4009210b980c00000c20031950b80507000104509104034403c200100b4145000b50503c00c100b20a80d1740c001c03030b9504c9583c034148100b00c0402c100301c145520389000c12056903a6001151260f01c43c580c00000720000c0d1132110b08041d200c3c8110312141500c42020f0207200740c119a103c0f0070301040001030b801070300000ea10800040740d090076180c21100b984 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 971384271 1250 971383021 971383027
    0x30c060203150d0f030e030a02150f190306060305011413110f07060203010906081501210c0e040303150f050618030f0609060c031902030405011508031c020a050702060c0102 76
    0x1201041030f2141800041c2e4010b1a40d500000404d54070107003040980905401414100c0303020350120f10b21243e00390b030300322481c000464010340407035640c016241c514000104000140c40703030560180081102d8000c0600003801e0000128a82403020f908200c1d44101a102082940e8031001090040c0f070302084802500a00300198008280050302402d04c241c051240182e41e5454408400119406640320b42a00d4010000c5804090303184490305044a4400700c01c03601d0503085255000800740481c0c401402c45901e1440480c1001200b0706151041f4442d45040040d0700b03c40074900541804c505c520a0300815400e800d00c4181003c00c05800e02080400115081e075030391200103410640041d0144181e40e02800030807074401c00c00c00c00e95800c6403000b0300452550420580c0a0310850f0061212800150000045020041e09521848008490b651000641c0d900d070098075860341e10040c0b0b4150450000460110480b03000e100715041c044060316598506200c56090003a03e4101e125040303000c1d5428 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 971385521 1250 971384271 971384311
    0x30a09030e04051807120b06090403090308030c0d1a03123010063906110d0606020313030b1b0c10270b060303040308040f05100c030c060203 62
    0x1500640703010f00c004815281241d444d40300f01a107002e8581e80b004820b14000039040d80498410141150090400e031180600742c0d6442c00c066076449813543c0000c10950001003000300b50300c3d50602506545206910500801c1555042100198101102503501d074000390310000c0b40c030045c08001c094008000f9028600d4040c90002c41c1c1c403018100540940b80c446080400c450320152407812809490281401c2c00501c000c0c0c2c14a4002c220f5001c0303800c10820072604468240c40b450006d52040e55030004080c800c40c48038400d07441841c0c004040c054003441c100781c0041440c0e0f001005907445101c601c603003440100d16540755103000300c90140c41559a99902d9101400280c42e0000401342507a1002c01080c0d20713840d0100304800c41d005007000c200c1c01091420110218840244424592a044018009a80c0350320000908500c51903200602a51000500043ca840e43d410843d044039403c071918008a0458a400d9500a1401c54010005a90030303100f0b000007038666000d903411201d00032208001c0d0610f = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 971386771 1250 971385521 971385529
    0xf0c0103240f030b1b032205160609050111060f1b0a050301031a010b07020108040303240f0b03071e02100614040b120a201f0f050f030a09030e 63
    0x941d000101c040400c0b100920910800110250f00126204000c55005d245240c9580c0c09000182c203042124a00c007028000d1580b40c142c0f0581415004000d4411124060320102c8404110784991004140824400211507008034180c80351400c42c100036242d031380c3d6540c0c0010a182401010080103a0800361000301310302400e4090300f031099454484e26902d5046040c09658002c0c10141d864070032038800010b020850081003a01e550560a0a16010310b4035186400d40c082c010486458803040801c4802d081c41000341501d0070122a400710000783d8468641e2005140791000b02c80300b2003c2844284a04070041c6c82d50f03602c4e1907001d160310540d41800d800d21482000e40300207902c000004002d04211390520324151084016814049404a401c010141c0e140c2d51280154600504441c3d0b070b50019840d01300101c400c4124158005003d20181c5181c0f400300b00e9a514542010701c0000c12003401c6102d0b060017071080300c2004c0910014141959503004146002e00b0041341c0440c10002940140c50050322 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 971388021 1250 971386771 971386841
    0x60501300203190c0306050c0304020d0305070f0215041a09010c0b09030405090a050619030507050607060b03010e030c0f0106051f03090507062001020301030c06180f090902120f0c0103 81
    0x44155010310b4102c0c5103042c14001c0c7c0340003824410264004205000041e174412880000407503160404c0340c2c8424031030034002000355420740040c0d00082c1c00e0700911103201d207010040064405141c81d1448074511900724201d580900f658a90110b00940c003240c011940242381c85500042d1002124681070b11140400c92103842698400c1c1e69139203800602003d0301c0c058691060a85001c0c61a50740f107459500d031940c1c4c44080e44034080c0204400280354042c80720a8000f07851408001d002880583c2e14a41d000c2c0da2070340300c00780c040103900890b59002090501070080c4401c80d00d0042131550380c0841010061120600b0f0750300e80041c07664440d10b0500240003408514002d02c180d490b04a01130003a61105010b140c8001c3c10080583d204000600000b8a20050300e01500d00c1f40c039001e015141d40d0319010300300c0c602c990001c0030f019080b06e000007004440354009a0265100ba600c0c2101e12450406440ea1250b10f0041554250000b0348074910760b51080d40315850400d50402d000392800d044241100d4800 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 971389271 1250 971388021 971388023
    0x1d062a030c010f110a1215051503040515131e140601150f1d031e01061e18051515040e0c1e090102100203070c06050130020319 56
    0x10751a8210160710b01c1082c415000750901040d0313801e280c10703034064004013217000d104030581c03406607641070340a4100da03040c07440e6015107030103003100300e85107507292409140d81c208030713811a8a8401c0200302d544201080c802c03e0300400442c078840c10803810a6445040c0d00c3d0245441c4115900000142c401040c6400d40e07440e07103068100060f001c55418181010500c0c00240101000d0000c40b2075410318250f4415069a050000d80340b0425101c042e5800180c1071580f41c0c2c0041710f0301c0c00d0414040310681d0f819400035041380d2803809100400c0305410796070202c081d424450041c0307004151881800051103138100b0365000c000f0324032075101000d103480043c800000b00000c211041c4030115047c0005000501d40540207540a461103060034100da50100716146580c002c2600880045441640b59008000001d044400450b0030740d04c9180c0b00000030019401c280c0b0680364030303003072a000251282c1c00a0110301d0043c8010012400e824584e6604190762502003002c07a054070500340c3c0740c24202c1e950450078000d1 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 971390521 1250 971389271 971389273
    0x90904080901020d080c1e09060c030301060e0a0e1f0b03010602010903080a090b070507030507060515040b0405060a091a03010e010b030f01050708070f200d1d062a030c 74
    0xd0140c10000900e800c84c0c00e034103001840350480511081040c50310540301020b8043c910b0090300407002c00d00000310300841d881244c01c140e012800e0201003c1c08409036068500c640d40d030b0040d0b28822030820103800014421240030490050128201501c24203210294610158408a1055179180039640c260702c01d074042d01c0181d64801c11030040651101c41140c1141035640207004031007036511040032100f80500311500303100e400201c2000b0140940140c1e200190040020045840c4c908101c20440f0f001c030003906d02c12440c0000c000c5040ca010301c1110301813a8040e104840301410f1403844001005524039040c40500c102c844106a5a003d005442040171032000102c0c0c0c110014041c10326092a09025542c01d9041200700b0448903400b142550f848400d07031900488060324018140e4050400000c2c0c00300c40d1410b1032050b0740003d00080c4040e01c41409035203660106d0001c51202c80c60b18210050150b221504000740e129810707882d21000f6005058504008444c44000c2d600f52842e846007100c0307102 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 971391771 1250 971390521 971390527
    0xa06110106061403131415060a081c111911040b06040b070b0709080109030e0102060108030c120c120a090509011d04151e061802070c061409090408 65
    0x10940207018810040240b030800020503104503144001e01c0c080103040d00b106550600c1e01000313004404040c01072a07580c03001a01c205071322100c8051005281180e025000b01d8003180c00050182c5c001480e081100410420011b0f002c203a60700c1100c5212066816000300d105a40c0940d04144840d80c030310032802d10a01a82800c45910010b2005540e551640e151084034144000c00405490104079004d240d8003100b1000d0a54405400307848134050380d0010405c562078941c1d44820907400200c90700e001c00090b02158484c0c0e0741c410403540c1d203216428000f901138200740301403804041c802c000f901251a01c14141c0b41240007500a2042c80e401c040007250000d10740342170411260400705812400350603807100b03201d88101d11924806070150003402c014403105142d44683d02502c0c180c1c0c018001d0f42904409695448400745024001d0440383c0290050b840848500b42005509031084420340b03944030071101c00c420300d4400188c82000001642124802c3c003000040c3e0240c0c1c54202d081d02c22403043c002251 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 971393021 1250 971391771 971391797
    0x80603071a120c0c070e10090c05030a110c120f04150f0306090209150304052e14090d0c030207050a06090905060f09150f0402030705120906042f0a06 66
    0x1e005400f91101c0040f2804110b0740701d03407000100e03040741581c00da021940300c3c07030f112030301680702c550300c55844640164509500d030848141e109005600500c40d40206000104426400d40042d1080140b142d441e17900452034560344401c1800030341500c000000d6080e00b0190750b0341c16a129104a407003500d0001e0035200349410300c42d405105100c054021840b046041294140101c0c905c11041c207400144001c0101c001401c108040021401044000d00001c12940c0221078660005d0740c00c0782848801418030080030406440286458400c1d5905401007200c114001c0e81030302e0300a44683c01340c003180504030001c034082c0c9403020b1880003040300d03039290398560b4a05007004c808c44402800c0c440c402e070103081707074414990b0b65548913940105610103039009803149070300090032445034405415001070010041007003440e0043d014200d0a01001080c401c20b03642c0d401c4a0303445030030440340181f12803034045c605d480e402507a010422030f000103045101c440e1101ca500190f188061341d48400000707042d1001d603003 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 971394271 1250 971393021 971393047
    0x80703030813030e0105090d2021060c0715110306090702030a020a11010c0516080c0102240a14130c0f050a030f030c240c110607080603071a 62
    0x740d40301d0b1000d516403060740c150307a50081c80035480d410720360304001c000b0070800219580c40b01c4003e17a0b10f41c4000d00f000411103010f00ca103000008414114802d158003483c04841c1481814014000d84480d40500142d80e902c980003d1940c00441095451100024410061125605c180d000c802d03030b01d080040e142c0c40e02034100049045d00411079802c542003408100c500c04e4000440300d91301d0354048080c1c16042034030380c0103c030f10b200d003c000580184a40c01c07010a00b1601881400203072012402560740c000c03852801a039a0344d40c0840140d041d200301ca80c143d4402441001000c0c1c006150100100e000e081c1c201d2a041c40400546000c0545088802c0388410000132960f690014005030f007254102d1460103001030300d403031424403000d010b03030002445503000c140c4030b0007035a455603912032040340744800074402c8100310180191410b15507a00d00320411601e507004d4070b1b08400c0700c0c000500a0aa50b55001c01c01c5400000213800c0c10380503c605100801d5070310b12060b0310031410300c41c145402c0c3c83c0c100700740b03100f = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 971395521 1250 971394271 971394287
    0x40b0f0c090f010c060e07090f0606030c0c140115060206060306060108072f0616030509010612110f060f071a0105210a0f0f050124060e01051308070303 67
    0x48800d22030400440d0321507141d1500b6603200803400d00304558024032508052002d0807020700b0180302c0e1b0207150004940010f069010505810b0005803c02a190712400203404450301d54455070003144080c007a120003c8c41c00e101e10b0303100760030440002c9006940c0c0c0901010413031441e0087d20250f04544108849801c1c10007480c3d5001c00c0900e811182401c101d40701a08449001d00d001400d56000c040000c00b410712910301c00700d803000e078000b1a00a07140907410030440300b0820840000180c10100804c80900c1c0500804043d00c00c101056545440540d0310b0084010304403000c0d54011030454203c2c4460b5540301d02402956408a603541d0381c0d10080c3c40c01d0840c1803e84414000741e0388070b840061140e42c5506507505504102140c203031a07940c0302e5024480c40c0c003040c03910040226100340240010440d0074043c0036512445800203020b020382d4121848805490302040040103c40c000f010400c0c907110b0609e1952010713041c18202e00d0201c4000883d081000303207401421555000f09010820150300c0482 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 971396771 1250 971395521 971395531
    0x106030b07170727050d030f080f060102121602030601060818030316030221010f0608010e28110c010501030b0f04150c0504091515020703050a0b0c12040b0f 69
    0x2d81072145010500900040000c10081c1c03101e0706440a01607422240841410103000c005000100c50b0140c0d2400a00c1603150408800001c1c181001107039406880c40306039805014140c014002d405068000e212194002007021800c20201e003440c1405a1000d00c0f4643c00703410302d42e40d00001803425048100064840040c0c2c0f084960081040104013880100078900c540d80b5454090794a0032260140c0c641992080e580104200d04100000361440d200d0f01d8642c2195140d4540c5a09a070f030b602842c180c03490342260318950600c1213240c00c42035108068800740169020000004000070480100c0246421803852030403940c0d540c000600c140900341c40c1182d03000c45206510080c1d4a0142c0e00c2205031001c00c1094071007661500c00c80d816950140c42500c0241c000324200b0002a65410140b0f2009603040c40b450003001c00c0c203240e0340001880032501d41c080d00d0b04400104041c402950701d28642c440020400c2410000034031035500b0b41c220300131348503000c0c03030003028034a807141040181940a420040c4c4 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 971398021 1250 971396771 971396807
    0xc0908070b091207050a080f070f06020a03181203030e061b0f0f0702040e15181203091009080403030e0a180209010311161502030708010b1b0106030b07 67
    0x20070055074401c00c04aa001040c180c0d00380c0703905160080050b19050ba650410360340f0014245011404810005200403260900700c200c494031a0ba0380c1082140308420701075900160480c80414020901612150381c0104134840d0802042d591140084001200b03002c0450019440710300c024800c8008001c1c0c280c000034050414500112001402e0506100c1d0002c842d801d03060103e059242c05c0141c005a401c856001303072040c085014050365480d00daa1891040e410386c4880080416281c400e03201c01d0400383c1c40fa0030010210000d44641520858000410440c0f444c880e10848040380c44a60145654481c8540c00c1903455606500d0094880b0700303072a007a0b81c05504003180c1044110523100c04054001700d030000050f034400364400101c016122186110503056000a0000642102055030308060b50088120704c0d0b0012580c0d20281c1030740310a661580000d08044c00501602c001e61000307001c4502608046021012004256030030744205e54000c0c1e818450f070f4020491303000d0b0008031a802401c103442c = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 971399271 1250 971398021 971398033
    0x70806012103020f06040f02180402060d02181c0b010e06010c0b0a0b0a14130203060a0e2212270b1809010906030203010b090f04030503040f060f0c0908 67
    0x100800407454a2001541c0039290206102414000e102d4181400b40c1841650303114070b050b0a080c0f2001400000417401555030300c43e207411030711001869034011036004050b50b1410081031740e248065041000c5426801c201028003c10710b580e002d8041814900990070380c01450014108007400000c164000704641d003041c1d08111140ea80090390303060565002c08101000c0d101c2011110003440f075a01c00e180c0141c2001000f00300c4280701c001029110008a941144a00750401e081090780400d580041e000052800240250751501c040720368050300c2d41201540954400c103000b4043c210000e800c5d24200500c070a200d08055200c200541d0401b90060b402c0300f400400004580013002c01d20844444032070105e80d110408141c11040b518111005104400950315800c00200038403851100324865072038107070500c503c2c1c180550540d1113045005000d0784030740d5442e10140d8080c0e2004008a070084410b03800c2d40001400703440b502c0281da6020f0800201c26403400c0001d004020143c10007202a8089 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 971400521 1250 971399271 971399279
    0x917010e100f0627090804091d060106030c0516020d081206030105010b03040b04060b040f1a0406060c0203060a090305091e0306010605041a07060908040b1c0218101106071107080601 80
    0x6030064454401620014135003205d0309041a09008940002c4a210f04014030501249081c0c01824001c040e000c043c6d901c56603035070f00c0540403210305050030804220b003403242c0e410303180700307481000c12450000e44400400e440b1a41d51107441c0c1d00101c40100c81000303807010301500341824490780b070140c0305c6c01c541640765040036202d071901401c004000900442d141da02801264407203803c5040c80c01d061407000e01c603290020464200708040707850618022458100c00282039840341d006580800d801034054807468071401115009012151130503014401d0401081c500d036110040046110000c452640d10710300c44000c00c05003001c40c1030384582c0401c60140002c1c0001e040c007910780e041151a0041d1030b0f0386c9040b1460124080c1184180280c4207540100e070001d400d0700200010f03e90070010b0911480d544203850001c4040340580030810216041c0090171221608054203900b80d440750758280701c9444418010311500e803600469076000060400101d400b5940300402c0303018054480040940019810 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 971401771 1250 971400521 971400569
    0x415020a0f12020109020307182019021603060609050f09031b0c0a0305011e140601030b0d060f270528061503150504030917010e100f06 60
    0x4003400901282d24145220034150300035441500880d0f0b001d81500c8400755200c0354a16540100c404a040750350600401402058003201030079641204243c1d5141002000780244ca4019004000a429413203440d00c15400403c00c0c0300c00d00c0c001c5200c1c00010801342c1c1041900030030b446018020301c0c7c40380005418408a55008410344400c00300c0c2c0304090104210302c1010030314050002e1146900101480e2001c0305006040d0401c01002034480d4030004400700c2c0c509040200c400b4109000d0041e0f880700042040317036103c0e8009801c0400004d22050171503216803180400c85511500310015140c2d64036640e0079054190056101c00b10030b400e6800c000b01a00d0700c801b40c48000141c080e0032070304c1c914044482000042d0300d840b110035400c000704110100440d4003c0c2e518100500055960959510554070b0a41060241912940d45641e60050035031070521100d55400c007181c5a554155200c0e501c0c0c0303064140c104501e10b128611030f540850100c48d02c03100351045510f90b0b080811300544487c050886422 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 971402877 1106 971401771 971401793
    0x100e06182101150b19030f020d0c081302030c131104030614061f0e151204020f0d0206160204060504050106050901090b0a02210903060c0415020a 64
    0x200c2c00f40b151090b610070712a4206201c1c08000c110403103090303c48250350741e0322075003070104124141d0076100c8142d8100d8003118412654a00105080c00c1d844065950031100c0e8800200a0310899004643c03a120400400341c001c0c100c0ca0040070b080b02007980075040d8000445c600c2a04d0781d8a925203c005400300305020300514041d0004103245240c0160918100c444110403042e050140074010703101c903501005401c0d44520306881e2001c190400400400202c507094020040501d083d04c1045441d00c50185240d024103214600d440041c1c035240219000e00c0c0c002080002e0741201440050080c0415070001a001303410800001540d40e0401c002e090303484000d0300c4181d10300303444d201d2411041c0201c0f810040140c0c03145030541c80ca2083e0f0070680c440d0341c1c4028078403840c0038948008030345030840542d07840034920740c00a030030000b12404500710440c0c401d00784040e000007486501d810316005 = true := by decide +kernel

theorem cover : BRFrame.Cov 971223021 971402877 := by
  have h0 := BRFrame.cov_init 971223021
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971223021 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971223021 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971223021 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971223021 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971223021 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971223021 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971223021 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971223021 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971223021 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971223021 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971223021 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971223021 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971223021 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971223021 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971223021 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971223021 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971223021 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971223021 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971223021 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971223021 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971223021 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971223021 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971223021 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971223021 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971223021 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971223021 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971223021 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971223021 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971223021 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971223021 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971223021 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971223021 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971223021 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971223021 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971223021 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971223021 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971223021 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971223021 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971223021 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971223021 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971223021 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971223021 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971223021 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971223021 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971223021 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971223021 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971223021 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971223021 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971223021 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971223021 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971223021 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971223021 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971223021 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971223021 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971223021 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971223021 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971223021 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971223021 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971223021 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971223021 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971223021 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971223021 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971223021 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971223021 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971223021 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971223021 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971223021 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971223021 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971223021 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971223021 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971223021 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971223021 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971223021 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971223021 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971223021 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971223021 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971223021 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971223021 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971223021 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971223021 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971223021 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971223021 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971223021 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971223021 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971223021 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971223021 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971223021 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971223021 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971223021 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971223021 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971223021 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971223021 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971223021 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971223021 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971223021 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971223021 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971223021 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971223021 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971223021 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971223021 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971223021 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971223021 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971223021 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971223021 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971223021 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971223021 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971223021 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971223021 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971223021 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971223021 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971223021 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971223021 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971223021 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971223021 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971223021 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971223021 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971223021 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971223021 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971223021 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971223021 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971223021 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971223021 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971223021 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971223021 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971223021 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971223021 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971223021 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971223021 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971223021 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971223021 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971223021 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971223021 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971223021 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971223021 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971223021 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971223021 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971223021 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971223021 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971223021 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971223021 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971223021 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971223021 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971223021 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971223021 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 971223021 ≤ n) (h2 : n < 971402877) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
