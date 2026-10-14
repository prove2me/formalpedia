-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1122
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T01:20:15.940513+00:00
-- url     : https://prove2.me/submissions/00b73e32-cee3-4784-b02c-2b548f6c7562

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 201618705 ≤ n < 201798561 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 201619955 1250 201618705 201618707
    0xb0f0403140313020d0c1a071209031203050a0e030a0c0302060a1103040b0a020904020714061f2102030a1a070908030a0809010b181b070b060f0a0806010303080106 72
    0x445001120101c2003a2030b600c0d1046070318010080c002d83c028402e20122410005002107008820f0117030004411601440f100111120b10b41d50103800d04860b448460400c408229004514800450b500035030016078500820700204c00811004092012199603020120005c150400c0688034038031003503c40d144204583c0c14003a2420100408402096040c00403014580d0300500c240c03900168007820020103505c8001400e800780c098491325039009071021131050144850b98840000b03a031101c3c4259030700f036281d0a6001021020841954010111050381000185041c82c0c0d00908080c080d02e011404540550000703040004420056401c9040c01840300d2840038440320081d001078a900380003070714500d030500301a107034010404030601f401a01400260190401e4005110151000f0f0811550404107402d01750541c0c0103850f80e9069000c4002d01030000e8114404549045401400030952503840100f0403242d4844100300c03d411030b880303a5002503814420800d090180d4800c0e16160000c0d030420714 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 201621205 1250 201619955 201619967
    0x1e0504050a0b03091c0c05060f0f0a0203160e030a05031309050601020d0f030504060f09050d0807020d080f0411030a05030306130c050915090d150e0706021506030a0b0f0403 76
    0xe80e0b030180b01001800501c0e98002607400b2289910340021400401c4441c09130b607550340000c0e02a001d4029201001048050703110141e20800d05100c02040326220202124201d000880e82401241e5a4018965031180151038002e07013520000d00b02c030708060180e5201401e5401081002c900805c20b40c1c4280652461409280d038000070a0bc01482039840090004100e000c141e0240b405060303485c0003043c00d010f482d401561424441c0c0c8014800c54205140486d82e03074011010750300010f12403001203000644003240842e0001c42913a1707600c00c0c076105c0c4e414160002801400885812102c002c1e0581107132014480d804540e400b0720003031602c91602000b44948100c080081e84c06141c03501c0c0310400684c1d04902030340c09555041c0d803031038181d00c8000b91454440c400c0d000030a602851100040003000410350f41c134066038003905010701200c1d8048000a5a4009500510b00035070000d40c2d0f01c18a8000c90b89800b54090801022aa0380c500c145d05ca110301d03000195002000d0400b00700030081410303040381c = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 201622455 1250 201621205 201621209
    0x3031d010b01050403080a141c060501030b060f0c150c0406030b03030702060f0a140d1a090f13050109080d0507020c0a081902010e09090303070801080c0306161e0504050a 75
    0x10000d10030107200c00002810ba01c16400020032961010400d04c15071803086a40401c00034049070000e80e04d13110704100d00d503800c600710404001c45d414868013013010b5100f4041c1030a030ba14054040c50034260506182c1d07109811942c0703049864443c021521030f01d01041c5d01c2d600d0144c100d140303410350b44d1070903c2001070a5944481191380258800c0011743d0040e20b80c44110780d40d0f0303144a102d050311124140021507005034060f001c144622004500298040315540c40a0303000c42d40341621401180e402000d01030040c0045850001c100807441c00910300ca00e1644c08441c596100e00c00020309605c0340c7d43c40844c15003003840c010740c0060350364003044200c035010400050500f0b0300325460080c1514050a05544200e00801c030380c0d0207082800c050b011039000704014102080000d040c10140d14180707141e242c3c1c03a00200e03094400903081c000006800e10002c00c103007107a02000b0700134120a50354031004040e0648550500c2040091080d00826001100e0070030050384211595190754480c0781004014500e40c4c4c80d = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 201623705 1250 201622455 201622511
    0x30509120424020f070b03150a050d06020c1002160210030e0a12170901020309070f06230705030304030206010317161415010e0a1401060e0906030c0d0303 68
    0x7003100b070080e10300180c0e46000004070341ca00b021064541e00c0040303003081c0307540100451354410140d0118980400741701a611441d440b084200d80340441c01308100c2c04070304601c11190002004152a40814400e030014040e6106c42012641c01d0007685500b4001c076400340d65a0f400c4507641c041a042140362920020514050307501d424005001240f495507210301d91101c1c01050140d01440b5194030324002c01034040c103882c1d1800703800c00034504205454081d510131280e448043c040c800001c1030740082450303800280e50076a07981003c205d840740c44100005010452450740414284408000243c0c100004c1d84154480e80c0a0042035256180100702d50481402e101c241d5081807011040c50b8410000c0000070941200340380210a135100c06550616910042040030782c5189000801d20792a03004880e4000c5181c0013042011041c0788400c81e00c600000c0c011040003960000b4050b095140002e0400d030401001401d50381c1d0b0921399030004668014400d012800302e0b848a41b203d0041441c4c07400e98540d82d40b1 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 201624955 1250 201623705 201623707
    0x8041220030d110403150507030e0a0c051f09060f0207050d1214030c07020d020f09040b0132041e0609090c0e070c02010c03020a061a24090111120a03050912 69
    0x5c55542001e5001a00265820076070f03038600282a203846608071000c4600c0c55010b946108505080819482205015140c002e6943d2300c01c2c00c41042504c0e04100c811611744d500c1005050504d00c0403100c99894141d603404522a00d80041031170b6540c2100c506103a84511070500034003110000142c21901044042001400c0500801241c0101c21081f0b031552581100c003102ca0b10524400a1904421403024a4015940004000811001000541c10707500381140c610f941101007180c5102d1480c15403c07503c8052554000c54606d070810780c2011920106004403642ca9010b1400c03071208980844d44003091090712a50351b00b0600510300e11001c040c3c02515074070081c6241054000e00740036031142000341080702d00c4c2c0d00c6d002450b100b440603074003582d4032840070308c215001488034203141c0300040350b40391068605184c01045079081c140d40680d0220400c42160800045100640344950f883d410344090f402140c000202622050f03004003e50032064600152900703208020a00d803608030000000d010300 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 201626205 1250 201624955 201624959
    0xa1e0c1704121209080309160801090c03020d03120903020717010911060f0403080f03061309050a080a0908060a0204031406040323040e0a050702010c0201090308041220030d1104 78
    0x90058103042d0104620300f480043c3d0300314110503c006010040c40503085000c003005126200e4404240070424201d106600019940c40303016150888054000061a989221f4420401070410607034088d907460081c00c000e40901f00040440055401c6541c0840058002044c10300c200604c2525400c00c03030755080700800400c2039507035074410744034500644903201d079001040c0c071070394100d001d0200c1c1d0145910140b125182e200c0100b1502243c0c00c1981c81b02d1003400c00709a040610701141c4610a400c0e50410000e203410700346502c90700300d43c1d800b94984800b081443c0d1170104400c0c1d010440540070b0b40d50381100603a1107245082603155404500d1440445402c05424440402c0d0f01184842c8000044a041030345a40c03041205251881160b00c481d2901d10b4110401c40741c459541d008034130819003a00288410302d13141c24201c0c00c0383c004103c010086801072000c20042118400c11850b800ea090403d0303800c07018940421882e1003500041141d9950000070940b240384d805000d4129041030341304282d81814 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 201627455 1250 201626205 201626213
    0x709060809071a130317040305010c0305040f020d021315080607021c14070f05010507120605150f070b010e040302150105060301090c09050a0f0f140d08030a1e0c1704 73
    0x718091840b4100f0280820320f0010b40c581e850070000216848400c8542c406120785058406401520095606510301180301c0800c074081e005481c031484d80b01a185040254942c2080352008044100b039800a6100440d0803014180c0e106d000c0181d00b03d20300030b00d4120702d4007482a140c07600c001c0500c011500a41791018100d04a108071f2f48000305036040030807a03411a00800072103406001d60241807121813036002428410107510090080400783d0754010032000390080c1c20b060b80d0252280315044510450b000045030f80c51405804001c6200304000c2c54035002e80c40c1d94240500070307003102c0004164081400105034042190b207840c0200ca2402c0b00c02c82d0715217000205107000511503810300e140c55a8026480601c03860700540a000e001f0580c083d110384420420810503100e01070700b10300c191040c1c00840c100c1481e0b0580b00d000280104240c800c00559503400b1040d0300040d03c41f0022540b9810860200d1f2202e900d5020306035450703000040e04900060000300650109034102003140840780c140300c080303 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 201628705 1250 201627455 201627479
    0x150f0f200705071214060c0d0f140703020a140a030b01080f0f070c08071407051c020a05120f150601030506090405100c020c03030301030f020a1e050d02040e06070906080907 76
    0xc03001c603a8410704d80401410110200d2080044000450041c10b0400009641d542c0242c80c120382102401c01240040901120464404030510b0482d0b0815400142c02c0074441d030001c005141092070844c0c12800354204100e074603000120780102280d1582340351800ea50b0702540603036102e90310100c940141e0070185e50039525000d0282c45c070820860351925080602802d0b404030303015581c1c490520884400960302c1d56032600c80e207014541c070079540a410461111400003420b5109030b0001c04d400040303807500040028012640002c0002d60140754140a50b240d01030284444003a01e46071100041c0c9000000101251f60080c00d240c0706080d01c03400c2c032011a0001610341d21509c80d88800142808004000385d19100f01c0c0d0702d04c154944000000841080383d07010900400030b2003034401c0300d44242ca404031001012400c10020001f026001d200300458500342c80000c020500113400041c48008070541141040c2044400c4004035172191001c0242030340c4010003d90119404000d04811424143c03c040a = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 201629955 1250 201628705 201628709
    0x90705070804050603070c050a0c08060108070303020c09060301060302030706031e0207080d05180109030207080f01020307022e06060e0909030c0d08061504030507030c0b0403030c150f0f20070507 86
    0x16071340480080d0382e1600030702824080a030130801302c502d803030410b19226200202c540203039040f50251800000d904a070000e03691003a01c0e4550058410300d201c52003805550701d00104555415034031804000050784080c0000340240c20660b50108150b69140d41c401c4240d100c1c8a00d90700c4880c810080500801c0444056680020510341c001c291601d0709501c001c4505000400c0300a194a449426030405400203468400c07951001c051f2401c41401007140d071f08038041150014096001000407081e081007070881040728601041e40307140100d6110f82d0000483c1c4c0281c003c8408900090715018981ca40240740365400078154004500d0504c002004a0301c603044054500301340009100480c1080da21a1407d84040c203240103035503150303540c80c107065544203514441602c0d07440c0c0a00c2d01140303409100e406c4a0590b41c064490004403109039a480070601030340281705220594036500342083c5076144c091031001c11900d900100b00914151f007980b083c00719008904036450710412890001503808140c40c01 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 201631205 1250 201629955 201629959
    0x6010804060b0405070507060b060306210703080406090501020f070f120206040905040821060f060304060f0603060b01020106050f0f0603090f0d020a0b1e040b10030c030803010509070507080405 85
    0x86984403450807001506400b400154440d007014100022980d020021342410341c0150b0003440059103040030b2280e94482900e034a600302e4200d02a5804105a441081102c03510310b100714ac000704e513241c44d600c403240c100c1c1c0c100c0000100d050318108a1f543c0e0400181c5084002000600306080c94000d800a00071000d10038480322401160216040d0368942e0280c900070800c82c8000c0c41140340c1443c1101196103c06000c4100402c905c10003150140740e031102c04d01c40c3c4e50151184001401d080100720306a0401481100c11940310205086100e00c4c034002d030320040d0700c281c0011944031078003030000e82510800d4120f54041c90b603103681c1c0c401e03943d900007010541c80000d0711407a07500e8540241103410310042555903403161189001c0d02080c56400105051014058085141c0603102d55001e683e81041da20540c001206081002c01e01251074034080e0381e080810b0b080c03000c0c005540cbe40c0d01c102e2401d01c10752041c2c42030700c0040010071480c00d01c1480030703921580c40e14010345440469528484180614041ea034 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 201632455 1250 201631205 201631217
    0x6010503270c060f0a180608060d02040207061508060c0c10090f0503040b09090124181502060901050604150b0a050403060204170d1b060e031b06090d090303080601 72
    0x1440e541e0040c4601c404151020704400d42da20464079110880743e0002441000041d102d090842000785642658800d641c0d2940d034109040d1187d8003006028900100c082c0d83c466402c04c64000001d0700f45c4996041080d160440345411440c0811150410750000e00040a8590400c0000032011011511303c0c0d03043c030f40d22800103000c0c4003424032503000180164010b000e032000040c04161010700c0e402800f550a0210b4508000d680c071200c1000812200380c541e421507050110320899120301807108000b035640c81d4002e5294040d902c100c84103004d0382c4500c541c005a0800300c20300106003c28000c066016005071001e00203440f11058420741c00d85148120f040198002ca40816458855000c0300c0046030840002c0d500c1d9911940d11109001d04c400c0800401c0c4186400b00f454140548880d490400780c41c8514502c1c088a61606005044003443e612600d01082040c4e00c141142c10150340c8201c91100000c04a9103009250b551404145601c55000d2004030003040001a5011500307e0703100000303282034 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 201633705 1250 201632455 201632521
    0xd09061e0b0d26040618090234050615040f090201021c02100516020d210b0f060c010203071d031e0a1703070306050103060b03150111070305011406010503 68
    0x8928040040c40050204680c006800207001390310401452882c0d110070105000296940d07d030380124401d05900e201d45003050001000c2031501054200d002c240400030364014001d15036241401c081c400c13250183e41e5200500f0801090805106041901a0140c400c110001b01600041d580e4a4006100754031000d00c9907503026064424412041c2c50522082c0c03e00590030050b01001c20b040416002d10014819600100c030302a00c2020301c1d03461010440c036161461006100f101c4c0292900145080e0814910ba540b200349071212401443c0c011142c4000603182c0c248294020b01c00034400c0142d004454030f092042d111759030042000c2503c60041409810001d04400c0c1440c146035410002a04c10f10601c51601c2d140c40d5410011881402c0c256010001c8985175401502210b503980105010a4018000158600806c8106421410301414101c0501e10b5011840b880d040f0300340c0003101c1300c2e511b5400c58803a106a848203550030000c242007850a600d06043c0f140708011803880440300c950b40103003403 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 201634955 1250 201633705 201633743
    0x2d04020c030414060c01050906070807230c0a081b15012102010903020d050d02010f020408070b13050910082a04150b0a090807080a0506010b090103020d09061e0b0d 72
    0x1c460508580c0c1d8000e007d24601040703400e480c1c1000b26540c1c404a9080d1000603030543c0308030080300d012407040d082e5121440d840340c2c001455420a0200f00c40a101d205560307000b1a64100240505d031407000703c02000c5802d4011018200540c1100a0303180c2d4140c44018040c090780c4110f036456196000e1601c4040c8001400102c48404503a8406904107000240000a0100201e0070903034071a40e44e0024001400d4000842040f44260300c075031009504508811b124925500c0000d00c803a040e4030210138095901ca20005200c0c1400355102d9440c14640d440400605906101441c0360305a080c9105070220045544145000b0164501d0f03803040d40d40d424003000c1c100c00c1c00f8a09002e4104820416200c80404801620074074142c080d07a0900e10526400003031540000803500c4040307500c40f004d00700c980d103403070080c001d6a002050b20605050702400080030ba1364003480741a007118060940030031002e0044c5200b2070310030000c46011240300d09200702065951261510201c030b031644500e044603080a601d01e = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 201636205 1250 201634955 201634957
    0x10c1d031501080a02010e010801052409150d05060301061805041a070c0201030b061e0a1e0c030f0e030615010201090c060207060809061b09010e2d04020c03041406 72
    0x1541d06059240303400031590203000540c18065034401c3c0c031240c0340c0c40c007070390019100030809124043c2e101010000105000e0f0644801c0021413410040243c1842001400905600310000042c861040003080c0700c2c02200e02d41c003a1036000b0b0803d90080007280d05101c89003803000301c0c50420041c0c00361900c022408200d40039942502d500c04000c4140350f5414003150041215000d80c400b40d00107820904981c05e06d00d42601122140e82d41c081949545144d20050200290031000307508007800403100340f5101045800b400d40c2100c0500307070741c1c001e4680c5181c03601a000000300c0800303008000c0190012502c60300c0010300c003034111151880c030200c4a030342000100e000d00980d400040c403a40c1d0540c00060700940025181c0d0a443c12902c81c5201036071030b00e1030390340c0d00e0390116030403d58030070a281c1c04100201c080000749051a410716201c03070301c00803d00210b00d401102820000802102da1914109030888070400810035208845c150702d44411f40c1c1c0190ba4a01a90103440d24417880044a1011561240 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 201637455 1250 201636205 201636223
    0x1031a0a0e03190c0f32060703090507120501050a0c0c0309360b01020613032703061a0307080706080c03060a080d030b030c090105180403110304080304080f010c1d03 73
    0x203511801d40681030300e04004600e0602502540006051b0210b11440d000c5290040304003101300700600c030590b03030320307108801038001080300742c6450181c00004103406001c030381c5200c0d0040c066800884c090901206c80000c450202c032103042008190704405000a0380f19a00004549283c0c400410752000300040100c4007914507000d84181c0c0200c100d81c058010030b0340010503540d800742c0980764180c1d100200d0a03800d00302c84000800142e0201b00c24800340195561070154007a034070002c9864241ca80e9101d0040b6024180e0120300c1d0406176012001c185000c1011001a1001d80040c00c205450701c403014102c00f9000e000549040c0780400010165160510352034001c08802d8100c45100000501c068000c00a106080380680030310b00600352241809808141298009485080d902c205031720803800e000b0000c0c00850810408086c001c258000c100060000381c0105005199558981210b07030f0700d031031881c0c09000d0499050011000b01150841120f0350000b00b1740111160003880040081c1c20072903d1 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 201638705 1250 201637455 201637463
    0x7030c060e030429070c0b0d060e0a020306041505130b030f1f0605041802011b0c0f0509060d050705090405030d060b0901120b0901050402070f0b01031a0a0e03190c 72
    0x100f40000d0b00c107601c0003800c41c40140c1c0d202104440107030391050b095a104400c0085c25004240c5010081d00c00d0700001010070510111000481e65100c00c100c05440304180e40c5118255008000d0000c00d150522407030070324000c140c1036403400034607000105020b844c840d401c0c1e1a8041e603071a02010540c50a10020a10344109016a02ca089030040f011300c0f2054014070300c0d85040c0c60100045418141031180c29504c030809031607400088525401102e1041807100c2130310b084c004484211000948405995000e0140310359410400740c00c01080c00003058000785003600c510004a40300010440100701d50301640c1040d91202919611070900610b0340c03150f00021040c030381c6400e50004415818802414038204240d0f0f5032640c0d0a00d5400f0380059031412003229038400d11000041050380350030350041c42d4a911900f122181107140d51a454291602603005880040350162903106980420140340e901100f0744008201d4804078820079a81d0307001c1c5981030030040a2104030786208a000b488085556a48 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 201639955 1250 201638705 201638707
    0x12001090c120b0a020c0307060504050a0f08032e061b0c06090609080a0201020c091e040605010329060105070606031506081204062307050d0824010507030c060e03 72
    0x7440a81070840b8111400645007581e1100204141c072209008a03070186100600860420505868100007804058400c40d424455036001e03500103081c400400003850302414990391a03242080b035a410301c40e528074810311203502c801c01044582c110200c0c5842626000e213451080310950481101e50a614000c0140042e41300c2c07000047c0d03080d400701070354045d500f00d40d495400f030564544140707640d241d41d21402405a0480011203905041410a85500040b4032035044904207003020600c44c000c2050303a09a500382c4d1100e00600510402c2c0b815030707404050f442408586020810144140c00202601d0740d410440c4c0011a50184034440e004040911340101d6084584c00d40c4080a4008201c94811044e245c05980700d00b0280d403000105442c1159010303201c0d0700d40c1503109078810000f0007206e070440c40c0424050110700081001040030919a12440c1c45e41d202505050301188981c041c840c0c0408044d403a60084011036991010503110940e5041c00c0030743d01707040d0074a04103019016940500c034440c40 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 201641205 1250 201639955 201639959
    0x1107080d1404062009180c16080903070f03050d05070203010f1a2103040e100905010e1906030f120309172205030a0f0f0203060117160302012001090c 66
    0x64694044c4d02d0703070f2011411080b10060030000700701c6980a2402da40307601c4900c81c408202030b50320035481d050340903039141030481c40d1541441d040d036050164200151400d20300414510f00f2414104103a0003c1c02074600e60303210551444d40d80395515562840e0780340c100140410030718210749003508400101c00e0b414a0a015100e9030607100c1070845140054144990a00020045508802000b070f08a83c200c12001d9454a810540e1007281c0d0700000e0032100400b140c01c100000c07030480e10321609020f484c070600808014109045912035131030003a007600c04110710b807500c20030014003441c02e2640a160300540c10301801c54503003010f60003082c090401500e010f00c1e4401003000150008010701105400400032158100e17114010300e80c0c22081d010342030f0150b01c91010000400d2030680482120361089080c0d20303020402d0381c0480d04040083e48010702488448096020441d414804070102648401d000c00c00c0c0c502d148c00013800402c1101248904010150030226080801c0d00000b920310b412502e41060300c0c1d = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 201642455 1250 201641205 201641213
    0x50f090612040203010b040e03090d021f181401230d1103090f0f0a260d02090406050301020a0f030b04200a08060d0f06110903010f060602060a1107080d1404 69
    0x18080b10102c0c8030354642520500c882ca0603202d08203a01081d1802141006555414000c80d6410940e0580c1e1110007003002030003c002640768280300e0812076480c100842009014043e1001580d00000d48141c40c0814000c440c2c1d034003c1007401c0e8448000b0059140c440d0b41c9103617000d548500407004030510704240c0c3c040794241c0600015030107500c4010480b1040792024018545a400100c25520a50018007490f0081103509080300c0c1d410002a06001c182100280841810341c05420b0024840c0d13000300d07400e15079190510900008240030380c000e515100d0310398001445003140209400030b0559070744c0c1c1030405841c2c60b4400c00e120100c1030100e2007200b501d01860b49458002840920014009000007441410040329020f04554031030120f0206540c81da40740000f50881981c0310071002000d00c50562541e600340030756555403007480c5000171581d04040001f410070400414030078085080c0180191010390b5102120605a000790005460760b2140719a00e020b4203020007401f90031138909007480144 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 201643705 1250 201642455 201642487
    0x30c0c0a050106031e020a0504020a05090303040e041a250203040b21061207060c030e041d0f0102160201140c03210901060518100509010f090608060c0a050f0906 71
    0x1880c01070702800e03017500c5030004090801070403150080d040030600204211605246c5c0150041d4200390805904000154001c00d01d1034100340d01000700710003080c00f80010f000030342c03005030410a407230a45605a0302d8103c10b00804a0142040003402040c01072141020300d10078000d460180c2580156599904d011069030359014184040300003c8003049404207a60707250070001c044030251725901401045281c00802c0e19401903220701a404cbc00310302c40100c6a25035413803180342c40210102503800c40d4640c00c048581e00e4a1160140b0103010f0f8810070510b0614944105001c018a5091a214000f144000e030141103038080c403180c0c540d89101c041000081d00c420312404000c002c011810040d00346c0e035020005400d864140c46100c1e08520104851041404d0421a003544410440011581c2c00e61b500041151110240c0c40700c40e000e038100d68203000b0b465290295030010b041c00da008200c5402d094222014034404d0690103002c6c03041c000390340151140d4840584080f0b00009265507140c5081c42904440 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 201644955 1250 201643705 201643709
    0x5070c1a07110f030408010e161208070206031608070c03081512070b0307020d021b09130c0603051522091e0501150902070f0212010e060412030b1c08030c0c0a050106 73
    0x1095003031500b05500f03220300040c070f225034100c0d01c002704500c1480c04d4071042c1030207403002007900c6841c000c1141d41c000d83c5030100158021829a00e140707102e0b03448210010040040503208908000381d081c52000440c0d40f00d041283c100284141e414280504680041c0c0f03100780c411900003c1d4010703803500040c03044904000e103114500075001d540000780d90b040c049031500c801480071150200b00d407000c080c2906000c0900e40c0d00600c40008445040030302e8483c14922803650340301100203074a510412502c1030041080184481081e01c0382031142055400e9401e61020100300031a1aa9450440c0818403c501c0c800c1000d1a52603030080041d41d842d410300c2c50181410351523060303003501070110000303040e0071a1003160314a9400542e08410090103608000000340c0050102081d907480b484009000f400601c0714034021131082d80c62a0700e24006074000b4041c0d402071030000d44507401c4441d00c00303a45070110343e04000d200c2d441401580d81c0d1b51040c450724002e00540c0341008080c41000768001c10090154040c0301 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 201646205 1250 201644955 201644969
    0xa021c0f050f060708010b040b0307031404050a02040609110f1617090108180a02041a0406060305040506060f090c0717040605030405010b030106060e130609091505070c1a07110f0304 80
    0x122542d19550150b030422800e100320700c0e41f004100000c00109801c1009560400b40c21324000c12036072030f0b1000c400c0003450203035000e55154011018600461510f4452a4010002118148a441035580d081441030203103112003558034030700140c08040072621500d0740c050280e02c451501d002c08241c0c2c0d100e074a25040140b5081c0030a1402c0040746460840e6445413410071503440040041e100d55074203100142802c3c3e0308000340c01c070030140e0350001036845c2c0c0907503405016180d6001a4600d0305d41000c80c80c0900203002c483c040c10b14010015615103501c0c001e598402f04c5040c03010303a035105626101614901c00c1300810800c1d54041404a078840d03006000354004c074002c3d0000e1184d0709120301090f088400501c103680224811001240c01420030440d901610881c50b4130005901d69039000580075144071100480302500c0300107611140300c02520030150041518a002c60144005546010349640a0b440803010912020300003414580f19131300c1c0600480900058a1400c0c10f402d8440303540382c0180c09914 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 201647455 1250 201646205 201646213
    0x503070e07020c0301060515090d06050a0b01121b180308030403080612010506062a1b1002070609030816061526030a0f0516050303010303120506030a021c0f050f 71
    0x4003c0e280502661060712001004010112202d5004440c603500540c03000f50080d03140094400883c00b68403e03a803054050603000319107000c0d50700c00103141c0cc1680710403a07000c91608003e140031800b404142e201d0108141004120f540684003c0e081c5400958001445a040003081000305030740116014040d1009450400700307418171800039400d0726400c1b10740300d801920030b1080c0f900e11010840c00714035034882642440c440702650101c040c108052000c003080b0b1081124030625044c10001a0790031100707480d10181c040eaa08101001740f0085c224231010f000d0700341c0460b0303004041c020022a11546984400c0400c00c41d03082c00c00303215401c0c005100340d2018603884a4400000c00081c42d00d0034090581102440c6001511001a1b800c0c881200c0b081003000340a210380344143e90784183d114500d60154008580743d40c034504c0c005210041001c001080742c4d0502e018010703140ca00040818580764100e4024410300019441001c40391000072000c0c7c172520383c0501c0042400804242c409015054034191 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 201648705 1250 201647455 201647473
    0x18090207050a020405010b07050d050a09050d110907050a080403050d060b0d060503060c070201051b01110714070603111804020d020f040f0501050a090603050c0927150d0f0204060503070e0702 84
    0x7071460244010203271054010050000c2058441d200801480405081c00900c40381c0315400f1480340180f811044410b403111035405180c9241045105a00c1a00c0d850810b1130410301c0c04c80106641d10140000f000d004004c140302181440c40d401a8004c0d104050500d521400800c0b0f010303024008502c501d500078003030302001c0f41840a041c02110740050301a142c8524141e416044508280400c00c10101e0302e5681c0d80d41100d02c02490070003001c605028030300401c0a100c101407200d0030004680e100c4424903150413010442c001a5906503030002400c0700c02d40a840f802c80012402a10403a92007000355440040c03d0f1015100a901900503a042d000030003c8480d101c10040d030703803485003440140116100300801c01c212403103a000242d001000c45030b0341c0d0501d60050045821003012000d00364800151103910140d4180701101c20703601a840c014480c2e1555525008500d00100000000c0c10415600081109540719074200702c00401019086070000f99490466090700d16060b038080005000d030b800c2c1 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 201649955 1250 201648705 201648719
    0x2180406090509120c03040902040b0c0606030115060518060301060c0606050303070f140f160303020105090a030f110715021c26070309020a1e0902040b030718090207050a02040501 79
    0x4441c0720721220802080c2d1894020704504885e0442501038517180320401c4003144020903800a080100414100c0380d84a1841450b400c0c14500003c1c00c40f8000d0785800f0100d8080c40c03100030028200c9005003403055071909002d40600d07040d0f0070b9921040c0c100c540003000003603140e8415462034900d80980d40c104621900c84003010b40782c0c4602d50b0003424a070b00c1800c402000c00c10380043c07820709440b620704031070010103840000c030705142d402c40381e105811803541c104100b07158080c040c2c2680554148040c204420055038003030301500c5055490740802c04605006c001d41314003000140701900d050007250000c80600d81d4029607035002000c5405a410b990420792080078020880c80d5410030f20302085032408010071601c0700401200401510405440761404000368843c403504030003602284203c0c1a11846d90342d40c026800265500032904144104002c00c044021482503d0b004031480c504140c080c00f1090508002c007600380c1110020500c00101c000c10440005200c0300b25500c00e0301e05004130b81e66014 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 201651205 1250 201649955 201649961
    0x20c10020d0f1112090d0b04060f06050d0f0b0a060509190c080426121e0615031302010e06040e01050406050f061602041d0102031509090721060218040609 68
    0x4032003a400da0121800c03c135004030300030150000d50405404204420381d00d4031139440254040e01d090360120360300e0f8800d02c00411a4012603000d030809803070034040c42c030560351010203c01c6226006059000002c0109184036401c1d0440300c02801c0042c84000b0340d0030440c40303425201994802c250103251400c0480562103004040051140c0e40001c541822400f149038143c17810f030003100018521100c1080b80484142482441500540302050000c007990712840501c044104003030800c030b2003039140c08401c0301040092022030f503102a0f02910b00c0b00c075418510040e13441e440c220303400981c032100205021440d8005507155904803141140c090180c15519401e0210501c480245250081000c202c949038414010141d240300c940701520000307003a200008050180c010718003540403165000803d1061525945207401203c071411a41120182400e100c0305598907541d110b40491043c0440c0341584011207510b08441042d003040e0207540e601c103000035241c0c9072520443c60500c1146400d0011502c410644 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 201652455 1250 201651205 201651227
    0x6060819060b122203202802060910020a061506080103112d0405060609100f050c0601141003050907050411130909021e0306130201020c10020d0f 64
    0x1204540780850303120301c80f080c034000280030f010a51068040300580000c041ca0f103500c03030340c003e5a40b075080d003107000d080404000300d82421902c19480503040c00302c00100d10241129103022040d54070402d12035807000c101c103805500c102503400f02e2200100103800342c000c91170b1021340f4030581c0204046802701310540e0090101d03001d41c1000861120041c00010b02c401c0da20290204000c2184981851507561032041c001818030794500b42024a40c00d00c0c02c0d0400740580c54028804488041c02c1919140224070700c44030020000c010056070040e6091300d180120202c844184914098400d550384823002080c4003428841d8103070103420802c10b40f0310518400e1150b039010b10326004c060700000303103010200b00c050726a21990701100201002590740c9401d200510200601103048007050445090041100b10f80081e840da80705880c4140100714585d40105a45030b000d10004c0c003207031080000c2d000403480c0141074105103401c82c0640350822041381e00003a1140701a10716540b080515031300d80d0340c201c6407600c2807 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 201653705 1250 201652455 201652469
    0x11060106021b0f030f0610060912020d0b06010507060509011505030610090b01050f0418050601021603020103090303020d050a0b03010f0c0207030f02011103120114060702031b040b040606081906 85
    0xc070b038400c0510301d000030303d505180d14014100c61010046001e030500f03208081d40d40341d1000900301800c00c1002d40181000000380f6050884c413440c0c0c0c0054002c100000b0101c40300502d100c3c50800001c08507801101614000368101004002030b113886550240203194000d22441c5101c1038103070016603840c0c0012100e102c1e80c0d41d450444802d51402000c540a44089009281807007000c0c02044000c4152802800017007461500500078100c2c40364100c011543c000d003003d0b046402650910700303200610021b03c0c0c2200d60a10b000902c02d01a818203e00070300902401800040c1480c041c03000f40c500c80c1d044504080000c0b0000c12920502c0b4035401c0c11500d48a20960141c0c03c6100c5c1000800c0009044001e018010705000c1c0c00b084410002a06591000b07000d1090045840f005010780d203480d00c0e1031120051700307840b441d14200300c1d5000a030303442c1c2500166152400c42c40d08010200d0b12960003200c1070031005002031203003589907000a0400300b021556070f1510401005a40c2c5000f00c68002c5504480903 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 201654955 1250 201653705 201653743
    0x1090510170a022208152404061526070518010201090f0602030f28020d1b08070f23030a060503030c0a021c08090d0507210204050703150b0c0a080a1106010602 70
    0x10703403000340d40d914004c2086c560322540c0c509c4009243c000e450012600c000c4640c1d2036410510b84404043c07045d94010b203c3d42c0090307010408003c90701c0d810808440b41086003803010102c1d03038074900040b805031a440780001d00c642e0b841c011280401c050f40d00030314001d00020030040420783d01d00b0108643d912409d04250007a240020030b40400711540c0c0c0c0100240d1490203c0411070408bd44882c0e459000700840000002c1c10603810000d00340e510104050b03200c1c0841c904480206440b03011080c4402c1d00c00c10048800000002262080c0342c540e0210b0014a000380540761030b103901441c0a5201c602440040e8001d1401c07041420f480e000700c1281031100f41d40040e000342012001741c14005c00000c620703c00c0f1054410b100303002c124200d0200300360390994198905003005c05564414031054900162191042c98146000010b40100b000b400b1016035a000c2d801581b1882c61040c3c05241544081c00540300017000030708441140c1c0d1101e045d12a040c1140c08960999a0751002269101c546075040401011 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 201656205 1250 201654955 201654991
    0xd150905091507021009061118011202072d1a07030606020106030b010303030c2007170609060408030a0207060f020702010221070b0a09080d0b01090510170a02220815 73
    0x99150310200301c07107000341400690991074924050715503000b89503504000d4030300c2202718095a400701042c0300d1002c6a1078107606116099403260500c0c071240448a10002090100c032020440308038040746143e401050080c9040c03480c2d504c2252417541a21504c3c0020b042100202d10f01e40140155001c0ba503201c0610f800580c0b860720214014030315100c00c1c00400c000400c24004040e01c450000b40c24402080203440c4080c9003c0b103a6030003001168200384c03190440d004100f107a840120b00b496101e030f0440d0794a0f540385e5407805080c0c003d21406200406286c90045200042d40d1682e0160007454400e03022500168103500d501c801441d00415000c55402d020400303400040d41d83c2c2c0016412122561002c280909030b5500c0c0384142d000300084141c05c90340c8448101c7c441d82c3c000c04440040c081a5090a003491440000070659808903d0403500028840e0111b55052500c1d0b0440f40003440d80c000003841c0890b0384079803071180825441140c0440c882c4c80054a0048940040310b0702072040740901d44143c01e = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 201657455 1250 201656205 201656233
    0x270f0303090901140d0c0b03150a0311012f010501080c2b06020405130209041a03150402030a020306040b1008010b060316090801111c0902150d15090509150702 70
    0x260402400c4d40c00c0b140c40b09240c40054a58040003014100e0308600503242d16004814001750500e10740070038424840300d0070410110b0000e2602d450080780c02e180c4081e115201e0710200410b003030707070310b0049241001100800c0559072041d40580e0680f824482951440c60181041050f4060511a40f0300310340702810600c2c030b00359801541c41e8001d0f0300c038182c0503040c07075600d40c00102100c200e11842c0880a4001490545500d4544143c0d4400b40642201c000d03581154400300c1c3d52940d0800080742d1006903003000c202555410848a0481d6030f006044810030f14140c03410f656592001e43e1910960080d01032b0100e0064018040c401444030060801d50a507560400005008655400b4183c280903401c000801c842d0403c0c0151021620201c1d10342c0c1d59032076000003903010b90500030021210140f502901e640180e42e0f41c0540b84041b4007440c60b641c0c84d2046100d0686c000c00c907004542d000880042c40000f1000c0c031581095104d03c028201362104208108561803491504a4200e40140c00c4290410424 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 201658705 1250 201657455 201657479
    0x110a031e1e0507510c12050a050403050d1e020105010e04030509011e05030601020d091d18010501031101030b0316051005130f0905010b210c270f0303090901 69
    0x180c40d584c4090a28072410b15a00c00203404401c422904a441107400509100c850011a4158440741d2034580b040c00ca540d16410910644445048100800041c4001409200310180c81c003868008060356031082c0c0c0d150000c3c054001c28442ca9400301d02e040100007650b0b00600c1a00d0417201c8007900c019980d5a03590303040351503a001c0c102c1c050601c803038044440301d410f100e0780d001d080c2c8000c5601c0c1d06580c0d0408400283c80e01c03d40c01d0f010410000d010809001c0c54903c11491840c800100f2000c441c591031300140c050451407240702d901c2c030541c49e1100000c00d00040041288203400280c83c00c210b03141050050517250021140074101c0410400703030400c61418a00e141020240c01031400504000304510b040402c800e040d400b2100200702445d0500c8002031602c01d550040454400c000d20300410140c10854146050385400f86003441f1200149466612400303e50045071580118070b4400c9080d003060717031043c403440b2a2070f0050004c4010b02d5440d003000421548080001060f01ea2141c1c82e2034186002 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 201659955 1250 201658705 201658739
    0x80403050c010e010914030a0e0915030a200418030c031812020415061b0503070f0303050a050603070605090f040b0909071e0302010c110a031e1e0507 66
    0x1041400c01601400100070f2040c400040f081000110311003646080c02034200008034450350322034008001052140b0740149070201e100c0f0341038801403030035924502d44841d20443d84042d142c05002c0da051310010007902c0c814410702083d07442607142da94210502131008940a8180c1055194502c60786d600110340210300c0341201500c6072400c00c50610000540038600e04a83e40b0a402040110b1840300440c5410b00940422152035003880403c9440c20074020281141d090f5128085151440d50100780724060040700c20040c2c0020034031200040d07602c2c009004000071618075540c5032505000c101c1300d01d070100e0781c03904a40141c0e9405003032030147d0081050720800c50728055407040da52402d2512035101c0a102074401c00840010b410603a00d0146007402110001c686015002c40031402440141e0b006548a00c2c0690803a006103038200d4580086003064525400c080d02c40c010710040f18008260148204008501c03a41e544200103010201070440c424803060000c180c1c0c1c0101c4828000003064400002c1 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 201661205 1250 201659955 201659957
    0x302010c06200c01060513140106051c060611010e0601062003041205030c0d0e06030112060b0d11040b010503190e0a0b0709030c0608090d030b060c070f06090f03080406080403 77
    0x10b20b031980c00e00718401c40c0d225281064007a510742008010510307050a10313031840000e1110521414000000c2288062014050710061204c01704440814400c0540c0100c00d140c0340d44030403c9420f032508030241680400f09991001c56080140603170409502064040c12605541c40e400024016a80003118003840414402083c0c03205210018805a404540031903840c0100091566a10301c1c109480c109a401c074a44018041241c1e400503090f2540400c681c1118903a41c61b6035003590780c40c605035010300404800a94000c4c4c5c0640c81400b40304005110505480040b142044011000801901c0d90300084030b090285030342074149087c00005030f401030002c4001070000da41c8102d038266a1081c0300d0f001901e805001a021220607c200144504044041d2003d0b0134043c40070300d04800045e44c0c0345400744d48501099110743e0fa8009035210360082d1110342200d641035030301c29522070340c0f2040303428498403820b800903110600014034440308040d81001e8a402808407450942000800e441049025004070 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 201662455 1250 201661205 201661241
    0x10e0c0a08180a0602070f03091502120a09030203060702100f0605010507140114010605030912040e1501030608120c1207020d0b0709030204020409020715051e180601060f02060c040302010c06 84
    0x100013401c81c4001c4c94883d108180010f62030004d4200100401529007080883d000342c3d412508030a500000e0b010010a0f465420035901e000716081100c441c001e40d40700035054803c19080c80101c82e00494103c80d00380401ea41008181295160b40062703d42038072507107000c110704000301c40125040c80f2540d9007480355500081081e00c0da043e11180502c0099100e880011408018082116801d00403481a00b030900344485c2040d050903400ba0241d08042c1010f0050010840048100d900279004980201544010b85800c01070109004030382d139022011240540c0a4000864048209001625001500500599081e203007940e2070880210024040c0028000410750005c01a9510300081000e4480300d0f0f405a2a41c416203040c40440074000c0043c00920b0500c0c0800842c411402ca20150a8000c06149403a80d220039140800010750b5441112282c000d1800100312a5007081c00540c401c50b00754215a0b151b41d401441003458001c44c00001d0000c1c9981c00200701007120341e00300711880d680240d004 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 201663705 1250 201662455 201662473
    0xb030901060b0a0f030605030714091b030c0919030f02010807120501150806030706080c0d0617060414030c07060302031504140601030c030b06030a020c100603050105010e0c0a0818 79
    0x640050700041c88403000560f1440b400000382d45d05026030b100912044c0d00420410b81072a80c4184207000801c50070b401421085c0014030f0713003408501c803000407020721140155207081c44011440e0f00d0f440302141e18056640340520f03910468400042d0804c8a82101c80c550500388241c0c011a8440780240c4910100040d1188541621140b4821702c5e0080541ca800105440d1407802d0140010300001c24051003030b003182a0130081c081d005000076034448000d41400c1d50703c1c2c0d400701c0554001c100641100001c0011210500340b00700300041c3e114041c038003600e01c4105241e00b07503911b0303a5070748240071480e2081e07040078008111050003038005c0c5801c18014810030883c0aa10302c0803904079122008060b01d001d10b01000e00c0290758040c0306003c3e5452003440d040c07001440580200303445102c06407113103504a030700042000300743c00203000c030045c0802d03d001c05208880e9a810803902a14081c0101e00c0020403503c003040803000010b0855003c54003035110541d5070f50790b040c003568088103d0562604140a0180b02d = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 201664955 1250 201663705 201663719
    0xe0c0904090f21030c02010b01080601050a12060902090901080f10090f02090901090611091c0614160e01030209090a09020303090312180604080a060513020a03060b010f02010507090b03090106 84
    0x103540030242055103440c0d40c0400f64800142035807201e611030b2043d0391509070040d0840e680129181d900c03060a0801999510200504032481ca47c03103008050303581d10700900400c414129400520600304208c8404200b030b43c0341c681d825100c0d0790070a40c6800b0740d070004191a40c5814075030812079010b4042c410005400b00540c0110f081c804c0100c4880c15265580c00245081016600c522014800c1c1c5091190800e40c1d614089200101e20248044040c03c1451b8400204022a0090044851a4009000e850415003010038220a050840b0301c04075100505031801940701c0d20a44248120090030b00d40b0b039031280c1007218014600c9880603a054042013007440300e180c074204a11030300d0028110405680c0d00100c00f8141c01d02582180c850b00c45c2c0d2080100b0400c1800025910b18600d400145c00240c40e140c609040c10182c0103a140207411030810400002402080e45c0a0003e02900782c84128800e544140c1c220708841089441c200880c07042441440000d28401c00785034480c0c0164000110551201c00d = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 201666205 1250 201664955 201664973
    0x80406060e07051c0b030717011512140a020f0904030e041e140702060c03070302040323011a0616050f1507090b12240414100e0c0904090f 61
    0x4100b400314400107192000100c0d4074007450883c0d0030641d000c00c06520b442c07002944924a034032132044d013407421041f00c802d022801c3d4000c52400200c440309401341c95840f8044000074003182c4040d034801d0f03080b00040c4141e060102d20f560a2544c02018030f40007400103001c00c02040f83c00380096003040002c05030b087c02038880d4441d00c0e11000c1c5941c0c00c0c094030310000207203c003610358580300b104801c640c5009202e01c40750002905508080141c0c0b95948991342c03254210300038007541d40b01404032001100c0b00e205800c00411400e0f00c410110009006600001c10707143c154040588000d0341061080200301800c0d010700c1031b082811031080d020f8801b045404012185170030070b1804a030b500c0c22554024060226001100100141f68440965007441000030701c910340441c00030b100f040310403071340e056501400410051100202c00c000304104455000203100152180e0103e502803984500b441d00131405000a500d81c912456403110224a031942c0003041c00040c0c0b8140a040310b5020642004c0800540340300 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 201667455 1250 201666205 201666211
    0xf020c0901060306050a0518060d020312160b0a0e070e0901020409090c0e061c060506011e09060e0d020603040f0f0f03050304030f080411150c0706020a1101110a03080406060e 77
    0x56000701346942010100200321001354009441512079003130100c3e12181042e140c95000e20103c0b060120488207002180c1404241c002200014000080b81480200482c2410810500a100d6149c0640d40e4504e254111220303007610791071301d80c4014020001c00078114481030f0320000410016088c1580c90111505032044090101c940310710218003800224031038450951b000b0001c550404400c83c4280450041100c1b42c440038010940380c900182e01c0382d0050707085400403004500350b26484603001c0d80040000c0801d00174900098803146d842c5c2c000d864507100074840fa9400412851960320303240c1d16812070348803e8400701e41d200b082c1540c02d000f00d9110040d00441c0ea003e81c0300c0e40d80d80c0c5018900240014000020071091003881c3c000d01c00840d503800082061500103036121040b200700400001200c0c018030304d400c4454171031a0343c041180342e80805d0782d0703a40780d100300311455010b61490700544010110303030001c1c003190741705802d80302c04284900c0c2015001030003a03d0005100352108102002e0030380803 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 201668705 1250 201667455 201667457
    0xe040906020f0f070213091e05010b15030405060903191101090611030f06090408040302010c020d060c0207030b0c0a050306010807140f12091209010f09080d0f0f090503030a0f020c090106 82
    0x2040b4030055080501e00280601da906d80d04210700710042e518140e82c3d2500488200301151800580d80400401350f211a480303000040107c4007407220f0103100509640120340072145405000c0102c0c80c840400400d0b00c000300350f0100721039115940c2c0310341250440e000508520080d034a48035050046490307071103a60004108091001e6072031400f001c2d0401d0060016000b9030084451208100100701c8101c10354045e00c0e0f091030100300d102880c0c000203e03d4070102c0c401400961038070b015402c03442c2d00041c02d031003100e2007401d07080b00903964111601440d005100103003010540800000304150b1045141f50f40c850002e09280b94442c0050401c0710340c54015140040300c162002410788001c401001300150b0010800300181090080c02c194040940244c00d03034035050042200e003400c03010b80950f5080010b0f01c0b03074600711464420160002410303c62074031059004200c8130400d08806e42c0c403c01000d420b5030000340085180c0011504100d54149041007000300314018405141c0c0b283e40c07000e800d070b4028001 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 201669955 1250 201668705 201668707
    0x4020d471f170c0304020f040506220f0606020f0c1c050334020a03030305070e192c07050a030e100b040c030b011407110a0e090115060e040906020f0f 66
    0x81ca14600702c41503805801d4508100b001d208002c0103039515540b043e41c040055802145c41e032284004160a24558516200c000079883d218080109695010901800301d200080c800d15954600c00d0303807141a03c42d00c0341419040820003400c1030804142d41e40c002017160309040100b0617981c030707060300356048050f000c40110001007003000480220a02c100c22010b0394084401d2040c0345074000790405010307110090905480d0380000381050700032144001028009004801e0b031111200390180d8400041c0200581d0111950b1200303c0d11524010205113000c0000189405840e800c01c143d41e103820529400d410182c0703031180107941e0001485107a19460084a0100700300304a00304010a031211407005000301450b001c1c690649a82c071041a021109042c071a0940d1484c032800d00e07150300720350520030301c0e00500c021100080c04d0b40681c02451050004d00c008100520741304000443c15603451050f000004d021080c00125450140d00541c1e4041c8204001498a0400e47d4580c0b146d41050854443e0900 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 201671205 1250 201669955 201669977
    0x61e0703030e0705060a05071502160b0a0c03020313080c0309060706050711030309071a0408030301030c03061b0c06020313020405090f0123130c0504020d471f 70
    0x1c2d04100000181c042142d21034240b0650a80042890240d100c02400e00c8000ba41b49561051140c1d04543e01c03121800c000c42c0d102e076070505010040300f10039030780034485516050308a59020710038820341c1e01404012002403540310541d15000a99004090848041e00040081c92415580c007001814032a10401002c81e8601d4001e0025080300e1803c0d900120580040041050020010a1302010f4a00856000a10050b5418121400d00541d00310b618184000000841441503030791084044a2090400340202c650480d4818032920b500c80c640c20100713088a031554000380d51500616481040c030981d100ca007070225000101901d1082c1e44905086e00169225000c1c070b0700078003a041c10b514103000c141031082c0214065030282c0c5c00044c019441583c08e00760707882c2000b825215030402004014410354a030541c2020540042c04070100703c15850807480d1f00c5014201e0001c801c1a80020b40e21001c032580d0321901c0d00c00c101c03041d1420111780c1c002d510707001c550791000c042d80c10710411556594a0081a02d = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 201672455 1250 201671205 201671231
    0x612060e150f0904030e150c030327010908040506160203011b110304080a020f0111100b040c0216090f02040e01150207050306090d18091e0b0f0f061e070303 69
    0x140b40040c446018101c00001c02c4042038024655983d00d2905594040400c034005131849841c2c001d00308020360600000050009a1440c540c001c1c008600302a1916041103031034003168200d4075140e000814159042c40100900e20780310014041d2842c030035581156a0701d003031740040e003110450a000c40c1040007040500451030f5010342503075010322001d0000c51a060a088007e03650720a00328000380b14a605c0032080f8240d0340320300d900e541c0070036035041103c110081181821025081207030700300d401146001421038106100040302c001460040d100300c42a90308101b0f204000d800800307461322035680c00b003000003a140703d518030b59802400c03050005008161a4a0003e0901c0e0742584018802c5e40010240110104041503441d000007550038120240302da000306085140c41c0d0755200c03820440c41d0100c142c50b01062101030000c599032100e020400880c10300208050b4810000c0050b401c400901082d8006040c658028412500c0301014419250000038410400e43c0c410141100041d4603201d03103003000 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 201673705 1250 201672455 201672469
    0x60c2006070c081212150303091305010602060c0a1b1704090603021c1502090a0e090d02210904020d060306150f0f06080c13081204230a0612060e15 65
    0x7031413503094500700d030b0000805281a400340507990b00040c5494900303440c1e13504004540441782c016115600b0f071805880300c44000e10092140c0d0015009400020b100b06190780d044803003150f143d07214003401481d102440007012217040421940e00c409030a0030180030384804c002d40018400e9408c041810b071b08510510402e6141c001c47d070003900c42d140030700340c0004003402c1c403104a040015000503110410400062034001d01c50307100c000300320b43e45810301c640600041407a199001098084424a00c651314900051384c400d84d2a14003001d00a001107886850260010f0802c268542004503800c0d459444603412521500401c0c050308080300c004110403d10701e00d100340200300100c030b15020a0b20704070740541000c0004007640051035000a040d460011040300200c060400c0c0c1c4202d0305607a0800010900c50f80c414080d181d1807402030b45601031441408005403000c0e8401410441e495440c0a40c190340b2407025140240b0354070388680300442c2414503500b0a42c4650290200488041e035048140521 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 201674955 1250 201673705 201673723
    0xa170106050a050301060b04060f0c0c0f0e06100219060204030b0109051b0c06040b090f0d0e0a140d021012020a0203040f05090411090603030c1608010b0307060c2006070c08 76
    0x6171341000b07000c0042c0150038042c0c030112641e41c284009070310048001260031859000c40100055403806004c90711113003c22004080e10300b00d54682d1810745442c0704000c010a00c0c2c00d8402c005921160520840624244010b500580b18840c0503091130f0301c0c0e94416011240980100d038003107130b03218100803443e0302550344c4c1c0f46d20420b41117071903151134080c900094a80d600200040c2c0016107080c041481c504007004101000c0280c103040e54942980300c84002c0803080c206501a202d90325040300403802c0d4071410300c2c00005140040c0380840d024810350030720085421244140c024043e400d680f041450542e4002800d14508550107555101c1c01c12401e08420042a000240500705c4034003008005008800740350310344041102e24110595401001034a14031600c3c10301100da000300c80003a110007070b29449103001c0d2001c1c031009021840c1c06c0424150f940411340b0829001502c4d104040700800c0440302c1c92405070259401c243c51242c046d4000c02c0d07241d8001c510031512100e048808114181c1b003070120b801 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 201676205 1250 201674955 201674959
    0xf050411010212130e060f0405070e0103050603070506160303140702160b0306061c230901050a0b0d060930080106020c030307061a09090304170607080708060a170106050a05 76
    0x100f45040c1010020165969000700d0a140c01040081b9149990341002c00d0350720840280240903601d0251030045c15415020290fa02281c200804600d007440d011035454107079070018080344d044c9118400004002c200c544800c0d814150b4514006d03107030001c0098440e1081c60990024031420a22110002d4164615401700e000e54000780203024080d56188210b50504062403911600285100321a900500c04e001c0103620107403030301040600210fa07001d445845900801e008200c1607540020b04815100c605410a50017610103540000103a0320354001a2100d029050604c402105092100c4282e00311080d25058160308410049507580c0c06404140944014400341040742c44e2580441c0c0c0c0c90080680052146484a0b070b00d6000404010340300032240801840d1078030508000505c43e46076400b90040103140c1c924164040744030301c0005480c0d1301074041a0395141d825606c0c1101181e14000240040e6485513180c0c00004850100f450740041a803484000040c086107410204149a011540018 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 201677455 1250 201676205 201676207
    0x604030c081b01080112021f03061703040806040201050f160f050607020a02091b121303020607020111030609072303010f0f0308030c090d150b040501051903060f0f050411010212 78
    0x3842c00e03644034003081c0c1114009001e4210b5800c0c14400105610106014035441095200314560400d505400c10700032540d030b00c100c0600440303402a01c01d4881c401c90184c0c5030700b540a20042001948904020201d08080b4074106d03040c03080d8100c007401044012401a5202c0c032180f00b0341c000b849002d005168014100c6e00041c400311180740e0104c0c845080051030454401070310301d0610f0b4540d0504003221140300e280e420000540c5050040710034000f4081e5019801403043c0c900060005005100d0a80300158042103282960340da0000c001c58188001c04000420400c560b0402910011500910000350508169500c0c3c0d03040c2000000300e001198801150399480300c0041004c242d0480860303030001c2c9441c40300381e5034104140200320031810820303006200e10b0082c441400c12558076072004114160840301405184d0341d8408000c02d011070a0f00d03907986000f40260810000300781354005105405403480201c0c8184d01c2d215140c048410440d030640d03003001e5080280c076143d030b41803044d43c01808010120f5 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 201678705 1250 201677455 201677503
    0x109030314090601050f01030905120301031406090712020a0816050f01050a050712110303090106080606040221040618080403110103050c040905102706080d020d0516020604030c08 79
    0x18a41c1c41a0601c6564024045c2c0c0086ea07005902ca5000034650302d81042c2140e42030321124803503045990003407209603018007003994028111000845d8590254005038011b103026406d103130811005510605040f6801044441c00140540d0300f4010308001642ca87c140b01c40452034001804040381c00e0005090410008128010321a5040801d55840d6074025064000c40300340400c0c2501d10210a0501715003a00c4044100811040150000c1c4195903132203003590210340395002400203070300a4850003400d1081901c03115005140c00110306a2040c0140400f0501c424408a0380401c00c81e40e8100381d0320350324009001c2c0180202a500c13002d01840a00e020006407410f00003608441c01136014940302c21b500c5102041d50701c0c02d4085100d001c1c02c5503d8600e8a14050540c40d00c0d03a4a40600f075040c403180c181440040da0b04404111881045004d401821900c4410001202c0d6a404410016181d80079000c110300580c661b90301170006548030f80e14915400e410710380c81c580790403ca122400d0900b6452404 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 201679955 1250 201678705 201678721
    0x1f091e022106030307020d2d080304031d0a0b120c03040809060307050c1b041406060a050a09090603050607080c03160f020a060e071d010b0414150c0109030314 70
    0xd111181e400541005025484400000b0b0542c03040020103540255840340000a11854020219040840000011003442e005494a00c1811403860103484541c0a00020300807a001d12454138141948004c40c4200180780300020713031802a960450508031501040080c404d000704c0d1754072074002400c07500582c21480d2990f544080342c4100c4100714083c80012000c90035590080d070540300700030fa80d542034a54403044004800500b609050348144180d0401380041d055401e40b0f803400d0702070070b170141244c1e1034030107440429602da5100352030038004c01030070400001e10000c90340705103800382d403045014101600b4500001401114050031034162048104180300750000c0d01c10090840b49200d0a0012211102081c01d074200070300000060000b80c1003d4030b18034a03400114030007003a903d0000340480c0524845003c9020030f03609002e46200d1050801c4107001d1840700e401d4800240350002c1a001c111039003003c5d0560103030044601d51003260344500d0703043e0416405004000744c403056200344400920b00110 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 201681205 1250 201679955 201679987
    0xe031204022205130b0606071109060f0307030b0a0c1103070201030902060d140a18050613020303090d0308070906170601030f0608030c070e06010c03020a0b1f091e02 73
    0x902c107540c40303924504050340d440600120301648480400c00b9151907240010380c242c0c000001c6614032119000210780b0f180c2034080e64800d40d0000c01c400700d10040d20050244d0040003500321a401490010005080c0d90200844d001841c401d24030381110b428a41c8004042c0c2c0c621035003480500425070140c025001c000001c4d1501580c091070040340074246800400c503e8400c034080c002100f42400307000421808910390680c0103d00a04040182a58010341108104018240180719801442c086003084041503485c582e03082c001020b5078601381c248000907200300000c40e0200c000c504070a04211502d074010000794001d10007414841e00c1311030309501941076400c00910290525076550684c84143e9190360111015144d80e404882d51640d003410440c2d5101070500ca10140d84070f9134400078003154420b046500d4129419002020183c2c43c0da0340740c10308110020540c1250b485030056419506010701282c43c000c2501c0d14001030580c048485009000d0012040e0b02c042c58010040e42880d01d040759 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 201682455 1250 201681205 201681211
    0x209040e0a061d1906020d060611120301050d060509070803031e0705070209011e0801060f05090129030405030f0a211e09080d060b031f0612020c150c030a0e0312 71
    0x100385070f030013107640c0e1038400020701030740c0240c0001510b0003602040854006200c100140b400d60100c802d440d000707601460a501c024010307950041101078851000886640149030482c0c000d0040c1d490140e04c1c0c600c014950340044401d008600c3d036401c031800c2d0110301c4000060300080145840e518100440e0085240c941c01032207003680c903603440c0120080f21100a01804090301c5084020f100103540c0704c03204080c28086004061103a40128000140c2003500e032003440d4000000b40d5403015400d0b80c482c480c171407600010300a40702c50100708248540c41084c100204881c41c61078850140c0249610600c0740e140800890b404111890540c0f00c08400702102603040c0c0610750741001041200162904e00d4407070141c01d040001040c00c281c07002c40c3c0c0a1100c009948203504143c5c50782d54040c0c04603e550140302842c416680410710085e040b0304e02490b41e40050001c442594222075040000c244421140c0b401243d504080d04404000e20103806000d01074001703490082c2004500b0b1001050180315140806 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 201683705 1250 201682455 201682483
    0xc03040b09070e040f23062e03020d02030a060212100602062e030606180509030f0306090c07080304060e0d09080705120114011203170f0f06040209040e0a061d 70
    0x242104102c86d00c500c0c0040c41c00c00c49031000030056115880e40d500c10301540c40d200c403a03107038201e1100020450720507000d10002415000c20424a9a02801180c00c000581030340c040c02101226804034501b400245058030010360342c500c1c0c0b031402d208800500c005c150400b9046401c00300a01035001d03134680c40890898001c59442e2513a009501c411440e14503543d0000340420300f0704000050251350721081d04003010501109111079600c60101d292607101f4942c2d500100b400a03c0881d0303040c10031a100e294400140103826107004072540703400410790030071582198072580b0f9144084c1003030424070148510392941d0418486190800b9070035a02c440d198003e01d800340307a140405030040c0400750400080c0b080d01c26005907a41d6160000440b2100000100750046001603030340d0b03d0b80c41e840714440b81c451031020703051710704a86555083c584803000141c0f03c2c3c2c0d4040d4090040d00340a6803603114140c8009900d80060007150503d20b011816110102448040c03c001b07000c98964143c0c000c80d00300d41071422 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 201684955 1250 201683705 201683723
    0x61605010f0b06180a12030203030604050106020a021005160804090b030111040f050f030a122a0c15020f01060602010209010806120304120f0c1401030f11300c03040b09070e04 77
    0x80440c5c6140610360040000d4a00399940005054000c8004e50003100151000d101c07982c4c80d11010382e0342e1401c0c0e400081d04000868a40104240b01e0b034050841c03c034940c1d5000c030200c82181c0701c0e1103403038115070441d501640c0c0e90040f41d42c3c0c0d45824480e01d00c80d501651031540c2401c1c6030610110480c0c445124140c0105041c46007265559010b002400e103550340250110b02004451030000d19900211485041e058a1020000300403164203604d0242c1940c01f00079050315a051600d0192042e0b170505484003507104403803292010060030700a50000e411150b000503243c10350320740010b18585018110a0151041c40300c220f00003080401201c06407030110f892071038241c0301c92038000350f00d001908010708090170301c030b03808229401251040d4140741341c241e07014400c0900a0105008990302480d06a8034035000700042c403c401c071030b40d4041040400c10b4101d400c03d000761600915032071000712001e40d034000700041003004200a03440203e80000a00c8000c2100b6410848100050720001d07001030441c4ca0 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 201686205 1250 201684955 201684997
    0x1e0c01030c02011103090102070b070507080a0c02270a06090e2d010c0e09070318031107030c120201110303070c06020315030d08040c290c010b061605010f0b06 70
    0x1000350003000e0a009002c100036030364509410047c1c001d4003c0c0d5800c844900c0c0d51008034034503e200e0815609090780088074039182a498040c1550440780e2814120f0700034240701c07019840720b40003038011000c44400ca58400c0151030905840700448416030031207000149403131071058101d1000101d070720a14041c5c12045216140c000a01d00c1001c4134030903110102d600300007015000ca41d0103214404c0c07105003030700c03a4071094449400507401d0324a1142074140c00a0760710001808203100b07900e00040351901d032090718162520b0b5285c003111021b40ea00300841c0025598195800c5503404880c001c04000d10101642c103505102e1001860400b45550280c070094001c808126803000700c0b0714040b051100202100c0b1000b0f239164000e0860a011101984c0418084200040189034454641103540400100484242c1c001c810840550401d116a01240d96242c225242035282c15000380551001043e0791440c0124514201342500d10700025601c40d242004c203082c0c00d60b00c403441506e8132080a1507541213401 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 201687455 1250 201686205 201686207
    0xb0603061b030a0e1f020a090e190f0b060a030501081006030c0e0403020106050a0602160e09030f0c070806091f02091e040b0604120614060102030f0d0b0a06050a021e0c01030c 77
    0x42c01e0140705030a41c1d070845c0d10302180e94450341c007d24040350691508891107039640030b2024403410407035024008141410302d0340b920100c5a0b0002040c06081c0000007525082d9002041041d0484507071071010070b5494006010300181003000300c1c544822030a044c082d090640d5900140070a00c0d10682d04440486004141014000e410040140c00702038a41e182940e61050001d641d180305182861410a40c0500424004521290a4450085940114501220242010b07007643c06201508501c0c0590840031440c480c0500c50700307000c2c2d9003c5000305592141c0111200e0b514081c100a0301100303104000b62021781d11400039510700c04148151034495000d10f407002c10081e19908a04c660300c500c0c0018003240c0311300700c0d0309039040c054010700080003612040008404840000d48045025910600c040d00c0c244010b100207001c004226035000c90112444030222700304804c0e80d002400455004100c190441d5030402142c1e800d804114080b800354075081210684500307250308114100358440441658403 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 201688705 1250 201687455 201687463
    0x902071208041a0a02090907020d2f070306051e010f051203071203020406120506090604020f0c0307050a0b0a2c0c030604060906050615040506030a06030f0b0603061b030a0e 76
    0x2101140405803c01c0c40c0044100d0001d50050201500ca990b08501040460348001050284144c0c3c03616145c0d42031502c00302a001880c10382c0300800643e6004641d41c05a4801800580c00451052101084608000394000d032002039130130170003200d110f000004101002c0344040500c112001511550103181580480d14250f20404402504221041a9800c101503056000f4800c445880e507070340180d054064140001e8460aa582590000707200c00494214075240d801010b400070b03014512031a00200c40301060468004007802d5030140c0042c48408180014035009941c850134102c020002c0a2641c144881201586203010303a84070407005411801d008100074915411500404803540c0340750030300d4480040d2110703800403100e081c100800310390503046c030b059055045455581500d040508000500c05175400050040e1060380c1c60307603000000300300d030b50112482190155141802c589031071400e140c54085e01802d282811400040240c40b4074141c02e054a8106070034002c04075070f0000345a805454 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 201689955 1250 201688705 201688733
    0x2210a050714060708040c0821091216060e060c0a060b031014010807080f0615030a060c0e090108340f0b07110105130303050d1104140901090207120804 67
    0x1251140f20188a401904060740600c500c0c411150042c1013501d490a540d00c4812039001c1000a0a00071412242d00b00000d0291026050150603100b640310340074202c51a10b0708010301d1810003081c10a00344800c0c0e41c41480042014400d4481525003e107075030455517103110804000e03200698500d0b10303811541d824041c003a0352031040e083c1484550005407403103480103000c1c031440340070f440b03200070000d0359480118030030b59508003440140026a90381030040d40070b6681850403a070b060007100168400100c0910070343c3c08140b060394a001a14108005200c80080103800001c1c0c40c0d4842403803450102001d41c0240001d0094042c008101e4980c000003030714083d0190041a43c200b007082c804240500140060301140703028480b800150b86510780195850321074240680e0010000ca03070180301003805000182444442c0801c00146911030b0b480c0b0140e1a001504a503000100c00a04081546445d80701680900702141c0b0462400702d140c0e503400c0a04030140309070b42c14490268005400d004d0490b50702c2c00 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 201691205 1250 201689955 201689993
    0xf1602060c070504050901090b0402060307030f0c0804050c09010302060a11030706020301080c10080c03010e1e100602070b040b160f0b070302070201110303240a09140702210a0507 79
    0x28542101c801d00a0700ca04050080c14026440c010028a056805004d07a10080390000388070003107030322981c0078800144d1005040070185612200b11340d12400d01403095030b900200b90b030b035203880a05042c501035041042c44a40d00f031062003490700510160740d4150403254104ca860514626100c4c0b00c007155403c43c050401c016090701c0c8080000074041d00e0100703410311008000c49044881d131414a9013030307400a20646981100000910050200007040c2d140c80e0b4101a00c082012891150711024800e282030440e031507030002406650030403031507404001c020b016018914640f03003000e09014400e200340c065604c088140c18026002e800500482d4915030400360f0304018004124078102d44064044e42c0140b07000c90000b41d41d406104488207010041d640502850200c0c0c1c0320030f9142c7c946041403003102d002c0150f40840c0e204400226909284119400b40451600c86103440c90f04140c068101000d141000d01c45003001c0c410f882d500949442250b10040c1c1c00c0c20a55142d40312402c19039400200ea00d1540c07 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 201692455 1250 201691205 201691207
    0x12050a090b0103060f06050607080d0b0111010c0c0b0a11070f0812010605090f0603070f0804140321011401050d0e03070c080c040f0e070302090603160f09050703110f160206 76
    0x103c20f103d2183c0000320501d1541d9404d00c0280e685500b88082351103074090107890ba403002c6c809120000c0294001c151400c0c8145888001c2108800d40c1e1803c465660048801003080080103c1c20041a154403d500800c1400c00700000f02c003001c90551548036141006006034015040301040201d40000d4828050124040c11b4080d0307198030b006000395002103401072246810088540c1c00e480c0217001c0f20b115900c190b4406043c804031800540347d260010300129500b903404c101c980e00f0540d04101074100c90ba00143c0d03000751a40d0341d000896100406070081080a15092800086a6003003400c541c41460300f01000940c00845820003421801181c000420b14210b030f850001c1c542d40c000035800d02000e8101c0c3d080003005040c84540040300c02403904a040c98101c0341c4100701500d046422181c0c4000e0240641d40030805418841502003003139080003181240e446014001c0600510406a11803061304007082041c04220300d8842c940142d0f0200c04900c01c0001e109048901114003074482c42d64058034113 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 201693705 1250 201692455 201692459
    0x601090311040e0d020d090905070e04020c0705031212060a03030f051c0203040804050f0a060e0f210f1c0207090b010309050a150f0203040b0105040c14031005010f030c12050a090b01 80
    0xa41b10084154144006050f44030041640c4019104d0b050184c0440d86841d808610703c0070901c4041e400440f00544140101100000d05440070302c03d8805080d0400320090395080b200150081c0138401802032030242002500c02d00c002500820140b10030049410100d4903440c1002482100c00c1c62120740ca901a070010041c0301c00c1190f048060020b544040318040007000d0342c20207004401280b88604030000303481c0307103002106051a200c403d89124010f0909101e04082c1411600b20315000c548050003a4045c001c002c2c50b2042c107000610700441400100c0518017403440009580c1c13100d40c020741c05107039558456100c0030303070083c0d00440b0030603484010f0314003000030b5081c00f16914188894581d4030390304084c500c0e507180344140b007168482e650048000320740364200000d0100400d0345011040a11031402003070359000c0c452101035445907494840e480241070070302c0c00051540402c50028014141040c0304045078a4120070b28580591400d40d002580ba43c078105454041d0007600000b800c40c2e2220000 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 201694955 1250 201693705 201693707
    0x9190308180610061b020406240507080304030f0c0b0a06030506010f0f031202030909190b041103040b09100207030503060a0b0408030a12140112060b090601090311040e0d 75
    0x59540715440c0c601040414044003940261284800c035010403030010854000d020042c0a5080009002207200307500c0007140050307010508542c0290019031500b03440d010005918403d100080b0301941d80c918085042180f0ba41d1811054000038000400f4441c00480085900303207c0c04a44400a0700405010420b0a041c4544801003030603000540c0d00d40101c000115200b9040b00c002c500f120411104000313501e2035a165584004a541c520b002140401c11401707035140d541078200703400340a0b007001c42c1c3c030208060b040180407161001034443c0071307508001941030340441400690f0b03400b0740c00c002c0d203a80a940d2150018202010012a01c5096101045e00c805055021003c1e40c8951000c4d620785a009440e440f00410500480c03245203400e5104100382c4140302c0c820304040c4541c00107800c0201b035480440b05540060740c2c00740c102e014070325040500704082c00f015000d400e44150f01550380c0034842c03c003400020300031a0b060102600885003801514041d0711154801c0b5400703040700e01554158442014 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 201696205 1250 201694955 201694967
    0xc070b0a1406090108031c020909070906090503190b0402010e031002040e0c0403020d080c01060b07140c010804050606060a1205090a0309082b0203070f0b010f1d0f091903 75
    0x1a22020940354000041c800d0304007500c05134180d5184078004c42c1860a000ca080c0000b4000c1c0c940031000a4084c8610384017031b20741850142c003980301a00d5070a803c60400c50700070000303440c940c8100d110b5486100d4047d960b248407076118074515040300c924080c5544170300050740c041c08035107041d903014401d604200a00540650140c01a10440c01d00c021590716041c072134a031030307010b00d003c003039400003030308180000061044c2d0050243e405c1180020800540d260900015604640c40c280c4075001704a8000003a20400d114400700600e0034284890581482d840302996820002e1909028010000ea00a13206000b0b05040c0c164428114060206280c40d0051903140c20404034118041108203002095048012542300519803074400802603440440000d80480300700c10f00c035001036000800400b004a0081c071401f141660058334620981d500d040c03840904140540c0c000040030310841502090304095502c100d4005586038222211511490b80c00c1d07040850041512105105c44000401010780000f = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 201697455 1250 201696205 201696221
    0x30c0a090f0f1e0b0a030f0b011a0c100f0b060408030a030e0a0503090f0607081812010c0e0d0212030310030b10270e0d0c020f150f030c070b0a 63
    0x4010310051030350a00320700507100c100714044035880c84030f150303180c500b16154030416554100800115110740c0c2c0e034a640b42c1e43e5a4130740054849000fa100148140c1129454003d01744c41c7c40340d0f89500d030040240182d80c0790080740508480c0c0d03945403001c58003c111250000340d40f00c84005c001981c1c2e19603c046160741c030b07071204803c0c002090900407110f108003030201348040381e683c210014500d0f007074141c1c04003c10034450305441070340210288002c4010407003500142454994400d449442d00e540d0000f0084000158581c2802c180e04081320b08400d60b0f80a030309000280300c2a10680c40420713151001800c0c83c188102c0c519510704c0b000c820419143c8681481d40100d034080c1000040a480301c54050b8402d001500900d14200226509501075601000c0c0614550b050183d00003204080400e106003000161a9070000046500e200f280962a1000c032010325801c08655040001c003410310b140c0c400d4000d08100120080c804400115100d46070300c00c1300e2140394402c44080c0503142460301c03640200b07140 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 201698705 1250 201697455 201697481
    0x5010b311b11010c0f0c0f03020304090c110111040b0a0e0d0602160c0605040509040b0601020f240f0103050613080717030f06240f04050a030b0108060703020a0914030c0a09 76
    0x550102c1c1041c5c02002911158981c550792021113004685030750741aa2000c0301c1c01c0702140b200f0040060407600c588581c0441468680d20720b12231004850ba400c1c217458210114401c0340034204820491090b44104840c3c05080d00d0500c01c000400c0040040c48180380484050f0607240001103400c441809405460080c9204045401d0105e0b103a140807181401a130089640000b01c000c003140c0441c01c040042948004148102e65000303050000072814150050048151181e01928446550b1000d21115500000c00e0001041e65072540d2100381d50744002500700c80c1d080b0038082e804018018600700b01c500c425007114056101c0804244203050750780c01200c00000d1892072801003245890b004602c2600d5402c035041200c45400c00d05008991a40480d6810520f690200070000e5652240c2240ca4020350055280026941c9428100c0c6c0c1020001840c14003014410010f2141150300005d81400751404a0324843d00065031030080b81c5019003240c10035038410041500001c4983c0c0c90f81180580040d1 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 201699955 1250 201698705 201698711
    0x5060307051b190308040204021c0605010e010318030c05031303030e040b180703020913060906031a160c03121d0f03070b041719020a05010b311b1101 66
    0x640303021540f51000d0070b04007419450700100f50400f00388114446508103000800042c9009500b0103625001d909840c540000143c45c0d0401300a50b6030490521529481c0c282000e1203010502140c81e0541210414000c041c080c00c0c070303a403005001080060300c1403401038102d08103e01b0313200e041c040c182c60450f1000a10039414024407082c14100303046002c000070880c144950b81c6072140503050380030703410855070160080c6001452000d960840d02031703140101000200094000d080d41401c3c0d00c0940c00002040071210706a060200780103854806005800cad46181c01d082c40ca0480c034040700c070404074480c2c4407451070034659641110030789030160082044040c01180d002c0080304407602e03200c2c050420040c04041c0504d001402003174601c60540408800e40800700e2030040710690804500f051001080c0040c0d000c846000304000c3d0902c80d01201c207104949608281c006840c0081c0d6010030b11152020030411241040e01c0c0085580013021400d031103280c0c1c60f24004000000030026212642c03081000d40c2 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 201701205 1250 201699955 201699997
    0x10c1b0b0a121802030303180f011812030e06190209120f0f070605040504020d020d05010b03190207020f060c070306050c0706051b0f0a02120f04150e0105030a0b03070506030705 78
    0x14803421080f50310340c0c003a024600319035136801c0785010001c0111200c2c1c1c20340a59400350100610038030441c030000202442c0c820002000b07060401044c440706003480103051402c7c19100b0082e030001900303540921401421405411007243c40000f90003103011031500300c41c0b0340116014400d00800e07030b007013003820160842e2003d030a41026940d07640614440d000102328100414400303414540c00820f05204000000340c41c0c5810b803d8000100d540076444002d4020001c0244007008c1c0b82c000040c1440d500c840800d6042ca9000c6e0001000701489203491403043e0341c005411094600d00b40072540055070811003c008900e03000e10003c016500c4500d0840d6510f2801001541500461070800840020f030000d090400b0018840078081c1d070f12420114043d0f1141a40711400080c44000400d003215401c1d84081c0c4070380c500880b9116805c5050171030320500100c0f100718082c4e41d1b401416a548140240e10114100c2c603000d0129082100580240b81c1010000042100c1240c03c800244480c980c03155101002030 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 201702455 1250 201701205 201701231
    0x9050609040c0618050d0302010e0f1c0302031306090501020d0f020723122d0717032701020a0e010801140d2d050c010905010c1b0b0a12 60
    0x140c03044074001c0101c1a010002d00a1921407008198400030501544410913250800903105014030441100181c3d11498003a150400900a81083c008803000400a080001d90400c0680420400340c0c01007550100001e420401407a280005440d040300042100744034a0401c103010394401500e40040c5130508082624140740c62084a0301c141c3c02c0494a0922164074800c0345410b200b41030071022a11072803030b001079190140d40041000d4207051001c0790104003c2c284070030741603d039000b06403001d00d0280920701c041480c201c1c012080341d44050314180d6903620038242c543c00c07005454440611440c00300c61845c01240543c0288005513994849100300340550004403003001c024002e00c0c0b540082c040a200060a00c191780401c1c052107854250200ca044400740d40d1010070103041000700a13104c01901092000c00e20000e6540307607080ca401c446060509001038011000d0280007404c43e15030301104460004031a6a1801030000e448a956981402200c02001c0003240307201110080d2512003219520 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 201703705 1250 201702455 201702469
    0xa05010605071a0901020c030c010902030d08160809210d0510150c0309030b04030c03080c0f04120203030c030f04090605040504030f050c011e06080606060412080309010b090c04090506 81
    0x10769008000710a440c03610202500540800b51a1104d559001e20020140f658140044c1092011001c000520315003d401010324006286682c0c900b400741031001e1001c1d00d0001d260341c1140c20500d091030010340e00d50070652460700028004084410b1180305c0000d425000b10002020100007042003030100b6200d0340c10020007803110b03129803c4601d4a03ea04512942d014401150b5070600074142000741543d43e0f00ca100c161602141c00310000340e200401502015004901e091b0840a810b14050130101d80301100ca280d48110b0244186c880400e1503036074210365080080310303103c404180640f0f0312481005d04034032541e0810f0064864460800344003007502d007007900c640d51007281c0640c2e0364a45805c00d20b0050300e0aa014070808480ca54860040132010645440302180804030954005a0546040b0700d003401d040002d00201e101c0c0f0310802003000b0741a0708102c3c3c8441c50790044022a40c0380c9a9042d22401006101d01c01600714100908021030b0717a03442d4000e00126072002200340a03943c3c41c8001c001302 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 201704955 1250 201703705 201703717
    0x1f0203131e050108150409111903020108012105031204050d020d0206010b09040207120e04140c0306060307020f0115060e010c030c060b0a0306020d06060f020a0305040303032c01050a05010605 84
    0x1a068503004100019031003601c0c1c1d01d42019446070341c689031105010208040d41c00071001500e5023040c0308012052814030030500d0750000008945006034a0955000821100c0c0c18031603980340710900211400c804103c950faa480d103603800f2081742e030703106140c0d241c0a07c20041207030181c5481c06107091414400e80040384291030b4005a5010300308136070030694109180c1d040a40d607590450b81c284651800207103c4c0c68400c1d40300560351900c9201e02103203802c100554001b00c070000031070481e120034018015806415690800c90860b10750303403280c0d00d462040380f03440c11030701e40c24503503600741120300107078607200003c40c010707034404d5542c64202080c0348006495550000500034000fa215000040c08150203911032548080004c08907040c440d525110070041c3c3c4c00c250b180d0b190b21980c80754100b0001f42c10940b0191014042e0000e0300e446842510084c20901492102400381a00d07114202403c00210707a0301d2410700c10900c113007aa0070001030010b50007032000702e4903802a6403504002046c035901030402d4400b = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 201706205 1250 201704955 201704999
    0x405072310031103280c0512060103091704091b0816051603050d051026071802030910020f1e07080c0a0b1506030103020f1f020313 58
    0x801000005021010345420715407420141e4400d10380720400c2000c4011401203418105100d036200c01581185a140e10030000500d03018170b450880c131007050b008001e4401c0e00c520720900501580c0d078880107030060240200001c14440240c0c01038409922000080e00548010100c00c01c40480b002c400901501c244030582c00c0030440726000502001c48a21114080c030300030b0308e8a1801e000100300e081d0070000150030210081800440c241d402d280d028490039601c41080815441034520b40700070402001c43c0c40314480b041788910803640f00224020080e103002400001002c1c00600c0342d0440c888002d402c01d641111032401110300202c501120790080d119a880c060000f1031600c0105140d800e1080204024078981180c188500b8000c9104039000c0d0034400a98000f411101e0103034584203002580c000c01102c016140111520384e1034542c1c0d4166030540e94180e844c0005c0c210070b100041d40031401042070032a100301d0b40700d805810550100c09007002c0001291000078051b12801d11030b00820000010708 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 201707455 1250 201706205 201706259
    0x103051b070c15030f1808031f180207050d08010e0106120e01051f09020406140a05070506040302070501020d0c050307110a080102040e040b0606071709060f04030506040507 76
    0x3014030400c080040c00c04a00c10640003105035600c54050750420283e0143d100801e5803440e16691940103406111010b4100000701d0348500d2250342c84130210b00029003d0018180911072400d050071804a080d07011b07161003003107581328200c00b441c8500a5804400211824003603c140010751500804505050b100f10501d070100070380c2066400c4a1001ca800b07100890540c031540a40488030080c400c1c0c1340501071122145203904900001505103880c00d501290b1000c0c0304102c10000154800c80800040b8010300b8103a139201503010341214140540c15010304940104018001015000036600d170440307800b0303000d8030311140007600306407210013440c00302038110782080090700006238030345921040c4c101005201010564a4440701422600642c002c520b00f01c0b130305400d01043c00032900141c0e91015003144c860b0b14014255954403523081100c00c4810043c080802d05400710b44e154000d40e490412002d0082e030300d4903900d0401c3e0713585e24001d07a0290707401c4c017500360007007101d03110b540c140c000e0030034070031054 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 201708705 1250 201707455 201707491
    0x510030501060906240c03030c020a02120307050111040602060604020702040605130b040c0c020618120a08130e1905060f220b010e010816050702041a0109080c10080a021308070303030b010305 84
    0x81d4050b02d89d9004c441d086004010300f1000680e900200c100302c80003480e00968031602a80342450031607419440340c0054045c00e01080004e15400a4541e5100c0d034259405030b10740069101140142040b6003240d44d01c103160501c200c48024895021000405003140c0601000d1008903042d40d01c0e00b80f5200c060340140080090700300c05d603034122104121940150000030001908501c2d241004070300c80049644500002e019003048064500c8840504004c1b076039408035052540200010501c103042d4400c220741c0303540020741d20303584440d4403c041c10001b92925a072a240d40200190400148140da0006071a2000341da4881d4420901c0407140c40c0d0613160140d00e03440b40b940840665030710349828802c001080001c407006031110701428091426019a0007801100030002601060300c0390001d900c0d6a210707503d4002d8669469881c0d11409800781000740d03040c2c96180102c000ba1150300098800d12801e040300241ca500001061400c60340a0766082000c0811000118113072082642c445400b180c1949103 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 201709955 1250 201708705 201708707
    0x150302040b0303162307050108011205010b060a02010b01090906030309030b090304080d03050601030b12060109020a0c0f03020708060f01050f13140a0506030f0f100510030501060906240c03 83
    0x82200c1c080c9004003180e0805203008450b0b54a500142000c81d1242103070744170800690a0003a8003145c3c001c4507009070940a00740800201034100c148103e1406081404509050000a45c000c000b082030180045550f42c0c1003441c043d0107080030a03038050010b40d9400c070000740c3d289244a1813080d644c0c959a41c10204d440c68644c9400e03844041d0510003103010801000404070303001c01c03080300040d0b44e94a01048520b0540f0002d8201c8805811071030007111102c11028003641c0c08a0214155207145800685600700207204450441145400412454020403150b081c1600001c0e078400b03d0384080c044034080e0342d80d407903801c520000a10039141c00505160541d800c51034599405403210424040000b2818210485002c3c0740d80f05444845004e41c1c0c410920210f030030306100d07c00300500307070304000c0c1444040352001d0360782c4191006240046903070f00ea02080c003004a50280600550b0040e00a00c29981c94200e1000280b01c07a114051505003030010300b001c3c42e41aa540f0003100b211790f0310b400700ca06d0707001c1d10 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 201711205 1250 201709955 201709961
    0x92301050a02031606051b03040f02100c0503030903040312090b07120e130509010e0118020913050d050a02281203110a020606040c02060f01031407030b0a05070f0315030204 76
    0x824802d50109002861600c5661401040b40502030400850a401c10310051304250355501c10084004074100b04010100e03820301c9940104540c10b1351078004032095014101c0709840380020040c201d002c00018000c00c0d440010140007503d0190b01842485070142f24159801000c44c03155400303500041c00080045200034a1034690450907041001d01d911000700051110036000b102122400d0b9110180221b010b024410141ca01d00b01c40b008000c0307511102c60702c1d070b05003d14400003842102940c00003402d54117407148800c0c495510030104c613031000349542d000d40030340c000704001c00051040e13a4a03c2038548034080795011401501c088010640419180c800d007417400340c44c100040c95125510003400307050324001804514010360152a086c10b04600700010b46210442110440d4010b5041c026400002e400080c1140d41c04282c00e1030784d065200c01d00c0d040803000d42c00908442d20000411156205075001a44120500c2c0e0f40e400c451114610250100e0301d05480814140d00d5000c0b0500040c1041e80c = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 201712455 1250 201711205 201711217
    0x1201050d1502030c13031202060604180b0603010b0d0f1a04020a0314160f0519050603060d060e030a17060102011512060902060307050a090b0c0c060a030e0d020d09230105 75
    0x15003010b29217070110a00d8a01c0c0d9840382e00c00c41d03d0340348031009008034a6060141580044d0102c4080c8480010204815041c404c40d2401a00c40c809074804604d01c0c1d90254041141c40001030076070327800c0000604296036504912101920380481b4860504440039000c2c020b180300b84d80c000c0860024074115243c00c4804511800c2c41041031158603549000508209011002080c241e00c942c15014105010702640041c081d1040001d01e69417501403156984410542c6d9000707030140c131f0011401c0c1075810003002600d550942c1b9002c5002c00540c559416a00c0805130800841d0006108070645a00004900300d40421102c1c0d09040c4400c0000c1c0f0000415141031512a4010703400403901d8103440d0005003217580244c5148011807030018180025582080030b120062644550380d40c10321000f41c0c0a00d0f12000030750035a5101e0300000603882040c9009500030a104400e2502f1a1024000ea96020303644080e100309202c0420300c403c4000800e61181c2c00b5400801c1c090340c034a180c0f03e5050000641d0360350044 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 201713705 1250 201712455 201712471
    0x412260309030304060f0b19140102030304023a0803040308090a0224070203060f0f012301140c0109030f121503170c10021c0204030201020d18050a0b1201050d150203 73
    0x70800187c482e9102c1d0340301c02603103405a08005a141c13034150030b0b5074590303d140c9202d410b64005108200c00b50f518022030f881c03420303034481582d6018411a514541c80580c8000301c4110001d48000050500628001852103130b4440e1f2180341c0c507a103841d9451582e81c8080720000390300c007000b40104100d00751180c10240c081aa0880c145040041300c0c1d00080c1060003ca42d00040c014001040220240322000d02c240100000710461100d1818005802e00048110009506008111841d007484030404411a6540034015000b08414801031500910715030700c65110368001b0364035201e0541c8a00c985d02c20b2502c41110036118050503032641e62852501c002011440244440510691180c0101400701c4074240c883c0d00c00040c0e80340c09140b5100071034036031900c000400070300c1400184010307600041d100900107054140844031b00034140c2c02c104400c4854200b5600240c40b503500042c4120310b60081d0179080d0368562000329907070303d072001d000b40304554000190000d00d900c0403040b0640003590045801c6061 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 201714955 1250 201713705 201713711
    0x1060c02030d03050c19050405041a0306130f17070c14280302011b120f1116090f060b0f090a09020f071e0209150907031103070e0301020412260309030304060f 70
    0x180c0c2c9d0000b0b04540000c914a500504420040c02c1c19203003e0250a80c00040c040451100501d180c640405c403035400100141b00034801881110624070902c00c1d2403a15520400c04412251940d41080001ca4003201a5016201864040025103a84620101030180ca82024a5850318503001110f840c5a0071004010750341c9140e036010b000c01d01d118004801381c2c20075103403403240e060031a030f0082c0905021071506410745c10180200f00c000756007403800000c5608080000c42c0b0450310417242c400804543e0b100f41c4052030006030341d01b2001207a0001e40a84030701283c03071343e000325500d080302c8080e03100e105022403500e44104140b4001801c8413a40e03035040c0070190311401d15286240c3c04101400300541d4203881d1800c82d024a0f65041c03074040d4916600c400c0c10303e018401c1d2034400c0c442c854035010240484081c0200207034801030a4800750305440040030f11070161411110142003140e8130f1006407206094010207a00b0304030b90a210345044a000b0381c0040c0c011840c540e50340d1581c400500600c1040e4503400e032 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 201716205 1250 201714955 201714959
    0x109021309080715020306100201020a081b0d090c18090506070807050c070308070b0601030e0c10111006060906090b03010506030a090b090606011107030201051c110301060c02030d03050c190504 85
    0x46402c0260b50035013503010050340c9003003000801200d0094a0108011a0b004000440d1019482032030907070406c00301d48113250f045423951494a0710b4014209052803451070007420700244802082e01004503a50460200c4075000840308280c20b0f540240d501a10a51100000c69035072440303100c4e2203a1040c080e10b00b6138101403095074050b00307001d401e070b00580b06440c0100305032007800000700f5060740001007401d080010001c1d00080303944038210010400d20404c02d0140d0382d05040c0c000d0791342242d84209101580d03061320f11a03958200510282c001d100000d09028408104640075203100e105842180203000d0440e842c0030100075140d800180800400d5469080440000b0f280d442c903a402403107000d0262615150001c0014012032054806070f4541d8800001040541d030020211500401054a149202401d0050f140043d00011030ba002c0100350000c0000780c0f06070b002d03280038103452003142902d20b03684002e18204d05840e800c0c4c59100814004200f03801409030f40300940f407100c5051b42860350600d5 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 201717455 1250 201716205 201716213
    0xb0307021c030603020108010902030402091506090d060905060a09170703030b100210051f1208120708180616030e01111303061d03030628230301090213090807 70
    0x1d868800c408000c00d0b1107240030b004560b000b003046030261840e203004600310b20f45500041c4010310041c010444015071000f502507583c41d4407048902e56640680b500d500100e062031b1a8006256030316003035030349004981c0442c1d50340c00203026a83d441a00000075421000b0340b0300e1806069400f025045041c1075458868200342e48848061049000e881c2c3c014080c41c0f10408010f20550700000c0426000e145098000d00310340c01030b41800c000390758030708200c14080c00051509000e64841d44590b105103500b1035082203006d43d800100c4e1481440600034034031200c03c010400355510390381070326a189904c08822044003080d105c1d03441000d08020050010404492400c284c2ea066405005030340d0401d140c00c9000d105202650103000c003103a401d040760409403421500007036240c7c04080c1c15240704401044000e034946402d554580c060064840c5082000c0c0d564442c00e0b1004161142c110f502510400300300007292034117100705134400d5009044007104584911411008050328202140c0e88601403065002103 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 201718705 1250 201717455 201717493
    0xc040b0303120c0c0a06050a150503190f08040e1819030f050d0e030d140c07030c020d0501050702011505040b01020709051e0903090901050303030c09090604020702040f0b1f090b030702 81
    0x546c040d150002d2a410000c0c0c12100761000d11410700b80e00400707290100901d8070b0020f525009888040c0a800d44604a03140240388248103080241001102240100d142c519450411b4020000d948000e810000407255283d118901d03540c511940d81c2c04040d104001c40e004500b88200e0f070310103161003840c0c451108075090488150001c100c01c42d1303001042501c550f40e10b900c9444851041314070440c0c40b6107020f51790301500d0b00c6441c40c02010424014010011511303980d55081d041039228009010524101d58024000e1003c1c030750314404821400000100c0c0d08191061040785d81c03069000e084041d061902e42009810080c02141c03955103c02082c0c000102c1484140780a030080351b001d5903076149118104101d503141a00190b20a800030428405c9502c825411204400c10550720044945d0725140000c0090051046c0a5000b130b04029030880700781225401000740c1081118083c0004060340c51031170446146015030f01c00710b0013140082c000d1450940195030701c418244100c401c010340d034540031045 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 201719955 1250 201718705 201718723
    0x90103050d1d09240d0b01090b15070308100902040806042d081201080f0304170106151806030e0a0305031b04062307030e06070f020909030c0c040b0303120c0c 70
    0x10004c0303400c1e07400c401e0140741d2482088020084508281c045485d071030b29144c1c0c41041c410100360f6555180000040d40b501030384200c03504642032049480d414603040290559500301c84920441800030300c0490500268426035040e50490401800c50b56030302e030303103030a2289202452a001c00c444a502c0101000700124542c440c5485146d00540750b9181d121600c9803540d068128603000d13001505041d0494030f00000791000c5034041001d1203100e092034410140103010941000b00510b2840145003059500071001d6918500780c0d11054270745c10ba0300c00049045921903242a4001c0d08a200400c01083c803900266420189200c4111480c02c0300e0a5403d03804e41c0f16038030420104299040074004100300041e4580030501e00a841c07490300000742e5004241c0310ba012a10351007154041803280c14804044a504203142c0d014081028a04021105c0343c0d69810800c01e000591061205404090406010306c5001e401c2c06801542030800144c24a400d43c04000e000c1010a203007400305500204042028250f = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 201721205 1250 201719955 201719971
    0xf020d0803100306112d0c150103120f02060105040207020609041a010215060d030503070302090306040510061e0b0a12050403030b0a080a0b012904080303060a05090103050d1d09 78
    0x101142c83c0d4940101500c403070a44070144e1690510141404020031075403a0036002d02108280490302d81d900103418580034003039184001c1d1180c4c11100c00390036040c00019041ea80540440c1012114519085900c40c90015421005070131070001004503091980140c4025840140300d07500b4004081c0104085541c803032194500380c00b014a0980315540c0500c15514900220084080c075403401ca40450b207400d05490005082000000000f25018400d6050366030100009054460031f003400e06007140da0320040c15503c3c0c13900d40b5000c400196a110403400841c0d04060306030110300c071450f01d14040040d07080006444107010007410040fa100e4400c0c1328552089200781c400259245024051042e420b0b07984c3c00c890f08550011a1100205001008090446021030440800301580020b038103040030002ca4000c10050001c18041600040800658841d82080e12440c818030350740c1c2c0802034681428803014005030001d880e525506849030268040d9003103e094020030307c5000d4004924001001c41c2c10007 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 201722455 1250 201721205 201721231
    0x3140c0a03060b03040309050f130e0607140405090c07060608030f030901140402011d0102160305070306050c0405060403080d02040315020d050906060f040b0a030203010510090c0504030c030f020d0803 88
    0xa0303401034140c40b0700c1c80502100c020b0703d419032074155000342900e4014082d56100d4280720b00440010f030348000c2c284803c90801a81406a64208a207040d0f4590090b5050320114042e400402481490101940d0485000606070f03040e0b5192401c0ca00c00b1540030a00c15141c207a280d003004070b040142080100031111424489595900d0b02115850071074078140a1000e103407070124180310250ba80860240e10900d403021160001000890050746008440c89012031210b03002e006c008203000003c03c0f200c00702d9000b05d03c280055610301c00c0d450301034450743c09030307580c8142c0c20700003071000c118046c0c0604007504034000014502526501c5d40900405880301085005400051101001d0500e009064010074030500a02550420400050341408030740c00da07034011381d514100009070344d45444400d0000c68014000300114109018048440344140c02400e4441c1c1c10298401c010b2031085007210108c4e500204035207000c40c219620703020b007040b0041341a03900c08002c080b13000215003000d000314002c02d4490150 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 201723705 1250 201722455 201722467
    0xa02190206010f080a0b010b18030706030209030615060f071109010b0d0b040b010e060d0908030c070201090e0c0f0306030f0d03051e0402030a1103160312121a0f0103140c 75
    0xe003c880843c0d009021250441c1000100064500d41d59606682c41e0310b10454a6424107000c000182d02001c40d0103506120b64100001d00e41e41507402031024601c1030702992650f655452140254039040c44495401201c03c000c0d0b0060400100068019944604100080c11000000040c1c03188800c0e000311001c62400182c3c00701020180c401c0c5110154242e5041c8040340300080040d102c10700c09404103000d0703980082d41e43c170341481d1513102c1050141c0c0140b03010b03100d040c66200c070602074020104c01c81c0811238005022403644150b000c403900c264078081c042440d2103e040c00c0382c1003542010304040d030907219400e00c2c80101d940a01c00c001031554260303000982454003610410181e980c0010109c455428101848050b85000c600d00480d60b4002002080c13500050340424071380500d04240e002401d41c566800300822407440440403804509607a48031408140d03000c203004070b503540c9190034401d1348281c291004d5070506c0404610300c0c1005050004401d0802c00300075103641c0c4101d80e0b0394510500003402e = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 201724955 1250 201723705 201723719
    0x6040b011503050f07051b061305010c090b0d0c14030a09030206010b0901410306240a1d0d03020102040f08070602070902030a09020a080d030f021603080a0219020601 73
    0x31103003820075103024801410710703a555130780740d11015103813100700240050032006849016016030301907007105d0102c4011f1300d0704da01c0c10700c402507000c0412500d0b5420504a4007109208580340310955880c11181e0b45031641940c01e450080c09003200d10001d1052440524240b01030000c05588641c1e000e56021403610403c0c1390090030302030160406c4080704014049030746142d80c04442148094511240b245155166807601d8141c071806804050b8074280b0340c001e500141d04128091030080354243c6100400030300d00203000d40440351440c1e1550450b1300c1440445031f04c91291401b02c0d00e00c40c00c500700d4045410084003182120040a00540160b900010100841203034043e000000341740c000040c2500c1c42c1050030080d210100761081c5810b140c0c0210200d2071024440e84040f01141d8001c18029a19544940185e00c41d41041d202c50082841e02e54985280d00c21802110300c0180c5042c0340c03010440d13030317030380d00307640400c0060154005582c5c02e1040760815000440d0842c2d40c03110f07a4008119662410213 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 201726205 1250 201724955 201724979
    0xc040e0f0d02060108030403020919020712030605060406080402040b0406093206010203040e0703060506040f150306080c0105070305090d0f12030207050706050a022e0e030c0705150c06040b01 84
    0x90002150b101200400c0a41404029942540c9c4d040ba050040d0b5294040034003c0d100c0d070305000c88015440002c2c088108080d0140c040201030781c903202031006a40d1381003086046d00440c45928041290712000500610b819440b02c01401710041c000110280c0310516032084030602c11880441034080242c0720140b40f90406c04012400645050304828649040000d407a030280b0b1040004854019000c51019070007a006800a0170f8064a41911155030340221001800f861241c031207180002c501e050f0400e8824059401611180c90090100c03d007840c00444041c1d010503029810400e00b8010003403955a4211854101170054288101c100c1c41810100f2503070703503902241014103104008074400600041703043c074110791b61402c10703540b580301d900026410050072041424030b51207141c60940359005034010300408046c0c040001c0002e8040c1c00c5140f503072841b40328074070341c0c1580c8031a000f0002c1d81781681c261781c0d20f0f4080b030745c1060602e001523040c00d192032020f0710211740c2e19220754014010604089 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 201727455 1250 201726205 201726223
    0x5010c022b031805150702040216080a020102030103060c030c0c08090307050405010b03011d090a030c15020304031d1002120f070c062c0d12091502070305011a09010b0c0c040e0f 78
    0x160750b1740001d1381035074505400c3c2c8a1108002d014036000300d2400800c40d03040c17080e80304180d04902420f030303500100d20ac000d000354024001112914501909001c41a00c80c0c0705603110b2030145e0321103030701c8072010740c81c2c3c4441904110411503141c86006000b0507103172074074081d4500a080408a040d103e50402034a2180780f55038032010704140205008000c0070100c005078166240c0d030035041c0780020f281c090500400c039140312024848218000406e2001305503100046c1300e4080704404005040301445003c009032042e4610862005038008042d005081d410200101704110701d00400500d001416540d0000c1000c2a80c444000328031a52010080d108020b00b40e0401c3c08409800c0d52080c400003000902c814480314406000c0314403e2005110060051000c0c001a1000e6452a0450514903000a40d1200180402ca405501b0400a000c1c1040c0308451041e13480c1004080118580c00c241c40d40f004c94104242e0001d051091150f6250f4540790b070302c14a09a0000a0003414074400011900e5103020070796 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 201728705 1250 201727455 201727459
    0x1905010e03031e0915040f050606010203130608090f0106080a15021204030c141b0102100c0512040501020d0507050405094203010615080c030105010c022b031805 71
    0x10800c01c142d03007410543c080c040724024816900c064540303c1d601440c1841200140f80300900340000d200c240602540183c041c1c03413250b02203a80d140d0710403004907117a0043d400031508564000909115603070040084c145e002180b0400c840220038010211425038016502c5811035030400c820754410300c0b44068107144034100d0f001c07040d480c0150303c401a42820070010409010404420a140d080207884040308045d81400c40440b52487c50a1010145159551034424003500c903a41e00a0440c000500508004103240d44a841c207118507115a51f003081d0300200103c8030740d54200601f44100c800c611509025142d0703a03552036129030500d024800c040d50098084600ea10034015450342c8180c084058040c00c0324940342070114a0309010301c4210208003428080d034994200fa90118600e001410203502c03000340e507525541d071910381d83d0600030644420b005607400a10080601005030800700c4c1140062500391082e8403509604c48100e45403021805400c03000034280e45107030410340410000e000054082 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 201729955 1250 201728705 201728707
    0x1091b180207030e01050702060d05090303160309110907180806060906040b0a032303120a110a08011e23010e040b0303090d020414010902210f0604110c1905010e03 72
    0x381d0703e0203400580d01001450400200003203c80854641d2429500302c212014010f00040c100340c0c01c10794403608121105000d0304241480007100d64400e018104486070004110340412100005000300440010541400d0200304501c13440d00310040102d030302c018104c110161049083c08010090840000380c01a0310490608d604040507664101e03203503044943c8080c1a0a441c5184001c00c441c683d8603007031501640c04042102088480e011000920820b00320300100009484150a81014011640c0303040005506500500c80b1400c2c01e10130202c02121b40d500d40b441590744030845c0000505aa12000c04400b00036610040d035604203915140503081110180000700c01c44010079504d000d40034180380300e04080c6030308000b0341d11076070700006251081000c01034096840c0c814a0001e54003039000c0c00e041c100384284c640e1883c2c40341003441b07014481200803666191920000c00001c0c202c090524401410204000200644c2c1040380e40410400030381c84200035503050400d40e08450303c3d07105000c1c6c5500 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 201731205 1250 201729955 201729967
    0x3030610110d0e010e0604090e1005011203050f0f04031a060402031b0f070b10031406010605120402041401080a14031813020408010501061e02070b0904020c01091b1802 74
    0x100402d070405901840e107440352001041d0ba00407210b2219042c4402d4115070009030119a656a640081904140c41000c840d101680407082e50101d50092044040c403030304211013840041d2250b0018815164500304850900c404101c50709820303409135008a403042c00c02d00f0015102c0544201071070b44410212011821481c1c03958005c8080340100d031050580140008030f000800d007440d010f84002580201c0504140d1824121071044001d05001c04d803100b5240840d11500380c10005249070580e11540c1d2101d091402c841e99140345408085d10890703200351181c80503040010164000e6008045480040c1282112820b00c02191000b280e030714036550308200800b400c0512041050329a03804c059826803511184d0125484c024060343c3c01150480d4202400040e03440c0d4044a1100400c3c1000d00e84803221000c00c0707003643c0c1c802a6214078502500c0038403103040e403441c10b54080d0403074140030f2001080010722a03840c1ca01c1c0943e1003a03070070b003072806644090020360143d21907640402c409010440c41c0c14 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 201732455 1250 201731205 201731237
    0x1510050a030b0a150809070902131202010509120304060e030307050a020918031c060503010203060d111903050a03030c020f07051918091b0506040311040e060903030610 74
    0x100c60010800d040c140c884004100e1519060302250040240005407050407a05020090007014159104000b5100782c1d04d010500c2c100700c2c82200d07694401c0314210b400c018505080040402d2140c0420780c1030100503c103c4140751607075000f01c6500b030342082c0659603581c00e180016000c0e6140c0f02d6118040c0c1d100340305800000c0e80015506402c2d6404440001e40d0341d9803000f003000c01c50728400400b001d9000100300300c44550811008681c440e54001018849103450340181070803400304071066584030000c00702e6040440e20700942407584a90280c00c4001503d064030b01186194402e5204644542c40359100350305242c1d051140100c0c2521510140c1410550300c911170b903490300c15004040c4240f201540704048480800301d040b0050135555041c0b0010381c1140c15881c01080c01c8182a2141c04140341110144c040c212030683c180c5400030241400c090941d200c41040a03140d10b0002d070090b90700c420070380107041d00f0010648500c000000440d524070348017045c40800201a00008184011201007402c85 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 201733705 1250 201732455 201732457
    0x4350703030f031424100314010501260a0609020708030f010806040317071e020a030206090c01020307060911030712050c06030601050d02130312110f030712081e0f151005 75
    0xc41101c48841c0039103291024940c038440350329442e6aa025414884101c0b1b0290550001d80605485030124005d45c0c0c2d0340d10042d0b840d071026034070246807100740030704030500b488400740d50542000011000086240e12000404101da10180e000c1d03440d41c00102c1080314450383c09001c1c50241c00380801070442410540ea000d0540002010500100c400c4540094038240c440c11905007002513107100341b01d4103610a03101079120700d038101086d8014020350002415a04c00000d2240c000c04042c0c1c01545040210344440f80100000c3c02c0403182004024a554000c1d60200002c0380980300354940e40c0500110780c035007940741891b01203d5902950050041007210b80e084000e9411482c009400560346245005000164078483e4100810b47c4007005201400554032000030014000c0d0302e400c858140c0310014081c1c1d901d01030054000d0003130350b0100c42d03682c104d4400d001c0140c00c000c000140c500c49410110b61604044030032610f40004510b104101300807918805240c2c0074000043d180c40b030407030101a00085c06 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 201734955 1250 201733705 201733711
    0xf0201080a021c05090606030604031e050d0c020d120606050901030902211605030a0f080f04080a060903030f050f1f0b0d0c09150504350703030f0314 66
    0x1403040000000d00c2110094040302c141c2058000240c02c0d88624080701c4004204c140c3d58080340348505400160a130030002042c5002e1901a00c070340d1608044c003402c2d980700e00c3c0085440380802605000340211541a03005003d80103040da000360848905261004001415081144950b60b040810401100d500001200d1850100380f03030101c0d0490307460010070114100d04402ca071983e00e80d095140420240403c07106a6a020b59a918552980da4070400d0f58a0701c5100020f0060010705400314001808000180071b8192400740103802c05945640d550300305500e245003522155120b2540404159140c41402103c00946104010300e0400184180c05000c0c002c0c01c84100140740c3e03000d00c0d00c80e60365400c0c00c001060217554140d0307500c190502c3c00000e4184d55810b1000302c1e21503480800d4040b80c0c80188000c4800c596104c40c100b40c0340c010b144000d0102103145101c130122829254500e074681110381801a81890010b0a401d442c620b40185030003401100401018600035944000f155262100350b0 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 201736205 1250 201734955 201734957
    0x1e09070b0f0d060806040b150a06050906070c030c06020a060501060815040b03010b0415050a06020c060a120b060406020d08010906051e0301060b03090604050d0c0206070201081e0c180604030f0201 86
    0x20b01e4800848a25004142d40e41058229102c0c0c001008100b00071068003601c220040100f440701c0c503248005000d000501402080e02044090100b0180703030a00e00e01400119011780c0e9417401140d600c5c0c0b0359034451207003a00034200603000504804103000d22401114010071712441c0c40d5015141c0180300444496402e904144119210100148155801d40140441c240c00900401071800c00c400003140d10304142c07283c03070301514043c4800170707810340003284860f50400041c0105141c080c0740c0300115031000c01849046880760f980c0760000c0381500c0d02c20140c0040c0c14141c0040040180041002e880d02d18141d122400702030510f0010b05c00c03030706d4401548019a17071305840030032211110800070340905047c3d00070000f40180481000701544002411601132070264040c1c8004001c0c40d030307007154011403401010350011001c1000c8001544168101580012110484020b0040216040e4401502690002c08800010030594031144800c945041c0c24a0200c8066150620b50341d2441e8080245d90300182c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 201737455 1250 201736205 201736207
    0xa0210120e03031f05120d051e040303030e010f06082109040504030302041503051003150e0109060e011a0901140a0801060308041505090a09180b1e09070b0f 69
    0xc95003003007500030031000004002541e4072442c0480d80c04034240b5540c149420003142c4404005140c1c1070904d28226001c0000010700000d264541040d1815807000d14080c0c0b801e030f005809600346034161030180000c3d6110343e078082142900c000c00603096503140400c0104e168500780702080703d03140000d1010031003060808040034103000c4800e486282e003d010b10840e08141407000700400c040d40f41d401481981c40303c004800000030f08640071022500211602c040302c881082d03084c004510003401806600181080103d0341c400039445550039600180b00440300e20361100c40d80345140e1002c0c05a0380b8000b034080304c40b503c0c01c241d5000080f0b070301d881849500d071040789000c0003954640b01c00d91030f280540310190003800110703560701c1c09a010740d005208401c4a001c01c8200d40f5604c0d84a00c0481c0d49030790006203031000090503c82d411000b84158021540540100150030740015402e800c0c0f40c3c820140d680c648c0c40f215605080c003041c0a01c0091a80c0e110360408801440329030421030a91f18100c00c100c0d411 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 201738705 1250 201737455 201737477
    0x9150507230909040b1e10030305070c050607061a01020a0203060c03090109021f1206061d01031d01050f010605030702060f06061b0616210f02130e07020c030a0210 72
    0x30116074880d560203150071100f8031041000b4001080c46190183da4800305984400e1085020705411981c1030320311900c1c1111000e0100042442440a00700080c05140d203c402c0a41d200c0000301503610209040320100d03140c07556440c0302c240e0b500030a44c50003000e0010701000d001c0341c4e002030707240d460041604580340d00c0800403541c3d194095014801c4643d01030071403030120400030320140e940186140308400240d44418400350031000d6010f84822140c1d503840d205100d80010440d40d8010030001074040c1011b03038a40c104202481301c40c048a040030b124500000c1d144c201909035116104058000b44e0901c182041400320b80d51740010b07102d9215041d64410721150f100d48001030120702c103000d007800070345580080c01001d5403008070f80c6900406a28001c0e00041c10f070400196081c2c1d9045040014450340c5400c0e038100c4450540116030300000410005251450003c5d03400b100c1300c466008448425404801c02c421150100701c6101a180228000d054000351307039001510340c0165030300303940030001c40c1188 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 201739955 1250 201738705 201738767
    0x1205060f0411070c08151e0403030c17010b130e0c0906070501061a04080f070b0301060f0201020706110405010215060d060c12060303020c0102070f0b03070c0f051009150507 76
    0x82c3c803482c0b540968842c90003035503200e105a540400849050f0311040a10206035400c0008900c240c41c0c1c4244c220520072590b4540f8140d0041c2002004081400482100b545111b06581c0300035000e040d12290700764403003508655564510045800c241c0c821034510b07052040c0006a2016203456010031035103941d0340d240d9442c1c12400350803103501810f00b00d00620500544c03a0b401d40701800c203450f46141241d20011100507401d94981003032180c1480c1c4c620420052000c640301300200d10190040c7c0c000589410f00650303500007181d403410b4030259611008503092040f5a81801005200034407103c06921606041002821884030500d008004966401e11110018018030241c034400c42c40507010041941e69040c00313900e81c14106400c1d0b0040c0640a00400e00d03460607083c0c4015a000f2801a50071981c0745002507454511458055407211022005200000e82c2000a4516078001590215101d520340c60890307a00d11008480752044c504080805c038545a2120f4040408003800d4650781020300003030303a = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 201741205 1250 201739955 201739957
    0x6120608060127050c07140d0e040f111201030302060609070f030c090b0c150c1c0b010203070f0c0e011202090f190906090215030105091302041d010c1205060f0411 72
    0xc83c000f61508200c10815203404500291075400e00820540c210a034450840e1500e40b0111f10701d440201d10391100b039000c103051540c00000a0003c084002401c2410300c3c0103440c2c0303074020105500c0f10940802c018020550305010071074004505a03080c41d12070030900f0019101c40b548042e05010156185105580280b24030a54001840c610b00c440c0d03518001e84070516241d815800300c000c10013003e0008140e0f19038202040302d4190403e039050b020b005e1001d80010000d4a48030030018110b100034082400455101c41e0400314843c815400303090120f1501c4840d50085105070b0001c0f24243c070949034500903840301411143c0c09481c4004104d4140d4a40c0ca510110141000c20100c0d510710304528101000201d9000420950080310300030035100e0310601c4a00144024010250001d5030135000c0b840c0601c48001c0445000e02c02080031607000c103000b00c5111000c1c0d151080b542681c1d1680c0064020581154020a81c1480400140441c2c03a01c000410001e1100b691107600840d550407484a407001034030 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 201742455 1250 201741205 201741269
    0x12020d02090640090203090a0b072d05040306020306121b091003021c08070803100e0603062e05030106090203010f12050d030b030c0d0804061206080601 67
    0x1080705440f50b1880181050302010f01031000503141c07006060069510380d0303081c504010500c54400703440042c01c1c10301e442e0181d0000360103482d0134461680c011000940381c1c90800c0c444d000c00d55440c0000203450392101001701840b44910108460300c801861481c0d03100c000c880c01d03607803c608090b03900e403600c0340465056203101c06001114050042c00b44202140f140d010344800c201295502403a4a6075581c1d50340c9464903100095000094114040ca0680c200d00341c0005c1d14052302c1e80d01d0400e00c1540700c80d4425482159aa2006100e0403824450500e060f4260741d00701d1820b80042c401c92400e583d1402e10201c60405640c0308524040e0044204643d00b10400301518026009020301555400d80724042d40080c02081041030f030500d404030303207880004110b1a601d030b040001030800039001c0c02c0035001021039030f11581d010b000d003059010240e26034200d0303180e206120f100ca443e91103140080c01803090021603481c5e0685820024104034034000080e0707880c1922255888144643d2240311407074003440000b = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 201743705 1250 201742455 201742459
    0x20901350303060405131505100803130e0c0708040806060411090d0b1815010e071103030703021806120106020c0103090309031103030714100b15070605090c030304140f010e0112020d0209 82
    0x44084002e0416280c0015004901da100b075032701d80e1a21045041d40701c0c0140c0013051280141290b0400c03043d40310a0700c564002c4d9100301001e2503e10310380c07503000096020750060750259114070709005040c00c0030301c200040c0384030000450703040000302000980e40001c50080501411010f001080c809101c404400c4c8452074080111400344240342422030040d0400d01c20ba50b118410240000c00a82c064104044e007100c15202841c5150b5500d2401c0d4000d41106000d000044645040c0203299290341c00200704241c18000c10801c1585801802440c01d82c1e1084000d04040c00c7c59a07131400a5040710b0f02c181a41d6001c002142070000240110b0301e10700400c40058005081882001160300020a00220041c0500c6080c000c0410384014012000c03d2a0888404090200880307008510141d120a0b0408518010389102034003100000380340d900250071003540880258812002e0b4501700104003105402807d102c440888180000303020400c02209510301c0c0c940010f0000c410340c5041c0d049407849400 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 201744955 1250 201743705 201743723
    0x803071b052506050d15180e011109090408030c1b010b03010624080a090602130816180507030608060c21070504060804110901060e030d08091e0a02090135030306040513 74
    0x3251f4980300035010300c0c4c0041c461541380c4586161602c0402007160052000070340a058940c54075543c1c000e1070361006014040d1003400f8030005071302891080850b03442c0510380d400814000c590408260031a4106c1e806020b80382c42006000070b000300c03103880e0710b4812015814125520707580d0200d20005060703000c0004000510004403a2000c000d038500d0032050b1846401112100f00e4081d4400c114902ea5000b08070302581c600062400743d4410b900b000e580800c051401140e4070b81c0c0c4403982480c100003520349802c6428041074402d9014403041c00e05810100442c0380201d9420304500142440c4181d0040c40108007818000406101455900c3c0d02c40e420b02070003410f491742c0c2d603400c0108030aa88142c40c0e4030a01030406071421651040340d800d402201440e000c0c020107145030140c907100401025000103a0f0190700020300245e614104010f009003950308200d038801f084482004442482d007180300c50101c04107005400408800425641c2c0500c2c1901d000075a0703107410402100c81ea1152000500c2001 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 201746205 1250 201744955 201744989
    0xf0b13120f1407080715050c031501021f0b1e0906190b030709030314031506030604061e09061512020304020402070501180b01050f09040803071b052506050d15 70
    0x240303800082103403501170006c01480001e0f11041c40c0c1924025500d03942040c605001140596020070210302c04d410050040300c44980043d101d954038035044503a541401d0b9500c541050302401d11600e503028943c2055014030307a601c0c0c0c82001640101002d000d050190705915009013103030585e1a0200040c0c81c110001c5512841c189000414440180c0821000540c00a1400c008404840180c0c0e000750041c000712101c4591050a100c00e94000401841d4030684034240003900100c48170182e03542c07024000c0c0444409041004920507201b09910070904030604207480740285900c078410100c101010340c1c0c0541d0784c3d03d031400094064010342ca4050615443e10030308024080390300380342506007841000c40c14003aa0b030f10710400100700408100b103a0040007460005d030004000c04000d5a0001da60b0070000b0301603624841000040c3c0084000b1a040c1d80680e00c1c0200c0789034001c65030b0300707400e8404014407031107030425100404600508000314104c40d192055585a02900c41c4184081d100c5c1000c08070710b100c = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 201747455 1250 201746205 201746213
    0x7091706070906090308120a0b36010303200c0a061809051b0306060c010915110405010c020120030313110402031608090a0803040f0b13120f1407 64
    0x160007607602002050086400007480703030103400c140f803c032a0044c07040c509014103400b848580e617000410342e1350390941c0c5104500c03a9a90303e0341018940302910360b0ba0040140550111108074040c1c03204c890b03610366181c0040000a5121080003c200e105200c201e072280840c02e50b161810703480403840399110b9100c000c04034150f50f0044e10715540c10f0707040a51500b5242d41d500520100c8030140c9502c50300c1420159011004038108005641002d0068407003854002034000311400c4425140c000c851a00400d079410010740007c0c090400d400c080d5016441c80c0c14901400a0003802d00004002d040c01000c0d84d1502c2080070025a030000384007200142c1e40d607454610b40c2170400b404030040440d4a0b0b107800c840c04520703007003c0c42503038858100351208580e030b003646040650724601700801c2c60125101d80c884000000c0c0e618809140114455494074428224504c1c2009e10348000803d20f0780c9406546411001098003c81890300340d913001d00340451100450709003201c2c149441043c1560558000600320100 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 201748705 1250 201747455 201747463
    0x4060b0309011506090506071103120c0f010605030d1103070b16030c0c0f080f1303061b020d0e061c060807030203060f15130902030f010507090f0e0f070917 69
    0x1120076900070051000c80c0c84000000b152603014090005040400600c1103042410040c10158041c2c01e84428000700180064500031509041c00300320203022030220010b202c1080408145000c00009000e0a410a004a90b44d01c42c26041c00d800c0048070a0001d01095003441142c02607030b0000c109010a00c0c1080c0750540c60f1800b00d410708002450b1680500c051441120310300d481c1544440c45144022a68645020310b070001e8007540c2c1c0302d0804005103a0524400806480214890034004c615400b01a900d60240390b00505000c0039504881c041c004500c1d4040401a42040f084401c541c5078070f002000001070039001002c880c0b04516084000c50820800034401085a00c220100c4195aa81001d0b0440c11107042e00c035100d0842c40b0013840b01080c0f422514692484c1c002c00700005d50000503800003460319014010220150355200b00740108036034400302081c058004d0038107000d0610303d8094442c03640c0324011b11a2420101d07007004600761a101d40075600003000780032480210007200151340d0351a = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 201749955 1250 201748705 201748711
    0x140a02150106110705131803021609020306210c0a14120d08040303020a0e0402030705120a0c02030a030905151602060f060f060a17090f060105040203161d04060b03 72
    0x21103100000225188224009801081d00e50090030815107444140886c4c10308503c00043d00540301e4026610b16114100583c0946029a0082c08050200501c8a51400e000d4105100003401041001901d884003460780c03140268a180c8202e0304401054800e040051500160382d120380000c20008481c807071440d80407042107048504204816000007440e07a900f09450041c5d010881100005000c01c1c0244d010f4100032a1500700104c402c200c0000080c1240d1080729030798040b590101e0201f007208900204141d01c8603074000200400100204080c0d42e0f4000e511034002003540350884001040402c3c00303070442c03503070400c20b805881d81031221107920706c0081c11001d20700600c45c0b9000681c000040000c500d00647c0090180c10303229945000303001c2c903a4807000b818414000d40040c80c00e07040c00840602c45c4203108030f00c003074581d05070003440301c5050001c10b9000601c03407170051050040c80c00103a0402458407040c1d0070050203d40100c0d0355021800b40702c000302c030b610614010300065a050f800303000b544 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 201751205 1250 201749955 201749983
    0xf030706120e010605011b03020a0b0c07060c11070b0904020c0f0c030f0706170c0c0f07090f05190504021201050901050a0c0203121603020c07150f1106040210140a02 73
    0xc42c1041401c0b10900300d0780c05218071800035115110b066a0354400ca0407452405002e172054a0b80100340791110702c3c2c0048207446641c074a1400040f10b0707080c04000e02c9054a1030101c1c1c60050f00742a1540220b941d203038454050b034040d1200018504001d43c6d9960f04403101e0204a50990b5031925140400307588814005040500a0050b81d803000300300e0304081401000c1d140151240c03d0b1801c1e9120034212001002007071400c180404014102e070400d010400c1400c1006500002c141982c10600c00b441920400300c0324145042c10300060110490207800e004845840c14800010300d41d1301c900024141d40c0c08080700702d010703529103414000c10482c10f4004d944992066001807010040300a4100d98a20480001c440740110703580125804251007010614002d6081c80c01504000d441c040f02e6041c61115800b140c20070b00c040310309000c0250044580701034040d1508183c0195011101240e849000041c002803044460360280c1f82c047e030084440c06456484114020717241c18808001070b69440c0c1c01d0864803 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 201752455 1250 201751205 201751211
    0x110c19030209161d0a09140402040606020d0e040b0123190c08090d061b020a061a0d0308060d0602040801151a0a14040522180206030c03060f03070612 66
    0x100030310300001c03007003802114aa413074191484081e560351039030080201e49258040111180040c80e00030500030002a100076080c60011428140b041008444003580f00801b55089001f4124a15070041708008000605460100b810391200b00100c0d020f9101107100030300e21000c1803c8888100480025180710401903a1207400c0302404101940ca04004040c000c203620350401c2032201a00b0010040c000c1c00e84503a201080c0d0180351150704041503000310f410701c0183c0c00620f40005012013800354034040c0c48420f1004c80170030200381c00b151420480d8107000c0d00b480b12100104446403148004e4010103500120210b4403a0380700e56055000e86000700b401d4407644510540403556030b6904160641c4882c9619055180c810960003c0c1d40403503288543e0320b901c0300300703100010303075511440d2042c002c0242c3d04586010481c06000000115400c0e40d0300d08081034806c0030300340010388403a0122a08864407103e43c039140c0e40d60302c00040011000d5825540c16004009c400110550442c03200d40148070048014 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 201753705 1250 201752455 201752461
    0x106050406050d140c03011b030b0d0b0408030702070504060b0703030b03060f150a0b0307020d080c09090424140a1103130209071205011d070c030e01110c19030209 72
    0x140d8045008050f4056040c0030901c000804c410045204030a052003070701c00c0080800000303421901004a540401d0911401c40542c16605205184440a04039800307100814192502d60038071000810040c060100000465111802042044020580200306201250712900025507030380090780110080780c02c02c020104207140c0070800310f100f421a81156210745c0e981780750040e240e200c9055969000708402d0400703d050f01d00ba400551250de241e4004103040c000c1d51800408070305000300041d039803034818096070306207070b6404900b15081078100055285c0f60700d800d0521b2543c6020410030011640c50880000f0020a0510003244602c0166104103c12420904401740b944400c860070805071040703040301001071130075080b00e60300428203180c040c00c0d405103000700b802141c0c0207800c145240c030a03203810b23541c1401c50030b5105c1d980300c4c465290140c001900f59401820f440310354012941445003601411904410400c54080400001044210000041200942703507243d01e0106a008213840800 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 201754955 1250 201753705 201753709
    0x20304030b2805310501060f0e1003120e04110d05040b07020c03070b070809120a060605010e06031305190305130503211615021c0c021209040e01020f0c010605 70
    0x30300351084441041c400c030f91a406400f18440b07074540e01c245409081058244c0c0010030360901c0b400c2c000d0410a1800c1c20f80c1c9080c0484004c03003c4005105075580c10075640d0034070000f80d4088620341c20b2041c1e4142812900003040004018081c0040c11308200790f0045603000004403150403290042d8000e0011084540b00c462040b41c8410b024007003142c0580c44180b0800c5a80144070082c00114080d00c02c103810054044c00088842100310316040c002d9000000c004244510f0344100001000c007401c00e9003a050308840030948500008000107100c900c1d000c80c00003400400d22403411030420554051140d01260700c0e0203071003038005c0440c00e08a0700f1150b230b0103d4203080016007800d42400011810006a00d01c55180703c00783d000ca035070b41888442200c0a0710014650036081485440e02d0003001da120004001d00c0344800c803000d1150a526030070552440d80040d008941601c2d4403240030391540c0e54410041c0420040c0100604440e0b440d840001c00507074810740480904072555203107000380102a40c03002 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 201756205 1250 201754955 201754961
    0x7090e01060c020105070602130b0703081003020906060c0106181d1501150e0d080a08130c1206090803070806151806030601020a0501050708060109080106080c060307020304030b28 79
    0x441d00494815504400998041c50282005503c00c45026151660010342210300c4840c503444445d105402044000406410188066001244000b4416100d15540000b440c100340500150300600000440369500303a001e401050190072486141950440c00c03810709001407180050070828407070070ba0316160781c0d50030205107100e4080b074211540382030b41d003044080e01c2d101d0030034411402070127402d11500c0219101c00c00e80c40007d9026010382a15284ca4a80c0070700350326002804180c203642203020b180002045010f0150a035141040c6d50700202503580740501c0140701603507000e032004001204016000d070b0b115282c4c1b803184c2416075150351007000001c03003200d8900510907100c403800301c3ea1f44418080c1c140ba6000d0340e440001481211407824807625001d084500544140000031060030800c1550f503006004680208490070081210034903002e6070b2130719450300c020312600c11900040414001403080080e40d000d90340008140030b0030b04185860f0301040c10051080f65010003010303000500340e00148 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 201757455 1250 201756205 201756209
    0x62004150206160e2e09051f081005040504080904140c0403020f1f0f03051e0109050601030e070f050108070c02010818070b0d0204050f04020703020706080405190b07090e01 76
    0x1400200380d41c20740c42c010b442d2100005030840d040201410000490141c4410036017100d9a4510b0301d02000c00d10280040c4076030020341086000d040141d031107000f900300d556060201100b02d450008010340b07501481c9040c0c1002e960242e5802030a00c000c0c441800090001464034036001c131410807403142d902011003c8000b040f11080345500c1c081c00200003505012200040488008288010501403140628a8200d41100b1180005c6a85851383e001642522a050704000000b01c0340c41525042101020144014021109011b4a900210b15039034041d40000c56207407440c00c1910310043d1500c1c104120800036124150000f9050404142c001c2c0c0684003d8010580603543c0d6042a42d0f01800842d4515009200b400c061080d480700242c20703030210010300740d4000b9280c400f580c1c3c1c030f140c50108402c1600305001c2038810761040110400103070f000203d44085070100d0508801c0c9179101c2c2441400c03d980c0f80f80c01c030302c0701082011920401c12803502251140d0881d0322600c00240d120f0081c2d4102150034 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 201758705 1250 201757455 201757471
    0x3b030601060306050619200a06150807180204050a0b0c12190522060216081b09100b07030309021e060a030e0304080f0f1c0203070609062004150206 65
    0x20440103c2c00420b5400880d095203d174249010013031101d0a00100c0c80e212600700847c581c01014070401000014000c592950a00c4011407154900701a020703900c0700e400d485041c00d035940404001c0e0401400703405460080c20000c0810360302603650f00104c24264002c5c1c514120f68011840703105001d191400c1a40e41034400c410580070f501154581c15100c85c1d104180031500726080c102d42c0c50440c20306400c003801400322503000d0110821f44000c25141c4809540000300240c0010080d602c0c0c1030b544001001107031400f190898095101c070780040c0340000c00307500a081082000910390003496095041104401c1c82503038151510107846594400340b078040701245501031300400130381030320520032b400038a50f200540f400d0f6031800381c4da5100503140c031390b0726620744c4042d030401c10501ea0008401d0210881400700e02080c84940e45103400003c1d100c4c03240310401407549580d618010280025a408403008088152030501d81c0c9100e43c801c18801e030441d110380340c40081e4800315401e0491011805074040c40c19 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 201759955 1250 201758705 201758707
    0xb0f010608040321140103060b03010c1b061808070c140415180e071502150f011a07060507020c0f01020d080a02030417040603020702010305060109060206073b0306010603060506 78
    0x2240c5030401e90b030f00c04d9180101e1039507185d0804503094400e40410034000d512945001511100074030615003950f80400204040c0101c3c140c1ca50002d0904800c0340c0e0704182d1142c40010003068010620005210904001e401070f400403c4110801c0346e010704507015602d503612400d1400103c0e10801c030170b40390f0400e207000615000240411004038980e040c000089017900d0081001d2244008288c03030034046510051132400104d12800b04983c05002100c440d01d08007100c3e41c0d481c64510548005104180720f42342c40c03145921103d80b1418440010303a1034080d44000c09214900b40302000a40d62450940024400c1400042200107580005201203500c507050311034404e1075540c0034a0744000d400017041910241500e560b181d502d000b0000040018000540f00180c032090940001800c50300d0052401b818041c81c03041c01c2c40303501d4001581d16800305080c940b00070403260b20500e02804030144c1d04035128424880c005541440304014010300f00c0308054003120390b0703030303988000c11020b55442e4030074150800c1b8 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 201761205 1250 201759955 201759977
    0xf0f0f13060e030c12071b0b03040807020103020d051e0703020a020c04091a0708241c030c0b010b0909090c281508090f0a110d02010c08070b0f0106080403 68
    0x7516400c800b40150364101964280301500c07000e1410180d40d240c0301500361710006480401c00c641c8045c13500a20340f404104a50f02810700502401a200160000d441c0300c002245441c2160301c00e804440f0b64a110b80300078031140c2404d0000c40700103803460403000104c00070f01000601c49413292007a12018071181c2e00510b001c0520a0510008203210320040c0d560917602e031105c5c1c81c000003510380c050190301070740c0d42d83e4058549800341c5443d482c000e5100005c002c0300410203036925555244079101d40c62036071052500100186c038080d2180285144000c008000d030000000d0941c0300780780903025400d0156850340c02980c0c4c01481c02d844058044d0045c0c0e100c914101030150030300300035155144c04140c14181c038080e1619042c40300da42c603124a5088000864070010005e0f0190140400501695020003c02d01002c0701e1b6900303110b008900302e005002e10348800c0b0300400e5a10980000c00390b1500f21654595901090400c02c80c1e5440858003443c840c0c50220002501602c2a03212030300c520340568800107110 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 201762455 1250 201761205 201761213
    0x50f030c0a140d080304050f1605030a080f12010b03091b090f07020a051c09120201090b0903070306020403140105060a21060605130b040e03070213090f0b0f0f0f13 72
    0x201c2010f6044544400c4900c00580c02c40300960065000704014290700030b040f5115880c10064a031488525083c1090411258a0010760100c1aaa20440154a440c1b5112502c1000e000787d04092201005c08000050581030203401540128862000d55440170700500d8000c24a20f00300710255000230700d05000500c4030101c032281030340206851058075240461074541a250118200410b80d0080210743d5582e001900311441c84c0041c180350b0f8550019000c03076000a03000408034820340c04074500001d0300310711f1a80e0a002103c044e55101c02c01715215901c80c14180c440e02c40c584a840440d41c13130000814003520b0070881400842c1c000c0c184882c0d5180588403401c895080141c8115050b948075900402c0d2aa64415100c0200301c04c03030800101d10520404000954140000014050700104201c00c050303240e40142d05000d260300c81010404828a14100c0f000680401000d00f2443e0f550741404001420004100c0c051500e6905e00c102039100d16100e001344000544000000010400040d4006 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 201763705 1250 201762455 201762479
    0x406052b0609050d03060e0601030c0203160501020f1804060e01080d0f03090b070509090f0705090d020f180109060b0307170603070510022406010203040612020f0d0501050f030c0a 79
    0x4034841c200120703015205a0b2000d203030204155040300401e8031405c040c884c104413116026440301d000d1030244890201004003a440b48140c00f85e104500031070398520000e200742501219076108140f22a203a64605400d002c68800c0000b102c070031712903820326100213015200140d155058448400103032140d1140460240e60651044070780605040d2110007000128021264681c4a04215142d16640308500782c200440020010300c20f603110807044081c0100035a0004c255941c001060b00c1c803152080c1c00340001020310041e441403a0f4017030031741e94054015030f203c11803242c1210341e00c090601c041c2da117500e50f0000380c1c04122080c0000806180104e0fa403d000422450740245019080d03c40b1940c50340301060401810607040300142e48035594403044074511004e007103242c0e80c0c002c0d03810307010b400c00b030740001e49a10480c803802c0d003085980c4000d503030001a00e604031210110040800c6236589a0504e0700006000248074641c410400300000c101c807810080307604058400020714640c44a030400075042e0034 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 201764955 1250 201763705 201763789
    0x32d0301050d11090c0403150c080c1b0709021c0b011b140f160501020c0303030a110d09050109110315010308030702010e0a08072604030627030c02040605 68
    0x100307083c01c110556261981d04025000d60356280007580d480d800e40c01c180803042021001205e00501d0007080c2c980d100e40c8591145c0d0413021195045503100007a69040c4114a010710000c400c0703000d20701c40040c086c80680e0051002c2e07003060705100f00c0049070805580840c0d82402c0f1071404075041084000450341c4810814405610504040b40b880e16400c11030f80ca005043c00c882c02c45031340705000c0c0e01c811440032600306000341003d20003401082c03400c002007500c90001802c4e080c0c2042e200c1610714200c0f4100c0d81942c004c00b1180d24100041d0a45080a0740030b095060803d54440c0c412102418050501190400c200e560100203114183d1071755aa503401a400103103180110f5580f502d09014526050044030121402070744c003541c44240c00d062210341061505119403c000e8206090b11821901c0b405403000c40e80c200c1400900344040b41078034400450500e0003811710b140b0481d0f61004250704440c0c01c544d09402a1400c01c081034542c41448030241c5000c80e91481c2400341d00030b204a071030303080b20130b811 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 201766205 1250 201764955 201764963
    0x3020d1e0e040f0c020115090c050d020c0717070519080606010c02032409060c0301030b0a0510030f05010c0f0201060501020703080c21190807050711150408032d0301050d 75
    0x241000000c581401244c0160800d00b00503515101c082500e490b00c0380e092406001d24002c20000d480d1071100c0502903200f1018003a070980e4020444006c000014040340e00188000164044580e5000c001180ca035001c40c0525485044007180d408100c0d00c10801c41426103070740c0030044c005601e1b000c0043d1005d40741590126894400e100d402031088072107030814503101500b4203101c00c150404658140c1442c0008120215882040c00108041048904c010303070030000b500400a40d507203818003840b443c02c2981d000500012078030004401000015401169890080d0350340110f8003184030b0b022130980d049441001c0c0103038000c210a00c04980f0280c01029014220300840704400f40104503102221008021021105004103072440c01542c5900300344074800061422401038942400d01910a00404001070080d589003198918503413a2110713514a50503d6280d1140c40f103036200d54403680c0e03a0290800c032a4a0a08061503420007448203d1415000600e540c2942146c1c00d040a0103900111041c0c251 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 201767455 1250 201766205 201766211
    0x160c0305070f0c0f051206040206120a0e0105011502010c020f0c010f0207051c02090702061b0702040209120609010b0a0f0b030c0418060e060904050a0201050f090310060303020d1e0e04 81
    0x2400078020b052580f0050064010b0500031a1070032040180e200c407005401182a0040c404000040e0b5411080b907050055000701440252078481e40b070002001200075464856103050008140d51403000d4107545156842d500070301211200b0542281c4810400e503044035079510207140d1425560113518071080031180343c4111008690b88900059402c640543d90880300580410030205604060300160f81c0040103000800080c14100d4140251a4451040081180c00820850115a91a0100c52600700000c003800c0d03083e40030f0782d00315440303610030755401006620306850300b00b4500b08100d80004680b420103182500b40c6ca002401c001ca83e100529802140108200c00308075440c0c1000200007501e5410380c0001d4540c05c00115034828540901994822418101003000151000440d40c00c0c066080c03174180c2e121019890020310714000d0b5450036903d070040084c017000003040c40d0b104000700c0303000354201c1d044405d03d0740040d01d1541441a105202c00c45484202d03400b507000b0f40203403208420181c000 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 201768705 1250 201767455 201767483
    0x20a0507020d0f020301061a03060d0303022a100b090f040606030b0906160903120c1506080313060806012c0d14061803120604021608070605160c030507 67
    0x110b00030385128089401c5000902c2d01000d604091081401800d803e050340402c5c405c0300b22458100b400000c0881c0e02c01c2145841d94410180700c0d80644050513100050310035a0000d901428058490313a118580e41d501c2520151000e21400e405230100c2c610002d03000c0d020544964030034042e004001802511100d489100000010700d440308141d02c10b0500364064141420501f04412005e08010400d000b008519002400812141c8515810b00000c9081410b82020a89403586d0f41d800801c40c030b8000c2c2464481c000030252000700080a028030039560301030f490354840304156516130040e0340050000303540080e45000071100c4004a00440320141290303080c109003c0c000b81c240e1003407141c12602d20f08400715200e0800003c11500e80c000c5450700d20700d024a0030641d8000d5a07805410540d50a0501d048041991504c03035904690142e014480d04000b20381c0641000101c80e0303c1041c04071503a038501000a2041d007070400080320594803d07942e102d00302030641c404a0f01900110029101c004100070701d = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 201769955 1250 201768705 201768709
    0x14070f0b04030804050607080c0f0c1002031003020102060c0711130f020d02040e09060601080a0b0a0302040903030603020a060e0a030303050c3c040803031303090914060405060301020c0a0204020a050702 89
    0x80c8a1041c1c1c426600c0700c0652070b19203402800c1010140c100c1c0300b4417000f40309100303501e0035942c250b40c245106200041c0d103616130590720910b04000201d125501500c00824030010740e19440825069a000380c00b107400795200d00800c0c041600c668140500050414041440940f1f859510200d052040c050302051003031024442a0482e405208140e0500e030340000c0400040c005d00458035800084c21003e04a03501d0000c0020388501402000780d5862642c40c10012060b42d240b900708005182c025104001d51219803502a00818860106a1184441c0704001a419104410104075100007074000c00c0840e2460f942075000e0f1001400300025000c0a121482c850396030110341000c80020034290074005c0701c4140e2480d0079840c0c50034000700c4140d0100424055268000200d0350880540d6000c0c51707002c03c1d40d05040300c40c440990801801c0d20305148044070f05034080700c51390740036a1044804010b01d80361542011300f01d00c911812003049402040908015203840d43c003900658203d810510f24052040c0c1c0 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 201771205 1250 201769955 201769973
    0x60409020319050f060d0b09070e0916051c0305090609040203040605040606120c0510090b0c06011a04060206070309080d020403030503010305152502070b0409020306010f05030714070f 81
    0x1800103a00c0b00701c0d041805400b4264080c443d001003140131140b250741000d0380840c011200102d009802a07001c1c0e40071414110b402c000e020700500174040c030190303141010980710381c40f02c2c02c40c250715043c22201301c0082036901d03108641000c072040584442c07807500c4259070203039242d802c07440099602010620010499486a00055104034419a800a811300d0140f0740a000c803031107600070205020409407020005040044280143c82048900102d111141c2c0d2048400007402c0e0401030381d1243c0424081141c85c1e00080b094141d40b1803500c0001c15407200c405118050040d0f00c16030006900000110f0703201030003540400f41c1580211600380c0707040711200c0d031182a41d02641c001c800040c800801001032120600111290034101c0344541e0050620400e46c2d6074100d103182700080600c00d00c2c4400d5032054020080b0900400d8003c000c1511180d8640c41e000094100302c0703031103011804604400900c944140300700c80c801d19240c1c599640e40035400021070740c6500240c208441217042c030407604011410400e = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 201772455 1250 201771205 201771211
    0xe0403210f0c0207140a1e031208040c0608040b0c0a030f0606020322080a0212030d151d0103050303130809030708060103030909060608040213090f0506011a0c0303060d020604090203 80
    0x540042803a41079102d00902d00b102030350000c48140480a140340b260b690b0074160004603242d918101d406446440c4a031083c00000f50f000520344024417000f08140c0360000d841d60b2165000b0311084801c60b5070791400751101c2303204503001030200703c141d400526100d48007409020080558900051a4030480002408542c6182c100f0310141c0d001041e0301500f044030408a545080400f603150003010314008030290303545160030000b880398403403200d0501711750f204100360780d542c80001505101140e1f818003410606921800f5100d140d410850009144140c40e01c0064102d81c4d00c0401075195a541c8100000d0b031101ca2081151109420405601180d5041149502411505c8040c180951561030040c185150903484490b001d8180502008011f0b000100c2603841074060307c51280c500c86165070710000b481035801c004e0100310b001e00d4601c1801000074000c2e05a800368a58041071044019021485002e007088060180e4010000900c644c106148212590751000d40020305094a603482c03803040e60422 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 201773705 1250 201772455 201772481
    0x703050609010c090f15052704050603010b0d112202030a05060a1d0606070f0c0509060307051c020a0e0109021809040b040f08040f08010506040c03060e040321 70
    0x40c0d400c0c4000c0c0d06081c400d40806012a0500b540101c0c80d219041110135084e01c10341c103038034005205410000d40100304840800501c03250300d50825032484011180902d081c00450f001c0d62402001803400d0030148180303011248014440a62142d503607030384021250071107500d40d8009006001100031105030209059125203540805604da241c845980c1007121001000c25110303107402c0e0010040248203006200c0c0e1914030101130b461550354000828068821128010005440515484240711044001c00c09850049606c22101d0f1140400c00d81d4451140c080c1c15030008540c03446100000200c0ca42ca903450b0f20241c80801001d50700c02d03010090301803d0340903c1c85a50001050041340b5800f41e024104040b0071620040d050400d0340364083e0440000700018100c0d85020910340c02e0000c0f141c2070f0743c010021840020030311506c511456028140c20340b102c601460620002c00c0c0428000d01504d01641e215440d601c140c0c0d075868030115805241d1400030b0404258003140d03030a1012460081c55413481c48 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 201774955 1250 201773705 201773713
    0x1e0301080606030a2103060302100e030c060f1b0c030a03020f1002120c07210306030303051b0a081503150402011d01090b0702040e0d0309020306100303050706020307030e070305 78
    0x15000c0300300d0900e00c000345041e1280d00300c055840005240801c10910007004031038688640307543e0724000d40090a0a410107503004450310130404c1c0e030310f41c01406010418020b80645822040010600010f4001c5a042d000c3c0c00c0c1c0c3c03c0c40880c06511010900d620b4004c0703000116450100300c0c1e004030b0f050030b000c21001e50058015403c03840004000300080340c0400a2440c08518000040d90003032010b2001030310318070111000084007018040b054041069000d9103440c072000c281a907450180017803000d4031007140840c1c01c0030002561076642149280700c3c02091240b95140c8202d1550132207240c40b0081018401d818000102c032203e4904000d54942074095409140c07150071301d0300000d808000070300e00590f03010361138074019460741c0da0241d00d01041302c03501c02d1803944403404c1e44009005008a41c260114511600b4441180590b0503040110030303600030b800750760303c0e503d4081d440000140349020180105000b00031450004445034011a84000503142c0090881c0300500207906200284e442900d072540 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 201776205 1250 201774955 201774959
    0x902010f030b3d020c010806090601120501081b0301021201090513050d0e011101151703070516170a050d0c080403020d1a01060309050c0402071106030109021c1e050601051e0301 78
    0x43d9448421490250310b0006000c0900400e00007060f8041c018502401642c140300811656400b800440c250100c80c5181403040b507840e480e00643e601030103000480d07100c4d070100e2881380c181010b200311101002d51240b280945da09041d0315101030600600303144030714503800c03170300340041002404561003800c1e4135070ba90203c44a0001c001048050f01c11910201741c1d00d010061134884840c68600009c4610f100943d0210030030030b010050440c050402c001c0c1250099030056807641405d001018261884105503c2060b1004445955600c055050041440d403143d48070400340d0b805000c82e0301d0614442d00825107070a0700ca6000c560081130245044038040052072003001002607054600c1e015142c6440c00708988075243c4c03181039031101c1c5440d480f8060b945c0040d90b03a040c046050035101000e080940a00c0e1342c1d5079203c24440c020741c00004903607a001118041c44105180f503000782030130800c0aa42c4007982501d040d80c808001e06001c3c0042c5e05200e01000b40030b803050003035654052201c0d10703004004c2d00c942c = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 201777455 1250 201776205 201776299
    0xc0915040b040f0902091804110d0f0b1b03010911130323060c0d090c051207090507051306030b0a091503020a090e0d08042d12030902010f030b 63
    0x41c18039002051a90700501103038583c0d07103980d88216420308400282c1c0700c151f1110700b414040301018800245d00454004020001c0c0034404442010bc2072054a105d0403542d54080486103501d002d48580005200420041011074076642281030860a01a1020700c0d103aa00002c0403d07007012a401181e00c0c0a0720a8800510340d0705030150012104140c010302810700d00380c40ea6505610030701032241002c0756954101d0007071000e400380c0341c4043c2101400d05004112503240c080c1d0384d8100da1040040c40c509110024401e540314900b901c041c80000c0c241d4142d1207003440c000f58043c05994243c1a08401d506c68000798940e000d01605c0c00ba80040030422081c1801c5005200c800c0e48076030003091b440381c20140b0507613100b940002c2469003421035280c0034009407902c0c035280c540030000200f00d62071840001414203501104c00424852140f02e80548094505540740070350036a105090043e0201d4000060700d84c03068080d401003010100010008030f080740e55602c8010f66415002c2240c4010600c400720140d0300c0c = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 201778705 1250 201777455 201777479
    0xf0207151e0309081c09050d0207051203040f0b0f0c01110a021e0d050705070e24040513060f062105250506071e050a0b070e01080c0915040b04 63
    0xca03070303180342c2407050b500140c940c1c1083e40b150a42e02d01d0f06105003104911264090b60100a40a07446010341c0e00303080708403000966071981405000e1142a1a01105000010010864044945c035030030f42202145461444400d681141c030001d0385180c0c0c1044010b00d8030102303204100e2801601c000040e160354040e507009150011403c056041003032410010100083d0000d400d102c059141c1c13403c0c960300d8990749841801d0071015071010480000701c500340480300c592440140303102d00c44d2204040b0300300410401c010540c0d0090720207542082c005003840d07001c141c994000d9040d40c1c59030b88021812a507180030102c0051000d081c112606120041c8220802106004080c8600c1a400c0c0d9001142210402c450030001c192107468411903000510008005500780540080168501c0c034080500f5603081c02a00c0701c40b0040103c944083c40000a842035028070b080f84d03021101a07450514a6655000c40e541503800f0744641944201080c00c02084584000000d0016003000310b095a292890600350003030f1 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 201779955 1250 201778705 201778757
    0x9130203060f2502150c07120201020a170c0306010804020f0a030b06091810090314070303090c0509010810150806010f06030b0103060b0d0209010311040f0e0a0905030403030f020715 80
    0x300c2881500181d9076070010704079445e01c10b021704103080c0f92100701418619105080008081c41c0c1c42a018001441c0c06601a005c0c14105444000c2a5038000a08603440c050448604c60100810b00220307005503c00c0030325540c4948003a04c44400e01101e940002c0704440070307620807648001c001042040c1d42c140109240e030819503c2ca07038515600d00d450490ba46901c00f0300701c614240356441a9003410f0501c40c3e1210104010325581480c0c0e03804440c1401005020206001e851041405100040300d042205403903040365900c03000380c0009103140d048040500307880034494909041410011400b02818820940201b11542080c8002860180040c0a441410649074145450404100500c3c80080b0844c0c01980c02c00780b0043c0c0e03032201070005074003c0051600600028901082c0420440f00782c20741d07641aa20241400e0b8030a42e103946400702621014400204207800a11080002a000c0c1541907c00d00f150300684541030303140e80600c50b80301c411440d0f040004180311104400f54503400701e603680c = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 201781205 1250 201779955 201780001
    0x402161e0506010b030c070b0109021810090501031508030a0201150e0c0409110c1006090e03040f05220e0312060117010605030709030614070801120c030209130203060f 74
    0x40040c0c4503032501900c8050500c0742c030fa00200d00000049010070540c0c21900e00680c803008030f0b1501d503100c0819400a422a2250342e04c160500b020240c00740c540402200040349a65032010b800f03e0801c8011000f1380300021410709110700500002c260410184081d10f031404c8250b000248000d50740d42583c2d155410b0398041a46038100e202406080d10419003142c068502c030582c045400050040e0519141c4035040940d51103010f410340b000000082c94100c1030480710f8007101405840e592041c400d449218500c1040380c40c07070700080b0130000c0381064440f0030a4018042c014a001000f6100c03001d09890b03050b020318400d43c000040030000e910340c0d15041500b104e0700b0300c0c1240c801c0e40e00d00c80c6080c040406020b11760a01c280480010101c0e0710401c1640701440d4401c40074007400b2004516004d118030150b8012002c2600c100c008a55000340041051130300341c01c8121946d0051441d0248007000030701800c21034446407074100c0000582c808014450052501850440b400d152005400d0803008041c03c0c110 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 201782455 1250 201781205 201781253
    0x70e0603040b0106030b01090314070303080702030a1e020106030f06061509120b040203070b0d0e0106060e0d0b340801060f1710030203120301060f0c020a0303120605040216 76
    0x803001c03541140b0401e041d80c20904001542024400c01a605105541d100801071085500c0003810342c00b01140d444103c92003610354200c16214150140d8490154040303000024502050452101c0316501921294a0305400001100c60701c0b40c4034000c141d4180c0308195283c0382c64090400a4003000c420b16450106207241ca42242410065244440002498046c2c10b0800041c041415503400b4061a030051840c1c5000554851040e4504000f41100c3c00303400d4095407070400c0005006001d03030790418240000502700b400c010031a60325a0490503001e8560b071242c40300200070301418201d80d108904d8402c5a400607010f03c01201e0401002504160012001c000303001071020920707030b080030340e4406211410301000b5655880b81b0070604016520307840a5814802c4d0f0000ea200c1340ca110380194141c1d0019910010200e038605000c1e40c9420f01080025000f00c03070404d0070004640315500c110342e5181381c5500419840d0f030b5000020141c5e0000e40842010b014200c0c080820040c010900f0351451440740442 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 201783705 1250 201782455 201782461
    0x2d05030601030b010302010305190f1a04050c121005060403080c010c020c0a1202030c03030d02090a06140f09060d0608070914010f0e1b28020615040f0204030602070506070e0603 78
    0x41d0300f0340c50041c0320090500d03840d04046017114459040644802c00c3e010010860703000f80031400005010407042d807101c0010b54203541012806c0074014140315651000840d80307804400f440b030602610f0000c20061140140c3c02c2c0209d5159500380007040110f009851403500e40d080c80d00c45500f15440981c004080d503024601d4800740d9261000810700b101c40d82c00e03494401c6075080c008241072410003400c40d50f0501001800386208821940230305200c0100303032001c5085980312002603c083e041141c160059900a100183c441c040c148010022010081c0055040030701d501c44004c103540e0030341c100f013007507802c45a03080c04010294407903040a0b003252002c0c09201c0d450940301c0002d4007404d00415210456080000d640d58100640010034200d800015990760141040341c240402111080b44204032220360140352000d10003c0c0160040c41d001d244c80a403020424200710040003100e403140c8400341c00380320004c041282032020f08061406072000c1c098a1800500041851400d01c441a10900082c824 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 201784955 1250 201783705 201783713
    0x60801050702070b0d11030a09060b030a050a230f0106170a0312051003021e04061703090d031101390f05030402040f0903050c0c2403060a2d0503060103 67
    0x403c00849011962060341d40d140001c070b207000740c418103c1d9034220000000a00400d0041c552111000302d008200c20460b41940000b01f6440d4141040c0141c21030340130074100c1c03000c1600a21094103e000c0340c0e001000586150f1402e9041c82c40c24201907803203075981c1004010055038400e15030003800d148d00150040e000b0380d503405084428880303180c40c0381598580002c1d40c0c9403880000358020b150028640b2003540e40ba0120080f40f5651411060302540c1402c0c00014490b030302c585005c070070207601c1d000f031410081c10805100c1d28a807980e506030100108285c95103406882032240701e401580c41190074086c210130411108003c68103070300300251031700c2942900000c60b42c0725054820143d80752034140d0350703901e46000050103001e9205901c607501740707485008800c00da0484e00802d40540003070b00795049908a5020000c1503c42c116514503500b800b10134030001000840700440e80208010008124241c8456013083c0d4070600102c0c514280c021103220084112024a000c001007208900800181d0b040d569 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 201786205 1250 201784955 201784963
    0x100501081902070804050402070503070606090c08190b040c03060f051002210f1801021509030d0903050c0a050c031203070f0309021804061a09040c0e1008010603080a03060801050702 80
    0x18071076200c0707a02058070820008540c00311402000c1c01003043d9119020382c240903469502044c0111101d915049000400c140d040c01a20b8a84c500c644808005686503400c0d03210401c8000c0c01d0164550362152518090f581328460b0403030f100096036001603100d0411072004d1825517190000d44c4103411880c4400009540042d160000094030303100b01c004440704001d82c0310240a502c0070f014540b4004078081680003065145d04c400c0f12000da085421101840f03c81892000c07094654441d1500200683d0760140307103903004010340c203210740350191600e20815841400c0c5102030b00101d030290000b0000c0e9066180c04c00c00761804640b4220460320b5070901e1840500140280d0b40400c040c5529040762000795520394141b00d035601e070f80f02c2c00e40e2002c0c80c040c40c0140007020a40401e540a403000c404000c901d061013107403140311720740c0014600162401c02c00c01c030980d090000e02c1c19a0407442c405020424100a0092000440c07050f4082c07900e8100301c000240035a1419044802941e00d003804118501d03034006 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 201787455 1250 201786205 201786241
    0xa0e01060b0307050a2312011410030c1205010b0306180c0702013501090f020a0c0803040c03020a0602060a0f05090a1104060b04080a02040b06030c030c0d02090d080310050108 77
    0x8101295151710b21042500d9080394a00300090440d00a042071040d54811001020000030f417145840080c8c1c3c940e007000240d0b030803103e0440d0b0000303d04003a000c5001d009601c03c82c250181c50410a816400801c40c0c0015250240c000030086240801400320b5401d005d45401c100340c68144980d010f6181c90003640903d4050b100c0040c1c10062030300c0c1110320900c0416188080005020850103040c8800361441120740005e102e05c00d101890a400b03110240c100b4829a0b030b40c10500c0d86c817a40812a240c68220745900040c0090314403410f0a000000107a40b81c00c0c0880003494603401030301481c50305000202c00c07610765402001041b400c10042113445000071036840450b50340242150030640460b008103004100c5500060660540001c000c20110400100307400014401c0302d0500c0b1a105507014004140410f030f0b00c21070f59003420f02c0420966803400c1d020740b10110000e4001818a4a40000522900c0c2c00500607542c0c194000284500c03031100c45001da000c0c10302030910f0480390800c00c00f6801c4401d192 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 201788705 1250 201787455 201787457
    0x40305030c0f16030e09090d051b010b04140702061f0603020a02101a0306090307031704030e100305190e070501050f0705010e0c0907030b030303010317160b0a0e01060b0307 76
    0xd20b2466020703068103540203229503001c50002042645400b81c050210005020b101d10700b030300006400317844001000c00d80d40010390b464500301102c8000c813640c20300e5000103a84c00c80d52582c10420547d110f601c980d2003009074580031031005041c007400103400c005014100c03000c0700003042c1e07031174485034000c4109000f160030034580140d44901005049041240640d04440e1181c00c2914a0740707c46150101401543c80031030070b44004c0d4890300559542d0f84502140240410344e100c2e998044040d141c0c089540c000d00030f05100050546100004484d00c007030006c4c03000840e66941c14031201108402036000b49104c030100801030305c038051340c0700e46e81c440071441954104000041c060241c2c03c010700a603018188e11000a00020140391031598070384e000d02440a000d0b074900000030f8855886070041c0b240c0580054044c504c0c59095888542e960310507003403040c180400411840001c0c030040c1e040c4858983c01a00f0b041c48174280000150700381d030403c5511090984c140340040c0a0100e82c0b41c2160740021103 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 201789955 1250 201788705 201788707
    0x3051314010f0804030c0b041212020715050712020c15150d02060904090501110307141204120311120601090b0909013609230d1101060506040602070f05010206040305030c 75
    0x1032450300312146c6072000c00c0141012060424002003001320004251600d0b42511596101ca0071040018124001c0c1c03180548903140800400700412140c2c0c0c00540c01081501c0d00500000d50b04106500740d170b1015030302800b242d000c01c200d00d14150040d14110b4000020622040040c104d0000040f002000b46a010b8811103001a9848180e91075071710403811940d02200a11002840d081c401a890700b04940c90030102d108140b0308142c00d0300320411241110a0352425500743d07265511503c9842140065120505a07603003814401c00e8406005000c003820407010030502898080d0004081d4a9140c1c080c80076001c1c1070200e003001d80d0300c02c1c008a0543c0c48151840c4c03259800c500e0780019a46403410f01481a940244441510105d07582101d4213a5000b140c4524441a0b00b402441c1142c942040c0700515422031407869801c83e00c20340c1a45401039420300042402500c8000141c001d600c140d02c104056409080c0030041e08080040c42c0e00184070900103440c1c285000c2d1806411031000070050300015034 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 201791205 1250 201789955 201789961
    0x3010522062c010605090105151c090b0a050613050c1c020706110409151505090a030203062d090307081605070b1209070501020c0f01091203051314010f08 68
    0x5000c2c1c00101d2080c400c8503442030b00d82c0700060780e40c02030240703008090003400804000b01e020706011071403075110300d01007108520304840c10f603c0100c01c450041c4005000da89480e240e001041a03e0a00d5000703007404480040d81d81011000c0080110b821444a210b1601345010090702200305815070b51044440070f616191040c903100003c4c02846a1354004207a40d2404640c0400c0c81c010102810940700c0b81c0108010304105040a101d22280910075000b80c2d030442130031036034140d1061015040c8139401600c0f090789207889500103400c0c0300d41100c1412005e0070b901c000700030002041d43c4500c0d4001c0301400c80b110900301440f00326201e204040d00a0b11080f40001c9101400c240c4000003054180c20a080e1003200341c403038400c02c400b617121000c0002840e0000c0c0214010882c003060740811640140c000b4600c11480500703000220765510388032414001c0382c0a00141e90600a000d0010340ca00ca031b80c0702940d68000c524062030080040e004054003d41c1c0d400e050600380d8110381d2446048400e070600c003032195 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 201792455 1250 201791205 201791231
    0xe0706230d05010512011b120209032a06090d08031017010b01090b090a0e0c0706062607033507030f0f0201020f04091512030903020301052206 63
    0x4540d55208900c10030001001d210207280d951046050764021600e0b038401c1e040800340b00b4243c03228180414000c081c10349041e070203140200c44443e12140c1c0a14054180750ba100006410454030709880604040c021320b6410081c0d11924151119660450343c4904082d03c4a020031843c01c0e107540001c1000d04004086600c80052000141c01003100e42045000c410741490380c0d9010b8602c10780098041441d144c00072031400054400d40f040d568000e49811384141c0380c6200c111000d1130113000030051110801c0002e01040b1580590380c01303424010154a01191030240c602040071030000540c0c15600140030500008000c0d80c465400c10a00c4000e404803110110402c01800c0400301c104910844006100310426410030894038083d000b03500c8518103000e900d00309070b0070b03489644c00c444c91040c1c0812041c02040c0003a0303c910f85038044052644040c548940032201540c08000c0241c2c0402d40c82402081103103400d000b115808121100d080d0307004010f6142024643e00c0d8084003e001f10f071034400c00340c070b46 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 201793705 1250 201792455 201792497
    0x91509030302130f0303090e0c0910050405030a080315041b0302031e01150305070302130303030e03070602160c09091e211206120816110a0f06030c030e0706 69
    0x144020365203d00b031581d20300d480b0342000310b580320403404101074610006004a0004020b803041d44001c811915143e4a503003048810200044281d00740030043c407000c122500c040200d0244030f4441d40c103066490038882185050281040d4586124a0405584000340040c0ca00c54a1100d03072641805070f203988442100006140003a07000d04a44081344000107448030350f92981d04020340054600300b106440f81c4100b202030340b00b46c6c90f00290005c0c07482810000284030398080324840402d80107aa00b00607541d42c3e280189e0f8400100c040f5103244414141090200108500c00101002181001040e480b60b5400c841c011501c0c24a001407444c2c00030300c90611000da000386808003254088850145400034010b4030b510301c0d0703040100d091032900f50085507100c00031f03604490113504500007500b04038840c25050a18020b007041207990200316040d0180c25214203129802800c21480064002c50030150010100c17103010500c80c0804fc00c0141162900c100456182d080c0d41c1c051a00301d00c040382c402005500 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 201794955 1250 201793705 201793717
    0x3070813050d11010807020f0d1809020409050603072103050c15090f0d020708150c0c0105040f1e0f020f0a03081207020115060503010b03070c0501020d1b03091509030302 75
    0x3102c8a40001001c00c0041d401d500b2040c0e1003601c1c2c4151a88a0481c12650351006d40d40c50000c5500030340000c5400c6004101150341e1040a182c000e41c81500c1d00711440c01d07604a544101c404a480d40c0500440786428040d00010306a8030822800080c4d603080a41003200e150710000e405d00c00c0004810000305802c0c010303401c503604441009200da042c841c20855840c201d5a808140702e008a11240040c20301c003140d10780c212503419004080d105083c0a00440c03041001d40520140c0c070702080700000c020000c4c0038241c81a0b010b26402502d14240d07003040308a00e07c0c0b9071611508110710003030034000205030b5044000fa05805955803404507101c40041011003045400160032784c003003c10b251000c0034600c02541d104036031070f50091040100325400c90302c541c41c4d14018a00403500910062011400c2040a9503000c01ca5141000c2d024900d500c0c0d050881e44007005c1c2a00282c2c407407034400c00a1852442010381890140790821402c03080e40c40d03503007504415540381200d050316072110000b410300c82e8040c0c0e04 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 201796205 1250 201794955 201794959
    0xc010c03090905090c09010b0406090306020d09051501080706030c120e0c0607080d1419200a0804110a050307051e06041d0615030601180b0f1b0a050307081305 70
    0x8807608040c4042903417200101ca0740351040102a0022a141e5203000542c0e00f101d0458941d1000142541d5071003010b9040020420020369542c644100800d008110700038010301001e83e0742d0f42c40c0d410850742a00700f44071900620140350070541d08412855000d4107007400601c400c00c000514000d03111080f81000e001c004480d50200d40030803051b00340a41d101c000c01028103065410056640e41c141c000008400484041c82107443c0b1b1b0034140442030254101500d0481c5015050381100c011081000745504240c2d00c1400082c070f00000c00040107040e07240180d03102821140c2005881c03a02c80040d43d190340038015180148800042c00e0400d588400c0c980503090703001008240c0762601c40340014500b46401c011a0b8806160101264142c14940c100050b444078010086245039120300054a590a044005001c50484c02c40000b5403d070f00344020f0000201c011181c2d07a92740e4001c1604074109c41d02d1a010322155080046204000f03900002203845050f800b0300b90039110160701c0d07880400c00c0a83d40c0066 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 201797455 1250 201796205 201796211
    0xc03050304090c1e020c0613050303040b030601230a0c05030436050402091b0903150105040b090c2217030301030b0114090106201903021207050c010c030909 69
    0x40b82e40d1941c0e0b00b002200f90710381e50f1010701d009031900c1d002081e00c0408204030050381051005407000d003012001080248103107019404441c1c0d540d0007007403650340a5404410052030200601015680c0103e002000c144024000d400ca080e505000f081d080c8511900079007130184c40200780c000c1000a0040e41c00610208402012900345060500c41e2050b072a040c540d0314104003003040205052910800d40619000b07004071466a030740003444002c0c20b04041610150710300c00c4c003450129640401034018004811408041c0e2540760400380801c0d503802c21754040c810214541000750b103c4500090304d1107400100359504211645076113158003614190004120004840040c40c98590004015030480b0300c6030070010610f81c0c0c2c43d101c0c008500745017200c1c0c55016914600401400388198a4440300c4001e0308600801c001060101d40e14080ca03821200402030003900c0e403481456018080c0000d5140140c544c94a0002c03280c1e901925400c1182003e41880b0800080030103142c8161400f102070500e400c010 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 201798561 1106 201797455 201797459
    0x100b031003170403050109062004120206280201020a182418260c01080109090510020304030302030a06060525140303041208100e0408070c03050304 65
    0x41ca0b514007040c4404404030320284101c2002a205035800955900c1404951000c602c51740603d804c03040d0140020440b07010141c13030208600c0c0c0c0c1120015907400d001000c07030b00c440c0000886001c1d100c042c407020100781d60301580248440d01107a200c1e100d108a044108000600c0c8501400c1200403008002c86400c8100f14a030007644580707400c002602c008001a118145101036120a80d882200328101d030345000711002c0c0e0240e03c29000080d003080c2f003400c0000b8002c6681071044c0c80302199100440b0090040622405007a040d00210965490503c0d0030002c2c00303500141c5200102501e000e0000813414050002c5403030480f051000c00c98540003446461440c01d0a203001a1817400085101e24800b150a000441c07144d48100c4040322a640151001815003a00400d45d03e06105000010b00881c8400214254045e9020b511503580d0701407032520000404441e40003c055120100300 = true := by decide +kernel

theorem cover : BRFrame.Cov 201618705 201798561 := by
  have h0 := BRFrame.cov_init 201618705
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201618705 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201618705 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201618705 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201618705 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201618705 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201618705 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201618705 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201618705 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201618705 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201618705 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201618705 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201618705 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201618705 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201618705 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201618705 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201618705 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201618705 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201618705 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201618705 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201618705 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201618705 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201618705 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201618705 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201618705 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201618705 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201618705 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201618705 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201618705 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201618705 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201618705 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201618705 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201618705 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201618705 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201618705 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201618705 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201618705 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201618705 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201618705 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201618705 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201618705 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201618705 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201618705 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201618705 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201618705 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201618705 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201618705 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201618705 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201618705 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201618705 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201618705 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201618705 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201618705 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201618705 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201618705 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201618705 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201618705 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201618705 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201618705 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201618705 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201618705 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201618705 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201618705 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201618705 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201618705 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201618705 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201618705 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201618705 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201618705 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201618705 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201618705 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201618705 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201618705 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201618705 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201618705 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201618705 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201618705 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201618705 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201618705 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201618705 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201618705 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201618705 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201618705 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201618705 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201618705 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201618705 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201618705 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201618705 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201618705 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201618705 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201618705 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201618705 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201618705 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201618705 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201618705 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201618705 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201618705 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201618705 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201618705 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201618705 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201618705 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201618705 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201618705 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201618705 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201618705 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201618705 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201618705 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201618705 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201618705 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201618705 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201618705 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201618705 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201618705 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201618705 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201618705 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201618705 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201618705 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201618705 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201618705 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201618705 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201618705 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201618705 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201618705 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201618705 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201618705 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201618705 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201618705 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201618705 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201618705 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201618705 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201618705 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201618705 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201618705 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201618705 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201618705 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201618705 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201618705 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201618705 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201618705 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201618705 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201618705 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201618705 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201618705 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201618705 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201618705 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 201618705 ≤ n) (h2 : n < 201798561) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
