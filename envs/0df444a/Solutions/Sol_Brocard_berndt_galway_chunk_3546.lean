-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3546
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T09:58:20.905978+00:00
-- url     : https://prove2.me/submissions/57066148-7cf5-4396-aa7e-078deea6ca76

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 637589928 ≤ n < 637769784 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 637591178 1250 637589928 637589933
    0x2070b25080106201606051c0b03060c0711060409090b060321070f1a070e040c09150c05030f0c0106091109060a0e06030f04030305092b1809020a1b110d 67
    0x405c0c500451250f00d00c1102440010704603008000b9010a554a80d8046d000101081002c4216000a0141989544070402142132452500010040d0500510b0314a101d90680000300d00e03903034030030703400142c44c29074490084051010082c0070b503412550840c05421810324403c00c0711940c622614000d04940700002d010781c01c110307140002c00508d9a0001a02002c02c0c0a8503004200560445128012802220b2070204528140c0300d02030760113525803242c81c421420007a6040f90707440111001d000740b080300e800c20300100301c0030006807034842040c000481e542c44203d80b401e8203450710380d0b210310a0182459405102e072517482c0251001e03a1803d4a01985a42118034110b8030050070030120354100f0340c008144a81000c10b62503107442540280c50a0105454100ca900d80d185942c1685103049200300b00701050034545101444990001860000c1c10300600c045e521010181c02d9118910b250350010b01000c0239908074101070510700c0c0b08200c00485005c603440b040788519500119522600000034007404 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 637592428 1250 637591178 637591183
    0x71e1113021603090302011701060516020d0609060b030d2609240a0c0513090f0f050a050912040b040e100b0a0c0b0105040608070302040903020102070b2508010620 72
    0x30501c04040190b0160b03030b800d010740001c2007800282d000074a42003180382c0303041109400c0c0d812100340d80d0380c079440e2550a0301c80d0701c0ba0300b40500089034006914001f62022031404d020300c0356a01c0c010280001d160741c10300e00b01803401029400000038400c00c500d024020901c00414403140e5401e14034030b0b03519035444dc2c18440c03c20b86103d051001600403003c06103000040200c00300d00c1901420001c102d0340c03100d0007094a950080806c050640001d1a03424050b86400780c0000210038194400418410b030620b851034103440c0102c800c0a19a940c0740e00f000784d00a030400c903003211003101c900106e03d000d00300701d15500580f080c1c0c001d00f070100c212103000c201c000c44001c172020001c0c082051a10b44818030b84100400c0c6c18420348095035030790f048200104091801d41310301c01c01c503403060340140041851503003400043e10042d8426000d65500748000b10100b0310070102c26200b0265105685450540d4482e00300203440032903c0e080400070808010310403140c000b100408441514120208490124a060b61 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 637593678 1250 637592428 637592437
    0xf0b150d11030f0a0501090911040c05160813060302120a1503080a030b01030e070f060e0612011503140f01060c0c091d0f0f0a03180f0308071e111302 66
    0x305240c000081210040b000e440c014002c3c01d240d413062099990310b61544098a140050183c040c144500409400340751550100c40380c050503060079420305030f05441c40c4c0411284000c0945e14802e00240300c0c5401d22b48901e400340070b03015509045080070080c100000c44244020904a40c559407142d02c0c094004810307080c07100443d4402180b81e60cc0b2150f04c0002c02078415030741494003190519040341e0700240045110030a5a20303085c1207080e02e61a16008550018440c2c2695400001c100074000307814002e03c4809000e403201c44d404d00c0c111600107000600311000e03500300c54030340c05224080c001d2034070480d00810704454031441c0075400c2c17851604005105580c0b95206581c42072401039101ca0041c00200080c0f0a44000010760b090003080c01d0580c1d481d82e01c50000c2603a1074000c07018041c00203000d0034080302c00c204090b031a0051355407502d4440460041c650001c0c3c0b028034021032110100b2111103040f07044052800f00b00041c1d0b0b07642e541e42e1000640c44c50146c510a2081b0880e00c0080c0300a581642c = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 637594928 1250 637593678 637593701
    0x42102100c05040305060f19020a03060f0e011a070803011214061f05061c020f1605070311030f0c060c0f0a1203110406050306041a04090b01090f0b150d 67
    0x300460603a07201c01601c1c9034450710003141d05021b0040000c08100407091003038072a103400d020350200c0304409121003000754003100b085010715030b0b02c446c045003246100c885800505a02460910103504000003000f07020698421080d0004003084008002480c0b842605d0450783c42c070481803541549442c000100f0a64007940780014810a010400c820f1803190348450f28102c240c840340c1c0c8242d00c80c8180400c51245041d5010350780c1135003042103106a490b90003040030055401e8030a041c045905030103920b01e800560181e407194450b800c14801d101c4079030030380360f084402100200b4502c00086c84090321800c044c50703064402c26000c06c980452540502202c403c129405060b40c041410901d4a110511050200e1100191902d050001c05030310307901c129130a8843c01d403562030540c3c0d10741003044060204005034941103c0d14800459094a0b2070146400562107180c2d08600c9604101079103048642002e4107106082c1402903208068841d00ea00f40307440d041040220760340744a0300c04050090030210809 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 637596178 1250 637594928 637594931
    0x115020304181d0109020f0315060d020d05070b09030c101d0a090e01021c0c14161e05010e0c01050d0504170f0a110a0206120703200a1704210210 64
    0x7110140c03d810f6222481031407084480c1c5100c85120014103a0311141c02c1200c0b0000e12014000c42c00da46007611258036028801044c81941400d80ea882c070b400d0040c01d501403005403402050540580c541032281c1040b014098803880d2102e443c200004101345141503624241c0c40e1142980c0f2002d440c1e5201e0440a4140c80c80c05006108000e0300141c002d62000c022480201d04269101418101500841b203150103240d407040340c044c552481c5515150b00108030f00d0040103000b0817100004c0e107040710140300c030802c01c8802e110806590500c54255242034116185030b070080b010302045603810034103407412020711140029041d56286011700c450f114110700b003044844003040b9250140882d400515041e241c036541d0703100c2050408012959000b44d240025480102800200101582807a19952001e0039160104001c1080c114000b000e02c182690034410a0000441da485c0c11b07000818400d41b03442c0310f04070510914080c1c03070703100440341049034803031a4518020210030660720030000705d11258441c180 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 637597428 1250 637596178 637596221
    0x1e0e0a08070f0504050609090604300f020f0604030f03090201110a0c03260406030e031b0709141306020c150112020405061f05131e03050105011502030418 68
    0x4400520242d480350703a105a0078240010030509018600b80c5c002c0c8142c4d40144103640325a620704c6503c0070201068401001d5100c0541c2e10f00d07031740030418880c440742d07600c880710078010b590b00085c24848000c02c0c1107182c2c0d00c078038107000000342d02c410fa00d454a20b0f5803800107104a5075200490b00d503003c103040d400300e62080f8007052041c00184508002280e200d8050315144806010007803440c1c0c0700c85d490000042c6810b000c2080b5003802500411001010207042da45009003040c01c118825100321808040c0d0750240105000094161045150710782c4021207041e4140741a89c08042403440c0310b14010001a0042070307103400340e1800c0121981c0762050081031300343c968603880800020301c001c1009178456800c08011072894101904c103a4041c005140807801e200e003511800365001ea115410595901d82c41380000906244c10165403c5003030f1000903096162450b42c180750307095aa042c1c0044a811210314041e01c0025000030407502100c40c2d0349175030300854015104090007003004800708902200c0b6041c = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 637598678 1250 637597428 637597439
    0x120607110a1a160c0c0e040c030b09010f0c05041a0f071a090d2a14070905100614070b1005120c10050a0e0418020d03050703020d1e0e0a0807 62
    0x140e54a100386681903c2046a1400c0b2004031203000404001803c214004401444105041c95a46512602442c18500c0d559600d588031603075800b040f1341003001655102c00e98000e1000b2030140d0982c54483e86000c0e0708141c2030018203034010024100182e413071400081c032401c050f5104019134018580014201000309140484412081d000f224001c546000d0400b000b0085402080380016000002c0c1209a081240310003440035156400420307590282803408410f01078a040100c2005030004003000300e0141001324100f0440181c580142c42482400c0305244481603040003a00d0f403081d0048114420394650740c10b41c0780203040c1600606d400240012074000c280e00005185280c5140aa036460400b000b5840116814010803500c000010340c0158440d010349000d4200c406104025030f8801018915540020ba0341c800c9144202d0101e0408034400c4c0034582c040c00310314040001c0d03041040c100c0c80038200360030403604a01d8041050180f281c10001c2140c55000a540103060850200d40d5800d4949 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 637599928 1250 637598678 637598723
    0x3030a0e1c0b0403020c2b0302101b08060d03210e01050c09012c0f0102031309061503110f160c0f081605030c01111609020304060605120607110a 64
    0xf120240d002d40700305264401c080c180540118540c0f0000c200070410031080740814583c440300c0329000d0f0118469002d0100e418881d5100d80304a002d100032a800080543c01000360464800504481c49000108410008a600015508501c041d17003512450a54109003540005004040e45054a90320780000c001240988000600584909807100070001c080800e10000e642d5099040b06051484400e0750002c1e030070605d018020101e01401980c2c106080031496802205240d44092850f13501c0703d10811036a024960110600099031030b041c09038003580d8869081c1403084006202c20444001040c900c40c60b48008088120303075209500610f2241d9555003007903902a13500640806000d9148a224100300804001d8112003014025255002c007140054600a10108841203607002e90b07919040142d002000b0000504401040180c80e030070107052803403c440e00ba4203d180588541a00001b00c0440020110303031004813440c107500f0f4002d09410003820103c07101c0004165902e2a1500107007143c24 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 637601178 1250 637599928 637599931
    0x308031f091506141813060b0d06090e0a050307170904051305060a140103141e01140a05040f060b01031107050c150301052d13050609060f03030a0e1c0b 67
    0x1d584c0310400c4c2d40044400c0b030341c284100c8088415050f54021a0b8000d400c1c820706484001c55481800a0540d6035600c0e0701c40290311140900076403655520052100b42840d04c134034000042c60100809501d50341e075603503030707580d1045400c081d0038041c0003825100b500e18020200d44070804064024032250424a80f400c81d4000f1140080b5603600a1200141e400416445200c13400c0c828038480c0c824903441c58903588002803054502c000700380240020705840d408040a1a0305020f000c200000d0300b403054141e20b040c4d0340382c040c0211404905080511020504d08034a40342000d4200c00000b231000c0341c0e000181c00030080000717125004000800d103039081c0400070030120920b6105403415451080e800c046e07070300e4a200034014907611100c060b40809040d040302800301c4001409114501c0900c400400166501030400c00c0140000c0d00c5108105081c100b94031140d801c00c3c010317034004803100f04550010f910382c05609074000420140700c0b9003401c07549d0340c804050403281110081040440c02403c001014190 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 637602428 1250 637601178 637601189
    0x30602120a020a09030305030a060e07020a0b07090b18180a02132c04030e030312091c0509010c0309030f050a020a0b07050304051011060c04060201150308031f0915 72
    0x180600080c410003910b008a80c03118401341d8585800c40c4c00e643e001d449039040a0040c600c0c207596624003080707001c801e0000034018846d40d00100075403101c40c541541e0b030210003407920742001a40b03803007000645414416200300c40e002a84000d0342300c0f40b40300400c0f0040c00c480c42100301501d99809000b42c00351303541d0042280d81031911208641c1502c802240440010b10340751001500e41c0c4252004604e600342c1e40e0950068424942407900506a50020746160082070074060000e8981003030000703019082000810741060b40b0218081c4060034ac501030054080c01e03a000f030521051702110340416100302010406554800e941c03055130b02260529550750240d11104a0160b2005031020444849a406a4174410340c460011032a080c24030083c05146604030201c031050140024016010180c00d000b07051040c11025000380c1c40c0c1f032030020002e003559511902c40c602c1c016442c0d028008201504100c2b90300a00c01c0d80c4d641041d020304121142100819400901712030303d401c0004501ca40c07030300710900c100d54 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 637603678 1250 637602428 637602457
    0x160f1a0f100611190f0b0406021201050d11270c0910090f050d14030304120305280e0a1505040204050609011d090c0a12120f08010b1e04030602 63
    0x5490707107000d481420500354000c0240c3c0c04014581110500d00c12000052031298805060683e004d94030f0441d98071b170544040307980d240c011420f0303a188102d50220600520f002c552011491010781c652030040100720041c54090304902c8881c040314101020b0307042c1c00d034100b210a68503d02d4151243c907095023284450a210b01c0011290701d541c10306c6020110203a075603140205007858689810002d540b0350601c400c6542d00c119a071040240c1c034090019520032400b43c001008060b00096006046403001442141905044100d40780d50a03c1015500c20540d14070304001010950303285030328039080e4181b40080258555402104203038005800550286100307440501582c0c03600e004202101c0c109001d01103a42909250005d1140496681300760801148002d0300c50f50041000800d02e007800700d4005d424941c5810201c0000c00800d400341c540640360615046030341c1a05554010300f0311806105809620601040004204104225030b0170301000c00f00c1d4407a507c0f6982c5c0307819000303074003d0104c168110 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 637604928 1250 637603678 637603711
    0x1d0a02091c050706140f0c0c060315030106050a060e011d0910030b0a09030c0602130306050109020c1002120f0c040801090b090607020c240c06090a1403160f1a0f 71
    0x4d078004c02001c10101d181d9030105051a508400212417074211000c040c825104203640407000351544401140100c00c07a5136199896906a0141420744415a10250150110f203008125407640721480280e05902403030031400d0302e400d07504148140529040c0d0154002d040d8818049800b4200c0381250881e40306480024660750f808240c2c1c41150220740c006000309620340034482c000382c415401000c40400802c040034050383c803038441c9822504241c00903a00302ea40041d2613262807108220501460b0b00b1380e203065203800080704501801120180046850310941d402103131000b80c41d01e00741c50207051400e00800000c541810f00030140d44081d59160344902824000c0791036184007084480700c02c04068445072050900b102407421141010a551114004c00e0205600c03900c018800355015240c0070006040b491200c1c00c00d059145410322a43d9425403040003203a0415044951214845410440b0600100707080d080c8001c0c00c0c420700b030f81b241d0306880034802c20410021820307540d8001c180d131f11620440c2 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 637606178 1250 637604928 637604939
    0x3110c0f06040b1501122c030a09081f0b0a03050f0610051807080603010905011d16032402070f121b0b190605060c0c191d0a02091c0507 60
    0x1404c0e030703422156001450726549184a080b042e00020b036101010030b80c40c0010010629100405518030080c00c10380c1c1c000240c41c5480d0f0ba4001c14410251201c48040e1001030395003034905690380a11a40c0d030744000d860f072542c60a903584410020700215000010380701c01c11540100300380c852000f200d040c14255070005007c102820181110403003100721059160054580c15415111803000500196041d900c0d0494032000880038050015280241965040c880c4078491034281030429854400241001110040012070100804801c48980c0c40a0094082400005e07050103449400707400303001503910140c0d8100f0400c2000300c00008117a071382e031440c001080ca2820106088ae807c18068240c05140b404541060001e60030110000d00d0071000240b015982d03c00316200d6004404001303855082024808c2d154248141441142c01e55107118200d59805d080e1480d1080c0480000700c80d003a4030040018800c0c54480d41220710040340144454035052206ca01240c1e03209207840101c403103001d5002c0c0081c1 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 637607428 1250 637606178 637606201
    0x4050405010e01050105120414100510060503040213050406110f091011150c040e07020601080d020d0f030915060801060329040b0403020307170c0d080103030f03110c0f06040b 77
    0x40e04d105a4489150000100c03003c100d10300080c1c000c0e60081c8030100c820901d04001c2148145200e024000410390b03180142e00094a00c016610280510400b0000c010060b6035100031030b07110302c2d000d204c0001c00c2e89660620070014104090140e10114002400340ca441c101d04001c0d00c003554084405d49800703110b041044403000f4644d040e624450340f01d54521940050302d48151035001200d1400302d41060303035400240c92203003004e86200016800034001408030040c03d0100da10320024900003002035800b44a0001c080300d042c8003050b410150b1f01c1d88510100b00d80c225000320300380380c2c00e0414002c413a1900e0700d8038000c0901344412203074030101d140c00180094418204840030802401050410f41d165140c00d215510014412011800104000c10008200c2142e0203810860740c2c0c456038403081c42003442441c01c0d440100e01e000340f190007001080002d034040310112448619140100703100042108000482c09003480221250040038000c0c4509080018864443c0f07020310304c0381c466504c0d102c10188 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 637608678 1250 637607428 637607431
    0xc07060f0c050f0703030e01090b180a03090603050a0209030d050306010314060f01200a110108010501031a0111030705010e01050f0c070c050f06070f0c05030708010b09130c0509070504050405010e 86
    0x4020500520810f0342046151014082c400c2c000d050200b64400c072800c00a085405140c01110340aa0100504c150310903017142122401d1070400041800325480e0318080c006040d0703881040101078541000400b0300040340c041c1c1d4035616014041750391207014441c0c0a481a0803c40d4a280000d18107510084446582c1000c90b000d9003025111207481480c00c0011607600740129004030001c0c0304401c070004010800c20a906a1500442515004403140303000105040c0041c1c0c05141010700304099174480e6007004034180100082401e001106201c4629541e0440c0078202d0090125441c18582400c81d40064014501c00c020408400703001c0e030340b02c07841c4d001a40500034002d4401045200144542e0070440c800744400c500082c462414401c0d030740c1c1e0344a42c3e0382d02610102c50884000c6000c10481c141040300001421041000744901d11454021494850009041e55044200c00c9008030501c80202c00c0c0c600a44006007600c401440c084501078002e900520174103014618100000450401070b010b460b = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 637609928 1250 637608678 637608701
    0x1006140307140f0607170403051507120902220609060f06080a0209060708030717070305060f06070204090501020a090807050d0f0305070c05040606030c120e151008060c07060f 77
    0x507a10700c014418003d01a2107040095044203040061a010418522000d030691460302603040ea00d506500d03226081c1514400b8003070442c400b00081c031694980154100060340e450400c001400101c600004000b03107002c003141900642080d40c0741d0030100307043e041181a42d80010040c481300b0b559080c01040060540704140c002900003000c18060050380e0000c09070504001c01e618100503840e02d61541c40d6000307448010110720864070310254500d040048035401042070400304928035141002c1003528030007218552203204001115421980d0755404081d010390010021034540c512800041c00a80d142c0c01140741e1803050301000541c0c1d1900500302c4620b258030032000c440c03003400e0f5501681c581d000b289040f900c803800004041381a4841c0c0c855517008110702e42e00428881c1e044000a00f0354801c0720304000c4110f09160303080d0755a900c001003010703003010b0003219440d00c0c0c2c0c1d40f91003010f94a0560b030091a41030090400380f1008840a04c003900700980180c104000c0c0b520646002811150b240f0000d = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 637611178 1250 637609928 637609949
    0x5070611070c031e0516140405010509072d032a14090d06090803060103110c070e090f0604030504030204050903090307031416030f0b0c030c090915031006140307 71
    0x180002100120746502c0010300c002d60f1350020700b150355010f041c412525a6130102540b500d038200b0400640d001d00e035110070b600303a500700160750400d0b000c5000c01500070030740390910901c408452023040100008901d0b2240703280c1070313100b600342082004001c2c04800140341c1c00c0b44a42030403040e1160a00640701d8070b0031100d86900384ac48644103014546508104069603000800030401e4021842c01c0c01000e401ca489a03104942c0d910f0b00500160440d6106441004180f0b420300c240b010960000035035074250f5650400c1061166255140d0354505a0205028a840c0c02001c05020402d42c016014000740c030b2088406101302e59407111003aa6038055071061941c90b80c01001c003000880c802c0460f014920040c1400e8883c071000d51400b80d051240c0741d50007142c4107aa400e6119003805004002d079a0131000c500a817900e982812041001c0070701070140c1c058420b0740c0d0f19000ca50b0b01d21568103d507000340b1000c0c0a0342e55600001c40000000c00051107444400c402d140510b200529020403282c007540c280c02ea4 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 637612428 1250 637611178 637611203
    0x302120c15010305071518050108151021090c0302090411130b030c064008030c0111030c030403030e0a0212010b0a0e09070314010204090e100f1401150e100507061107 73
    0x11503170610080e04a06128010000d070305419150f1107a40075200c0cd490b100c903a11403d12001140300c07201400c03440f545640c604944100001c4500000004480d01203900d460741d82c82c4d600b04180407244800c40d03140e0180c03001890701c4076004260030001d84d6034001c42c141d0720040300d1281408030a2003050b150110424a6010f2181030001540100d024a034254101a104c21946a02005100358640107208a984042400744683d0400d00171440312110310206d0354254103020450540364040600010145500c41c1080401d2010400c800551190010115010b040c500c442990081940c180082d000d03805100b4042030908480020780c0c000e000240c000c1507080e01e103444a05211001600625242d5000c02000039481a079004401c584030851000c2d001142090345101d0495060021401342e0504040c0d0354207130b07003280300c1146045030700d103203101d150100c03144508451103035000c0754444d80409000140c6007081d60100c0540411445280d040000022050003403000b4060004014074203c010b40 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 637613678 1250 637612428 637612439
    0x1203150e0c03090c06210c0a0503180a0606030c050f0901081207060902040615020706020c01090303050a0309052a010c15150f0602030d060504090302120c15010305071518 75
    0x20000c42c1d200821000b031303840080e140e00004403654003800c420b00010703040c040d2201400c007001c05c40daa0054241d0a00b680380c828081c1003c0c08a0000828124040001c0e048002c07109105100c0c001005900040c1040170070b84900d851020540b050003058050706004030800c6403810441d03101410398007418000c01854901c14080305042e80301400c110341290700d4419190058442d409a0809040140c5c85409120342c2c0d410000d02d40b83c05684098110740c800c154104a590300108103206680d01480d110b0356451694000764040d0464a400510368482c0c2800d5003182508640400c020080b035000755901609440011907600d45c1e80000501040a01d0b90030108101c0c25502500c5e003545c400e4100c544050f91003818484014090740080056003000a80d0a000800c51007403002610040343d0400c0f1202c103d0700c1c025a42ca2410f0303245403540c0030008103404003003410007140b1400c0220b03020b2044550f860b448d00c180c4030920341c0314401c001c2a900207507600390340c0030b46501c1291740b0607110241203007850030 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 637614928 1250 637613678 637613701
    0x12010e070309170301060e1c0b0606040e180c0a062c0303070b0603190f030809010b0301180b0709060c2006070f031e0f1101020904091203150e 63
    0x3038040030034035507144a100000b84442e0010b5444401080c9026200d41c58064050030140f2858681442010812442c2d91200043c0e8110b840c07440d00407403200c030940d6900c00410304610030303900442105006482081030031984030400c0b114940b80d00b0300b03984031030301888180018641c0078041c4501040420154054105d03000024540700000c40c48844203400503540468110b0f0300004042c1d81105c41c070001c0000307604080004042000c0d5903403d421203281a41c89131410108858402801c00072240301041a80c4825042811003800080080010014245010b110a102d40710112291455000000d466a000c0c1d05964201c80c1d59403901d42620b02190755034044602c03080c003128440c0c038641243d540a03031a00005402864410102c0d601c200c600c5040c00361001c200b102e01c440e800000700b1180400710b0f40c407035400a50000710b800d10510902c0c2d51241e042c0640114490990001d00d000039110a05c641c00c0c103075880041c004d0300c04000510241c1290303105480d40c1d0061300d0345d0481e01d00c007103094000d90 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 637616178 1250 637614928 637614931
    0x20010902030d0908100f020409020712030536010608120d20070f03051e03150d020303160c030b1e01060518090705120109021c0902090402121e100c0512010e 69
    0x101b04014a03164031910703402c00700d8101d49419a00d510101001c0500c003600340c8101c54000c803044404003c0c20079542c980a0015805100c401c01044c4001c03c01c00140b8400d41000018007102415a090961103074195100c03600942d80303034010b082c02c0a106003c002d415500541010b54203041d601d00c0c120890b111954015800482102040010010007255015446010007a0f20410423050780e03034280902c8130502c1b00880e0310750500c46d02d0442e10000042c0d4002085401905428001c600351243c1d606040030000309592014100c820300c4010494007602c0d210003411721410142e00d542c41641c0760b801c121010300a581d5800382c0300640144003040c034034000044c40d5100310149481e51904030400c8040d5a00c0c3c80030b03406101c4064011441c5a0200b0060103000f9444444000030080050b01d600001c1c082c039006030003c0e025442c000e48aa010150038081031aa01083c040640441c001701d400032a1b03a150b030084800320591900103c81d03405482001104c0600c0403ca5811070541d0800c000c1e031800a20 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 637617428 1250 637616178 637616201
    0x51f0e060f010c1a04152c01110c01020306040c1b0b0c04080a060b03011a0d08070807020d030924080a0e0f01060b040503070611190320010902030d090810 68
    0xc0020100013400a100004110401c009030540b64145840c000d0b00907118103030803c9142e4189101080e0301f202520201d08016080c0624802c80d400d481040783c0181200825000210340c00925040d0b8078505400450041c50240c4041001c2200721004450340c8600106480005829498040110b15070101042e007080144900d030b883c2c541d032140a246001c0e00c1c407204a50040d12414136104901d02845244841c2107403414201100d061800011001041c28ad001840724801159210078409200d0655204940c083c01500700c2d604982000381402000b44560400d400340d882c40100780b0058116035040c40303d066140d00810742c0719100100b014000c03820340310086204244a100c1d00300b00900505004110540006a9a03410b140a05050108a401050a0240301400210130079030000f080c03000c1202516841c001030740503280440b14881c1d1042e119030601d0382000c2e420300340c3d2810f43c8000c1c2080d20031400c44041a01118003903503100314170b202eaa51035402520341c1410f00100c036008101280c0c03 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 637618678 1250 637617428 637617437
    0x9030a0f0509122503020303030a2301060f17100317040504150e0901060b1c1103011814090d0f0903021809010c140313080702040f021902031801030207030e1003051f0e060f01 77
    0xbc2c03240600400001d901140000703000015035032810303030031a8424492000505140043d40744c030900d0382101c4501440002c016160b8488410035000082090764040c0400400c244044114462101080d00950185101428804010501c1341c1414806c2c00100d804c0c4a50342c6040c200a4024100600340c6548080509501c50100d00b01990380c41c00194064802c0b0742d001041d91840340c1c3e0301012211800f400d811504880b00900050030b0300003802c1d40001c0100e01c1d002c2006115200111211402c50380001d4000045030031000c820b030310b00344400f40b0030798011000b0480340d142c8401c2115843e00c528aa44410101000810a105032010302c0c41c4800c0d0245031140c0c60103115138086001c48505140d8038604550118144401c0c41d80142d040c034212145100440c1811300249000c0c02c01c00b0203800280c1803640c00504c406c20540161500c0070542c0d80140700964071025464060050701d02240c1c80140c0e0405641100c58100c0040e1001c0c3c1075903071640c003101030365560406110314584a82e01d09410710 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 637619928 1250 637618678 637618721
    0x1903061d04060e070830031605040806100614090109030b060d140a0309060807170604111207030605121908090a06020f070b0309030a0f0509122503020303030a 70
    0x2e0104004007002072801000418024000b110046c1280036100c0c1c02e600e00b280d0740c00403245820f289800f900e03005034000032540040303040054140e5043c8030b2a07000700528015641041507483d900c004e484101d400644828501010400420701213105a0b26800e010442602040c408561001030f0580c0c40a006028203130310080755203a0101e0a145003c0000d2960b2043ca10f034810190310011180c000e0880303080121540c1410741000d41651510050052400c40c241d0000d00c0540d9135400801c030b180d109000113659146415507141003004202e92140100c4e052007000105418400c41003800440ca540140c1103032102100401e004110a00c0d056405000c10f01c0001040e0791000340c10001071685400400c039004450070418100301e0584d000c800c80744030a00030400004404803c0780c1c1c45240b00c1c178010240701002e01060740d2500560041c0340d00840d030307034104034284e10740041d09030310817843c4107401d4803091f54030141c05400400902000313402d90010300c041030b642c54a0f50880d240400c40c41d41004a030 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 637621178 1250 637619928 637619951
    0xa020307271d090c032b02150408030406050f01121106090a1203120c1d0109080106090f0e0f0c011d0607060c030510240c080d021903061d0406 63
    0x1406004810041480c0c140e90034842c0341c0d20100a08114000c0c03c1d0f02801e001c02d6034019030700a444481b80c0c07220210b5200320b00e1003d484e10a0101c4601d000700752802c00c400c0d087c41d0030400010b800c00c890445849240c0700c0403c400850500c0050704840c0b54000d14002c4444d242c8d901c6051280344a846134100c03c091005a1a5664091400d0302070b00d48803007101548006030030028a11202e0141d0070420030b180a0151540c654800140c08901d17103140c180b003800b1106040103c48820030b60380149600d5203000d1004c1038400c250340140e003002001c4082030094000101c0c0f0070707032104a014000b404c80d5000c030070b01c2c40065001d00122002d088454100030302c00d20b4802c01295950b031082c40100d0b50a039403840d9034252290035100c5c1603045800c0643c0180381c141031135001c2c0074164038400c0c0687c600c01984401030003039200c2c54014004643c00404c2640310a40e40900a0181d00426183c901d4910480040c80d400c901ca07208c0d040403208014590b03a0b0405000202c0c00c000c0c070000e8000d94025884201c0c0455 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 637622428 1250 637621178 637621199
    0xa050c1b12030c1e0315212a03031603080c040801150f0e15060c1624050a080f0a180c09060b0903070509220f0204050a02030727 57
    0x401d191000500f1381d00c01d003502c0340d0a40c00e14010f2564003101c006005000c00590f240c241d109210100759160009285011001c408007000ca240000c2c00c2d10070504d0303a40c11811441e2080120140412203200f10005030380c100340d00c1e8042d070f4445802d203040c65102c0c02c3c00b1900c03034083e81e1380188500b55000c0c43d03e526540700074203481d10542807910b030344122081089200510030304da40041c500600040981d052252203050308a203520a0144074580119800704181000d10148000c803ca200002c01d0300ca42c5e0300440d101441d221116001c02c601006d411441d910b000304101c500030b0340c0c1c5944402c0a981c401d0101c03403180c4130142c11002c04513a03d00c0d040403809400042003c001e800380d4502d95019152440c0c01040e0b4103144c0104803120401d1010f03440c1502c0000e41c003c2601c80c2102c00442c240d6174009280610860081200300071304d11500e01005110b03e83c00804d502500035541809241c2d0303680c0201c801c2e4841901c007440000c00c1040c00c080c0b4840941580b0800000c030070207080031a40e40d06400c04 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 637623678 1250 637622428 637622431
    0x913140109030f030501050612040c120501060f0506161212020f1215010c0206160203030304080304030e0a230109030b07020102040503010b0406030b0c13150f080a050c1b1203 77
    0x41030795201489014940c000041c03030240300b400d03d014012581400c0c0843c403940a5008207070652050320010600300030324082d104001d81002e5042070400760080c10714034041d1000b031240c2e4140c5501d152010885090000c100c0d6601078070000d542c101045243d40c0c1842307006080121508101c6180402030102405000404a11018504ca00d41700c5025a8a4841321100a04010521115018545a82d980064024122540403510180c440c025000c07513805c0f100d0058402945400300100308010003411001550113a406540c035441c2a902c414103210000295024a0ba03d4021090a49108030203008180d00000300600d002c030100d5940340d4508560590664028026035004601440035080034405e4004444084909210305451501c0e42030f04440064280300c00000005100d03a00b600c0320503043c00082041450b103104505200000070a00c01c1c80c001d41c4000103440d080802d0702d40c182402010f024103280d2190900d0202d43d1210086040700c0b1002c001c0a6004030004008440b02c98070146 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 637624928 1250 637623678 637623713
    0x7150e0a12170d091505040501140402150a020309040603030f090e010e0109090302150f0108240f0c130609051f1205070903021e01031b0f0c0c150c021014090913 71
    0x111b42418035250040c00c1d1499025040036080020b000c22015030b0f240030801c440707202101140750741c5410000d02203056220303d0006582181c1003544c004201648648040c02c6021291740e140e0b85140c5920139018101820322540058615190050040f10900e40c40000351798400e004854204801030700c1c4168030300c1c003100c18600704c0381c501004016111007030017a500101c9541004141c41040e100924a5000e400b800f0400c15050100008810580b03250844107060226503598030280d0b89c5000c024408011401094040c0f98054884400d00c51390b40300712181001d240d11001c0c1e0068a1100000080400500e001c080205128001001d03860b0300028880f804007621b030341e00e00000030000240507940030010601b013010712103001100207540b010313145407921000e203000000402c071801c004014000c681c006e880200044180d04102c00d40080a000b010b600c05d46002d2921351100c1816142d116900040c01d001c10400c00024010340741c644101588070020b0008481042c000d9151610f0001e61440f11 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 637626178 1250 637624928 637624931
    0xa12180e1e190527150603030702090406050702030c07080d031803020c010e04060f0905090c1f1209080d020d0f06080d050903010f0207030c0302010b030c0d120207150e0a12170d0915 80
    0x840b1280d00908444130342c4191b080d40250b10340b40e410f5011464215000304040c2505030740f803011130300840c820b00481311010306410450346480e464442642d1114160360070000460b18008103041c0f40c40d00c0c1603100c80541c0d0542c000e0140180c02078015038407104242070131036100e40e546002244544201c8186005485101400aa5882d2070603515151a03450708015220705400c0080c0005001902042c010040081c80c1c0007607054515030700c900c042c20182c04018500e0340d0204482403550640d9026202c058040c4030244100c10b420082c6c0000c03120302e402a0343c20780c0c00030418010024020f0700107040380e81d03000d0000581820600f1001d0120307040000110001a10380044900703040e4240100802c21358200c01034030301f0356a000002800d00054010080c0b20798140942d01500034005e01c84400200003000104040100001001f042425003c403e00d2141603008008100b0b0409180e0a45490760300c102951213900040700b03001c006410184540004949690f402c40000ea1803001410124007160780 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 637627428 1250 637626178 637626193
    0x606100e030a021c021c022101020705010216030816140c0c030f150a020c030711010509181008010e0a0206090a0b0d020316020a050a12180e1e190527 66
    0x4000b84135540e65a06c1803e03580c1c0c14180030141e621002e0914507150b01e003d1911083c0064108240a8004e401c0064031075440030815800c410080342d03c0c002c0c0c1030311a94500d0019680c401c480c440071000c0000c0f000000d40800e00100350142c002c401440441c980c1e404440c1d2059654001034034140e403000702d0803440d402944481040c0c2c40154061500044042c4040d400c002e01098926602d00880360050440c14401c9100040c50740101d04548205101801e801413116614108228000342030303402e241c0440c0c204200081180d418440c2e1511909400040c084508058013044070075000031054903803090010030001210b0503810b000301085694042d000d40c5a1903d8075101b511013034046160400d40d0071030800580084e6010908003251680640c100545820724201100e4810444081c05044410039102203600e030420000c441c40340c0d2010003035150040903942c00341d14244099a007141007540d402c07034451141c3c0b103079001950701c080c40d0410103c168600c0e100030058035000161020103904680d0 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 637628678 1250 637627428 637627433
    0x11250b0315042003060d0201030624020d02010c0c020907110607020706030c0504080d0327050105090c0a050901060c110d0807020906010203041d130f0c080606030606100e030a021c 79
    0x4030440f200c141040007004600f0328101c0111840000d080740e110745801180f080c110fa020f940071b1005014140500030380b02c0c0d10200d00011030080e40c84203802500ca26100d2525640c41405801e0090b490f030b42d42c020900005500b4000c90440150601c418494592542c00c0d0348081000050302c42c8070241c2c02400c0186c581680681241d4403000d100c4200841040140002c1c800040d480100180d07510b000205030340000040500155409101d050280d5035080503000e110054119030700032051181540e0742c2c102007008100009815208060700281540c00401c0410b00440481100c603024031512800b04507a032001a03071342030840380300302d86074000410400d0070350400b800c0007a44404280015071402c4d00700009031040da4061100781505d1440d032800a4041c0710f0441d0003000e01030b400300528070041c40314a081c010a00441c002c0300c03914071803480010824540040c1560040c0805401001c0c2103540740400c0740e2903190841000c1d003501c18880c090006031101010f58801341c800e00705040c20240240f = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 637629928 1250 637628678 637628681
    0x220b04090f170711010c0c0b1303030905040506011b0c120b01090f0b060301051903081201080607020a11120c130f0c0c2a090f06031211250b031504 65
    0x18001d03440c004424004400020290200c50003104d000342042c840c0d406a41c03800d80680c2d070701500002e180803804030301c0c0c0e40401d0383d1a03001e42c01e0700d00c40d4450700f400d43e80b944c0501c41114070031551140068594506412084414030942040d14014940b0100d80750f1070381d20382100b850740c9607404c803410030461004104030f00c17042c4684410011070480501c420b0004400207043e0f40018082c543c814004820710000007541808840300466014a0090b250345e5109021202014240304401490007208001680d181c80400c0410003141e124201d2141d14100b141404003078a90780454217228030840310781700d8150f80c418515019640e4000c1000c01c03001300d844004070a035104810000b050003105401c03280055640550b10b280c0c1680d0051401100c41030f01c11000d040c81c401d6001d40ca1642c07402400480301794240c1c0140040c4d901035061080d40b04100303042100d118030090a201100c0d04084034a41e810702a03d86007034030521140d0f83c540c082ca5264624110300b035009845003030340f04500e203c0100e5542084d = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 637631178 1250 637629928 637629953
    0x5010504030e04270213061809030f090803071707051e07080703030e060309070f080f0d14070f0201050c01020a0203091c02030d080603070b04031101030b0906220b04090f 75
    0x24800840e951011036814a446804c407210000d219203411180000700041c507502c10701c02028420a502d1011080200030801041c80c0d0381d060300000e160b2803000b140c4500840f070881c00c403521321000314a086142e440d07211220714010007080c0306d1b4400700112400f04104019100f0b02c90081c0040400740c1c40b00d440540d140c01416404500715400112041011903040031410741002c9054502070384e240c0e50713102480c0c20061160040c02890440c0d5001198800700000c0d003440c8030019a00711407441503008003e6800415402c100c2c0c01029003004a00c00181060040e96141c91042c10401d080450203861385007a0303004803003c2001a84003298152641c50480340c281c1500301a44001c00d0b90441513001b003602d0302e0340c05d0010303028007180d0300103c0c2103502c04200b41002000c00f003235030355161600c0f032610b10001d9640ca03ca0380d00103420002e08075031626100c40c079140281d60040544040031320a02c24040030303030b4445001c6607043d03660f428071950984990040302902071140804840d00007031031a00a00c0b20341c5 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 637632428 1250 637631178 637631201
    0x3090b030c0a0e100c060b040902180103170f0304060207050f010203131b061e1107030605090f07051c0813090501030203060c070812041b03030513051801060e0d05010504030e04 78
    0xa0b4005440b8134150001c00e0151910f4104501044108142010402801c6240e40094000060540f800140d0f240b49060074143e1b4400e44800c0c150019464011040e0700904036440a10a03040000c200050340075402080032900c100103a884076003c0f481c0a03400c981007281c4c01d0901d0350032090a00c1c10403e840c0c054110141d1000c3c03c070480241450340c020301c0c902c080200191900a07006807000321034000c80b4060851000c4004560f0855103d14101c0c0103032200b62042025440781c0342503881980300100743c41c400c0d5a80070b003c404021042c0d45c210104030760000400c0d515a1750030001868104240114000075084452000c20310703514610526140150003007414407807820501c2800c000698140840e00249107103c40481d00380c9450403c0003d1072003d0a071a42c0d4015081000810540c0100152002c840380c0032520621966034030a0081c80b421414203400c2c6103c81100501c41d0b503004000e03030901010050804400e1491540d90301cbd0859405460950103c3c0c54810a148a45098000c038034000c2d8 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 637633678 1250 637632428 637632439
    0x1d060a0c050c0316020d0803070c060606080601021c03020f03090a0210090e0604050a060801023603070b0d060f0e0f010f05030d201e1203010e0c0703090b030c0a0e 72
    0x30035020880f80c0300d01030b0f010b4002030700d0118081c4c1303070655440501d696449500181030741c1d5a400d040d03074050b042482d4040110b40c164144140003420318055994140310b0035060f0050000160b44070010b100084000d41e4100600d58240000c84006404101551140c0c0120004002079001c900411102808a840e000100180c5103418050303424406445a0400000d6030b0120300343d1600007034003004e08401d4118400d95840810781c141d1850784030701680450318022001c0100560100015842803203442c0c2425010341c42144200700750404000201084200310100181444d100c0d02d6050b81c00b031085d807105204501920034000d00302c01e140001d500400b80e2402c00b42003545040d001c00c1c0c490103600301c1181071180c00421403c90103108407000c0c80d5200c501050f1443e045030b00740300d908142404e0440b040244141e000d91101c81d80120210b80c10b8640a030360340461a51191503800060b44201c0e0220100b140780c400005207242100051030240b56051031140c3c507042c01010050061045a91052284 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 637634928 1250 637633678 637633687
    0x15050403270801050916060c2108041103060105030a0b0417070305120108012310031b080f37050303190506040603020105040902092412181f1d060a0c05 67
    0x54092482101102c8640c01e00188d1038556091141480f10503500d034254040d181c040c2545020340c08800607100c1c0344502c28180d0340300000c406150b86d0f4a0700f400384035010b41c00071800a000c54600010701ea4172901c40d4078140900001d141d25503003150007504040300070410203d07041e1545004000501d014142d00f9008001d54241070f050440301200380358191691200c250007150074101116416000780d9044500700552486610825a110301c983c46144014007441240e40089007020400807004418038108400c030030361010b0324808840115000c2403043c202c258090000030018000781d0f101e0310500754075101e9003807003001d05000d490005141510444c0341039002c0c00141c0c3c102040c0d42c20744045c04401616400d004010a0b0b00c0d044a4499001300c031848c2a503c48007038079070001000a0b510403104801191104c2d004481c1800e80044940301a40240c18004800c2c000c2958841c98140e000d800441d1046030414240014856000c0381c0080c0d400010801250044c5400b542c1200f012510740305281 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 637636178 1250 637634928 637634953
    0x6010f020615040e101505120c1e010504170c010921080d02090a030602090f01080c04051509041b090f08060114030109020315070e0d150504032708010509 68
    0x800140264030f0b00c51551000313645240801080f00c0001c42c28004020010750b8005401c10900f80210301c100303071040c50452140c500401c030100d1520303a5910094101c0004802c29901c2100500c1d16000ca2810401c052000040030400a45800680c500c10805003484000050006080b90256081000f607480c1d010002c01d0302c1c0c4800018000348603004405141c0307a0414415400c0a8801c4040e5030307901c41851a0084140b083c268000d21800904072501a070b51281000152a504402c544440382804180000c00550400801e6000fa04040c00b19451a0032004000141151646100d581034208a800b58000468200401074090b101c04841c4820440c0f0386401295a020140540311070302c0007591301030800362003d4000c0a1901da000301500c0040c0202c0104403a030b62001c0740c52000044070b0400c199910308001c0612030340e40c0d4100c1c0341414201a10344204020304401340040701085501040b80c184070341000038401129040c54103c0b180c4038506036086080d00c03005800461035802a2400f480d1 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 637637428 1250 637636178 637636201
    0x61017040b040201090f080f060105010f050414240306040605092205030906040b0a0905040605060a030b01170a0b01030f06060801030f030504090606080403022b0311070204021206010f0206 83
    0x14419842003a40c540c0d40c1d910720041700d001070284d00c100c0008071030000c0070582141c0810f44580d203182d2001210b01613a80c1e240110780c0020100c001c100840d00400060169000303c034030720300421f02c000d0b0100000c03004065241d004070301021b500400c0d85002105000041c5450700840c07000344400c0b1f920001d00d00b01604a0a185a40c00c0e41c1d0070100d0202044140c1005414800d840454200074202c58035265201c002100da41c0c0030f28426400a992004089480e2401e4420f1105494029104a080010001042d0001c0c2600c80c0d105040c0301c0302024442c074481e603802c082807048850210108000b241c2034000b41c26100c030400c001c0001411b2510a110071540812601d04481d080f82045e00094502d0030280d44c1c0c0e1050350425103850b820185c0c04100c807500003445038001c62003a802c450300b0b602c048000e00c4c000103030300760f0314400640c01d0303100301c000f44c0e2083e0820107407036032000041c4d403812105038000b41c220b0b03101c0e8018140e580c1c80d02040245a68101d07090f8081c15620307001074803403031802140414 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 637638678 1250 637637428 637637431
    0x60e0312031f0b0703020105040b07090b030f1504290901140103020f0f07212c0103060906260604080406080703091202061918060b0d150203061017 65
    0x5001d04100c450003004000d10b900746100408034150702d10342c0c440702d07410020701801c011582501e10b07444841c04542c0e1544640113a20803900407060540c215280c0c01c07818100040b001d01784d48001c07020035045540c41c0e501e1b440703004160100d02d0a00410440030384240c0d8031204a15480c07502c6013500800400184441800c866881d030300074a4010b0ba21458441892980d008444103054288004a0a9810404031320760307581c031801c030010000e200d086420008550301025010501c4c0200107a03528080000061b0541042009050602240c00380d21408504219030180e4480202f5214412114039072512250032034601c200d000005c0c280d5454a1340351307200035110342c3c81510300700210100003441b0180f2030352020b03880aa01800d0203140e081d10003002075840304241c81040320b4084c0ca207071040d118010351040203402c026189190030b40d024951100030040000503201d54204400c5030021000034541d00004880420324440140c49041c05828021030302280440c0e9402d0000340010310500c200312124a9 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 637639928 1250 637638678 637638691
    0x1a19030c05032a0d1e0506060607110409080c030a020106180e07030f1721070503070c140f1f0c0306051804050f0d0f0206061c0311010b06030a06060e031203 69
    0x1108000c0c44200424004004e041d03003e05005107100074503104442038659030340814014000c84007076480d005c081002c01c3c801d041c4020103400403440001070b181443c1e0403403229580948812400c0c81404070700749046a001e80f1020300180d43d40c01d014400302003c50080001c9503140d590404c6400c2c90701d040e00b41e94404074000030344407100e034441a4041242016201c00000d84040000d03461710442c491f9140c038203041d0514100b00f10f8401d400502182d01c1801520705c1a4015558041d925401c1d4852825040c85a40c1c1181c10f4090301c1400f0b06075220800510010210f10a103181c0c0c450300305d08038802100c46074202c010800d07080920804c03107590b0780d03100d465450024803181304058445181c07840c54000703030034030488450064031514260305030040c101139410702098094403d03c0d44c030002088440d1500585c1d0015410601c55410042440742c0c3e4bc0c030210001510002403807844400018215400c1181c84030550f5031140d8081c01065400f001010395800183c00030122001e003410301d20784900008042 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 637641178 1250 637639928 637639993
    0x20304170102130f0513050907061d0319050f06010305060a180c03050c0a050307051507030527041406100e1302120f130503030a1a19030c0503 63
    0x8a04034410039412208004891100c4611860b511021140b015800c0c3c0b00e0584110300c04e10075800065524001d072441031003000060500d00741001c00030b5541400ca0310102d02406a2103040b150395460030880040c5001c030402500f1166805440c02c145402040601d42003c0d4100c00c0040000070800a0f0954100d004180040384008403210519030400300c1306000782400b0580c003000400d0007408a000301c4400b0040da580b426042e02c030814565a00164816640c000c4010600f8103600700c0c2d000c0c044d0500d5882440c0403450100d014444110030008041c01d40b0802402490f039a1003440c1c644038901e807082420300000d80a03e01840000ea2440840644800b405074041c0c40d0101c43d40c400c118840211403031001152164284045070110020441d10748100805000111700c1c0004001c03407004050781e0081c01107180d95102070b0940b01600401c24196203e051910074194555144401c07021583c001c490880b02161a42c184800f5504013030b0b00160103a042050880a1405460007941000000b80314 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 637642428 1250 637641178 637641209
    0x10e0a030c030c02220b0906043b030c0106090c17181f0f0b090103020a03030c150501060305060a05011805012a0f0b1501050304060c020f1b09010b0901020304 70
    0x11902d002c24032000e001c01e40c2e221405e00c6485d0010703940b00e82c403600d005486140d441c1e40c4040c00e01c400c40ea8400380000c184d80805e013550903801c10356290703c0b0484007a4400030310741c00d40046215246800540b001c5072240d449135420b200c00c1d1050b2148504411541c9444c0000c0c04c00c4181c1c1e80e05004001c1c007c0071450804040790400342800704802c411000030f184040c80c0b07601c3c1c1005034000800c0302c07034080010642817103000c61007440d20017203a40c181c9400902e0100801d01c1e40d0f60030b45100000035011600300c0243d41c1015241c000921440e8000c21003503c01284900e0302008024607191160004c905010100b503130244440f4012030940c00340d403005e0802c04180c84041e405e102069036102540001d5446041040c4200040303e950000c04503c241002485500c03189500344401007089056030002c2c60600000c0c000c00c410390481040b00302240140c0d654442d01d22651818041e50700006030004800d09034003580d9083c1800d010340141a4083c4032801d060020703000070744a02c528454140706000111 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 637643678 1250 637642428 637642433
    0x10504020705160f060816051204151a120721050309040e0a1406010803070f03030212040c1802031501030b011e03150501020118032102030103080705010e0a030c030c 73
    0x1e2840b41e090321107804202968483e03220040841318012000001c5040001c902c2c0d442040c80c1c1208105450f071030b09801c0021010034940080c4008005584540100211540540380c0c1c0c440c9140d00c62a100541e065110000300703010011200b0110f6118540c00440100b201c3d08141d9541c15440c210f05481c00e28840080c200189940500b40d030142d84240313400500110710100280c244405403060007031003008041e0810645c6c54a400740700b0144550020044c600000700a80b100d48d07444d42c442c0c1001424142114146a034150080b20110b540403c410800e1220052140d0f110354000c07400f0109610b9490827481100300004040303d410b05150b2920758205c0a41c3c06140d180404004a505c400364440c010500200a8446143e0b024800f41c0208004296540306001e140d54064480901784c1d0202400c5d17508842031004c9180b2580f002d1030007809000c2c1c0c0e2245000440c002d5000e95901d0342c650031030307040550844021110740c3d00c55a01c003400800000e07030010710450791241c16003080d62094443e030 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 637644928 1250 637643678 637643683
    0xc030d0f030e24251b06020a080703110c191415070e0d0206091908030d020d1401061403100b0f0307080105010f17090705030f03030403030506010804020603010504020705 75
    0x2c01011490040080b140d90520160b81c030b882c0315205822040642d52102e01420048480300b0700015521034070b040c11180c109000d02c0b1020700180741545090700000d07558541c2e00c100e0b080715803290000f8841400b4000243d9150140482c402d400418886c502030300f29011720358030b001440c04400c01ea010712003410284000c0844007240b19811805440c4c43c101403244c0e02c824090b017100c00c140070030004c0c2d00081150910644209600740e010740b0482c600b061a0302044801480007850301d95070b0708003040c08106441c060010304920b6541c4580981c80d5a861096601903c18513440c02500b0100b000041206961107248045560b1801e0009990703070311111070480400c03910f034200c44581c10780003d20521901c48d460003144909400c4c0c1e1000b415903240c0004448031741011034800300080c060101b070030705040010101c607003021081c070403100c1b11039843c000b090500850f60804031103a00007008000a154050045541c0300c00240380000305442d0590002c0c82030b0006004080c0203070382c042191070400104 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 637646178 1250 637644928 637644941
    0x203040512190506011706011406090f040c090602150f010b0d02040308120910050f071d100512160f05070602431115070606260c030d0f03 61
    0x303800b0440100c00060034216a908401e04c58400d1045401441941100d40450164180d5039980100b0960407420380c00c100d002d030000c0003440e5003c00d8140344440c00c0c0e80d47d072085880a41e481e41313401220303d1401002904003041e041446030b4001000d010044a00142502c16054411300b090780784e01c5041c940d41c1c0748020300032500024047e42000444151008141010034400c9a804044960000c1000700080648800b81c0340c81c074840f404440416242c1d4041d8011090402491400c5a2817030328160004200b400f01843d0000400c0c000242d40040702106081c0540c050004501c1000504041c0001815401c06d00202c801304180402d0420030032019404940e80850800000d8094034098900142401c2d600b092920485031400c107501240c1d43d59032648684250014008426440e091040c815102d0151010b6883c10508001500008101e482104080d00380c0170401c80040540740e01c10020b0034514604c0803580d91042407064056035000548100c3c403a0359142040f002c40314540180c014118 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 637647428 1250 637646178 637646203
    0x1e1b06061215090c1a0904020d3305012006070e120a0f0b09010e030c0102090102062211030c0a180c030207080a110312070c020907030c0203040512 65
    0x404500041c0c40902150666150b40110b0b110204148490100b07412210442c0700140792a07103e641c00c222101c4250720700071007203400a959628058201000404aa102d4440008101d50ba160a10403171240088a910340c45145402c6041800801d019402164010300c641410003000c680b200407115681c01880303003224140c00072030300356003400b540140121411a0141d800784024885d0003407102c0c00000d4210309244c10000445009a4507291220850401083ca00c1259220380100351020001c00003000481214400143c03207051792000242031840103800d440408481c80a03100580d0054898040000c1d0b01c1a914107a051070300d0003080c181441d026140d684102c12060018081007000d29610303014800c1c0504000109541a0035000c9015890028160034001e00a10402c20701034003500c806c04c000d007001c0f68106200b006070340302c40c00800c1313440c031000800e0400441e01b1420104040c2e5044085410240294180303000e00075524051841580e100302e1900c07029114060f42880004d05800 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 637648678 1250 637647428 637647431
    0x30613060305060415110a0e03010b0a03031107090506090c0a11030f040602070f06090e041505150f0d05061b09040501090507230a2d020606101e1b06 66
    0xa80e281406919003d003110140d6220b041c4400c2d000f0b9282d4540b05525181c0300212425050a1101800329034060030343c902c40d0307003640daa10620020b5030385409400c030055200e541c0d25040b07483c20b03c001e5814250140c3c003100c00541407006002c01e40d55841499940a10050705050b1288100c49003198800340109854815010002d240c07914460a40001c00550b880e0303400300c80c1940d543e880001d0700841e15200f04400502c00341020300004c0151854241c00c64001e5001446490079103c0d890116442a107404e404040d204c507070100541410010501540c1003100e2000e40d01c81c540d103c8a4031800c0040002d924440c85113642d60140c184581039828901d800340c000c200740d686644c1040001d02080d152a004280c513441c859465030b02d0b5100185045411441c40c40c2801000c03e003da40c84104d2245c036a01031413951000c458031201d00e0380e503022290034a50080c809400c1ca90140100d60300c1d01034811b010004840b0803201c070305114001d05035005015144c15030408546044103149210311420080855 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 637649928 1250 637648678 637648691
    0x90310060e1501020c03190311030408010209040b0603190b120a060e010605060f04090b01030603120e011407050a0f03020f330f06010e1f03020d1802031002030613 72
    0xc841001075441400e020300d18440424584006a980b80b030aa0000c3e54150301c00010702240303800302c0e001c05081d14401c4c180000e07083e8a004603142590065005101280e50114221496160902602c080184180c8607a0300d58103006c441d882c51aa0100160280c03184c6400d07580c80380740c54180909219135480c800350b807111252490040080e020813008480c444d0308024000c55545052000c6500da0350490f0221894146460b031014041c14175030b801030b418075580e420001301003031441142c0c2d8180d40399559081440400d0743c0015194210140c55070020440610400000601c0010040480d44e000b101c2d090080752249030403460000c601141c1840c90240c84281c0c80783d403100c07021050a07503480002d101e0a5185d030120311040c050040341d120803130444143c0450103a5002d401c09001d0030001038002204203000258200071401207a10450020ba80042c1d83c0086400d2803242c04032100c00340800341005040d98000035a01c18402192030000780d40040401c10641e1001410f8046082001040c8102c = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 637651178 1250 637649928 637649939
    0x2503050d020f040e0609090d120b090a02030a0c03060b0f090402130b0c0106080c0108150307090e160506040f0b0319150e0a1b05130e1303170709060509031006 70
    0x20f9042881600700d1040030034041403c0c1d10f030805403544200718070802004044454901102c2040361164034207405542d030b48012120752640258148a00c00c0d00300090380d41c0c1031002c0c84104543d036054012003010f1801c08148240300f50074040b600440c0c11440c641c2c6d151018800060001d1007034401e4032000c0d548924000a11409003070250076200348040080203856a1750104e40c0c1c50b92100d01489001402000c00140d220801540610198a0140c120707000d00d61158090300c21201005510219580100c42000748001704160b80300180c2400c0d070740d2038101032820300d42121511403401040005c40002c400140da000d10604046480c60070a0f000b44803100e01c2d5074144c02d04c40c0082c0101410301c800d1800142030442c60380a01c1d0300e0500200b82001c0142c5c034901c01200c15811440700f54a000d481c8010028003210164007050148400400303030501003001d4640940172001003046031034150b070307008100078009403c00200c1e401c030b130392609145a90b40d540c100041e080807150300f4446c00d0103140c0f82e4040341 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 637652428 1250 637651178 637651207
    0x10605010801140117131403040f06020f07031112070b0423030c04050a150305010e06012319091802010905040e06060607020d0b040819052503050d02 66
    0x211a42a25032440c0c80e40c0720350f039a1015118144109000c90300d031500441c490007014841130751001c0e00000c0390407900610f5452807501f15031424101401ea02c04102484640d990001802c000c0080740000d100541c2544c410782d40323500c1341b80f0000e00701c0611104400c03141d032565070004403c1020001a104c056889260a4074980c2040c01a44103c80005815070882d840242d008280000010300400c050004c2d141088068500100280d909a40320b001da00c000c41e243ca99000c0143d4824000403401803103002485252110503403240c5030302102c0101f08011107008130ba02148a510507200094001c0c10344031409920f92540d4071030f11109180080003051500f0850060146a00c01da03100c854181d9a5810001920022001c505068110002040143c80c0c0301e002450800d20190080402000ca0744501d410700d00101d400756900c940004485100c06081c00034000f02c51000d0425504000407030021b40540c01000c84e081c04080d07206003964040c14014000d81d010408085415580c0e20b200380d08031030 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 637653678 1250 637652428 637652441
    0x30303090c05011d130b0607080706050606160314040b07110901080304230f0409080d050c0a0801050f03120406031a03030406053a02030609060d0309050402071e030201 74
    0x1605101c0c4000c020a0a44c8542d08049901440001500000e5458000c01003030300d141d1400710139a00e5076070600c6800794440c88094070351203005d5805140c5854807400e04400780c0b000100481e01c076001c1001120170700c03091505200310880e05454400100820800300c90b0151256030480c1c14503040118030319003000100e10b014110b0440a4410342d659980c0c40501c04d07901e0103a800b03400104440c407005041042052034149010f20302c0105001c108020a00100d02140c55824040d03401d01000505400103803014010341d90421410000503280a61207003000b022214180141f0f4840c0300008521046990200300348800c0c10000c9900540d07482d680e00000d0000e00010744d096035010304800b204200c9240100680342124419201e0603e4400300980a425000801c1c408101e10105450100d07492603841c00c15800c003454038000141d403030820000308008c0100062100d071080003910300c0d00300080ea12402c440200c1e0000c1c5c0c2e015072500b045280c1007002c0b98050394903559422440c11460241a41500920b = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 637654928 1250 637653678 637653683
    0x90d06020702031504050607121d030a200d0518040f061d0405030315010c06050903030a0e0109050705040c0903050a0b0f10150c020a0e07090807050a05090a051008030403030309 78
    0x580c0313200d20803045910900b208a60103000c41d04400000b0701c080d405040910307508050003600240b0304460703010403401c0c0742c400074680c00e40350f001190b101c40342d0f6000004421021b54543c05c1e1102904130400d0150f0b50410015a9010044007140541b5440400c1900c6a01c00da0000e205011500005d40410010080c502c82c48803e554a07010741c001c1c0f01c1e03400c10050301440e003240c09180346a44030300720700b442c151040d0009070420111110390804528a445480e0050040070061550790078000441c84c1034404218558060340d00d4402404009a00041c2c440c08988083d1000b0940148028007622040c007140c1c4050154012914510100311910b8100c510840e03060031141510b031248400082c005c1968018154901c4101ea006880d281c010a0b050100740c1c0b009140340040340d00c4a00012114a055a020f404540000014008428203201000140c1400d8483c00c1e01c480c60078000622690021703141d14040d42e51400890107000c1c52001c80005045c0c040101d1342d40e03075035920740203000f800c1d5214103 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 637656178 1250 637654928 637654933
    0x5010b09074d06060f0f03030316090f0b032d0f0405010f18300c08070b0c0d0e060705040302120f0105070203090f040c091208090d0602070203 63
    0x1e0496014041c1d6038026079140742010010341c07030a82034401480040c1e81c0c2038894842c0680300d000398501c66649070341c03100304640504018100b44061002954440c5a4984100305c5c8090200841c1c40000039039a100c0220007507034802a03841c54080e40c0c5401a03410080c0c101e24007100c0885c801e564580110301038103410390002401016002c2c21a01e2007950442e038803e500d00c20010034105a1019140340c0c01034054400014078040800322981150140200c1c0110122615038050503c0b03004500a4600303610100420320a01295810f0030102c441d0752105800d00090394005010301c41100f05960405601030317110040f50034541c80c200c3d110781081e03403060000303401c00c6140d40c0e0403080854803a010381029214217003018115401c00461010980000e1010300c82c60782d2501d00042c0034001c00d4040c844076006181d0320722085040c07210850110407400d0080d0b0602c1c0060701a2139201c0c50203800c0f181110300c0c440d0070b520285808a82031013074844e03441c0e106015103a40c0d0b0610803182e00a11320103100300d04 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 637657428 1250 637656178 637656181
    0xa030e040209030d080406150e04050c09040b010b0d0902041104051c1203020703110706080901060e240102031306211a040c0e03030f07051e0307020609010905040905010b09 76
    0x400c4240e01c03034010388a07019004075034407800b41030045c000d2a03000303803040c3c5000c81c1c000c01400c03400e4803a101c1940481200d990700c02c140400c0c882c00f4020303030b0007106061700d21280e5072a00d41c0b5141c0585c2e006118081d66a4000103100702110001d41c00000d80b194003d00c207003c40d801800303025010350003500405211b00c07502e035503c50303441c9491604801115070080300d003164030500140a6000b50095070041d002d000b82c000d552403416109001e00000380005888619050500080350790031500326810000003100510180086940100800341d00340c88500740c1c1181000c04140101d00394060003400a114007a421800b0500a4009204200380c0700e1f44200098006441010340301551031001c000350301d5800540222106041682204c0c0410b0304504100300c0301c0d604440428a154003d20001000d42c2e008240340e801c1190a11500c001c0c24109003000e20500d031034099403506c03071148220091080301c0c00038201c46a81d0082144000a200041081194040310b04140340a00307020500782e8071807440c110 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 637658678 1250 637657428 637657457
    0xa170c091518060405310807020607060504060f0e070509070921120e060d0b1c2a0614071b060f0212030c041719030507060624030b210a03 61
    0x400c0d2801700e41e0250300c240c2080c40c51481203030300c1b860f80e45815100c15030f080000c00056120350000b01000d9100d020005002e03c1c05092034000c4401c82250006403604000804910607000510102500c0c070496807145c4c00c0d00d4503c0c003950041d80131b0344040101d22a0f1071201e803480301010f1001c955180503404800c440030141804a6180041d018400c0d4050020300c1102c96131201540421282a4040c090f048040c9130301d404034140428a840c00c645040074454a08070039000102c40c080522404200c900b107150410781c014003d011030710080d40c40c80340041520307810302070040700c1050425031240c01664003030b403140801045034110301407581c09403050f412501504140da50403203201e95412140c46040c1801d00b192060036030b804601c000354521408800b58030100150f80e80c42d0300d403442a00c60790b54407440d40c6005d000b42e6205034020010141c0e54045c240704d80c0c1d04036070064070940c45464000303044249500000d0600c8144a20a04052001070081200307010004110f48500e01079103c5444114000 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 637659928 1250 637658678 637658701
    0x25030e0105130b1803061303181202220c0e1e010e010e13050a0e0d09060210050612072d0b09040e0a080d0b0a170c091518060405 57
    0x2c0148a00c80c0000700c000b0848040b8070300141c10108000100c5800075640003000a25040c01500c0388465840c001100008054002408400e2105e4018040340c0d0303580781001c85102c1c40d4445001034021b401c5801a0841e48241400c080030407146c1543c00c020040b280540106180d0200d8075160042e0705202c4508072504a2035020404004140c0d100d5400070780150044620702d0103860b102e504203556044035101016580980b80c3308464002c40001e16907600c4015524061880120800b030040340c080c103000c055400b142812808005070301c0480c0c651101004910309040e141c40180e068010b407040843c5804140780d02c1e000f038030790450240c022010581e0041e80a04030610a06200c03001c10400c5a0407402c068000b2030884003001c00f9903940988941300d5902c15802040b90000d5203640751104079251074800b4801016100254100b00144407450540d035540040815184c41a966039002442d41880c89481c0c3e0018000544203008034201d040070032100a001307958603482681444000307518100311 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 637661178 1250 637659928 637659937
    0x42603040b06060a0302070510020d1d0d050f0f071101030501140a0e0c0408035a0d0c050403060e0d080106081b0724110702060c0325030e0105 63
    0x40d1141d03680c80360002c20280e075003c04200c00505400303010a5020580c04e01151441c40c04c00c03040541c0d140034484030b4600b100e52010704003c04600501c08603000c9100020041e0030b1558a09201d69036071a602882c10040c010b980c079521240000150320020014881e070f040b01da00c04203803424010359032940700c80c02c1c03000a41403c56800c0240c6440170002003e02c1e40c03e941d08115a1001140307059142c09225007140e10842281c1020203003e841c810580c004405480554441d40011240300380b800001da0b4030f4002127190052155040c1c5555081f40c81020040341d5001c1d18010f42041034207601c8a01400b150040d101c1a154107142ca0b1440c11101c0001c10b0324802600c0580d5090700b03d070b082040c00d40e0080005000600d40014006c200c01e40701d23440360020700b1030600800000d030481410100300140e400210b4102e01403242421400340c100030700310b415140d60540c110703145034860718900c902605e1400f541e48413004d05074aa546030201070850800000311103010750f03200000540182c0054a00b0b125 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 637662428 1250 637661178 637661183
    0x90a060b09060904060e040f0c3204060504060f090b060703020c0d060902060a050d0b0109081207030e0406093602120a02040e07060914030a02010f0c060504260304 72
    0x281040804203a142c15070090200010050001800c40c0e01c41d0f0900d20714100440d02202c45071810546c0c3d005104548820741c0080100c08a0120540c0ca14204903075903c0701d60f180b00900c1100c1b014110315569960f0044405044040c200b005800d6840d59452482071a0f07100301e41c110b9142802101650a09074100c80345107400d038004041c405c0c044014460a81408070040e1042c43d80c0c0ea80400043c2d545200a00d4001542e94070162518000d40d0120226a80d0001003818000704000400c508234000c55000e0080b11501d00f516160390321802d050354180d071080c89850f8080c3c034206010075154070a50003030740719100b800d10103d07000f0303402c5250954003002c281c0da000d01c46901480690051810050a840d407a03030704420f071581c8079031a038013103429202910f00302e001039007000505001480c0c0c00300f80100149074540c0610350a90941000c03e46402c0c0001c0043d04006094180000040c02207000b40314075076004504000e81c1c074040c01c24458911602120121200c610700d41b44110034013040542c2d0140344c = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 637663678 1250 637662428 637662449
    0x20d03081008030c24090d080c0408010608010207030e0102070605181c030201060501030b01140f0a03020f0d05040507090504050d031d0f010501140a0614031f090b090a06 75
    0x1405840a440c600002004401d80044000340032031082c505001401039105004010418101007400071886200318481e0204a031111804010034007000060100d0020018105400f0944858403d604640b00da600007200d15030070700c6400034140c101540201450b40c000e90b52015510781e80401280c88524500c16000041c4080c0036080c4504555000c0c42542138000b8042d40d5908150144511015800d49080d00540d5403a0010002940c140c000d148c0032000c00d213820f0706c51296901a0305040e00550440486603480070403a0b80c281402681181d01c82800426003585860031507034120003070320301210125228001c2450001d220011030003518000c691004c080c01400d50b19400840060507100000e20551500041843c14160140044411241d080d00013050310b6051020841c0d00391300000b0024000c0d00040000c000c410791059101031081d001004071681ca0716514083c2c07030120340490070f0f591111400c3c034002170440440e50200303c03800b00c01c0e2002210341d0742c0c0d03070740101c03c807400c030310803000c01743d = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 637664928 1250 637663678 637663699
    0x60c231c0501230301090f060f052d13050a0c03030207050f0a12020118080114090316030c140304090c0206183403121b05071401030207150c140702 65
    0x14081d40c40e10740403c1d0003e00005051040d030348801e8245040e500003030342c4640d030b41e9585060382940e03401010340c404c05e82040180c00e2251454682c248082e80c2e106034100900180208045c183c00c10080400b554101c022201c0c002002d0030401100c001030b03c0102d001d0303c12468001554107100a40040001006149201071440c160780e00300c1d070101c3c1007401c0b4100110780b498055208000c0c040e1030081e24221000040c00c003913820343c4402d40f910281c0308001d603600c1800020b104405c4001060341c03455051401e0340a030304452904280d110507141d400d000a000204020a40d04100d500181d1102c00950842d40b8a403610303511034143c1a2408420503041d00314000394078006610400c1c803904807111548000d100d810002c0e1540102000e40c000b03c40c5440e121101c0018254010320010562a04c0071000b412201c240c0e50b407a5641c0c2161240e095915240c854140260f8040e0707056070712489d00584008000c0f09103600038002020027400482c085802c002603064085211700586059641c06408090031 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 637666178 1250 637664928 637664969
    0x10203090907051909170102310e0f041109060d2406031104110c030306042a020708100608030d021e070b01030c05040c0c060c231c0501 60
    0x20009015405028040140d00101c00458003280c0b4004d8041d034403294418100f404126529514011201880e80148800040d104040c5150024841e044007100644180c620048190301a203500409207400803d0170000000c0c1091440c0c1c0c440c03803207021009901030030381042283e01e08058400c00d030003100038503c00e00000c03154004402c02d5201d415003810340c8460042484103407560790300110703094568105c81007443c1c00d060080503c80d03007168015a06162000500607900d0000405052042d0340356000724201180742c0340d00103500d00742031099000e45619007402030b5580d00c1070f01c0b90070707201c1c410f03141402001c81d030504c111000c1d90302e104091490810380400803c00f030f4100c0600390342005412000401c40b284c40c2c4000341030151140308071030415891800e100b440704601d80d10207405a410f0280415040c0d505c40c408a5000d58800e01c00520640c41c010205c8001d03002d9440c010311a50342d04004840c070030f100bd001d80510310070851b4014043c0000c400c140282c0c0c00a200e80300d034a600c03ca502440 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 637667428 1250 637666178 637666189
    0x20a0b0402040b0a030303090606050306010501120b19030605041a090a0201030908090307031515050a0621020c0106080c0a05030c15071a0108100c021b040605040501030b0915040201020309 83
    0x30803600040c80480e02c016a180000c02030300c1141e00440c0400e0740c50425130100201e6004410007000c08078040c000c40e601d40b03800a41141c201c20341d440c00709980d07204030001981d075481c848009490130084030342042d5140c0c5000c40080a06072010746d0342c1030b0394031242103a201856030114402c0c0107400141880c40410790040d0050212003500315003a8809000e00d2615440c10440030004500442260b420f140c51040203c00725150004003102d440c2c500c000511964480c1d80c1c40d402226418546001916102c0544580d07031032316020344400c010b0001039910919207054115000f903030f601405940410707402600708940c0042c1c9100c2d094154200d0301d10b400403807130010701c800c0485181d17115142c54a807140d030b940842d03c16211000400c2001070310040c000300004100d1800682000981008160038400d000b940c0e81c2c070a032481401c07102041c03004000d60340b110707044100181005081480503507181d03e007100e598241200c02101074851a03400304d51400296402d98080c0e901038000d5454103c89005015 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 637668678 1250 637667428 637667431
    0xb0f0a090305060f1806010501050403030f030e011401060e041802010e130e011407030c020601140301090f0501051b120f07090302090f060a06020325030e030d110d0807020a0b 77
    0x410300c8400000000854414004070380305101820403000585401541031045c03110032543e144969100100503c0340b660018100c0e17003940e806082940c282c06403408214003030040d4455440280d420a0f9a012240300b00d14401c2d4180c5556458003403144e5200400c2c48201d0324030321209045451303054038290155004803481400d01002a20102a02078001c0c1c4020030f50301c0051240d06240c2d581c9600711240e000200e03116030461804d203410701c402440810000e50340c0c80107022f985d120b41640764005c4165a070035800900c03050388c011446200520030381001402080708039081c05410350b402c01403009128241080394220424289401c046031200c04072414403c1c030042040301841140d0308048056030b540c400c114481c0818480210b070510b003107001c0c81600507099100000b59070060011401011200305e410001e40446022074229034083d050884144414060094041c050f12035002c005552281c41c802e28034048001b156400340c0034000845410702d04071210001038200e1200600000c0d082582c05 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 637669928 1250 637668678 637668697
    0x11b02030111120f1e04030810090e0304091b050a180308120702100b030a08030604020409061205210d020d2a021c081f09060308090f04060b0f 63
    0x90040302c41c00400455a1058101e00340314039419003000074002154003113079880f2140c5c800140104a0b90222900a000003420046c01d212009002410104020300044014204d03107a0920020740007100b142e41704e50050040c40f101e5030400f0080c40510168a099050203241c580c1c84170710f0106400c1c012254000030b9506421f480c00046400000311b212000074004031003842030342c10068100064041d190444c030759044d005035420402e09460583e00443c8004c40703103400042d1f0b01c0e9a41c0d950f8002400901c15074110404c040e181c1940402c107540800b540013030f46407080c80cc0b00c0c62444028040e0220a94440b0407803c103120030460789000e14116000b41aa0350b80360800410710042c820f242c00000600300c0500c4002d8180f1220400304164104a00706810340c8030400500101045003005040200040071004403c0c2c110401d1005612540440c8000f0407201c10204501c80d101e10b0044829848500c10902c5007800721030504140c50540f044d00121040c8900320b03071800c03540342c000500682007074019 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 637671178 1250 637669928 637669931
    0x60a05240d02040b090f010e090703020c122b1b03020c0a0611090a0e0405060c0901021908040303271403010b0901030b0f180c1908031314030c011b020301 68
    0x314003809409001500180000c00303c40c4d910390718036000b0310003c54600e440303c83c10840e118512444d551079041400750401d20500e00540d8460400110305d1902c06209814a10b045000808144070a101e00d6907404121110031500d0810821030480d405550241990034800d5034003010711240d032402a402050000d4011f81581e03100d0505032070b15000c40344c4600c8103400b811000590f016451920011500242c01d00c0440740000d810301d13407591581c80900070912040060001114a40e90b80204084801180c10180c0480080c2c91407505e00c1710b94001e48811404201240012003d085d04c11440034000c002800341642d1003032130011080d11900d0318600f02600340d50b0b00d90f8030100769282c010642c0e000e14000e1040c60302d2818004106219204002e103030014034814126281e00e08080170406070780755181120842e103c1040070180c16204032683e800351406200000b10740d00c1c8444680c2120040740c80c8211140340c54400320f014980c903181d0401500d400204c800601180001c1d0500c40c00a119002800 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 637672428 1250 637671178 637671187
    0x3150f03032107020d090b091f030903021501050306070c031110150801020f0d05190f0e060105010e010527031e070602190807020f03190605060a0524 66
    0x2107411035000d02c000702003030344401008140075042e41a103560890407910007001000703c2904000c0c0301100600492030708410002c1c1004c5243e0703075500860515140600720300c482c1c0b407055901600070706603000120058001d10310070346052800340e0211812220064040d104136a2040000c1b1180e0b400d02c0c400714148500101c4038054039004120048000000006c00a4424200e050603268007055600603040d80e801000541624065403003a00d0200b195000013003100d484070b08901d0200c0050b00360800b80203103840040e00c04140141c00c0202c8070307107008042e074a650b41c032003004692406104045902040e400c102c8090b01114241c003040750003c9400b5540d0300c2c21440c00010742800703585094181c8056084404d008095030a01c80d8900814541c001407080c08a030015260b4502c1004502402c990404100141952580ca40d55820f8041c004d050b21900842c10201842007000e0344070558080f860400000d5081c100354000ca8181c800c0109600b40004a41681d0903009151043c46540443d0030300 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 637673678 1250 637672428 637672459
    0xb0d050303070c050705040e070b03181b0f041104060c0614040506101e052818060b0309060a05060d0f0308010612020307170903120c07060e0d050315 66
    0x18500640b107503a6407250b80702e59800c4c01840c0c50420381069120354508095001c050f50009000e81c12105a1040d030381c0c03030740d4038044a1111100c0e12800040c00b03025148211448803058540070280000803a90407420340c80f06400c0c0801c482c101070398000940c404102c140011070089164460704c0388618004120740803440c0c1c0307130350300032606480864080c0e00400910808000c0c892122000d0000e8942e50f20030b05013506030701400081d5134800c05002d0441401c95102803899003000d140c121a2415000740c0031a40c030b054003c00125245c0722900c00d9071601e080800d200c800b0404507405494000001c20b042d03200c0c82100f100400f4003a24241d44080700e11814800506102d06c100c91540c0642c40d8038405615103603000d4190a40a80520051881002000f1800b41c000d108011241042d4a00da1810b91366a8402842d42c820301540100000300102080350500c6064020420709101d0302d41440b590301304042480c0c2e1901212480320105500b40b0026012890f40842e03c00b0760000140b8101141c40c004 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 637674928 1250 637673678 637673683
    0x90109052a06070605060f0d0c1406040b130302010906170604050a0212040807030801090507050a080a2009040b09040305070809010c140c12030a020a060e01060b040b040e07210b0d05 80
    0x3da07000c540140c1ca035010045207160026541c50320080541d0103511078445545d400c41030010354051511891880c0c08403581545032081601d0203829610b0b0200d55030b904480c0380320f03a0a0b00070302c4102e00084c000030380400c00b140701c1c543e01c0606803107400340b200054071010200009000024254584150b0901c91850082480aa804c1c00b582c004d8009690740c000a050041a40d03005802440d13605040100b808000c60740038040b81c1c500c0da01307454110380c07a440c0c603040310000d04000f90b600000010320ba041707070501c0c101e001c004007510b000440d0104100ca50980a000048d001241c000d40441c2d418441c01e00414407280003404801d405240050391145d0980d00c2e111380007081081c070801030b80000206003850070141452821990300c07078011400c001c13031301500035a10090301400420b074a0b01e840c81d202c000e87c02500940040c00e001206140c0b925281c807218000e9030054410910b0025864000c0b071581402408001c0c60403502c42145000d1004031000c800c042c08103a0f904039084103100d03122001241c0d05 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 637676178 1250 637674928 637674937
    0x460503150301050f0a050f0714090d0204050126010b01020618010b09130b31020103180501090c12050312060607060f06081005090604030806120312010608090109052a06 74
    0x1101c000c4140b60070111017140071a50b0040034401c0c11a06841030052281e04045003580101ca000da1541d5201803040118200048015009401034104030002c2070045000c800c0202d0a00c0c0100303100035200b40c100c5000c0c20703204010201c43c0560000740108643d200741e51800307a250301c00c0200116420441002203155507004039501e42e082da4849a8a00420150051a980245260003600040b00030680c0c80034248090001108810078138400d90301c00c690181d04107d001c070094020440100c031042c240580a050140c604507440e0000708000b007450329004807146021500107008504050941c0d180900031040500304591060301484503800060050240b42c148a006580108149141ca0004c502c0c2031b541d0407051091b0380c104000c018a6003400141d155100c0d805203094105a120700e404603030400d0026001c5078036400700107401000c00e0700c101078090407603000d03a880c0d200350b076903180400e400c079511300300000c195401c020174145c94104409515a181c40e07508a9110b40d40c40d0305000966a0b612 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 637677428 1250 637676178 637676191
    0x90518100b03070804171c050a090524060102190213020c0f011a040209010c06020708040302101e0e010f081807060c06050a05090a2646050315030105 66
    0x40b4040108012141281b01d0154840d852260f051011804112440e804400d45440116546000203840e849594000c620415000000d030f4050740e0840708903042c0c05090600f9000084c4c1251b010580c0743d4400070704141c12300d40090001390590803e5003003007101025917012201c4140c0038841405070701c50a100409800c000702000060100d0428000c2800992201603240300d01e105018041c25a40c009201c1e844c119480007005988000c10300c0c048155000d01d42002c2d4100010031440002d00d60424218100d05100c0c540d8605101d0134402d080f02e00290071003100f80011006816070f11058041c1c0c040c16000241d000c0049a07002001d59014a0285964081c0b0f001038400d00022090107654400c60b41c0004404100340018941807840a42e00c9140700740090040100442c20107800c81c0a010124001c0c10884e02640c3c0c0302d101c882007560702407405a5240d0310250700b8080d61006501600d101030520000b10304100c9400c03801d50300b580e45410080c0070480c02c1074480002e40981e602842150710452 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 637678678 1250 637677428 637677437
    0xc0303041b150c140d0c1401020f0307180e01030f030f02120d020d06171e03070819170610030b03070305010207050f12070c032d150c090518100b0307 66
    0x3d610f8140307960b040400e60000002d6401c028480061150300040202c00c0603001a180d54110700d4030700e101d500a100e10846081100e002105101b03203941c1c400e01c0810301101866000c6412030b10340312007d0030440c00303100c02000c64014111120000380100d02e031a560700c1b6580180e0b41c240041c0510386400d13a102c0b40800741559800192004032134445d00c1228054016803a08100017000c902e0140e40c1d4038000b2010160404568009aa00040810850350005c0d4040c0056448196484160581c92546040400850307002c7e820032003c00b2481d610980f04aa00902d00c143e203109814054004144820b07000340c15000c0d02101202140d003d00080584603c1000206240c104c030310f24031401c000a01d400c00c001e0000401904000c40c140c0c00948040eaa0080c40b1060303016240380b079141d1050401c041501c0ca50403200c40480a004c403146080800c05109038041c4400488d0402c100c0f401d002178007429500020b030700500301c3c00c0e80300c0840303c42c0c1c0034108000c01f27090152039100c00b404641085640c80c0008 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 637679928 1250 637678678 637678697
    0x1401261e071b1b180f11040e0414010e030a030b060711060c010209041b080c040807061404030203010c1205130c03150209031005011e080d0c05011b1d03030c0303041b15 74
    0x100814071641d0611000031504205060f0046e000c0645841684030700304c1c1c01e814100c0400c080c0400841011001c5001d40000c11a42d2204e5042d00d4907500002042004a45040c0203402182406420ac9512561040b0503605000b800d40410140d504540118841e85d135003400000031030348591249110005500007281d98044101400030105540101100042c000c03d020406c2104070020743d0b0f0003603580c14180309060810300380003d20706006560010390705600380505e01084a4110641450f4454001400d000c0c1381d60b0703403414034915400705a0080c0784154030b039010408140500707800c501111140101619103007590f00040c6c42d02d158041d190704810340c1c690040090b1154011504500d00c010010420444c2c034000495454110002d055000d004280b01c10f4010084207602c0000800340c0c0c3d09480540c48200d2400400481814500700030f41c402d1000c0840940c80d000041e10105c00b5480020752079583d4641c1d900f280a240b28981030015009584041030b404c0038525400340e03050306940ca08418 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 637681178 1250 637679928 637679969
    0xc2f1b0301050a0204030812040f020a0b03100f060905090a060923070c030f0305072c0301050a1a190801061701180209011401261e071b1b 61
    0x2180c2c0050f24590b0980d1040000b000054a10750a5403840510301e054185280e42c0c0d17060905003a450003000039031000114030040b41d0a201d201c00f03036000310000310180c1c620030340f01c08000700160104c1c0500400324908a004001900d000c5401d070b80d010620b04070125a841d0358200341d0054a8403d4481c6418024610f40d58400440d00b807905580003101b46860010000e0743e44003d41703406915800142010b48600000d800580206a5030900203d2149200c4c1107950108101d4554000100c140f0b2203542070201285004004d805142001507041c03032440d0151200743c2c100035242820322000100040021310000e100c00c000c1c40340c18020b10445a20021741e9085540480c00c4818502c2011041c10210009802503160901c2e254152551041c40503c2424000010b079954140185106c100c859018664421148098000d5000740913001c8104204508000d01000c1100c00715140f000060022404031005802c40d1100780045004d0400300c0055007011400c485052503a400a21070840d2103c022080c = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 637682428 1250 637681178 637681181
    0x10605091201052401030b0316050406050f130b010c151e09050a12033305060703020607030c120f06170304140f03011b1e030c2f1b0301 60
    0x906141c0700000c00440c5041003055a8003005030701c14540d00803070201a900f01d41d00942c01018150001011640d021448400506070103d450051038001c1d4100600029141440d522210a02c40003c24800c51080d0105c01b0500401d5800085410025204810008100d000b01d4581c02c0c81020715020030561a403440840740520741a614032029841e04031908046500490b0801003a070303101c408074000740443c1508801403c1c2e0003600080c00700901e54500b40c41e0088800018404280d0304000d5030045e80c0d442000382c280592807000e000340c0c00039000100e44a200e07078009000c2c400203003400d0450f0059084200c0031690000700c1000d5041d40c8480c24410a020210400d803444000c400440c40c0074146002543e20780a80c04007940501242c02201110380e0f800c0d0000c1030314402e40c0b504d0251035080c0f6070004006003404460001e400004a540c051500d00c03e0203100c0d02060b894958207855421045250f05801448130a02e15160030011114032007074042c0603031450b12800b9411090000413a404050 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 637683678 1250 637682428 637682449
    0x4060e04031e09031a15150301050a05010f050d1503080f0c0c150d09060b150403060c020102032806080d030e0106050324090f1002071103060c030c0c030405040501060509 75
    0x43c01003140041001580c407810b8002d04110b002d101d40c603242c444810080400c2c54640f012940818492901001004048040c504039141220680300d099920790055030072508a95072440010346c00c010700034511069400c1a01038040400403000110f941c0e4031880b4054014442c80d90b1031002c000745c122486001046a5540c01f04100c60064980c640c42c0304042c0c05100c0c250b10040c0032070701c540314041071012980c0488a0b040000e881303000030440b01e000c0c6807c1c591150008403912441c0ca000c40ca080c500c14400c0e01e101d01840c0540c110711100c045101841d240c40b1b0f403994100b19803101004245840140100001a041e0340c03804501d80e1888890741e030a68003941c11490190f40004038102041c05800800c4440318100d0304101c200f80c841500f218202188103440e00450b10800c030003c0d80d0f1103c00d500a080303103405444482c0c2c6d4104400304140d1240320581c1e01001645040c0b010a0380c2d8420305006004003c0ba079003c5a04c0e1640c0c0f0000304013a01c0d001d17400400450008503003660030341890407019 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 637684928 1250 637683678 637683737
    0x18100c050d0b1816020c0d0606031b0e221401051504020c0c24040f0302010e030c090402060a0509090c0301150906080115030908031801231504060e0403 67
    0x500e0342d140d950200303030124000801107401444000315144d886030003440300361040c0700b028101c1d024200017800c1100180441d0b1100300c400c2c01c803954115070340040740b5868800742c0e00803500280c07082c2c882900900009040c900819500b24182c0c850300300040602c2c2418642101500c0080341500d03151007107410300300a03200243e009500420418294800210780300702088400c41e102042050f2082c0a5500c01c1c02000044044403000540401c0a0072007801007001c0f41d100f41d880d4080f0750340180034581c86202104089030814402c0780402c005140c4403018245121141ca0024101000c080004030388034026100010740500000050000d84588000203400880c203040060a191405030020b00040c01441152240c04114542c04201440fa410210059421540300c94890070000072598000d483c02400790600d42c0b0b4a8404224010880d205842c8180740809008a0b43d803000800380c8495092001395510541d0f884010940340090072640703000c2e5020742c1d14071400c1803504100302985146072009 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 637686178 1250 637684928 637684939
    0x4060501020313030210020f0303090106050310060602030a08061207060c0506070503100312141c0608010605100309022110150e060d0615080307020414010302060318100c050d0b 78
    0x141e1804501905491040380d0b81500c40700048406d483c03040341000d5404103c651540030010500a1441c815084002521002c1b0144d41c0100b608044030400c07519140328004c0960800e01600020034000c00f05546d11520251001e50209081c0200d41d0030240c994111f80085440341d6000c1301031000810030350b9800348081c1040ca24600b0464603612200d2014880180000c400049400c45148a000c00c201000803030f4000540300c4448445225424807400c61110200b0b203040d0340013030685414090350b0101d810203000d031034908401d0101103000c0d006502050b6005030a500c07440c50403001440480b52a0400c2c00041e050790706c501c01d890350659184500c10f4401c0c480c1c24a0900c004126541c026801c4a0111098841e050380303441c0810140c0141903101002241c0b500c4000ba203103002000620f4182d2080b10104121039008901c03d074480020301010303400c101c2c20b100160780030b40d41c10810100c10011108a5102c05c071105940c5d000da91200d003240f00012808111003100d00240d004844415108880 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 637687428 1250 637686178 637686187
    0x9020a0206100b1614010f09050c0301050705091005130f0609091b0804230f010617030901030b01050408121209010c0e0123040b040e0906010303020703030804021302070c05040605010203 82
    0x1c450120700949030300c0303840c1000f2110301804005c0c5600d0703543c0300600a0303c0244028580780c200c240003005440070684681c0500b01030310059181c1889510310456503038645a04010102cac0078005141c0381d46020100303021042100c01118a54800280024036100d4101001c05041080c02021004952302610845050640c00d110000c1c00e29502d100400091030220119070b150700f44440414020b400c04002e0900741040e6210a11000c5006220454880000d1014940d641e0801d001d030b9091080302e00d0715404c01e002a00ea6984642c01520701c0140506d0114100b988400b2086d007003200c1818a0754038107400051031100000716244c9035501100780002081070811f1990040d203043e0f907103030010781040f40b031211540b1000b01c0500046181d10340d0101881e15242c0740c9018020700d80c02402070303071064940e0030f00280101c81d0000c0e076141aa0b5161f80034020f40c501c0c40c4c1e800d94210b10080d10490780800c4109105801c881c4901c0a004a03074041d948100610380713031800b03100c12140380c3d40000341150010031 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 637688678 1250 637687428 637687439
    0x180e0a06080d050304030e210a03030b0303070c1703120702010b10030b0d06270b04051e100e031608090109151d041b0c05191203021c0609020a020610 66
    0x16640d1094241c200001c5441c6600005400f4240c0d00361201823900100740b550315100c200180a4050901c6618200092861801011b640b8065803000811034ac0340c40b0400c1c05003071840d0252003000600d00381103070705000b030603c01482c0010044505c40d006079515a401c00c541d1078041000791940007641010040b4040800c0400d031000034008000d4451516003200c500500c40603003500341103002845005448180510b85040002030541301a109480b540f121443d0b600485800c10580543c0d9500030038500742030000000c05805446c04511444c0000d01c50b400f464030061403213a440e14071582015a803418403a00240c014001900401404200840045041ca401990b00c7c9440c0c1031044c4200d482c01d24000c002000b5044642040400b081100c0c440c07078203c0e41196104e54120320078010b40b401e040000240819042d91007001501e01d89048101d102c591340658020025402455484210f0210991001d404c1c0c800607400603207030550005410000a9052100d01d812500c640d034191807451400 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 637689928 1250 637688678 637688687
    0x100c03081003030e0d020f09090a0309080c06070308070e03060112120314011e03050d091a0f090d0201020f07150e010918110412050102090a06020d0816180e0a06080d 73
    0x4180c000d1060b00b074228190364847d50584144a401810350300b01d440c3c00205141c8541c3d20701c20803800f103640d001c07000c6600e00740807421a00340d4401030300c04c40c01c0841a032421200e01c00c0192501044c0910922941040d40b42844028068440c2c40040b041103c081d10380b0041c0c61010010f40340070145484110f0704290316504d804c1c0c1c119040e8680ca000006040301141c0e4020790150300061252266041d50301a2980221240c8112407070b6141041c0010001402445503200e00c3d00940d280c1c032410464a0342d02e16183d85400303155070040c4104c4450013401541c0c18075141d019046100c1420b0002036a480c0994040e1191010240c00e10f00b04040c10b203400103440c0c00f8107a0205c0002e44940301c145240d811866071090310000e092100a001c1c40900390b09009000754880c00000b80940583d11012414500001c5c007200041c00d15507844865649440360000b80301e000c52424000c0000001220104152080c40c0b0006804103012071000e0341003109488040b03442581c090ba10b603810500c000b40c40d15412 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 637691178 1250 637689928 637689947
    0x6140c0304051b03031308070f17150a14090604020a0801090c03081806040906030510091a1015021b010c12050a020304091e110301050a17010209100c0308100303 71
    0x49210550315580c140f80040e0660142d12806039a03c980d050000541120000f4108100c2d00308500802c2e046440b85900506050502100000c903070014410100c410803404200f035008820f2400001d5590714500e40c2c1580a00c25115500582d100009000a51402c00c07046001481c82034000c0000c001165078481041107940b0001e0046d510115040c000456441c8810000d082c0040001c1e695540711042d100c02800280002da400d03105145503249815060302c05c0444076078006203d00640f0a644001495110340102101d0003c80d05410004011518242407585030701183c020305101030940d50071104081c9141c4d04c40c5c0c10408008155030110b40d0708000d00307a1640c01072802681d196154442031740703184600d9100d12500c1e40340000084d0380e0401c006010b0f8600518040602c150000f2a0b4502c640380401c0c040c26a110181c03031810054848110f01c18085d00c10000c002500300300001000500c186484c40c400750105000008810415911980307140c2d00801c444801c1c1c504506548004010581 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 637692428 1250 637691178 637691203
    0x901081b0103021c0c051e030c040311040b03011e050c0f1611031606020c04090305090d06272a1401050d0603050f0c0102150a150b040306140c030405 66
    0x80c001264140030391110718184a444021205002d88852405c00070100c4c1d020b41009041e4115100c9182018a0780300112070103051412015410302d42140c4525480200c8454095072080d41e030103425120b41c0b0280161030f081d10501c03126212045244a01c2c50958a00801010388024104000b0b00c2e1110307281c090b0f4041c19585045064906141d10300303000c1e0303800e4113101036505110342901c6440c404d844202a030b06950a41d429155032070207400600060318030b00080200031640030b0041e00241d0614100c80051140030f0b810108070384440100c10140e0000804e2001e02100c107034000f0900303200c40c0307900380c920200d851001d000200d11491f0701240780740c0081c003441c60003160018088030380344e202e10180c404111020108120742075580c64929a107071081c0d00700d21824094036184000315170000c40e11182160718500c40c58039030364440b840d410041480c1c1c4807080301090481408504c00e20960301401c042c6110f1303000021803c075401142d40d4002002413a901c2c41180820030000050408030b4080c05102 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 637693678 1250 637692428 637692431
    0x1514030f03031f030c09090c05010f020607030c0207170c312313020f01140706150803130503060c09030a0f02040e370c2702070602090901081b0103 65
    0x115a0f00c856102e2240340c0c2c8054022000c00401040c0901d491780101c510394841d403441400c3d43e0391000195800c07030b41c4914240c00343c0c1000c80010840b80c0290024215214688181c0f2092600c480e000640c411118001880540c0001103181c19030800501d2442c0c413011032440325501e02030391041c0c00034804c0000c00c21880d05071540b80c09040007204182c19031800755018440000c628080c90b103600410007000099100360b44022040c102540299111419041d1704400c151401e5a50741f0340d000a40048080311840c02060100000d01e101d00340083d1020001d001003282c103481c541001c0616200c40a816000341381e508010b0f400741c0d55000500709017001d9120b180003900300140d0002030000d00c0b5130400035220340106041d0b10340e41c0010752403a002c500095100031034041b02402c0094005d4002400040120081580521000526a02140e42407080103807008001282d03501c21000da801c4440d040781e56a80200e4414000e24010b41614098550000142400c0040021500c80120810392850500d03 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 637694928 1250 637693678 637693711
    0x708061f050a120303061802031f05101808120a020105251101060306050a023024030706080108190c090f0209060307080403080703020403031e121514030f0303 70
    0x54003a070800070060003004548098084451302c000d0180d170007110511000c0301c5c50120b40d400190f1245c007c1058bc0e030050000f02641e5200c040984101d803c91800303416008403400006045401005041c1c1074a801c242c07115242d11800340003030700391400541209452a00d65001c03011b400c00d00d21050039003600030b15002400c6a0042c1981d80102440c1e040a407029041c181004a481416002410741c41c00706a1581604114102043c042804440c1d540200c0344040002c1840454801e030040101200341c0c2c000396800f040d10303002900d000c405034000d01c0428600c00040200d0b4a09000a2440b4010003000e60540041c554601c80010702e45e0107003820003942c2c1c4010f500d0040e16981a01c3c2001005800e071580d9040040c00034141e01c80441d4120000b40c141400201c2c0a80300b030003034404899146c0c9501880c1000c204065000548030925402000903621400e8203401d080d01564034800000c001c80e510705814004e804e40001894410107000c1e030722a40c0c46004040c000400c0340d6100d20f045441c10b108 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 637696178 1250 637694928 637694933
    0x303020703210219170f0c0f1927060503070c061131050d0f060f06060e041a06030c0910050d0b0a081f0e0708061f050a12 54
    0x240b0701d482e41e5504000c10b80410002800e2120381c000c200e00c0054900081c1502090300c41141d040c03a510030840c5001480784045498a841000c1c001c0e0810380c0c1a44050800d03c4031443d60030707240c01420507041c08056003091112582d40200c5242c254183d1980c0a20800055581c0c5211240480c4251020000c00000080900d80b08884168429501c80030500c06082900c02800094000000c1080c0b41d4aa55500440200103a6048002c05100c03560040d42e0a01d85001c000071030130411000d56040805021000000d421841154151710741060b00142c81c6081c004000c0400c1014200c2500813444d100504075420340100405e0f0031501c3c100c5a030b0f662039a0f40c601990090003107201440d0000107c81c40c024005420002a188213002a0010001d108001c000c03c0550800b6100e0f82c031068000004900d138480d28040c1c408210a14828003003041c845a5094602d045004e6000b951603400520921620314080c5000004400d00c0c0000d032408a8144400112100040d00c6105c50315200020710004 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 637697428 1250 637696178 637696187
    0xa0b0615070c0905010b16060c200609061f050d021201090c080c0d02130c030e06181c02060f040c0f0608041e0b2a04030f140a050a0303020703 63
    0x26403124485258a8800701c0c9480100308520b806801c0000d410000040f031028103840c10303600c0e8500a054100f1400c101c40d02d0300b41c01403081300248001c100f280c40c4c0a110706a1444428102481400010302151900c9143c441c00d000c3c3c080c2c21100c44202902d114848507481004400a0741c0c8210348950b10f9502c01e03c005040c0038114048048036500303145109061202e0f0b8882c1404541500341610f000745918000c0028620b2202c0707000f50303c44030750b038000316000f074071640300201c101018100040c888174030031040c51400c035045030030398141105119402e858040038080d400f40c545c80d884542d1507000c020500a1b49580004100c4030104010354005014880200d00e000024024284000c002540300c0d40014409901200d040c1c0e10900148504c2c081c0a1076426071000300d80d001a06202e194a43d07004405800b00480031030701c051324004180850504a41000b800150b114a01c001d0b1150810720f0310307041c000b80d00e036528601c070b030041d00c00c00c0c02007080402d071307e01002e9151800507035132550b5141c00c1d00c = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 637698678 1250 637697428 637697449
    0x151504060815010e09060105030604030822060b04060609030c05090916030320030315100917010b0111120405151612020f03040f1203020c1e13050601020a0b06 70
    0x1e10340c8103056030b224550031101000d9040c1c1c1d00d2504902c5040e583d01d28002d560b0b01c001c1c8203540d01603101c8000074001c04c0c400c199064003d0108030121000740544580290004203030101a550155158008502860a446080700070440f90805082080c07454540145080443c800d00e405003140c0000604150024802103004101c10031400440320780340d040042c042000740c038501c2500041c1d04200c2051410010503248101c2c4942d20041e40801d00d0400d1160b00804a81180c080c400c8540010039501500c0d040c651305007a01d10000220750b04034a00051410380e504903039034017503040444504226405181101c0503203100365190b8100f40200460022180325408101081100510305541084001c02d8031384001d104d6a401c42e06c5a00c03030800596103d2095106100da420350200080008004c1011007003605400307401502c24065083e0f02054402d45c0748400651400240080303684a4a4020b14060110009031000c014501e01080040d540d0141e08030043c0c50a02c20400240941d03503000c1d59503 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 637699928 1250 637698678 637698689
    0xf0901090515040603050105060910110f010606021c1e030c051306020a14010605010921060e0304030309120f0b0414011b030e0c01050901050c010219050405100215150406 75
    0x104064050b014900510f5002401400c000a0508000041c2d038a081816600c210200401026001251042c00d80f410140c000141009d0b008100c15075891410a203d44402840d030307500900b0320040780d01640d0031082a411480e4050103051056020031803614400812001d855050000f09082140c4069a841c082c400152202002d6510302190680c1d0104005000b00d20411410800f25080c030402c50a8505602a06001805094081140021210180c0c2070f40c20000c801900c8007a09031904000d60301a0368600c4000c0d80300150805c200356005107050010003c000007120660081d9460500d040d00100002e09001407aa0200781800b07012805030342e80b40041c10003000441c0040d07464242031941d0890800100f843c00b4130342e680c1c1c11404150100f00ca00c0580d9414605203e02c4015100f540040c110300301c0075036090020407441c0c200500c0d0b1884012094131140d07260752030701c02084114100d0100c00000c54009138160800c8088032119140c105820950131040c003900c4102040040042d0340c840e = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 637701178 1250 637699928 637699939
    0xc060f0309170d0c030603050c0f04090f0506250f030e03130e0a0e120301120c1d01052e110309131b11060c090a0b0304050715030c050f09010905 64
    0xa01808009460052a9040303001ca030034000302a44d000c098049810034880170b000341c0c0100c803c07030b42c0e149001c40d02c10174481c00081000480030240d803150070f440b5844030f80c101e52661000051044e05100710140c1400f08160310341d100d01c01c041c616802440aa44c2c2c4207081c0a042d02d034002c00790003a070f080c401c1c0d84c80e0780e0b250313031404201d2640c1e442000118441a503907003007941d182c005039500052010484031841d040840126246901c0c250f41c180c905481a00c0550343d9500f20080450130b07600d483c4100ba09081c0c200d0f00440d041d4102000c0041c0640c40c100003c40d12444010100d419450107110301c114101107003820500410444061400c40c400d206030198092101d14944065841c26400015030405180052140b1034585d401942c00c8108600c04901d00d500c1140003407403200005e0020007101034064980c00b0300e503031b03a03501d103002c203400594044a81d6040b4800078021042c010340031214035415460240441d0400c0c00d0081c220748a0402100c004540c0000c85140503401010320320014800a000c = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 637702428 1250 637701178 637701203
    0x316080702040e070905060406030b010308130b0a020a0b1003050a030818030a031e090f06020306030c090109020a021501060c2a062102130504090204060b0d06050316030c060f0309 79
    0x52a4560444c2d0040c81c0310186070901041b001e007031038400e003820349920481000d803613400d54807007000a8226030021140082c210f5400714240113002e01030301807156141c0042c01494075034034003800b00140c000c1c501c1d0000c0d0030214081020550008404078419014145113a003a203a0008803602d820301100e04141521000400c0b2203400d41c9540312003034202060420002100c401c00c85d00050b01c10354200905225800f82d20750303011603d9a402981c204000404580805800d100070580d1414241c0c46061f2940d4046074081c11550148080380042d4542030003c2c1c0780d9810722001411000b2404006802e0381c171186905c03c0f86200b644105840941e2500e08511000d6031407400030040c4803070041c02000302d290540107194124440c0260f42e480002c0d481e500c0220750522090200404c654101a81d125480c1c5c000002c029071140000d0010041d0a4408038681782401c1c249071038103a15078030400000d2041c9108101040070711100310240d403a1850841440c103042c0b101100680b032006009000c001c0c8045 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 637703678 1250 637702428 637702451
    0xc0506070f0809030f030606030a0207060507030911031c1206081605151306030c1b0305130e150d051c02010504030906051918030606080a02091305031608070204 71
    0x1880d480745a80d16503600141c40c0d030781403c51510b0340905014101c280034180080b81c2507181c03031405180e020300000300041c04c00c0203644500d010350f42c003550408003107644d441000003030003400b41a90304e5449040d00208091a24260350130007000ea11038403101049094100c400c003140860f0401c10040013014115080221682c180680c043c4062083d5480b42c009840c0c104000c7e8012b1096514000c0c3e00c4d5400b003207a91821000703801400142d28020200804200ba8040c06003d20621000107402907075807035150342c00c05c0074248020b032003900f180314040300103000c05c4203884440e4800b14a1513400e50718a440200945006803800b000703844c003030450192030303400174040d00d50550005118a0090343c40003451907560000b80c0d0b40e403042e1070400d2820000b21291070300c03c80c01000003174141141c450b010141c9a9803a11405c0c111030042e00042c845400c000969407d51400340710f40c03500142d078292103e03156003141e61341d1030b542c3c41407804548260654182802c2071007c0d00c0192250940c016006020b908140c1 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 637704928 1250 637703678 637703687
    0xb0a090606030c1805061c0219020d03141f0b03090c0a15020c0409080f0d09150c05120703110a0201050403020106061806030b0607170a121e0209010c050607 69
    0x90080e071000910302040303201c159100c1e840809505010031001e804040c1010144000d0394810511a4014840020101100d10580c030040c00c552146000100c0c40342c100000c02401c000031516114209818107258482c02c0c81c481040740d800c101400b0342c030a0501000d80845c003140f2400d5120071040d40c1c0200820030a00e40200d00c100703008100b21480c1c1d0b0700c2502d0312003a01e01c4a41c1803910703c0041c1e010b500101c1207820150b01c1406014011000039080c444040c419800e254403507104041c0075a201d40d03206040000342c2401c00480b072a491400c0c44800640030004002c0e000e0140c0e110200c003400c05c0070490f81c9000e47d0145d55030503028050302e551009203890190181205407030840041d803a00e140041c080b072044911403056520500b0400c03815240690880107480010541c9502c0101089100d00140c0c004a100700d6244001c001a034544080c0000a04107007010300269280b01e09004002e00c1f0581c86421119101094510051702c0e08169070041f224607000410040c8188105018400410f811 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 637706178 1250 637704928 637704941
    0x303020a150c09090f2a02060a0204060f14041a03090d090303050d1d0303070c1a090304030b070309060f0213120f0f0212060c0d06060c0b01180b0a09 66
    0x250910122114800044104842c0c0804128001480000c0c042c4a07400580d04140d1070b0071008000031950788110000716070760204510030303414510b4010700380018042e018000b040d03002a0040c000c60801f13141160191589000c10350b00b004000903440000301c21410f29081c0c2d4040d04060f0341801e000301110507090500d520985202040c2c0c0715001d0802c940ea84078030a103c0650b40c1c10f503101c40c00c062070090b003507012b0840000100c4001c4031040c480ca070109030800140d807040d0140d40e2030400084490400030786076a000d0500c5411801c08008000c140300000048808680e8000725072104c0d0794421608070300400d414640149510f050024540c0c0c0d4440f944c000d0300b0412a00e81d290003070b46a030307468141660304484400410381c2c810400042c000c03944001c039600704180040c012108074604990b0b550708050085036402d210b9000883c0042c8415a144651800f4124904241c00540401d85942501d1035051107440c0411454071402e2690f80c255802c402180040545000c0441d500d40c4c44c1000a0040d = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 637707428 1250 637706178 637706183
    0x1050610050a2c0111010b10080c16110108090607090e04080c06070315090221090717030406300b03030d060b091806130c0203070804030b100906060e061c060303020a 73
    0xc80304580c84617102c0610440124440041c4080054508000180c1d071101c0010311682c0d00e002c051040704280542c5100b0040c000e07210f001010b451a85102c009803001070003401d1000c0507030014040100090300700c8405000c1d140c4c40600d143e0250b0341ea20740140e0700d200744010401580a540103000c19550550003003024000304100c00004c103034403944030b6000c034050b0220010307003290301c00d0b80b6802d140444001543c003c0e8104081c0c4d401b107521b460f00781e448a1860701ea40d07091a4400170f400c00110764004a950003039040c3c1d0841000c0840c100390743d545048406907452850f250f03038090510060b6010030031190104440c80302480f03000d5454242c8041500300c002494014840d0328038090200b07107058040c40c85060000c0598040c1c58940311484001d003800f21082080d0b2004000c0480443e0741c3e0809031000b18802c0c10140c10314074040000609003881588403140c41814075405000580d0802c030a82c1e0320720f5082d51066100d0100300000d45244800c14820380c40946000800700915a003c124185102e0 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 637708678 1250 637707428 637707437
    0x3020609010e10020f0f0a0801030507050306060f061b061602010b0616030807090b12180c0901060f050d0204170d02030c0c0906040f1a0f0301050610050a2c01 70
    0x59525580078282c403844060940c0d190001640d400c00340d9800e130f01030480003001700307495410300d0b000c01008540d9511026074807000c600715100420030070000300300050203054260050816410400003186888400c000a2407003141c0100301d101c041c400026044003002c00d40da040324010b080c42d10755900306507440340e0000019400c4c00c0c07141c0d142d414004101d07240c80304034484175200c001007601c04640402003d0014000c00505060002c1d820341c0280150008922110041c1142c0c03d200102007021804110803155581044038240300326900c00303180328111251404c06044100c0c100f4400c90312031080040100f03125101003404220000e0151101d883c24000608403a4507501c0048203a90b80c0c080d038040e00e51503174009070301d0720f002d82040170403103800a4003d000400c40c41202041c2d10191201000300b8407043c009900903003254600f081280000754030660080000d804e01c840860003880040034502d06000000681e5619140314000c02a4031401e2016046c61320a41400d05041010840e00000d0005 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 637709928 1250 637708678 637708681
    0x506040b1b010903200a0503030703230103380c0f072003120c0706120e0d1d0d020d2603070224010b030a0506011e03060504060b0301061d0a0f030807030206 69
    0x10311b005080350084010360039581d65800031401350501c00290000d04480500c9203108070030b400c408901035885004800c15924a407039440051174884140b0f00c444005610200384540c440390111038107c1307282d80c0040d175a000d545880394050b1117200b4004124841039110403030441d104800308100c2c02000ca090310104803460220140f075025684040e0b04680184104104440c020750303900b0800c908207071001c11503810501c0e115080c213480e190a02c01081e00315990351030304800c1e4680e8070210038040380c50403c0c5c50071503000315840000c424401001300c03a80800c3d00201d241d81480800ca01d2002e0b1070361076030b0792504d808000c0d2a10380800c41d064903400d80c100021100d60004803214184c4003030710203ca003940e032082c0030100600780141c4110305200501100f070241b60400e01c050140c0c2c0c441c2d5100452050319000074002118056406500003d20500050200036800f29000b00312200b10840581580400d0b000501c001e80300368080c160100780792000008002c800d1001d04a000d01030b8003544d403507 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 637711178 1250 637709928 637709987
    0x120f0915071e031404180b010813200616030912021f0e060d14060f1807050d090f0b060a030309051302120702010501081002040506040b1b010903 64
    0x40c0912035004246074000040c10700c20740111601c42d08954000c0c80c0035001c000907400300c10542c5e4840d800090151041500484050125026400035104217190505540c41e0201248000011044004212141580b906170800c6540702e100903e0b081c00804a5039200c000603a0304407114909c81d0228049020484001507020100e03201100054002d003040c5101c904003c0075031000d507100c81f6140b050220030a06485191521070140074107509000000500081e5410649142040180103511401c00c00c4d82d0a030140d03ca00d0340800010800e000d20b851203480300c030f9094409001e8074008946141c0b41c154810144110b0008182c20140100124901a140c1d1400e204500c19a07000240206010040400c05402c2000c8203001c040da903050014200807040829404240064600f0300043c0e44400040c481000305001c01d46100f0b2810004610b02441c000114030140680d2007180c40640c1c0c04268008a50148020b00c451468520020012100c0c1c1d454040c0500c080c108084204801c00a80d0121 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 637712428 1250 637711178 637711219
    0x509150306010f0302010c020d061d0303071706060d020306130c0503010320030705060f0d02030f180f190201090e0412030e010b0a03140c03150f10210203120f09 71
    0x7541c5c1c040c2e442da0b50b8031030140c09105011aa18001b111120344c3c61484205000c00c0c00a130181078291040550381d60700f0244070003030400303880202c103119440034101406840d43e038080c12221010189080581c603a6a1a80010610403104518640d8217081c07100c145030a5920800441c142c0c0c1c07003901401001e81d11004000b510300449103506800d540718490602840c6000d03000342c1205112110024a003001c0c00229800340d820668201e0b404103a4081400300100b45520900711032000700004180306d04155040c01c4d500d2004401c058294080c844c0e40100b564400d407486000f07400c01d100107040d1410a0b14002e070725002c003507000c00c00083c5002c910300c0d1101c6042c000c0c980e401900420300c900c0103045031500011080d51740289091446003108540c6107441c2448007014500051802e0b03500b0b49041c50b03081c041404010052030804610b00c1041c04140100200b1650440600042c209500800d2010910b4003010602c1a00170741c40104110408690b540018014088242c0791111184818200405e = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 637713678 1250 637712428 637712459
    0x702160b07030c050c0d0506041a10171518060604060b04051c0b01121401090b010b0d0608010e0313051e0108100306020a030f0b0118120c050915030601 67
    0x2940c45010004280881d00c98900f8074189800b5000350b900c10b8001800040d400720381044125100c2d001001000180003030030007291698603511003000420704d480e5011400403140345c02080103c00024000d0b00200f001000a08030003d44040109014280728a48061180c4e01d412801801e1040b04005125401c0034000d150440344040704090030181800704000c103440300c010751508041500c0f2030100104144a541c20700034508000368500c03031949420000d1021034540900407280e03060541c600300050740800ca2074119607200300e0302901c540d4030700019005400c1550001e1110340c00d140160a900f4400b00c0101642181c240d500420260b90304140003007440d240c2020382c40070514407a003000c554016180b0a034490a04500f80d16000c0d05d0ba80d0b108100c0e0021711210000a46d40c01d0900c0c84040603100d0042c1400007400c00002c080160800032800308224050170100c550200da9000420010170340041c05047d00818480880c50b011480c43e9820311030005c8903103c1c1c484c0900024030110310442d1301 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 637714928 1250 637713678 637713689
    0x18061e03021c1b020d0f12090f0c0e0a0501080a02040914070f050f12060c0f070803071d0612310f0203060711032a2a10080a05090111030c03070216 65
    0xc08245901b64041e90300d442001c9030310031110384030340c0c0705c60000e007500c00000e842600c00d082805d480340c2044072010303440c0d0005169024841c41c00c4010f0003684000540c02c9155a030480700800c0128442c6040400207185101d104803d224204d0003158445c0d0384040b000680d4000d031902e100602d0711070104122658100c1d9480c510390004004100090a0300c4014101c070714040038010300d82082c0b036459512590040352030300c00140f103031102c0c202c5283c90010304a8004400316051820454544400d100707880018000500e10480f445212400310b4201806076a90205d848500102d0381f050705046665552441c4120302c6800f07800c0c00a0b071042e015000710b4102520240007941084a808011040034074a008080c02c02c5200305c0c03448012420030410141030f0003403252814a61180e601807440200c030341c9001c50b071090b000f080c800315115612407641d40d4044d40424009c41d55880384042c0d14018012044c1c10284018000b0800c002d0200c0b400003140108400d07400c030794030540b0008130418491018040c1 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 637716178 1250 637714928 637714937
    0x901050f010e030d0302040503060109021206090406061205010e0d051201120804150201020a031a0112050c090d1a090703030509040e07050303030a0b0118061e03021c1b020d 76
    0x50045080415800941440c1030401c01c10003455100000c1c0ba1050384204400001e40020781401a414203000c4103004100c052001d41c2000721095255803030250080c50f41d4007401805c8001000d002845c0c09c00c00007058455500c511441041c00c002d4064195000c3d148900d1181c80703031074108144610111121019034525056075a42080c0c2c0e00300440040207401d9550308010302000c141c05a107900c0c030001c41c0041d500016564610201c0203404c1e07035541c0c04a241804c0c101d00020300217907001108800440c04551002850350744413000c042680c012501c030f00b0f4004812100c1e502c20000c862890303d41c080c3d070721079645078240d40705070340c02d6076030b41d81400020001003040c40707800c4403400c0681040c0c0b1002c2c50f6030151803c058648010a01e55001244d2000c056601c40c02044603550b0048081161100b441a581c80d0540c14800040c1007100c514580f001c50103002d141003003c0c80e1080e8190b8006146150541c000c800215100001604000704240890b400c0c0688001d01d084c00099155a030701c0090710b4 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 637717428 1250 637716178 637716181
    0x102121b1e0c2d101202030a061e180207060e16060801080106030c09090807050a030206180114010611071802030f010602030c0d030c021908040819080f070303060e0a090b0c0909 78
    0x5100c95820601c01c00c10500c40b040e2204505c4600d01d00240d48130308000203000504910340503e1503001090000b08901e03c0c1804d00c000d0001207665030301c2c003101442060001d07035240072a280c60750040140490030101e134010036614100c0c44568800c00381c1290a03c2d59102481e90300c42d1009400c0b1012840000c10b0700c0312542d4100b1142165070090402140580e0743e81d410115681c44003030801c1c28030a4100d005820a01c10010880ca0281003c01d106000c1e8008000101100c004107081c441c060090700288810b09030f50f00404041044024098618403508402c43c44d01c00c4d000f103010703400580386100c03485c480070004a6141e10001c299081d07042101d0050603142a031032416801411321601002c214000d0031810746410307440c99a8103080c81c0c4200e030091b50740d502c3c1401c00b40c10145801e0610f002c00c08401d2000011030002d43c02da030b10144401d82696a510210701d0700764000d001e680e001d154010346240c00c001c1c8181559002c1c2041e280a0010546a5a00c1c0c0c1e1002ca0144202400305500495810 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 637718678 1250 637717428 637717519
    0x6061403120724021201170714300309100503040506061203040f03050a11030f03040b030901141305100209011407020604030f080403060b0102121b1e0c 67
    0xc92004401c00c903080ca000721510b005010800b81d070f03c0101c45c50320a01d029401000382d00c080b401d05034240c0011401800e401ca0401280750111032107007081e107120b007035002443d00d800140000703103903404070b52281840c4110540a00068880c2c1040090510038400380c01c07003c00c12805041124843c550210207801196900c40c1003160000d000c070a0082644001c0c040800e001070b4030341041003e98010070003885480700c146003c10000501181041c000c0e0441c480c3c1c50444603000040d07405950095100c25101ea840141160040c1420460104130f6042d6205005a5200c0c2c4c40c421030760741c3d01683c103075110000402c2000099204101e1218002001080100c03603100003a0040d01c03a040c40100210b02d015501d84403100c000504030b50503282000000303420801c101062003001441203007800602000365071704060011a014244407440700981e2442108106030080c00201144d100306001101c14500d022600b654030302d20601e14502901c0c6070031160100313101800541e00c030001d031500520048643c40 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 637719928 1250 637718678 637718693
    0x608011a030702100e03040e010b0901020d110a0b07120e0105220609021305060915090609040f0f0602180316090908072a05040509060a05070207050a03060614031207 73
    0x1040d010460281003021301c880481030068414000c0d210004545581c141154414000c0041c2d002c5042418108000700c00b59802088850441f156424282c1144400c11001400e080c44498000c0002882c0782c1040542c0b5005400c1c01210800c9410410030090001e4040f4200d640030f403a00304002c54020850542103069100c01a0398605c6000045018001680420406040c10b200001042c2d2142c041040c1410007001c840d42c80b9048400d04c2c0c090000c803401041c441200038080c0c81c01100310000080503c00c0d1454003542c4141d112100c0c24004c040c500b00307100203401400c59192600d2480e0940101d038580050118180c18003c400d40030300b2403820803088000d248860040315110414080c14020604034410b150603600002130740e551503502d5500b40a0081002c0d00709070b100d140b91074188540d80300b0003d00258464040040011a80c46208040e0f00d400c000c1e03440558003000d40080801001610f03000300003110003040d040c40c00d041c0c03600c007007544901c45d030404100620f4080c04540d0114064 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 637721178 1250 637719928 637719931
    0x90b101709031201080706030b0603070905062a06060a05030a0b010e042f030d030501030b18071a1210030b04060b040b0618030c0411072301140f010608011a03 70
    0x114110b03842d14009194160201e50264811907054000210400481c0d0301401901c41c41c280480d401451403800d440042e200548a01641d40107100204241161b03410f248080d810795195100301503281c00b4140c8031a95100011a1258011a44128001407a00700011a000f1440d8021803a04040e03007408100d04600c600104195100c0004010300c1c49405199030301c48075041ca140c2d2114036101c4480c020300d8945400b2580d00350815152400420200d00c3d04411790b44c1241210380d05915281d1440c1e0010314bc9805500580d1584844071951980080060000d0500c0d5244480d800013560750501c1c0100100603910000e048505400b0018000035010792158000600c0100002021044100410940d4100100c00f41010715007030a610f04910307013040030440303080040b1014825600304044100c03180c06003120080100030034140140303451010b04107410050038154000c00c6141c00c102061a141c45040d1800703d000c6402c6000414074911400143e4165843c40f1802071045111100c9069160320 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 637722428 1250 637721178 637721191
    0x90d0509030102071a04030f02120307210f02040f0f05030a0b130b161b080a0c1e06230603030307110a0b0a0b011d031015080d09090b1017 61
    0x500700203420014505000202105d81044060895881c0502d000380903c030243c00c4c0001950701c00c4c9103101a481d400c404a039840450f901d065101c07002030103411000380d140f0214002c5000e040211203000c00d8070aa02070030446a104198070911643c6540502500185014480e05608813108110218800c2c08207030790851000118480b1007040d9450300920810142e0b04060000680d25070312000650240c1c0d40c0644c80c460030a1041000c0c03103599100d2a43c40713585a40014089854201018403480b8680c0507039500c140300c3e03070f2132008080b4900359001b40000c00084816201105002e482e04d10300148580c40f500e4083c0003180795495580302a50841c41545800c1124452100800300091b6001e401c1ea000300844007000c2203002d910380024140e00d41c8104030429000482404180954000801e41c24401d002c150000e0344041c5d401d07105411080d180c10800f05441032089034480c0590050140c0100e6060110801200003c601088101d1107200000380004140031601064401c011065640041 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 637723678 1250 637722428 637722431
    0x60a1d070603020909060405100501030e0c0a09020403022d041a0d0606060206160824062d04050303030a0c030b030d0306050f06030c03130501060306110918090d05090301 75
    0x20100842610301a46030304a01c00003600400c02c3e000e02c4c1040b0b040507401a1007110103000510340032900000c030401600c43d423810907468400c80d0110000a00c1101440382000d4660b0b805140c4454640c03020f540320344002c90249061807a818200c8400e004450784c840040c0e100e800c0c0422501081102504012800c4600ca10080320b141495a41e00170404c0411031042c040171802c14030301032020341040c800a100302e45030034910400c07261321948030b0340c2c80d0790002041e16000c41198440742d0907011117103543c2d0b405410080002e15201a01c80300501c0030700c0c0800e140f03920025140c024080c1c0c0c58070b000341c1c400c0c203030140d0041c40404e9111155070000340710310f0740c9403034001491003042c0006803608602e1000000403030341d111402d012a00f40007030b006205100c00ea506524500300107030702d01c1407840700605d41d040390358507074016008116080d0441c20065401c0101071254142c0240c0c401c5581e0b1029500c0c52140c13010306500c215000d2901c030140c2c03040d10358101600a60003000011382c1c183c0e0104c444a945035 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 637724928 1250 637723678 637723721
    0x3120c180406090506030f010509100f0b06040b0301091a0a0e0402030c06181503040f200303040312020609160902160f0501021b0606100c0623060301180203060a 71
    0x64807988590b1004103041c42c00400c0d6410040c4c03d0600300310341c5c0c0e035510300d140c0d040c58104440108001204030054810102c002041211207085000502400e404598400c400040000d407610310680a18180c072411001006010b002200565061a80040c2113802c140f01d40000c001e50010205000e41c02030001d41a1040382149100045943d401510545c542c4400150310212609104001e407045802810100345903040546440800c00000f8800410b030062200140c01254a4a0702c101603510700501280d488035102e2601d8036a500056035070f1001031107070400140c104000020502c0d4181c51a600940c0240e0500c260240a03500c61034250183c024110b400500103018180d03600c01080c0100300060701c0d0408160317208420b01790040200d40690050043c040305580d560314021140c070450411649405072460280040c05424100031102c80a00c6103189070841e480f60101d100f03036400c8000300000300802c016419101c6250700c0203074240c2d0202e000181d400d0a00d6203e000311000707806811800 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 637726178 1250 637724928 637724977
    0xe0106021507020f1608010c020102090609040c050403060f20091011120d020705190507090902040e150117240a0612060c0e040203071704080c0a03170903120c 70
    0x10504a0704424045d03034105c01c0c080040365001e11030220070303120f039100035490842040c0000e0303100d00461041c82d00c01c2d076681d6240c0da4514006c000f19001035502c400d090005003c501325801c01070110341402042030303004101000e080c6601004507407010b08000c12000701041d8041c3c086418072840d404184191280f00d0582404c81071400251101ea401c41401603a0341d0b006103010b47c14503010122035000d526800c051380d4005200824664242c48200c80e00080003c1c41d4000900503042c1c00d55004a107010304c4030041d4910060340c0105041e04c00302104102142c1001058550f0b030300da0b240a810070913001c040f10002c01c102c03001007a40c001042207004106a503c826003000e021551083c1250515507411083c241190001c0e10071040e01000c0324118194502000041c000800408070941c0e014408800a81000440010b54075500e41010846022107160316001d84100800c4080021440900c40005d005040002c00c468003d81d107850215890f469211204205401128440c0b0351344111283c0c0080 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 637727428 1250 637726178 637726183
    0x3040b090111070c0f05060a090303260108012307050901111e060a05011a03040b0a1e06081002031303050318010c030c030c030e12180603010303020609070e0106021507020f 76
    0x500c1401122007040310340c03415040384d4030604181d03c024000d10080c044180c08d940c101c1c50740703800c032505810403202e040088050418100070411100d047d0066400000c200d03680c0560040da050100c851200d00b0b40c0d84403030141801c01000700c0328400000d20070041015035510520030340140120410881e00903062440e000034801800005508040d804541005002c0303440f030007040e00400d0065800c5442850700341c20341c20140700050000c1d0910f80c15001180502082da813003070084500c880d007010305040b40300940314003511041c031440d0068464408420301d1901c440c0308881c0980d40b189a848100e4685a505558540000f40603504490340902140b0680901f801007120a191940d00010b640b8215000981281c1c2c00c4584c003000c0500d840e00c030158075078000500740c000841b00c81000317481e03041140d44010103007a11840c02c0c2e0044008000081059000030f0f000780140d10340c1c800c1d500401d494450700318911a0910602c0010f078446000e615520b0b804510380c642010191060310f01c8043d168060070b1 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 637728678 1250 637727428 637727437
    0x51311120f0412080c0a030b030a12050901021002040f050d140d030902271b090411070326060402030a02090315100816150203040f090e0c09010b03040b090111 70
    0x2032000e03a0450802c02040b00400d61a110b0100318100070b000d07810641c022520324040c0c0000b50050565a00d071250069404005181e15a548461202c2d4202200c507401005500001010ba0140c40782d4846270560301e40c0c0b802a281035480c038135040e00f16207190408111800080000c1950300b40c50400da0340c840740105100c4010750100980700428000858414000c6109450042d6511080769582c89400b16000380d081541101e08009400c080f81d84040c062502c1d849004100c3d5802880c00a80c82c0f04460b0000c0580001e078000d4032100b03400c61003000d80d0079155151240e81c40c0c1c080740400000f0038501d016406560480000d00c0e0050038403c2c0314001c02e1a1902c215130160025078464200800e00d226006444041c3c031421015184901d0300e2003084052032000e01486400784020a1010400c51081041e01d008103000c000c0382c0030f038503036400c9003000429080c1c40d40d206502400807100d8260903c8103041d41244d40410b81179241d607a450300c03a00712148000e08206180d54a40c1850b1625052683c01380 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 637729928 1250 637728678 637728691
    0x1206151409150c0604150b010509040c02030d0e0f2b03050703020403061e1a0d141c05031605120105041d010c0e03010f0908040e19021c0c0905131112 66
    0x2d0044d400d1a040403551803804098182c03d66060480000090742e004050760035218003a00c0114002180d034205038214001c441c800c2e214146440f41e400701c022400540e0b40700321001c000640384007240047d0041005992180b241c064200800758001d0140c0c443c0d0300840d440152031900500341600c0e507885006448580f140e5408540241300802c1c0e50f41c2c580d00c519a4403540c20415030425159400116a02422811025051015688882e149200d081c070441d105140100e42032183c04040c10030103003940e00142c891046c0e40b0303900034281c3d41d041d000b40119010a070b12004071002581c41c0c1010000507010a143d042101d086c00c8643c01b503445030901500b05070407529200c1c4041e410400d0107144c210303a0f070b624010744500e013862504004034640c40f08403000e07910410814611551081092800a00c0241c2103004180c4002140341c0a03c41d070001106a00000541c107114000e0f04d1b4604960524840c0107e42d8001456041c40c001850554029001c810640c1507170313030030075450480c5c8190240084514 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 637731178 1250 637729928 637729933
    0xa060c02100306030c1205030f041e0b0f0d0c110706050301140307030c0506030c3007032013030c0f080609030403030c0209060109030803071206151409150c 69
    0x42404628100555041185051504000d039515645810042e0752262259180541c1d418986209221080c4200c40165945d40c1c0c24541d65982c4488079402c41d40c0b525000680da20000d000490b100349001e04444040c03950503801810a808a11050001e242000ca00418010f034801551813125050010b07400600c6680c680c1d607160f601d02125100c41c0e01403114018070a4011060903c0041c008a403d203050300c6041d650a612685c81500400e0180f0030014511403074903896030b880b0700a0095900c42c2100d100210072600b0b441e01c1e020307016415143c420910b13144801c00700780c001c05022100d10103403c211013240b07484540c040e07684d1100c050140301d503007080c42c020700e142d54140311980c010400980c2140c03100b8010b5103403500c0e60b100200801580c8030f009200e011010041440c0707030300c107000c0003018541020101e40d9905051801601c18a400b08003a10290700344100020080c84c0117401d00c1014040d5220720300d403040004100c0c8a40e6001c120000c0c0c0c010290022816014008009884480d061000 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 637732428 1250 637731178 637731197
    0x212220302090a0c030b120613241e05060108131511130b09031e100f0506010305090d09050405041a0130080f0c2a0108011e230a06 58
    0x1401000e40300d421b440daa00808000541030a84040090b005511042d01e88014400b205285480303041101d40001c01720a04c141561203a00346804c50b40046070484074424180c080c44000d40303054080e40e034115922404200540c000a61241d02c80048641c8203114a8104961062400c003510480c2c410b8203911a01c1c41c0082041140d00c0254001c0034041c110121040d030422000a00080e5214894402613032100c8044219000002c010418810300700404242441810040c1d000c1500501c8116440c500090130a00071880079000481c0301960030740305030703036a0302407608010510020f043c01400807030741d4205d07002143d91403030a4010810b02070400d91409107012041841944110700f800d10f823140610241042280009400c0801c444400b0000c60500e9221150800000e0414260381d0036040700384020241e000d900140240901944042602c8105040e6200c1481031300b0019901865681c0d8401d074203003804800c0880c050f000300c0f000ca040c40da1548813074080214501644070707131240010403150303c1c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 637733678 1250 637732428 637732451
    0x20307080d09080f07180906020d05060f040e03040504020a020709090c080d0f05031801090f11100903050c0d05070807260f0a03180b0304150501060212220302090a 72
    0x82c0c1c080100040c6009000c1820500c19681c4ca445880c42005494003d10609040d0400d10b500015181ea410110840d01c030000076014402600003103a00034841c014450b0005518503107885120b02c400c4580380103500301030403e014031000b54481c8081d18194071980d140060214003601400d6142c91103143c565460038a0184d00c68602030545a504003072140940c02d030741109500c4010b50754008204030144490200c2100c01a0040c8070340d403c0601038000011035401400000010b081d840c5105031000103003211045d004448050740740c0002801a00880d07031a5a1900d0454032200149010303100f0b0314000c40c0d50703007150b07498058254400704804910310354150341d0f900700700351b20399804071002c02812501580029440d181c00602c0c10080a200d00348429065881005d9000c50103810b80091190740c81c01c081c203080307169522132110f010100d410800089901c40c40480c41030b801101e007452050505082c422021070440c2050030001e21110011000000b41c0d0b1a6008207000d0303520508001032610890 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 637734928 1250 637733678 637733687
    0x20307090209120a1e0f0506102606042a120c050f090a110f04060203071101090e1305011b08090111030702030d180602070302071e0b16020d020307080d 67
    0x30f00552489400c00301d0f05501061100b0b009085200b01e0302140303005000c0078940301054140400c4060884d220b15030400094456407201c2c7c0c03043d6000001e5400d45a8a20541d42d1602ca2500102d1090f94000a01090001e00c1386a03d180e40410814040038407007107001d203003108504d500d600c2a03240380d0010842c44140040001c00001511090b070b401c0040c040e002c4080790607210302400300e01c5c61954071202042d220b40e001080d280618941100761344d9a076a5134800941d690081c08098905001090141c0802d60140901404840824800d40150750726054082001c2104040c1524070b5500c51046841c1280d182128900400307281d05c1e04582801c06522050850f0140041c038121040d04209004002e074000098442c0d6400c100c8011800b20200c4000a89903400c210b001040e203400403421104140d00803440d07005032806041c00401010315a080c0e45940c017154412561420303010825031010301403e0140040c2d1368000780030f000020b44180e01280c03078446694000303c0b04e03401401d040704089034403 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 637736178 1250 637734928 637734949
    0x8040303050903030402060a0806040f0c0c1a060904120302040b03010f0326030c070c030507030f0302150705070209070513030615060c1e02030a14070e0a0c0903030e010c020307090209 81
    0x1040151308614150b804a034442c464180c80009000c0ba110005540b0780e200e402040c03100d03601000621000c141950041d00140113800200e54080b010004180006818a030041c46460001c080c00842d40340e82d21a2100c107102c012072202095000c00000ca4a130800c80001c44c002c180c0c0010610896180d42005000c0d06116440d683c000030300781c1c0f141d59200540c802540c0c2c0002c450a103503a90303445107240404111040342d10061060160324800410302015608100b66180030781c081c0c0703580100345418094504411114080481d205210706e42c0542809d4806c40c3d840720840c201986410500420403910034440e91003103400e181c4a4130000d0118a003d55500018042800c11178001d042d1079890f4080c1200c409a1000700c10301c501a040c0075950300f00032a2204c9038003c009040c41007803a00c412511044540503117482403e042c0d0124012204612944120096030742e00c880384030b030071540c0464441d500e2003d0300e4100170440c00d1000140e50180f02a1000301004c000040c0d88486560030302c0035018a = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 637737428 1250 637736178 637736191
    0x30106081006110a020915041109040b0a06090b0a090b181f2307021914010824010201111215010c05120c031201060f0801150518041107030804030305 66
    0x1030f0300c945060b420500080d03080080da07045802e503c0580d221403141c0440307410391038031a07401424904103000c250000001440b145d04c0c05d036001d108908030f81e0180001d42005126a5000550100c002c01c6800d00c0240035201041c243d00e80300703031682d55440c012041d9401410100340074001c41c5001140900d494100565414001d40002c0d16040b9000c10140507205158010300c610801d82001d24410610f040c00c86501980c014403a80c101d445104c06d0a18811041c0201140040710401820696000381da00a12030f210b038540440104869001d4481481c2c988141241590348602d60400048000c402070607403400031041a1240f0318124460440c01c0e1044414581031202c3da9800201142021442a4060201151301a0f40c1c030700540f1801d00e54440c0001d512210100340d000403034210ba00070740c20100303500940c2d24140c46989071f0b0700b0545070b402690040710200f00c0030020020760941c1c9884070001c03440000c10000700034041020003845541704a01c00c07800907100400f000105601031140c29001074 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 637738678 1250 637737428 637737437
    0xa060506040303050f0702150c0d0825020c0a060f03050a0e07030f050322050f03010c02071403100e0106050907030b010c0605060d050a0503250203120309070803030106081006 77
    0x62401011481a104a01028003080b000140302140904888102c0b40d60541c0078001492000e10441010b08030b42100c82240450302074003200036803e6102d141030741d01580300c40c950442010096950740c0c02e074801502c00501540a122083d01141d56a0300e07400005203030030385550501c40d0740c41c50020304645000b085003031a00e1070035524003a500400209003064940c00352810742081030798140946180036000d1a05c468651160451110000f05151207040f43d00580e82e41c07008440031001c150a82d4007243e1070320b0040c3d00c0345904004801c407020002d50800005000d44a00340c1200500e482542c503440181560783e911114104040c0c00c002d032495a1050151070100300203032406000030002c0010401c0500055220001304489507a01010134101c039071701c40210348000c0e005140181d140e4001428007118559002c10182c20f1070150f02440b0f2641e07500401900c58003641d40c00302885508040c00c40d0209100d15040452952400c00095002c0c1801e5121900145010792426031110503a800050410 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 637739928 1250 637738678 637738691
    0xe060921010c12111b030f0706020a09060c17031306051f05100c032f15060d0b012102060a03150b0f12150a09050406050603070509040803040f0c0b0d050a 68
    0x50500c1340c113448020500750501441c4913807101e400c5d45103000708015180b08510004d19501003040a5000380328042c9d854035400e1030b050340c883c400d80340d1806e4104040e02090410a51895000b40c0100459000d052607801e9040c2d116962101411210120740c43e2141d0080000030007004001050280c0042c1000c4542c1d46d9030300c0302100b0091141c9024000281440408004458554405160300004600c6e80c40c89906a408044c0460758400704484401c0c50a102103011a0007801c1151410032840c2c3c0012080c1103507444d1210180c10b0030090a9000305080704040b24000680e10300e001041a00741e581d40c00310f000109a0400130b1108802d0b805100340c0c0d281008040d00760703840c80050300c182500200d07a401c807558603100d01d440003501b0641d4140d8045003c0e10046140200c581c01140207a01401c42009150b842c001803540d035644900401e60b01485080010b400a2468030045601038440d01c0746100d13120365550f034180b0f246540e4208004524020800300d4048603644211a400500c0340000e2050 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 637741178 1250 637739928 637739951
    0x7051005010312080402031509030a18140f0a050d0b100e100e040f0803010b1b0c010206010b071505010308090108060307060806060918010906060906050a0e060921010c12 75
    0xd10702d1211510140301c100701c0060151f540a011201a030102034480c1d210524050f52603648135804594000b020800c02030b40c1d60b08180b440c600d118152003030340b98071414850174081006015025100019444a03115002042a842d50f0300103140e2184185000031150900c61646030a807452a0440b00804017100208244100c07102c0242c000c03160911106181341d2101d00b4800c8034150402c03005400020004000603400e41030100500104000ea020307209010300c0d0b4402c184c3c45c1c015001303050703005911200050240740c9131100180a81032040c0c0f100c440140168628500355035090384143ca941e040420440c1c5e0b030f542c0021455034001021006008811b05003100584484809003030b25004490120f407024840d222003065200410840950030070b40e42c3e48910010240c15180034a0340040d94080c40015058000c0303080c1d4030250388649815002000d04018058607070003100440f0390284400080c0d102c001504407440303807460f1503000003050f00c2c008040c002d0300c600042c800712401c0910303007041903a0 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 637742428 1250 637741178 637741193
    0xf1e0c0d0803220305090102010608031204140f0109060f050a2c2415010f0503060103111c050a18020a090f02040f15020d080606090f030f0111070510050103 69
    0x1510354885040380e280c3e291203221511103403000451000d0b10340000b103003605054214010340003010090340244040350321a171403603850303005403080d250015405101180000c0c1100941e08600300e100012035000bc11100813040c00d4521145003960090b564099801d40c20a1602400341d110310040c00a00156010301c0c0d4a0030600396007107840b0701041c19003002000030002800341413601102010001c1001080362040c00d01e052050342c040c020101056089809035010f00e0b950301b0a1400354072103600390365600e03006402808024250b94500b4004012800c0115a00a50300c000501001c000041c079181ca83d8040c4212070200d0b40c1040342c00070b40718051005a5a45144805551100700d01090510302600340714060b001d2900800483d840480010509110260640658200540c201c8442d42602242507500d5101610229000441003214085a0502822030000c40c4409000c542c10748912640700c900311038a40c43c0c00065080005006018490100541c600d0980c03a909e04008651465441c0030703 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 637743678 1250 637742428 637742449
    0x3040b03071803153210090b1008040804120b07020f07050325080708031206060a0c1415070f0e0609030604032a0f0201030c031505040905010b030f1e0c 67
    0x100980c0d21092008415295042401400002d6118007501141503d450a200c0f03442100d00909403005621b00007085202400b4502031003201424041c1400c0e04003600300c98840004000b030b01c180008000001c0d0040b407640d8040b403094006c4100b455582404d01c4003c0c104209124244550f5012210a2000781c1d000b04418030040008241802ea0700c110140c1c10449070751035400040345005450b0002a09140400180781c0d4480d410900840c1c0d0b5955400c2180500620003a0300015400c41038a500107420030300b0418404009804546011060b0b134138894666804455810000d8280000101c640f07030016200341403084110b03240c905180c13000020a969650040c405010003200d10081103680d81c60150484c2003401c08140c402c1108281c0c20b0107010480e00d02403c07400a0300e0a142c030211f4511034420300c10503031441440c00d0407052904003000054080850107071455542d030200c94810b998108012682250b814002d4009005e008501c0400200c40002003840c5400c014204042c03580d9480c000c5 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 637744928 1250 637743678 637743713
    0x51506061801020106181b03061d070509100e0a061707081e0a020304210918140f0703230a150308030f041704030312180503040b03071803 61
    0x7248084030340c00101e02604269120741c0d00d01501c40c4001c9828030068001001d00c500030b4000881858003560200d040300c042d4483c4403103804046094001801c000180360742c0000303c6207042c80c05d00555000055454840060840210341c40e0100c0c10698100b01030b24000608290a00c8840b00105200144e00c0c3c180040c480403c001c40000018260307941c2c410709085801085d03000400d9444c00762071840027940151415503440840c2c00c0d0755040350740e011300000a240b5481d554080c0c0c192170241c62032580d440641d614042141c403107440900c0400e050104a10401c0b80241c0d010050504403800b0b0100c51480c0035601a60080d0f414600e8000580c064250308078044110018504400307507480824074595400061500700d00105004900c10102880d5004500504044030869005109902c40e480fa03440014080382603900f1000015400340e0281c488400e1008580c0d42907007482e91444d045510642005007076174070100500c40707000c0d8003545030501c84620b05418000301d41551140c0000800b409087c = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 637746178 1250 637744928 637744957
    0x302030d0201180b041b0603051014030d0f211a0303040e1b0706021603030b010203190513080706120e0705011b050709020c01020405030118170f04030b040803010305150606 76
    0x200f41000280b0b11120388003850346d920101c1179a102d040040180206071040142042e034601c010581510440e01c105080a004000304845200d440084d50105520441141070082c15010a000c10786200161224404416000100083c03040c43d0341c8040103a03044840d00940c0b050005000b0100590304184c0c0094404003520890200489070901d20300c160040100800d001040c44074501000700c00c1c07402480d10a4405010300c01c021001240e40b401400c03d219a0f0b2940c44200000b220f0040009100680203050001700194171902c4980c40c0c0386c55a03002e800052001c404c0d42c82d0300607a078494581120315650150809501d40000248000358003d00125850080d248560802a003045071000404000b1070554a440395040c0c03440c000d400510500703009508010994581d140503c3d101e50482c2c0d4004070f9241544812009840950414030709020a400100b00c08000300310500340301440b99208103101c40c2d50f5810351500341c0c1841c24149203d00780c44050000e00c083c540d00c00090f1070700203005c14207 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 637747428 1250 637746178 637746181
    0x5041101051806042402060f010b1e19080108070609060807020102070204090b1b040b07080a02150a02090f03060613020c0109140a030801080f03090f06040e0f010302030d0201180b 79
    0xb0224054071080700039540940002400940002010b448049500134561501a95100c0b540160b0b11890115011513070010701000610506c040d840140031000c007410480282100b40458808050340200c02c1e6a1041c05845444c03080550701101203400352807640003901045150810180020042c0d001c0c1c8418070580e00001513001d4400d5064500c1a03800400c248070144440c280161249816618a8801c1030501e0350703000d80c8078141040b00c04071a00baa9503140303040c5854540d800d054000200000440c083d40d8000040301e40a50030450042070500c60061743c03264000708100d00005c00e404c0c10340c000d4006808000d960760b61110f2030310214074681e00242ea503200080b01c00703005101180c0000c142c4201000c4900d8000c500003401c44103a4400d0301e90b228240d0300e90f10065951003230240101c42503841080800620b040440c2c035030100c010301611141c00c0644030011035007600f40486200000c0e8401070010025881c041000840d2070200d40020044801e40700c000312003281d0000c00240560b400d640 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 637748678 1250 637747428 637747447
    0x10506010c0b0613091a041506030b0f0c130806060406050a05030a020d020a1701050a420b18242d03040b0406060602122a010617100504110105 63
    0x80180d5a51a441b0b20309000c81030500070803101000c000e5070151803400319406010000c1d03015104a906894100300200955650701d10080c1260400911a940c00c0c081071018079000d01101203c01d0241404034050f0440e440e043c000d21040302c0181d4000ea100b02d038248800c001c2502c0c0821340c5038050703406440c0100340d1041c038008030b0803a07001a8020410b40d1040b00da19101c40300198449402104008014449803c0000c5001e5000c00c2c00d060083e08061500d0300d154000201e0904403000e000c5c0e126a0011036079880c5500c1015070040464559502c02034001014a03203800043d00c40ca070072100910b50074000102003002e200b07001d030051061304481c40c030b25030062201c0d15000e040850034440e541c140e81c80c5007605d40124580c1050b6404c0ba8190b0500c5004100703a070020640d007113032040b4a00002e003000051010200b14a401c201b040204180f1030010911030038003801060090031030400d281c0308404410091a1606040042e8141014a000b0911000400301c1d000901010701c00d180013902c85280c030 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 637749928 1250 637748678 637748681
    0x2503050c090616020616060b030601032103060e0c03071e09180e01020304060905072c070c050d02060915090c060901200703030f030b21070302041d010506010c0b0613 73
    0xd04080c1d406070000c10b4070480d04200c8094682420310447c01840302050b1401070650380c000038000202848640a2020040500c420252034000710528001c01d00d20703a81c1155258074401a070390210100d200004201025803c9000380706d040001419880c440d00b4105402440000c03c3d0042e4441d85039550300d46204a04e56410002000301248021962170402c1d2520700014140c0b00d80131201e03030044603c0020401342035881e50084e2075004100310500700c1400c80507080743d40d00502c035909001c508103501012400c1001200142800307030300106014141107904038a002d020340501210140c115080220449020a030860b07001004d0f2010340e2940c00000c016140303031010407820740b154009546028410310000580740d080703a00a880704541806491000c4050381d80903020640c0101c00c0d040342c030b035200d0066240c4607841103170013042c1d0f60166240d50002d000d95007030320b801041b20334841c420b0f04103036142881580c2d000750302401c28003001d4a0655980000e108010105803107030f8014903404006074401e = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 637751178 1250 637749928 637749967
    0x5070e0c0d0509210705030a08060402071a06040513170705010e030307030c0305010605030609132406080d020a020d0602030c070c09020703020c091003080714062503050c0906 77
    0x81c89400c0c41a8901400015640d40851410030f01e4880e5102001072485050403c4840441d0018003441ca0640c800f0b80039280c19102030560b94000e60b08101031030104258060a01800300c2c44449404242030100400043d0b6001414000c8020b00002000700001c00c8071509100c221030010b40d094071460142441401081c1075400382c00329000c00000c03c4001030b130640c0000c9a003401c0307071001c00950346c0f00c241c2207505000c2143d2254010b0801c801080c0c00c1c400e9000c42914051061811281e81c610140464440e0480d4060000c0340945400040c06540418044c4401c6528148014484041140c00103080d060355003201501c9641d001000c039140f003844170f080350429034009207036001956888681500a510020090b00180126180003031546456144140190024100422160300b103440d0103155510843c8104d071004501200178403542c4050040030f124802c0d02114603400300c0c00c042100c008414409000041500d807404000c100004141074403121030040c0c1e0341d583c644d07049011001c0c11480 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 637752428 1250 637751178 637751197
    0x30703030e06130803030103140c10121506090302090105040506010507200324100303020304060f0207180615020a05030a2609060a23012106020703020304050111060405070e0c 77
    0x3110300040b1305040004021412644141802e008107070ba2200e90035140d402c91041d10307512818019055801c1d81c464200d52240001849001a13000e402c5251005141d1250f0700910115031880000c00079231400c5071280c2e00529003074a052040f840c2040000f0101e00c1541002400c15079007101c2c012a050254144200030380c400303004c841d1164054184a01462a0680c05818141c144000075411000031a82c0342c007100e80c1900110300f0b00d4200102503900e03070b81e02d00000b401c6110300c0c04002000618082c2d2402066840200010030605102441c0c036843d80b41c08440095502006c070a400280c0f0000c2190b1441900785446c00c0040340c150980c00c2c8100303803641540528a2800180074000d00f012503140d0040402240c10030194084070f0440e001071001c0441c500039a00681c0c010440c00c0b5040d20f0408081a4010ba00c1d00d0f05035040e41c0d42c1080343c120140560050b88086414000c5581050030701000f0b2145000810003403070a580d440d50b940119000e040c1501243c0400302c0c1d00340032004141c82007080c = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 637753678 1250 637752428 637752457
    0x30f130b04080109060b030a03020601090e0c15070218010b0708070213051005010e1206041401180302060402031515040f020c030d050f0601030e06072a060c1805030703030e06 77
    0x2070b980e0454074060008600c0654441d0710b045030409651a000607104001a40b50b0081c0015a00e44118a0f0041c1580c1a050f07805020703203d1040500c4d65a19810048400d0260740c017a142c000c0c0703006001010f6885040700c8028031101e0014012240c1041c15a0007260b0b200f0320090303417030306036102107110350403030300722442c04241407206105e0005140304150040d20b500f81e8601210702e6180c0104100e00240c1504110035070441703000b0402203404604409404043c000010130015843d058880070040c01c2e280a4005030884024441149818800755494031030354140308006003010b000100d0a04040c3d0500c9214694810307070509001000d80548101060790800e07651541a0412160090701c1c1c101e5001d00c0c101c05000018080f98042e2241d80c44240170348004219654034004145c414110030020704020854a1561820341d0000c414002400e910800d008504018107440182030b48655a91426040358200006c0c03107207481c0051000100c94241c03812244001d042c0010035064840d0b0041c5a6005 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 637754928 1250 637753678 637753687
    0x6050c1212280228080705091207030503040f21170903120f0a03050603060f04030c0f1205040806060d0803150f040e010b120c0d1202031209010605190503030f130b 72
    0x40103540f13950003600d80c680303400018010281d604403182c04017101e181004c5201848884100e08021076410180c5c1c03602812910006c2e03c903216546550810b40c0400d4031404145810b0040c0d4801c0300c901c8010a00c9200d0130700320130100d43c1d1210105580c40940054036040440c1c01c102d246d030100b0ac058000c04a01e00e5a55031194004100c1406078015400100030900f864003058032402c0010741d0503c5444080c02c03502e03060300c0350759080b0f842010504040d140210101020404507102a0b64100d1003d007a4484030b81d1035140030f9920b4100380000785440c0c0f0800d8900040c0d000702e480c040460b1b0340410301c0303040414003404900004906118103034880340c011786041100c1305030070b205600c0850340d1341040790100007840621129541c1c45030040350b12500208510303607040028140c1d65000504d144107006490500390001c0a0000905086413a4440b5070b45813182004242030400750703100f06d090100c080001d42410480440d40e13a2007440218220044006034074401400c001c1c100b400604a0000c01070703600c = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 637756178 1250 637754928 637754947
    0x5030714130609060f020c13090215030702010b010305090a02010906030c03060b0c01020919180902130903030542040e070b090916021e0106090606050c12122802 71
    0x24055180611404107114031103802105000042280281400074028239403540408140c0d000b9007144401280c011074170303030b45801c4d54000180c0614441d01080c1c0c000940444004001020341d0030161680c880c0381c0000c0540d5001d07076800014103041c0c032024200407850300230403001200103221541c8940842d40000c1f1300d07803003040c0040d0001c0902000861754100d1005c2d0711a00300082400c10b01c04c1d4804091450498140401941c01c1070442d00d000a000c200c00300c40da403000381c0603146103e904a0000b5070340c008100000ca80110b220200140c0010004917078001203010303414050000912030900c01c40f440783c42400b6507894201c07070200c0300e0079804d8904c02640c1c0e80362449160051710003184101412030002d0048148800a04144101c560081080c840049401c4030301c0700b41007038615aa0754a90b100460601958091040100450780d5440da4448510380c0082c20040d0466030820a20810040100742e8810840f0082d049046240051890301c0c421300c10160004245007451070990010895400 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 637757428 1250 637756178 637756187
    0x807020c10121103010803070b0919150501091a01030b030a06020712090b07030c020d020a0503030c07060e06070c05060f0705070b0418060308040b0c030705010e010207050f010c050307141306 84
    0x40050b4040803e01c401e50904403101c5107030000f4010b04000c2c2d40103000380710125480d0400560880003500075075a030b040031a040b24818044000c0242d50b514210400201600d05510846004040b105810086c01c05101e4049681441e0405210304040c0c5803107041041c0d54080c46041091640b0410440d5600094035111811550814103140450f035101000100b440000084655080c0d261b5541d040d114056402c0014403858190140c0c0c100400b0003004c5600c0d04c0401c01000b0882a040080c0792580c0383c91002441c41c5c2c002c088842c05030100307020080000e2200b003c40810b0b241d0445041e1380b100c02d40c0c01c80c40a54000c0003400761103403250b4038000075405c03540070080058440350a1524224146a03804001707480180c4801007400700108000c2001c0d600400c00b51008079040340a8034034041407602e030182903d016410990b0a42d500090307400c20403034100504086a000b940090083c800c680001810714040100020700b4051440348020384540c0b24400c4070302082101d07101d64010350b110b000050 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 637758678 1250 637757428 637757447
    0x31b050c0a060e03060f0a0e011401050a060905060a03231512010536060c090429040c03093e0f0d02011103030a091707020d02010807020c10 62
    0x90041140700c00110700e5a104400040c5000c3c8060010451502c500080c60540c1d10010b08010390103030744103403204a0b8407082c06144d8402c1c0981d0046401c550501c0c0c20050401000e40c440c00600c0fa46032400c200030748600040d03c0790041d0a05000440142040c03403124541c18169580d002005c120080040b180e0a22520700041c0c181900c112241c000101032007400c803a8240d85800c4880381420044c816a208030000e07100e519144048682d142d0b48001e03c0510b44002522a20508080070442c0d5406080c40d1142a102c3c0c000c0c1c3c0307022480645000300c174000170504001386c036020f02d4495400c112200e01039000360a040fa80008841500040a4002031400d0980140700c040d14036881c082200103d500c40c1d10341c4890b00c0040200034150060300420103148007001040b41400540c00501c1406081400a10311030703522250080b40024240c41d02c40506160380740c2d0841e40c100244080c4015031100303901d95940c2c581c282031420168841c84416440e056000c80c00903840407202600c100c0550303010340900d = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 637759928 1250 637758678 637758703
    0x20d08070506010e0408070f0312150509090111040b07060b130b01020105060613060809010e010e06041b03030e0910080d0c050709052a0d020a211512031b05 69
    0x5030601e13600c4410050000c0001e44001e810543d05001c0d41001c00c3c05801920440c51003030034400120014170841c07000750303082c410708a40100c07280042081541052010242d000d46c80100801c045846200c1401d07150049005042c5014008a00541045050391100c814008000c140d902024a45035030100941001e0080341d006508040220f012801d1501c29101000d0188042401d95810300000f290764100060140844d91b482d00f4521071030030803e1181505200c0110040c05440c500ba003046c04141e110b810030140030113050281000800d50000008030201c40c2190300201913201e44500e4542c821480d00181d40d80e00600b46075408042e081842850041d101c0e034141d0f00140c0da640d032500120b440c12951506050952140c000b8020070400780070720b4040da14050760381003552107040c03002281c00100c0507501194007000c880300d40015171000140340c014581400c0c8860360340b4490402d00c4a25600c00c21a00e03d10382c05116040601943c2c994000b20001b10001d6100402402d05554a81040402 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 637761178 1250 637759928 637759933
    0x3061502304b0f07061a0a0e07080a0506121005181f05060604120308060a142d06030a060306050f01080613030e131d030702130b0d020d080705 63
    0x1030064944071000d42942c0c100003014841c821503103030b49484180c1d12036802c1043d0500100101c80000f501841085a1142029003203440007440a061000343c0000d500720380d0b01d0710a042d0410a4481d440008a42e001c80c01100100d201e444030408101c1000050600c461a030040400070000311100d030307000521400c59200d1064941d07d040c500345848000e40d85810518009050b0039040700d5005070400c0b900064040d1145251650b95101641102c1b503e03030b004c9002807081c00600c1001e04d4100f58030405005c141751314602030401d00340010038040350032400307501080b41c0100c00c824042400c2125a24510094800e82e9607181c0176180000034880741c0000c032a0940b5040c080b81c40d000100f50001e0588014500030401d076154040d0900c4018200703142101040b900300250310143e11071f6461a002d0740c0c203040000c00d0501c001c0f289081c03012481d1442010365402808020302595940f800030442c031503501c5000503001941804070b80c40e8841740c600a5003016a1034071800070403464000410100c0d014205 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 637762428 1250 637761178 637761247
    0x110f0f21070b04170c010902010206060105030106020c09040602041e0f090b10110102040b16030314060310020705031b0d030e0304060e040b010e031c0306150230 71
    0x100305211000e9546028144426800125105491500503005100c483c0312660600340001040d0721400c801440c1387d449590780c0d011540c04005081d0480f400742811801c42d03047c043c009651b45d01c40c0c03407014420258540400c0c18441e0950448001d840d514446a0241c0d00004100e18180c03e90320030741c540400380080005080620384a4188503490003000d803911070755880c000721034400000d0702c1229955800c10002030a044004000c1001340229256903241c0e042d42e0502400b101c241e20b06510800407854100a0256008540306c03e1841074040700503101d155074144180f55024968800f86c00d908021501151801c0014240c00c0c8510250340a0000e418008203a644a0040b031040b00082a50381d0784000e1149800e8020b00170078003042c500248440c00f070500282c80c1c407800300070314034550950100d00c000751a031600a5100ad0b021500704c2601c0c0c2e040d2a503001f50342e0b246452040c940c124110302c503407940e84907240348a55010708034000261035981001d0b049000030503071b8a1440130001d5410 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 637763678 1250 637762428 637762453
    0x10801080724020721031704170c07080d0804120306060905010e06090d110f040204050306181212190b0d0b100509040c091d070302040c110f0f 63
    0x20316102912614600d030300803254194124482045241405015405001e50114003a4040c3c0345c00c0d12807036510310f040d11290340f4a0801502c2903180c42e005024840680c400c000c00320381a05c2c5050034121001806554030b00301106039900340002e90300070f900540601d4960301c100d20781c414415801540221200c4440c41c010045c25000c44d94940f16000110750001c000308459802124002080f80014040798074000422001420034604014100c600000310502d84d0700c1e07410408050410030340140c7e011031500b07090000003951303148010404000a188c10741203c00041084c020314500040010301d164a69070309110450350114116240c07560800420780c5440701d00103a0080040c2c4400140280d0bd410032079460f04020100024004980d44e0500c5000003046c0d141d540003244100d00504c01041c3d01801c100b508001e031005ca03010320700e0041d01a1000000007401213505021030b9412200018014520641035410b440310038001d8200d070095440b50f180841010460401c40e0b242c5109980c10041040c = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 637764928 1250 637763678 637763683
    0xc03010e0708150f21010e0c03030c190606030f12120b01050304121e03090213090201050f0904110d0c02070611120306060c0a050706020115050906060a180f0501080108 74
    0x111024880c84601c1d0f58402c03050704003003406403a1a03a000c1e00c0b02c00c91502c9605e180108401084040500369580d0310117000c0010103200f41101c2d0b00017180503500e0090081181551011194454216140b004280d081000151f87c4110700a40d400440700b644140d941c00d0139407040e00e16048502c08541025061582d035402882212811a016162581561600c1d1541003440154503e00740074001c5040d070b021007545000c00d01c654102d18541d00070603c04602d10601190b59600d08038a640c2a0030500c8000060780c010342503a400031000c0c2c0400751140c1d0340100240c090548910307246501440002d44004811a80d00039480340d039066001c46244940d16881103c050195100c150743d9a004901e512500e000c2c1c0b10300131034200c80000c15007401e02a8007010541002281242110300c0e030b0110804200381502802000c0030681300b901018646d910341008034040c40b038010300443c0f0070341001400c60070040c010030b4104a01d4212820400350582c581244440642640c0241c0740410741400000a03400e200 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 637766178 1250 637764928 637764931
    0xa150203010303080c07050c0909100e0d02030f25030309110a03030210023004120509010207050d0303090c0b091e060703211e2403080a050409050c03010e0708 70
    0x2699035800c484c5d491072881942900442011a9580030709000030344103507545103125020710300078405042c0c22682c2ca450301d001c0310400000c1020f181c210b0740c4951030795a000720a8410f0040214a45507460403181c40008110b64080720f20000c141d50001c0c0d81c000e059169200c100c1d241d110300701c6030b0080c0c03224000304034010900d88401030041e07210000403400501c0340d0b000760640d0850b650f4501840c0d1200711181030341c1c0311540708d941c0b2804010801c002c02e00007111445520490503042181c5010702d0700000039181c490341d000b881c1c002d0454500040170103100368042c402c0d2941012800d49200d440725003503040d99100c0c0314100d12a10030b0a2100c030341c4040140c0105180c01000f04010301d401c2d980e0341c069958400301210004401c1e0a405845002080c40c0a01c2c0c40c3e040175581c2c42624003610000010071100240c0090503034040410050030100c54540d440d0b000da035000742090741ca03000c2c0508100c42501c582e4000007002c60a003010303c9080484180594103880f0046907100d0f05503a482002c80d54a0070 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 637767428 1250 637766178 637766183
    0xc040e160626040501050915010e06150c010c0c06150b07061802100203030106080c09030a031409060735190302071a06030d0807021e07090507020a1502030103 70
    0x145884100007050240480b65481c250041c02c4940a140c0240d90200c1c840c02154203503003c2e51204200304042d0f80611804244540c810703111020740d4104101019400401401070307014070b02e40444059200d42c1c2c402034468104005000b40300b110b0303c045004110342e184c075808941090600180581c402c440d502c0340000d40b030400c11a00d042880d03548440c0e01500200d80380046102403030424030003684034281212081c43c01900111741d170354540040103080704401801c05400c2c540a110101c09036902055224031aa09803401c0d0780c50034800041c0b1401449190841d0350302600c00100c00d42005032074014240101c0c2c0c070800350218070307000040d42e1848205040c44070300301010800001c528500c84140001c154407071482d0040c1401c030a6036a01c200e1060480c02c0011407440c0e201004a980381c208515481c50560307143c40b2810741050340001c0d540e20401c5040c0f50070304172240c1141940e81c108003c00c400501d00040700748031505000c80c01a450b81040102510b003c6110421000100c05038001c40c0c0c122507 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 637768678 1250 637767428 637767463
    0x90905150d02040f0501060507050708030412030804020312030a060e10030f0213060509040c08010c0f020304090b0111101b0216061b05100204081006050a060e03030d05090c040e 78
    0x2400c850401101c05440141260b000307a540b80c202c40d98400500c141070280c400340e10703031039580c403481c3c10444c0c6403050560000c142584200814040100c819980000c00f039454107120130300d502c40b4030000782802d1103405e44140c0010080b040045036040c54021400704e681c1b0706201071040d1540740402d0540030080c00084c00300d040d09003080e001800d00d4508244201c08071900002d4164880c0000795809800381c90942e11170030f03c480107015100742881004c00b40e50850911502501030300c500030352240558425080041d984082004099000c1e00031008054250f07800e03501d5100081c41088014200e040d0074010189035008241c0d0094000240211181c26100c0880175091604400304e030a200d003070318080082820300b1500c40003d0810010b2054050302c1040158444d800c2004040c580b2584010784048141464020081074440c0c1d20500141d07016858220610740c2c900022a1030b5210b20301d14804218030780001c0000c80080400e880a03840720859040c004001c6107442c80781d64100088035101c080 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 637769784 1106 637768678 637768711
    0x9090e0a15140c0a03020702060705150708040b1f030f2006040b030c090d0210020a110a0e06090711030403050724080c162001090905 59
    0x1401d80402004581510622012a400094010401803100041d42d00c20b140c469012140b0541e000303040941c2c0c4960600d0600e5032800c040440004003000c82000c10174141c440c466150050b43c2003403614919841700d0094013200c0b441c140c00919a03c2d42c0d51000400600442c40c0e90a04c2d50103100104944128040c000d0001d0301288401403043c1c00030401070080586c3c81003a25040001c2c2c080003601c0340340307210100e8560484201c000c0d604c60034030350f00070a9083d40020494640303441080740c1128110810705101a60b9001e001ea01a105442000503603141040e80704950700a555190072898100006001421503209030404d40d540d40001c6014400101c00b10207001c00305220346070003034030625400401041c0580c0680300c02240d0380b0010b10640d9110011b030040074525040b010021400f4070781b03c030050050308806482c0b0b02150a013600000c050400d480f410380702d42205040074106 = true := by decide +kernel

theorem cover : BRFrame.Cov 637589928 637769784 := by
  have h0 := BRFrame.cov_init 637589928
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637589928 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637589928 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637589928 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637589928 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637589928 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637589928 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637589928 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637589928 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637589928 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637589928 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637589928 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637589928 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637589928 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637589928 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637589928 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637589928 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637589928 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637589928 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637589928 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637589928 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637589928 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637589928 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637589928 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637589928 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637589928 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637589928 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637589928 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637589928 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637589928 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637589928 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637589928 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637589928 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637589928 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637589928 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637589928 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637589928 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637589928 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637589928 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637589928 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637589928 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637589928 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637589928 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637589928 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637589928 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637589928 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637589928 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637589928 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637589928 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637589928 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637589928 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637589928 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637589928 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637589928 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637589928 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637589928 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637589928 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637589928 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637589928 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637589928 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637589928 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637589928 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637589928 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637589928 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637589928 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637589928 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637589928 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637589928 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637589928 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637589928 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637589928 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637589928 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637589928 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637589928 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637589928 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637589928 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637589928 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637589928 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637589928 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637589928 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637589928 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637589928 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637589928 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637589928 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637589928 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637589928 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637589928 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637589928 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637589928 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637589928 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637589928 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637589928 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637589928 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637589928 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637589928 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637589928 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637589928 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637589928 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637589928 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637589928 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637589928 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637589928 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637589928 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637589928 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637589928 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637589928 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637589928 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637589928 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637589928 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637589928 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637589928 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637589928 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637589928 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637589928 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637589928 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637589928 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637589928 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637589928 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637589928 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637589928 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637589928 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637589928 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637589928 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637589928 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637589928 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637589928 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637589928 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637589928 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637589928 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637589928 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637589928 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637589928 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637589928 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637589928 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637589928 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637589928 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637589928 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637589928 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637589928 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637589928 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637589928 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637589928 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637589928 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637589928 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637589928 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 637589928 ≤ n) (h2 : n < 637769784) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
