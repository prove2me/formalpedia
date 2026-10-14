-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2107
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T05:39:46.61032+00:00
-- url     : https://prove2.me/submissions/901c4990-537c-4d06-bd5c-d548ffed2562

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 378776978 ≤ n < 378956834 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 378778228 1250 378776978 378777001
    0xa0e0c0c0610030c0501050702181501020c0f0d0f08070c24031509090c03020d1101260103060e031207120f15053604140a0b1b07020d08030609 63
    0x40f690028802d904041c18071004446680c459903040e40c000d0b142e02c0c0c400c55071a007204c0e4003030301c117403c15000040c1e048403010009003007100b00340b800c92003000c102e45c009141365604491000f08951080408c0021102441c0581d054050110040c1525520010000d41100501710309499000039082d00585096419001c2d0201c80d80140c013080c01000103181032002001aa2002d08950701940240202c59602c0d400035444802c0c5110445402003a05e0700c090f0556004540c0b81d641000c0713088015401d04855000c046582414070026000300c1d15245080c002c201c041c000ca40da0781c00800241503007440d100c40301800e4030365105110341682c4c1c80d202c500030000820f80f00b1084d80004254040701c50920b004204400c0c0407024040e006014800350000045408454121000007a008641d52a5180a04200c1107090120b01c0e05c0d0700640203001c1c881c0000f442c03400704960000309040104405d21004080681c0c5014010009410000c0d001d461014402d03144040d40c0b10382c100b1234001c80d66584100b07100a = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 378779478 1250 378778228 378778261
    0xc0213052401031e0b0102121c2009090604090f030908120405061b0712030905031002030105060d150512010603210c0b0c1c0b01090911090f0a0e0c0c06 67
    0x70851003544c11030555080c000c0d041400c0e034000500c11194441d42c924120001e6600807012041010f80c1003080c2141d800c0180200100400c2c8020303a100b0b01c2c14815012141c0d44a880c00e030511035219400014038603075032507015105058021191042d5088240b5000e4008141801401da05104154400d108070b4072034400c0b501580d40180185080c0003014401c050340b800d4548000501c0e000d03112005c1011120140d440c03910500a90f01c0c109032614241c103260800c0b0f0b2040b60300b041d290041005021a45506081310010b03031451000141301500c8140c40d0080e0a41c0c0d402c8591721815100d01c41c0010780c0b054201c013013981c1c081c880783e04181100c1d254581b0401d554280300008158110030090224507064440c135403000301b440d10300340382c10703110901c40c00e4800030111500e200c03507560004800382d5640810440040c10011004110a00004012034040d01400d240c5a200d6038a0031041c40e0903454491a410043c012450354082904110700900201e400c140c0404400e44923030000a02940c0f035865000c1c = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 378780728 1250 378779478 378779501
    0x190b090f10090b0706020c010c020619060e040305031f08280b010611010b220b0f0f040c050c0303070305041a0601050d0f0b10020606010323070c021305240103 70
    0x1030140b203241120f22109608155800e4400641c20301511031441801c1c010b8000d40c05040e07000d4407061030203050301c4500c0c2d810344041d0018185080010701600ca1704c0200700d5001505030400d50344035a9a040b10b0700018480309118009115140700000f41e265002600c0807020001c447c116101305c04d001c44001003205056006811902c01d0001084283e0103034400e030301c141c040080085108805c000c00320710407004580c81c404103044084461088858148103240800408640c40d61303c0a0000d030024203190b00f40e1181c01d22541ea80d443e2204142d020b42b08460146c0102030607241c0b04d1911080c0903004101c21901036030744040740c0e104208140718402d0318502c6110140c464501b000344400320040201142d04400787c485580302e0310607159a80e0802c289190b540194020840d52411a000500303440d0381c0322099082507070b280f082c03060003442c9000302d59020091340703040e1014144600025820440c4010740d019058600420b03c01501c026030a020b0f001102444006110071400004504407001020030 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 378781978 1250 378780728 378780737
    0x1a0109050f18060303191e020f0606060a050c150a0b0a0605030a0911030307122709020903070e090601140d0506040f08090612100b120a0209190b090f10 67
    0x515215400440e016080f44015080342e0601c2281c500340c0c4005403031940043c01003507408600149940d0068600c180e10701c402e04c050040000c0b26043c41d03070b03078280180500d48194008a21551050b04c14019100703442e0810b8212003125088148201c1802c405944900ca610304103018804641415502c040481d8040e5070352615550f1101c800d80010300e01d410b000c90f148454802a545150b80810103001843e0142c45400b0300885041e10141c0030050307016403d010010200007405a556203244417004450411101503a1100c45000103402c01a1541008004444160900096080008056040c0d80000c14000701c14042c0750100100300c11030b0440100709a00c0a80082c0001e1510015812458803c00190703003010000c0d40010203e421000049090481c401700304248074012211120007000e0103e0f903940703807007401030095a16410040034452625000aa1682c050b15a40514a540000c0a40041800d07885807040a200d80c00046407611550f00c030300742003205180c02d0f401c0c03401e600c0c030b0b6455 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 378783228 1250 378781978 378781999
    0x5030609060f150409061506020c0303092101020406091d0105061602010905060c0a031407020a0b030702070504090f020f18070c1103030c0f0601120305090904151a0109050f 76
    0x500301c2d8007030040100c150103c001c1054282d03500c860142909042c400c0d000801c0c90391400e810b80a10103d90790112045504c41c005868980c1c40120841d6106581582ca401c44060700c0e0300e05202401c00c05d0f2070324446e50b02c00140024001c0d40000c0a00aa41290b140005950085410f2292a00c0d082c0181c540c04002045038861003c200038600c01900d1040c180540400c1c1d40f107000840310781110789180c0c0c0c61f030410700083c0c0030558000440c107019400d0280560400d5003503000f0520f503400360b0044200740000000030030f100c0c030300030004d0000030180100300380200b00300307498115a00c400b1100101d0140410544410551822502603611580307090369041c5295a011422600d94000c8403050700d03145101c52202e900f646040c40108038010703401000700145009906424540740f4141c0c8401d55404010410b1000a82e05c801260041c0310222035100300c035101e50618482c03e1a218408901481c070388400603215008494420200010076210083c01986c1e403000d0205400e407240b06281e001d50768a0 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 378784478 1250 378783228 378783241
    0x90b030601050d0e060103030306050f01140a0309050708101a0d03020c150d0203011d01080a050c09041e120318020604050d11030d0309060b1e10030f061e0503060906 73
    0x40160078000000070000c501038020200d013600345402a00143d0009440e417506021074242100701035026002840d0081004540a9901109010f408840d0040545400401003409400c0000c5000b404044c000d484140440940c0c2c14010281184043d42c81c01e600301310404180f500c8078481da40700e40c040d0064030034508003804215440e41c407050500b500104c10b1081d07400814091001c0e60103001c0409061082103c410050302034039070143d0000341240d0100083c000094004120720074496002d807241b0800da01e842c0f03050110007041d081140b10340311083c03c180c0b06100c1e41d1a0800b80d204083d0328100103207200d501c02d518100092580107034100d81c0804c8104000d0400003070f40340d2120300410719040700c4013a10f800039007414981d00b60711000a880e0b003d103401f0300600703206a00701408110f0b501030112010181303031f4403032a855460f017a2050740c4148241042e18065040115200290001007106907200d0311401980b1110703188003241880740b880d02151601b4005000e0b030140ba040d900402d815520348 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 378785728 1250 378784478 378784487
    0x10f110304090204060c0c05060906070b060121090c080f0a1113020c030406030b1801030f02190602150907290c061e0a0b010518060909010803070b07090b030601 71
    0x6584001248800c000005191000d44058405824295a425802d0f800c1d410310b20800d0b84a034001901c245030400103096981c2d160001c94090300d611010349000c6070f481c0b000681d04032114068584c5011b202c1c8520030700d4025145e006807141d84c450903564810a454500c0d0355504d06940d815883c0d140d1105a04101003100c40d200e02c82904401000c0d9212020358144280c240c1e0805080005c0551001c5010b00c20150540035a4003410f000f550521450400c0da01c075119a034006110144c918185400301005540718a031f1004020340d202991400c80584d1024000e5503002000000300160100c0c40204503d50400300d07462085941110010001d4141002c190f80d2950402802e0f801c60300302004100302000e021f010007849924074004908840c80014943d981402c00100700c01e80b501d18002c90480160781000503281041d0a454101e40d0003409803011603c507124104100c0d510070081000010108000002003010301d00c109a138110030788481c038040d5941c21150080a0340039030b0034800184a035104 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 378786978 1250 378785728 378785747
    0x2031002071a010b0a03020d0e15070f0503040f0605040201020a0b09300406140705060708070e010215040b0a06121511070506060907120509070f0b09010801030b04020d0c090e07050f010f 82
    0xc501e0004201d22110080d501d08000ae40c01940304046900400050640280340740344540ca19040042c0340d442c180e51110055880d204004010642c3d900c045429644200500e041591380003400b80702c542011400300703688400001180300300c081081111804000240884840300d6403010505051030f0a0200c292171015810f030780301c0002e240510162001c0741c8100282d0380a4542614cc0028034146448000c049403000c2c40302c02d05544c000c030003c0019481400c20f0551290b0030001110071500d03804103600c00361035590302c182c807001401d2080360b0920480e0510800172032035001d410010310901076030700710841c010302e4005006a08954006001814820402c1d94403d0061400b80d45801d12041e210781240d04c140c800e0f0303c2c00d80c080301c000c0c411340440c8030150014001140101741460440342c0003d0598005000c01400f062081c00400c2c11500c0d640c20180c02258400212a03208d0340b1f800d0f81d280140383d0203c44021034400c0c5031002601c0d040c001c1e005a400d88042c0d4130f03880d14a00c1d07414143d619912 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 378788228 1250 378786978 378786997
    0x305120709211209031502072a03030206060627011b0501050609010509041703040f021305040510020f0a030b31051b03041103070312020c010908030301081f0902031002071a010b0a0302 81
    0x9d01c9010000e280f079021001c000358805000c00301400360030b40c04c00a190000040c0058000d940030085540548441c00c0803010b40d8aa00d0313803114100c4d0010004031008658000c015000c01d1450803440100304e019000f4a01c5120203031000c1c0c003541c1c6c0e21b500304001080181da02600c0384881a01d80d24108a84600440d131042c050f10301c809009196501083c24480c07800c0b40d180f802940c800601c02000810700c84107160116540080d07060803011a0303000b1541c400c0e4030044040c540d13620240c40a645801100381101420040e100308080d00981d400300320842c1c40600342176407d20301000520740d001c4102c0d131340e4034890a5031900e908645d01d55907903030341c403040b040011941071186100020010303140412445507000180d0140c0500c844c40c000142981d052600100403503001030005001881000400107881c04071a000341e40c0d98140003010800600d4a1803019426005040c50b00c010400c403030b00244400c0d441043c071191144409410002840790a0007020407a81c2d080200c0142a0700c00c2c1c01030503c000 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 378789478 1250 378788228 378788243
    0xb0a23030c0f030c09060d0621020616030e0303030f0f01080a05030702220608030c0d020c0904080f1309020405010909090b0109151d07030507080103030512070921120903150207 78
    0x38400b000986c46400991121032500c0e02d5080601a0405d03481c0c14000041c01c0075513004c400249540020032038002c9040c41c811111713160f0001c002b0b25208241d00c10303080001805803956400c01c1c0c0f08500d075403041151915020b00d00300c0c000003a00d020008074002441d40281c042c506105040c0d081008200341c01e136001c081444c4003080803030794085612070700300289823410045588507000c182e10b0342484120045041590440d124014840c0c49a10b08181e01562100700c20341d039020750100d00c200f10f000712080d072201e481d40004003091000240d8003e20a07114245c0b035180f462a0355429030300c20b9a121000c000c25240d20390004221000c0c170340d00003400c2c1590b5191640c500716206e04e185401c0404175024900324829806c02d021906401d0320400f0f81110b0b181c41c1600680d811514040d140344a85050400304415013000070340d45034405c40c4000c012340041c40c03002001200e88400744013061102a4180c9503000190b060201c20781c0a000c81d501280da0140d010700a04100612180003900500c6e02030301d501 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 378790728 1250 378789478 378789487
    0x150902030c100909051b1603030b0a030c0b07081303030809070e0c0a1d030a0b010e060f06071104060905131a010602070909110303120a05070e0d080d060b0a23030c0f030c 75
    0xb414007005055501404c2007147e40054142c00c008043e64208001ca50044c0105507003480401c401d980f44200307889a006071a0b5440c002483d00d490f1500c24686101d1880005200100800d94081e00a42c01610800115102103842c3d046070f914040c82a00c03040309240041290b407170240d0007241c040038580000c1c101641ea142c885270109040c03c14a84089600603a810010702180c810680c03c5900480c05840c02d035040e04400300415001d1040b0b420207807840745000d110b010b0399580c0c4e41001000e460342206c240001d041c801000000111a030790102c4503101e501c0204480c11604040980c121a425802801c482d40f4041a1100078888010f0a4a40b605400c40d09016a20100000c1c5140012a031000103185003c1e20200200c0d1009031620080003400a0b90840c9565100101e5113480d4104510740e80d19401a24914010101a808040e00c000c0c0428586065500300c20a5000c03c10b206588540150100b56054601d20040342d060b1b82928080c0280390041c080040519480a01201e000d45070 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 378791978 1250 378790728 378790771
    0x1109040b01020f240a0b01020a08070609080a083301050c0f0102040608041e0510020c15090f010f150b03180109211b0b070c150902030c10090905 64
    0xc200d444071348610524000d40d030340001e0744400f440e0b85038000f4a0603000c00c242280000000e454045400c0054903080002ca168001d000860b4810445140d110002c0d0f0381d00d944070300024000740400c4405020711030440d00c114584a15588009412412001e14042c100d0036180064440350000034140701c843c81800c10420360082c0900c000d002a004a4883c44a80c0c41e0a28000034400c0460300c01c11190b000d010805800a08005070094510050510260319003c1601007589882c2c1c0365181c1c0c5414913407400034041030b1180421559020090140207000c1c0b206141c4a41065401c9030002c00f42c090606c0c4070030070034460350001171604003508400d1800744101003003640d0f003901e0700f007181503d8007460440409180d8108003406102e4107402d0501c06400c203d1988040650161420302401c0c0410410000e80b08500c14a01d0f01c450f5540290100180c0d40b10408040003007150007c00c80c060b10400a1001940c80c042d40449894246079035103444039801c01d1152001707010050014000384450081038840b = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 378793228 1250 378791978 378791983
    0x905091305122a010b151c1805031c0e010c080c0c0309180108010f0b01021c0306271a15070302211c020310030f08040b040b0a121109040b01020f 64
    0x421869800021034030b54052010091b0400140031142d83c0302c002000418012000b0b0322119030840200da40014034110b803440c4040f0440c0544200618901001801000305000c140c51030207a400341210805c0780d103c81c81c0d0154202c0c1c0030103240201254418000030803111040009005003903008040e42c0c1092400700106241d5196544803c111aa40c80e006211007a0240708800c00000f030030b10b0a1018903403a000203034032403402100c003142038010005400801d034002d030440d000801e003640120304560040041416600743c4a104603900340c2c01c0030200004946955461212407000600c0189030700c41e00c082c03d841039400324600300c00350f009044502051a51480414000185c0189855510320740c4900e603d040004490850301e5183c414010300c0400300902aa00060b690b005030b102604403980d0800f03100600566101d001340c0c140005001c41c40c13505d458041c00168140741c0721807080d0141408042d050301d2850b1401021901c0512500c1c0301031505400a080c240e0060040d030311000a00e450150 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 378794478 1250 378793228 378793297
    0x7020a05030111031603020901090506031308030a02041e05030c120a0c0e09060f0411041d010e010605011806120f02070501052505070203031803100c090509130512 72
    0x40f08803004020864060707030000448440408a28007189410018000a040500e03107000d01d90198001000095001d098003c00c260440e400110280d12490600c00e0480a548903000300b079103c0903005080e0014405100fa20015600000e000d4400c0d56042c105015944d1240e00c02003d1502c91401c0c00380c003080f03030006900090103500c070100c50350b80782402d400d500d0f026000d8481442c099821040001203448501400210381e07088801140c0e902441c3c070118016010306186401035441c221034000b0074401544850100e0b202a20f500648035200340c1d1460545980d80305a1001c20342c0032256411000841d48207490420030b40070014101185900c5150841e40c00b201d030703442c01144504080310780f00000820710300d071401c50707103002031034500d450340403070307120f00410240291a2080d8840b41169660070301a03208044c00030442040700541201c40180b2030b030340c0740c0329480c000e10003c004030300c8003890607805503030b000d4101004101751084d84070442215030001312070310180c4e42000c0811000c40e05104044 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 378795728 1250 378794478 378794501
    0x1a0a180305150903070b01060e0607050f060604141504110d02030a0b090603030412021c050f070e010509070c02010e01020106050a09060905070507200f060309030318120f07020a050301 81
    0x746002c0e40049601002d10b9800341c41c00702c1d158030500c08200007582c0e14400a05442c4240b5004800000c0301f00801c4803400fa01800804034086c4401d218460740b4001041071049130b04440520000305c09000482d92400309480205023026803124640490038142c1040801000400230580380c07010218200081707170001c0d5602502a034131450651000d20704846a16001072040b0040c51a0510f043c0744021a2070841c24024081e10041819280141031082e401140c1500300c2c094815400c0520b10440d2154424081c841940d1400000884c5d641001c01189205a010340c031111114201c035001075840c00341c2c1440850456403106808501d943310460300c20b0041000c82400b0960f00e08199510050f40d8000b019101004814007a000104208080180c00c88440f02c64003415900c82e08046624501da445485801000c00014410030180000085101c0c2c403448480f08144000d8588580e01c810b003e081e85034a1450a210082e62500e0310707070041121601c001c0000e00c681c0d40d51404039007502d9904098 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 378796978 1250 378795728 378795733
    0xa12090e090a1211030a1d0909100e070b0318010e1f1b14030a09050109030806030607020a0201140c03160609030206010b03010f0e0603031303110114041a0a180305 72
    0x401001072907011400981c0190400940c1c400a110344d6503600d0080f80224810030030002d0f281c1030500030000048020f0b440103400700e10285408001550303030b07084040440d2440c41c0341c0746449070000000b003060030603940c04106951442d221603a03003d8140d0b0109000107400d5503a0f0500e0054800308114544e08403012080344401d050315064450211072110344441c90405c0d00c410020142a030004c0c0c8000c0e841040303090310b0313101d480b010807010081c1400440113290350b1030420000d05158000c46460b20800c411811507105559034203040b130725003403800d400038085102400d14001c85104039006e01841e4001e80c0469081801103030481c02500e103504803d5444070380c0c80381c1c6d01003450f505125041c0901268a02c19146515043d41d03020f1244403403048640380ba01c90710105200d5941441140e00c2250f0396051508800c2d00c80c1085a402c2c0e40907540640403070039070b038000c01c10b0340f4810050710704807411070400e010300395410407983c010382e40200c41d00350411107079203001403014051141ca00c0245004400 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 378798228 1250 378796978 378796993
    0xf06041110030b030a1b0e13060c030e06040b060d08040b18060304030e09070507020d0b010504060512150601090807030c09050a0209030307110619020f060c09030a12090e09 76
    0x9009903440550203003802c25060100c18103064500251002d06540d00c80b80380b91030b004850b4401d0440409a8000c0f00000320040c060000c84003903001c0421140c3d01940b810071034035021000c254202c0c2d1920640c41c503030b9040040094049200b20782c401741c0c07000e40907202004101107545d4560050384190000c031185000460490743c142c903c2d1640704940581a96403501c5c0d400e05440282c5003210521b00a445600c1f8400000c43c500c1c0300324190b0704c0440d0b02810700c941e5980545004000300409008050195142610006452070000000c10b6100c618801600510740a607403940614913000700a141070001450001505d0102002813200850141541160840c14056050b0030390b000508150440390040c0480c100325600401182e84541d840401a00341286c4840460340c540142001d0900c00740c0c0e080a004089034021840301c4502c4ca141054031500c1ea21002000c840d406124501d0350554820048440043d0200a0300380050f009410074054159850600d500d0b49034003210704a0403504a0780 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 378799478 1250 378798228 378798263
    0x6240c1c03020918041101030902030f01110304110d1e3014031b03060604030f0507080f03030105150903070312020d020c060c0703081c051006020c10020c010e0118080102030618010e0c07050f0604 86
    0x470382d074010380e010444052072080903c1c2c40b030340b8080c03c0840213003990f101e0407450a400c100c404002980281c05124501c0442d592400e0951a440e81c2040c01c0c03008a055403088c103081d00840f60480b071140ca020f041b0b1003044000074040c15103940000b405503030000820071011000c02e041c8001034a86900c1030000703140c2c0b40d04100383c2c1800e21500b400c00c440e9941c0148014811a030f2140d00d00c01e000315040d4020394560514800207480c240c03003927102514030440c01040a0380070354081580c0c4c40880c1940c003100d07a1030070700c281032003e1361107100c4007a102504410014000510303480300400c2158800030081028100301580d2100300c50098079a040d05001e50341d020460300303805000c0102d085c6411604050558101c1340040e44400181000030304100d82d50b03401002c2c580c0544042950780d090050f82c2c07280c031925034244034000e501c192a0306100e1030400b402d006868501c81c4030103041e21108140c081c4d4a840e40702d030500c51034004060860350380c082c4501225600398104146031086000745185070303100d503a11 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 378800728 1250 378799478 378799493
    0x11202030a020c10090803060108040501090f12020c0a030f0303230a020703090815010306180b04061a190e0a09120e040506240c1c03020918041101030902030f01110304 74
    0xca584101290905c10b5900c0802c08000c00e4030342c011030a00f005145a900d92902c41e0041c035a4900050080c20344141400500c003000d1180b00c1c5108998007111031000d641c0c820407203007404d5888001d044051b0a03814100080c402e81041d42030fa8400072a059004031400c100c0d0341b0240c000c0341e00d0ba01c082d0380400c0702014140d114010f44010f0410030094181c0303041d141201d0000b1070f0140005072505c3d8503180302041c41e04039007410558181d00403090760103034102441c202016245000c0c0703c0e014842d503240c498002e0300d010001d1240015103051484003a9143c424222400d58004150740b4400d035a80d0000c501280c3c004e4202d1040000c10360b944804403040104020448002a10440c0100e1607400161030b06205046502818241d2070203045e118070040582d41e241034040100400f00140c01c5180c406059019005441054805c81c0c510380780110f40c034240d040c40041200d019001543c00740c1d907164954082e07403003892250300103010340703295a5100d8000ca00303403040510f0180380344500008100501c00700c0d = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 378801978 1250 378800728 378800743
    0x5060108010501081f050432061018050402180405010e011d0c0c0d08092e090c09020301060207180c140a0c02090c04051f0207060c02011202030a020c 66
    0x90814500a5040c000004e03c0c81c0d00051401106403090100c0c038090071442051a0000c042c0184140204201e0000c80c5010000b03e00314060500192a20820052802c0900f00d2042001600300031045480c20000c4808600c01c44d60820481e50103400401c03e0b403164001440c0c080503031b145210088071050309000858805903c800d10a01c0082d0052040c201640c44107000507805404030f065035220480250700500c41c04500085a125510314001e003640c0003081d43e4400d01c852019582c0d01506100b001c0c0340c0400307a01d90b01c0e07803101451800598803d6175501001459018680c1c91451588441102c822644203070032860150703121503000c0002464044640114a04000c803d00840c194502d010b0090700300c5000c445288400424812261446101c1c86900150020920051400c020301844259445402101c0c00b412496041842004030703000d401c0d2100d501c6ea8001c0c4031071403628200302d40d4200303030040481c1004101c8650400c528076500180d805580e40c80e030010303591030b1140e40d4145090103 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 378803228 1250 378801978 378801991
    0x910061b0309060c15060305010e060f1302010f020c030d031b14030105060f0c060403081e0402090f090109060e0303010501030b100c08090d080a030902030712050c060a110f0a0605 79
    0x10350108910019611070365581c11a000780c103008611110502d04100681c0015240c0c1c90782c9840c02c200007007401015000b1003010200d03501601c402c1c3d182c124010200d81001c4a101b0141004d1005440041d4400c90803840101d031240b05070f80340c403198580024101856840003400103510348004003114196445241541c482a0406030501e280b00040400d00b40414800e0a00c40e04c8045240159003104108880c840403074041540c410703181038940038003140403c1e05e036505840004800d05406224104000d8004c0d500201042050303a10707800f11150034035004111a4455403603030705200028000b4001e42100e1030201001e03684030341c18103000404030f40100224520640800003c000902d4115010520a680001c11541e440c1c0c0414003241244025003401031a14038001807680343c079941680300f0a0550700c00c8050b940314942c0d0399030140442e201341e000078005401c005501e002d2403412200800d21903429051801c00d400c0300700350a0b030415400180360f0103940c10a40420081100b148161a440380 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 378804478 1250 378803228 378803267
    0x28020a170d140403241506050703081b1c0b37030803010e040201020c091321390f05010f140402060702010207180605040e060912070c05091006 63
    0x600d192160340f0001e440302c4071700001d0100f03117440386100281c075001419920241581300350126aa07407002012580485c1c0305400050040020501c030071549801c03a0050307a0030000d003509003180441c2903540d00c0038000030034500b2035075603032418542e8076005000d4041c0403c2d07601e10ba5040c0c81c024031640981603e071201007007092903d48148006130340542900d040d07800011085105039070340c2c030040c0d103084180d101c515440340d052400c002d00004203420350a10684940e125140409216a003166110003d00000008c150340854650001e0071000ca0740828030070300c543e8140020751040c1112961843d000054540400c805007050a020b0f0074020081c4415152100704030640c05c14011110030080900000c0c4624400203410040d680308014160103001c2c840781d40701c18900800a1480105050b2103220b000324148800700440ea41e01160075445600c0c000b02030400320070b003804030800e568003204040380c0fa10101a40480c29071a03410216100d48444011443c0060901d00c010f1300c142480700d844503986 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 378805728 1250 378804478 378804487
    0xf0603190e0721022103090409080306190602062e03082106090414100e03030709080c060304060914030c0607031406030d050a03020f18040c0228020a170d14 69
    0x142c41300340c1c0786445110003170a0b002d4070b10700302034805d400c520400e4061503000341000c00010910042c0c000843c0188800c56103044201d604049500e5611042c3c440d0301e015030084070002d4107c41d90045035400c1090f02d0840c560080c00804507828600134903030030664001c1c2020070b0b1115010085080a480b4031803120325041c9500d048000100e80310b1000748005c02c0050480d80d05030012900304403500b02a1f400c02c4041c0010540641c40c0b5603260011242400000c40141c40010650008209032501c800d002d007085185550b1511554058503a40504840b0501c20b41406114002c2c2130020705881e4001201900a60804030002003c4d1404803420b403010b45070401c280805540c0000d0100c498036000c0c1425919022aa00140c00078040c1065600500a00055440006060f080640c07001e40d01180e00f001403011a460032640c41c118260031a0702c50303102d59041a06040031014285829100030b0003d80065214200c0e00c014000c1180e21000a60140c181811516041030711510303100c841c0210710b41807 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 378806978 1250 378805728 378805733
    0xa03290405011a0a030f0209030d170709030c0e090313060c0b101815090c02060603070602030a02060a0b0f040c110c011d1c0c0b0705010c0903020f0603190e0721 71
    0x40d0300c1421300300400e250392160105030003507154050341c0c1e6044004040c0c540075545800082d00300d0384185d0003440d181076075400007901240108402402e4a4102d80003031840d5080c915801c441ca100a448000244001c0c041c510081801c1c2004502074106036650002842c0c103071410780604c0307c000d4514200021402d02c1846100c0190401e04c5400c07075190b0004c12401000301142c1916510f07034100624590506510a0101d5000100799009610950858402c1940e0301002c80c0c40c1d01440501c4070050b00440c0100e051901d650b04101404480180100340400d424400501280d0080c00880085101c181d40e84295041c1403008801c2d8070003c0c03e298100e1002d00c2200416030b52180b04881c400d4a0890503080c84600d42c0d0f98129040354050b607145610350301ea0700c500e0b003507170001e60040b01d1941c2001350b00c4440a2180800c6801c80e9030117044030804008890420003d500014005c494007102c0400c1040c60310500d001b848507082000000d45803441c14a00d141c1400e0030b80700e00d01081c1c40341109d0503800 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 378808228 1250 378806978 378807029
    0x12011211060304060905070b0703140909060114120a061401030b0f0112140703050619030210030207062a030c0206010506030f04051c0f09120f080a0329040501 70
    0x10500220740c500e980e583d4034904000144100003025180f8441d84102044080c2020001c1032264001e4944000030180702003d41d440380308520200750055640d00100303200e54007030120402c05911101c0c9050420b00280303007920403e4030489040301040e8450320200921542c024070400708071828a820700c00b8445d040013103481c02d8142000b503410004041c155080030429544100c21321175403c80c1032500e50422900c0180500001d8074098804d03150b102605040314202009881101c1d03010700b848a69a08a420a0b4003c1d00400800e982040d01c03403805a035550340403a02a002144c4c4590f8044c521256000018211109010000155408100140659a01c4c0002e40b540031022203482d1149540d6498041c0c10300d4003201c140c80c028402d8031441801c2640003120803001c009541c2d541d1050607901d0303a840e01051984103000d0402045940743e0008162004000c0c529400103080200b40c401c2d0b1140203030822028a811207104e403100c81c80000031854503001e001e00502c00101628401240c43c050301c1c4 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 378809478 1250 378808228 378808253
    0x5010f0503011b050307050f0706050618160e060c0f10050a0e030f0a030902090a02120705091e032d01050106020706021902040915050601122c0f12120112 68
    0x20f050000220004048911031f104a48207104001ca1450701d400b0b151800802400c0295a0548034000710340701c3d008015806164244104401c000640145d50354107000d9940c89622203110390890030400c00b0b502e4480c0b040050703803c441e940700c1c010600098150501012120007a041d403000d2400c003121900791240010540749055180c5107215035a1501400c02d070001c00d2007190094200007007000308856405143c0c0981030a0440604440050f0b0320848126100d100c0c000c0000ea01c003504100f4915004810369440820840c050215040103e4032200030511120180c2030284441d0311802543d9804001c7c0283d0b8010a03580c0014401d460802c5806501d44a80302e10341c0401141c00004030065550300e0700010201c41e001965600074910980c0f00c400680421500c2c9800b0583c8100d17080f611120512a040600c405c0b0a07800b101322500050a465010701c0c804c2c40152441001603c015003007007409031140880040000d6a515265074508418140050b031044c000e40311103034001d9000c10303064010032 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 378810728 1250 378809478 378809531
    0x20111030907031b1a0c070605031006110f011a0109052e0e040207080d18080d181209290403120c0f0308010810050103020f0f030307060f05010f050301 67
    0xc3c465006441500100303000540c8207001c18154400701c0103c0c3d05e6200d00810040003020290746001d0380303c407015105440300307503441c1c0c180482108041010500c1051030710002001a01500c1208440c15616405c0d100200504980c2c41d5482c1c1d0681415a040900c1800510058515035043d0740b21492800780241c0c1e140b24600208a4015010110b0744a005902c2000c1c0c401402191a01c25600301002582c10403850300c18543e207044815079801c08561501d60312240d00005052030521100c913440041d10304200c20148000100d01d21000242c1c0c0742503204d030710003111342d80e4008051418201d102454000e00300001c0c0c88007418501c614801800d4100c0f0b00340c07600450b0b85c6c2402c108000c01180d41a01c040c0d001f074654070315100030740d0030560f11105041c100d5480c101119105146081040c1c201d980a01c0000c0d0312450700d40700100350341486107125201aa000301502d0900c1030f80c3c1c8445c41511032400240f118503590740c0040c4084451000f41c003001d040d060300200300f04503880b5001000b078186507044 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 378811978 1250 378810728 378810743
    0x3120405040c1106100e01080619020a09050d1a10080303040809010c02060a0f0201050610051b0c0d050d090b031303210e07050307080d0c061107020607050d02011103090703 76
    0x49500b41c0740104420700c09105580d0449030285850a0070346403044040c000d80702e00b8280c2100010b4144000622180140c2985d0f290502d60381070a12514002e500200a003028480c00c264001910360392621004c490500965400c0390a04045130000554000108800c0185102c464140f0990100000750b030743c426440081d042e40c514200005071070b416582e101c000d500000020303134445a69407140000b8440e21003034000380041d484040030082e001c2c4804141900181040c040e200c0540c2c850042c03000b00d8040d02003a94007003080350b4007050182404071402e4800764406c00107046417a9001210300c1c0100002c0d14024190704080f80904180071024001a0410540e0000c8034244005013000d0000030030400c4040014001c4010740d1900c43d41b16220780c61080c0902400000e0803000415400a0b20580e5503c1c12001045980e03000c0007030a10b030740c8441c000c200a02ca90801138407080014444580100014a1502c107142c1c5c009081d180a81c0e44034104d07010910070f0142440c4009241016031754440d41 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 378813228 1250 378811978 378811991
    0x1909051906030c03060e011508010207060621020112020c0303010f0e090105220c05130e01050115200f0a0311061e01060e03010e0a061d060c0909130501290312040504 73
    0x203050142c80030030501c81c020b40080c0c8c0d0005514005600406406110380c1050204a40d21a12445103180c110b0710440030408502c40e140c0198410103034083c03803400103400181000b82105070705140d40c0098000354a0102254400c0c4035800c0e03e500380561094035480284080d26000c000301e07000e00110a14152500508201c082c100036040200c4800340001a00d1903400c4000806a03074064600080340390f41e06d51a040000c1307690359410f0000c076981c00194803050078500800104516071b0800e405003400701e005040c0c2d00440c680301030151100e414081d956807410803040c0f100e91410f21344060145081c5511400240690b0180002c21604488043c14940c01c5644045c000c640506002c164942c2da81c0140d6400408100d01644401050f8116059900704400804411981d0f01000d8a00c000e4004090105040615064104540c400380c0c0b030b004907210080965546081d03507800c9482480000000310020101085140e860032581e10850082902e5a07540d0b10564244c483c03402101d005035110203 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 378814478 1250 378813228 378813251
    0x30d030c03090f0303060f0815060603070903080703050301060906050a1d03160e0103030224010509060105070501020712030b061204060902010c0f03030902040c090e0f061909051906030c0306 84
    0x5000c160b80b030b42c218400340c01440040c43d0040043c01640510340c10901ca504012422120001e0031707804450321080340c102c06441e05401c1040c9504000d02010402118810100000d9841400740c0142c5209841e40d548a50500034050207011103500300790708014080c01118803140e4024100c807086c5841605d070745144110040403d041a50b0280300100c4a0a64440000d251a030300c2c000b241268001e6007a201c0040c1d808a02e1001114954021048100c1039001401540f9040390603507001030050512505c2c0882566696003a600070700c5c1c00b558408140b6113107000042d0580505150000101d542c24036100c6000c0c0c00d804440b0300580302509440c2c1c1d6042d90400c690154503003200d1070b40c0104100c41104001c2c40e00130054855003808a0003903092034004000076002d41c40c01019a2451150a401a650840104940304e002040650311520b80d5003145000901030180c00040c11903a00041005d160940d041030141074140400700e201c5140150400100707410500c894107503540028007040d04012003 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 378815728 1250 378814478 378814481
    0x213020f0f09030106060201020f030115020102040317030f100b18040906090c1401031a0d060b060a0314060901080d080a0605041509050615091909050408040320030d030c03 76
    0x1402004651400078628554824600282003900c1d01200240403103925840102e00343c0c0212151852070074401c1c0014001000ca101e50a04030403501d20005007440c1d644e49130510f000b4001e43c080300000f90000103108040e1501350040b03030304c0050940c80e200c280d40f400203a0a594031131181d8041c401c00d40640070724900d40c0c3c0c5400c075511443c0c11200502100813581401c0b0840c180c41d2086c40301014120101c0d0b4010b500031300440c0007015106c03100000c0c82c9502c00511046200307900084802c0d41e943c1c000d00e800c1c0e03980d160241401031b00960f000248140f441c800302c209000d0140069128024400040040340e000060413154507a02d4981001e0944400241300083c15180d044241d0080c1010400070150780319510520440d460308500344030030f440340401c0c003002c02c1c40c100c0407103c10070b0100f0040905d81070032040300d08142003240c6804209540c680480d401c444050740c048032000f40000c0c040050003118691040c141803859555420885900006275403000f00c000460203048d1100038650f0b64074000d = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 378816978 1250 378815728 378815737
    0x20a120e010c0b04031707030e030a1d09010e0603070506070b0106140c01060803190c03080105150f1206090c122701020c0d0f02010902010207032a03030804030314070804021302 78
    0x5041c019080034540a880443c2e2546c40091005000700010369152003070144004403100ca10140d44bc1404801c0201c405842200c10285807141d004d80582450f1200c01383d160080103045840340860805104050600c6000d0340301c14420b50051006c40040340c5515082411101241481001420103203103e510500884080101551a101000500110200c000d01450744102403132902c0c0c1800c44010b451040c1040c5014001900781c0380180270600300b40003c03a254920440c541410b00c1d4900040b1401548203041600d00403152405100d0f4605100b0542da070000e1224007e0340c141500c50340c1507020306000502c00c010304010100300340e0807480b100352050310344c030341000007950354499007840147e68100b4002ca66001900316148020414030620550a6450341640a020082c1c03458031400b003501d20202c8a845904030019162005112107254200218420f4440041614203030501a0071100480c5000035441c0a1008100c81c5caa40044170951047e4101d40300e190303107a214070034100207008 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 378818228 1250 378816978 378816983
    0x1d122205100e01090f06120e3405040e120d0921020f07080c01140d02131d010f0e18011109041a010503060d03020309041409010b01020a120e010c 64
    0x5108500d902402c0d802180407912100a132a42d11040d030769040c50406150040c4a100c0005180e40b05242c010000c0da00320041210204045030111420b81c0389010201507003003180e656000c5200307002c401c88400600360400900c0304481c1000400107a091164841800c88114003602000082e000d20380d8086601c41005980c214034080c0040c0c084007034000401c2414500310000d4468007006c00c0c030411740041e848043c6d403802009000b43c03981c820010740d41c82603001030401c80d000050048036000003552004d04183e08904192440c020301d0856404003c400ca802a400d41884450040c0480000c41400d83c040742c40104141c0c02c0341d0f0b26051030b04880300c014545502d4550030200d0022401c80c140c40a4020544121010030112102014445100b01181c2517140407402c28400100c0a203003d0b420450482d0080c015a41307001c0c035003000601210b82e00c0b0880400e03201c0240600650324400d104030404814203000900002882d0346070347c9a003184a084080400c0700500a124560b44103001111b0001d5 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 378819478 1250 378818228 378818239
    0xd030306031a0402030f0105240105090d210203042115060824011202060f0409060906091103191e0212090606101b081c1d122205 57
    0x992000d40007400c00c2c0c60136440b80c42a0b19032080c0b0b0003030601c942c50080ea039941400b491740c00700884281410102c544114103020007072128203416129808100000ca1203280742e85840c07450300040c000d021101c04e81d010f00b1035009000c14413009544180c0140404441102c100c1c509246140060082c103d000304915190b0030001c1c00241604005218a51214080501d00c8511340c12060300c119000c0910440c40230030508944500941420002480035140103010245007545030b80e032503801c0e13903d039134042d0121603514003040040c04441d1051007a107404414910385903003001c1940d540d030031094456072a0319603680c0c4e14045803545424608102110300c9401503403a0303c00044980c9400d2011038481856006050001e511380c5010034543c0700080054a4409101e0301550301940421040710302150b000d40104000300e0041c0d1002c1c800c03c0d0a41200c140403581d00c008194004440c0174400d00c049080c0c1c050b54040700141c000c20151101250080343c9a0200c0c203280669a41c410100d50000380c005 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 378820728 1250 378819478 378819503
    0x40209041a010206010902130b0a1106040f0b06100e0f030319020a15020408071802040f170d14040501030f150308130e070f0804050a02091603050a0510050d03030603 73
    0x41400d4801d91500040036029101160ba986e01d00d80207a1166010425040741d03091403e008850107000a00060348e49858403100c0d81d81d0029800d490b0200c20360b42030303900140c889800420060140545a401642134404202c0e200320706001070140c0c8010789000e0700c00d80c07520f5030741c01854034200251554030f07000b83c1da1400003442c01c81010b134641441d02000d40300a959112620f0055006000301d404403042032000380101c5291050304030400c90700c07400c5034017140d8007044002020140011050080c10480210100300c003070002d100d614000f0303080c50301c00902804517a02c0080302184010743d02114028200400c085203095000c00c02400c0d010300200c03100309107410200c107011030300c0d001d030502c82400c208581415071180c1c1c1005541c5400c450203800680d00c013002440181c41030b074034030b50481d00c29400c403014441c0660005207403e000301c1d031031501d44035400640f004080e49405841d030450107100007000b1174200300e92200385000705405568001c1080d00c07001000c0500c00d1303000c07100031034000301507501c0d0703 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 378821978 1250 378820728 378820751
    0x5120708031302150f1b03070b012105070f3f0201030908040609081002070210110f0616180b04030201140f07060605040b10090e06040b09040b0402010201150e0106030b04020904 78
    0xd43d0050320f00c06505000a0541e0081b000380007040390030883d080558001d803a03107000e50a40900a40ca0702e4058102c100c1031440c40010070810402c4090031a54003095041410440d14070214803000f0300c0d907440c241380728803102046582401d41c00194000045545414034039800140c029007010b15004003028400100082c955038081c54940694052000381c41419202046074800d900407824042e51110038050700c4501d40d4001ca00000d00103584100740e42000c01740e02192800c1c01c40440b41c000b45a0264055200856404030307c60a600e50070054100d855800c000e02d0810500607404000d06111501e00074000000e901000c2c2d4038400b000b440007076501d0b596440c001014042920445009074140b512020a0f464541002d04900a0a40d6891110361900e8030189600d44054049038000740d64001d1000d25031904100644118014041c4541900f0b0a00c002421a4041d8808401d0f5514486050100311400c41c0c0762411540d0034540402c60134600700c0054024864410940d61051504014010 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 378823228 1250 378821978 378822007
    0x1501021213050a080d080112020a030f0609060e01090c051504030b09070302040c0833031e0607020319050306010e060705010f0b01110a1401061707030512070803130215 74
    0x2039400558012a080c3ea8544984d039075030b0845403031100820307203500041c012050034503030700310030f0600040c401203246540351a00542d15408070790503030361782c2d8880d4240d030207100b814000c0e0f104020104000300082c0180c1c1d210010440c4490040b10311542040c3c3c030020207107142c2c034141e5010319003000a003182414861155552210350b848220701032420305030700d207040501612800b440740844203900640b03412007001c41503514920b4506540ba26141089900c86602c0c05c000326040000760741000c0c0300e240c20109085d1301c3d1410041c296021503000700407069550700101899540c2c1010b60401a8a0b40c43d08030042c1d620340a90584144c2184011900d0018014150003950740c0b060007140c10403600007018011100508451540b8075254403407000380c00003603002092000480f0b0000c0c000501503454040f80b203c07100034521104119401008184280001400101c0141041900ba40d2804086541c0c1c0c1c142808020b00200308456030300084020754550440a8400b00c40034105a90340d104443d91448 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 378824478 1250 378823228 378823267
    0xf0c050705010b0a03030903030f031d0714030601080d0c05030c06070c11040c0206071409090408091309031722080307020c151b0a0c08010204050f09040b15010212 72
    0x2200d030760802121283c81d0034003030480c000b907a8040c3e446840540c1180c8041d9109050580309200b0035644240c140348041c0d2005001a1081150020340303201890030400c403e401d055030401c28480c1e0000c0c001000a170200058210344200d52342000000003160782001801c40c025400000d020f8044d0000b007002d00c0f41e03c01108040c1510441381c1e0748101c0c40741c00501c02107403c41c900e54409a4042c00200d01d95034015100030801c01201b200303003494840c1900c0442c40c6540203560850b00d114010a10351064541085c01403620201d1a0301000a0b0601340c4005100520a47c888007440701000c0c041a18541542e0180c0108078010701004800348192810200c19071003100c1583c014098102110031034540110444c00300e1903401e02075400c240c500700074100003540c4a41b1029080c40350311500c400250f00c80c900200200001400141c450b8684002d02039940c1c41c483c8114400c21303180c0100f00c0018903002c00c981d0000717102c182d03102c0e03080e140740b0050303141103c540d05541c404000411807000480c159003a40 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 378825728 1250 378824478 378824483
    0x30c010606021e031606150503192d0602160b100f0f350d02010509071a0d0519091506081606080402030c0405011e0506090a0501120f0c0507 62
    0x146504100000f02070b440b401014010030320040180302e41d10201e1040e4004011040103210701e81daa1710303910b8000a1401400d490035040c4800b862009100b481a44803508074020303001a000020001c039841c808001040250008120540c0441c0403440072146080581001d98056020b0005d0b0402217980c905d016501c0c0b041c482018105040031600c0b0343e4000c401d600301c0360b4208110100041940000904d0804102030700300b800e40085d800004444104500854191150000985c909201c1e103154281006d903040041c00c00078119540c2d03c11418034040360452406030500050703944600e44800310303001c040544a054142807055020500006030707030542c4010046c5200300301e4580e984c0b40d11764680810341b0107110581c3d00c00104001450285a685038030620013006d4500c020202000a0222042a0400d42810103400c260040908840c20a075001c0c10341122a18249401c1070002102015903000301810411600d21a6030b09012940041103401a00001440480d9500000412503000050203 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 378826978 1250 378825728 378825763
    0xb0c0f0f0d0c050c0312090a1a0a0e06040f121806030e01180b06061b0109030e03010c0806061b07030204020a05031e040f030521150a06030203090618030c01060602 72
    0x10010310394010400c50b82010b804d4005036040a01c600341c80090040014500381d42030243c000d48100140d50214103030350402d1030010380d100c2c1d03007030890110085a2981000d400340c0d501c00380500c000304001c4002c41450543c4040030040315001c401046501c01d4036030b261440041c0b4000c0001c140d858044c0c12800b044101203000708180b074407070302c4000601c440a4034054031b03011440c0b000c500d25091090007400d03005001c8500c924403411845500b401c541c00f142d2b00703800107080c02150b07400c41e280a000c2e0341c00d080043c1c6080311590915000040e168812546c029a00c40c0305030b001080203080038031240008540041c0115140c0c00d89040180c8950703c03c44d401040e601d2040c90081035190801e00581c0581d4005880c40c0c00403029580a80389a4007001000310b90b1703500e01000750603039401070440c10f110b21a02000480c81d00b0750441030181c415640d4008105141c01441004911180020182d80c03040c0d5026022080b0140c60140c0e41c01d51040c1c20146885509100c808030342190000b40030254442804c41 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 378828228 1250 378826978 378826991
    0x60d021603081608060f04020724020702090901050424110c01050709050a0f0302011d0d0507060e030a0213090f0b01080303060a140d02100504120303060315090c030b0c0f0f0d 77
    0x1803c8410304421540546d10241543c0c40a406042542c00b6156841c8100341149031680303034074883e030000320004560f000c00f0740d00002d180c01181402c42400c4d8000302500020702c02c900342036480c2e80c9000c000b2544036004180d80e03034000002c10302d1604041a00d465064200e5554441c03118000d010307010488000011804c65140040c66003030004884040742d580901c90309810307086600440340c0b0074040b070a0800d410b0030300c000e8805a950b00340c0c607200500d12031402020030914061010b04581c003200800380c403c1d00b21242c90700c05a264005940c5810540513000611051b403031400345000c00d0342c2500904402214000400e450400200540c05518100d42000d400703a942c1952004070307501c0740703407840d041088840441d005050070482c812215103030707003001418107841e1303c0780c11080c240a5a050b00020b850310703000c000f8410501031a619100000c00140904d40d40d0fa202c115035011503200040c17400404200081038241104107685030181943d81040e070f1400c3d19090b40781150440c00802c0c0c2c41e107182c0007 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 378829478 1250 378828228 378828271
    0x80912070807060507031205180709021c1d01090317090a4407031403100303110102090307030b07021e07120809150a08091902060d02160308 62
    0x201002162050001003030414100a411212078000303c170304031300b40107055441f110113071524050750b031180100c5880400c0d80546468690324060940d8400c0313804510403c0300e403500610004646d07080d000c402c0404101403961202481c14036400c2110a0525481c1105030b10406901c0400141001c1400303041611a44422080c40c0d00d031641918024415510301642c01a0320040500c580fa83c0c041d00300b042119503a510030700e440040089001c1c41450500040c0c08020103421084906000383d8400750f6900f145010078140b501c03c0700b240809014030110000c603003642c620940440c0c005c14230180903580290b54914080c03281e21020b507100700141c004c018043c1c0c2c00c15042c4490000d003800110003003400c2460403201c6840d00d5040b40003030740e160004104039440e90f11030085c007900213400c00782c4c100e130b8800070030100030b01024000d00380e0031058100746904c0d80003005800c0000041d640407520945ea807072402d41c00900a114584900101e80c0320301c51400107050f005040b0740e1040b61034482001d007030f5042c103 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 378830728 1250 378829478 378829483
    0x103021e010509091f0e10060c050a02010309020d0c0b0a090b120610020f0f0c01181a0a030207061b030c050703140a090f0b040801110a02061902040f03080912 70
    0x140d100340092810700c80b5100d82c0c030740f814500d40c02c190100501c000142c0c8026465001d600c03035802c201005810744050200c102403891104e00288040d1400d4400411650703503060f215103000e24060704040e12120941d05643e240802c208120f030384808045406070f03499400d0b049580145030044041035000342c0c002010141c032011150050058209081142c4d074280800c110f050318200400118410055400000c01040001c84e4524526400802140b400040010041c0100e0490141c4404a150b0100300c08103d01c90702080315907801280350f8680b041c02c3e400b02c009014401c40034000e2420710321090181d118015000e60305680a40e824860807828201c1540c1501c911400100001c0241d060800f02d405200080c0852400e94540480071035038a02000d80181d9480d00800b101c11800642007102070024498503070400c8142038028141004070030f02940b1100001c3c00f03040402e000c00340d0002204699811100078001d50600150440e0304d81c1080c024581080032400e00401d1250603003020f04100 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 378831978 1250 378830728 378830779
    0xb03010b040513021002030d020a050403020f0a03021f0e0d0809030705040b0618060d061508090706050d09030215090318030307050a1b0f030b0a0528020c07030614010302 75
    0x214005024510701e113070300388000c900343c070b0a0400c1103000900400500b225940000c215500d40340e0385960b1154154010001c404640241c2188540c0e0302e4802000141c07a410402903541101c1100c661500000c041c095644c0d00003000b0255100d045001d102c41003000c04c40140c0406402a011507803405d44510900c0b0495046400301c0703034010350a014100403c0005024446600c0028003100e0038001d5103214041681e0190f04074028810014009400072544401400c1d80305040c00001c2005602c2c20303030b02401606c59000c140000b140c8680890b401e040c0200b285a00340c600344200f00c10345180904081d52030360007015082040e003213804055580d9240c000103a4071003035004030103803016190503594010305034100d0040705505802c20000080b280c4c080e00b80e01c40114050700f85045946882200c01045800040c41c00002c482c404a110720018514100b8002d081c00451005945840018140d450b01c800b6a0000b007d0350b0525203400385696508102604882c803d440302d1302518045410120743c6200c = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 378833228 1250 378831978 378831991
    0x9061205010b0d0f11030c040302101403012607090501080106090207050705010e010c060207060b090915010b0a030e1207050d0801060f0e0f03060f04050d02010b1305091f0b03010b0405 81
    0x3062040358102c4003280d210036240c0e01c030710070005001709071444c610b4420b030400c580b5052040c0f4041410025824414601248030030145001c0e45e00c020012007445c402c1c0810f000b000701d07a42810a800040c0c52170012034808000381d450444404036a06c081d16006044240185c1e13403a54240b520001d8400c01600940d604107a1120240c00c42c241800011a1010203400845041000c40006140824558030080042500462021469512510a01041c0b41c1c000d8203115142d840000580501100d8007400f5040d0307a610720300e555480d618640210301801003d80703406081d025981c003000f07414400d0402052258418410f0310071180c0440360540b0240d000340309580118001c22081c514880c4105901c24040e03000400b403416440400d40800e02d000b0701290090241d2509200340014040c003045503843c07940192000b0710034440703c8004212032100240d1030f0000f00d07455002051840105118403881c15072200d01c0c0c00c40d54003aa5031b4400142040502e001d000c1d519013500c2031814282401760764403130329 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 378834478 1250 378833228 378833249
    0xc0609090103110301020403080d1505010e06190e1c0b010b0a02070b03040305120405100501140319110d21020d140d060f17010b0307051809070e04030906120501 71
    0x2c0c656280e042e9640041d10107203038155030802c03011001540c1d4070064100703a50010b9000800f011038201250000c1180d40200b0b0601c405106003440f07070b540d00011103e800b4174011600758282102401980c80c404c261a1b80c5074000c0019002c0040796946030001000c0d64001d004204050342e891042d449103104101c02c00300140c001507418054803000d1002507400901c80d2070130b2841c00181c00c640c0002d00d031091301c04481d02e8100204030003005609000b55070142a055580e00141c1002500103503940d42c500700c081c03061044421070581400500010003c01035800380074102d8007400c0d03281075810b01c182103100341240c203000b010610380948001000d041306042e645545100f100000046d9000e6041000c1d075412094450b0808641143c15113400d5000b00fa490b4a20b03540800240391030350a507050036256500991007503004100d43d58a44141c103044a840741002c0d5040d4903030050041c1403109680116245c0c18051003032008150f80001e102d811900c8a45c1c1d5009603005030302807442950800c0c4076504401 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 378835728 1250 378834478 378834481
    0x90a0c0e07081b0c070311040b01110709110c01020c0601081606020d110a060c03060807080312040b0402060412111c1a22060b0102060c040e0a0504080f070605090c060909 75
    0x44495444058440b1003000d55040c04c1840b180185401c0c00b03a0011034080140c600c94008500340b0380920b03282a102400e007001440d2424130107503650304072440f60001c113a8440c0324051001c405c0c0011502d811504000035581c074900b070400b40c1e0703994100f8403400010b03104114180480ea210b80c0324a6040d64007a03400391494550382e450850f0990b42401564540f400780f500b1400000740c3ea4820300010120755200850148d1a00d00424107100b0551f10001054108200520307da00810400c1580558048050b84041e2664004119140200e07003040340c400307204442c2c44085c0000c080c0100c081c0c03603040b00c00070741c0d5415001c152800340003503100042c5600d034400d6080610041c0560310350750001503200c3c10381e454500ba03040c801e50031078840707000c0c3c0d41959154144a001e50381130140c585d00404601543c1c3c0b600d071408114410400008211284455803a000324003000100c0c8100c484c95083d85030065183c04242c10b181004120566a40d0414800c03440d090302a402c00809546905000500d1031429 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 378836978 1250 378835728 378835741
    0x105040203041119050102160e0c0c010603080c0601030b06120c010c020102010e07060c050d0f0807141903020c0601081c0305040614011d100f1809020603090a0c0e0708 74
    0x690005001243c110325810341c040826210220b60b22091660f41c01c044101030304d01400a0304001e1040c46440050300c03039007000c0c803100004100d140c0c0c010110a041c9603a40040c084241c1c01000160801050f510f00066059610100020010f050324050203074804642c492800700319000741c8503030005400e9001001e048c546d540c050810b2005841c0180000b0402d808807040650424041c0d070030580c0446c1d00c08040390180300c801c006406c3e11106034200801c91140c450009411034200074000c008010b400000031821801c54400e880c0b01d0a070f04100b605423a8085a00540650030104a074210351086800024041c200002c0343d83e036020461b480c08291621054040380a4040200250f0b2610b49511008003040d5401903154020b010480340c1d41c0e001c50541c10f1034001c00e000940503d000e0a1b42c66000d00180500303c2c1030008441106000c100c8010170b8420000180100300d41c003a40c0000c010080000154020802e40a0a48205800081e2541700c61681c01e000d2019904003001800d1940010b00 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 378838228 1250 378836978 378836981
    0xe060a080703050a0603080a03060320030a02060a02070f27110306040f1e240312050c0f01050a0e010608011118130504050d031103040f080f2a0c0612010504 69
    0x80051301501d01180084e1662922030039070f40088000c1000a0f611f04040040c40410b0303980e5850000c00031400f80080b0503070000283c0c3c0e00700d00c80d0040d128140024000c40b00e17600070400341c001800340b01d522125990762400b40752100a032000518003c01011007400b40c90441d030f44114202c1041c020001421a103840c0e062200410001d84810000c42e45c0d03120a02003400400803460852a200c900421402c80091540b10317441002000c40d00c454421400a1000408080c402040b000f85440c00a81711030083c0d40c0e152a00e1440522955254685020301c0809603140d08510002c00d140002844904d6650304140e08a5181030320002e0f40c2c0000340480c0003981200708140351030203002407260640400a19940045907001c1d5400c84140d0320043c0d040703e680c0d0f05402042103403841e600c0ca8506602c0c1c281c0710f820403128800c41c001c110400011744d25500e6901c42066030485202100100c4c1170020024000c1c503520356694882c603c2c0e200e050340d0340c5218a80401140d070b4811802d041d40304a40d192800340b00 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 378839478 1250 378838228 378838231
    0xf0618090c0e03070e101d060103020310030614060909030a0509190b0301060905030705010e0d11030f0a05010504060e01060f1a040909050604121d011107030b0405030a0e060a08070305 81
    0x107082040660090b145680c0c100702840103481c892907041418204030300c9080c00742400d40d019400314415402e0224020a445000e90b1384100d003801c025070749030b5a141111075041c0382c980009103220f02d003900007412070f644419841d00c220006d8840c0340b49521416019556406890f0080300001c80070041c0c2083e40c206452030035195503090039401001a11043c01031202e4009800500c00214004001c0115260410610703009040a00380514000584000320300401d040400107089800440c01810b00b549003000b40c0c00001c4214800e941c01800b45251044c0601820740701a100c4a050509050550030188103071012116002000440705140010800d46141039a40304001841c007448000f03840440c6000d0031340058421000343c84030b40341a1070700005881c4608030103401c000102c0203092000507000221030b5410401d0a089095a416a550074604807480d04010050400c09040c0000c000340000a48029030442c2c860460046548050080a003d01c1400c84000760100c4081b60000d4020350146 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 378840728 1250 378839478 378839501
    0x614070927060801050c0c010f06050609011d030607020a03030605100c020d1505010306020a08070c02060f0903070b16120f0503150103021b1f0905070e07050c0d03060f061809 77
    0x2c01e080c0da48041e01c90840c1c404884240c404a00003c060f660f0314801c0c483d0700156022201c0400ca0a403d00340450058003d00285a061190709840000c0418040c0e28400b0040701c02002c4600714a40781c0e2009440300000c4d5000c41c0800e04051000c41e9500d480400c0883d86005aa590b80822899408020030390000140a491000e56921401040c003100e009140c042c600604c00503a64201000c4001c1c20440c00411a00c10011618803542c0182c1e0360804a40d0f401c0d40303103010a520380030b811001a040c20b506610183c4555030003d0003248079010041030a1465010b41d0b0b2030b01c810b5400d101c0680e014042c051110000850800010322040307180f44c107050110b0411700d030040c140714054402000c0c0e04039800440da540da21084c0119000304002588060707618038500c06110a101c1951026690390b500d0040040d0400c1000015030070500c920103840c81c00141c0300890700d07106d00302ca00c0a001802d09000c1c500b4051885100031460a01500c48221284010610135854900d0030080100500818010 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 378841978 1250 378840728 378840731
    0xd08090402070f1a18030c1b0f041401080f0307050a0602130e04060501031b21052503050709020a050711030c040e0102030a0c020a081c0b040204030614070927 70
    0x144408071303940301d01000404900c0481900395003010034000e29050001d284403040b541c0108202d01c01840003149012030360403a81c2202c440e140c9240c000a442084c03c1c0b910942003417030603c800600c403038110300c05030481d0100d6003079a1841140d1008a0f0701c80c850700c403015102d64030a6840c0000581c0e40c1c1c1c014803900021020401c5440d4646210314008442640c0c252055500c43c40103109101103040404030900c0140507514a41d460410b1011640c2c2c0c0c0c000303401c105070030f60f00703280d8060040a101801010f104000d210107500100c03404141d55000c036010541d10f1f880741d040f0228030b800c824400c480d00900c16484240c180310181d40c41130a481d88032410b068041c00745800040080d142c501841c1a2114441c00244c2c80b031522221560440305182e00000031036000c10400302c0844c4140302155110144c8505000030001c22081030000390002640594101d440050000203002031548405200741035820140c9041c3c0720070908448036111b0b4040c07400d0729100030104450b10b84040c403d0b142510000e100 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 378843228 1250 378841978 378842003
    0x1080a0b09030d020a020c090601081b07050f160918030e0405090109050610080c06130308130b0a03050405010c1805042004081f2c0c130f0b0d0809040207 68
    0xb201c03c1030340c118040c0b940142e84900c0e40640305140c40420703c0ea024030700b0702c1e2941452a141d0b0050002c8803410201c0344d059000068500d041c000103003c40c04c4d9185030101103030200d2201c103141c150410454821640c01610b0400c454104001d440d2031010030b150155596180310200b1400c1000500e000342c18603e207907503100b20100000c0c0c410300aa510034880780851960407450300b0400303401c11140c244094400c0504103c04c12100e00e400b580c04060320381051740c03d030703c0fa00800810980c0032107580200300d0342070012031a8510b9031351580026104521840081c0310740300c1082015144408640b2802034502c1c80810300b03010300d003815484002c0004911040740030321075541003000c03001e9009800428031130b040704d4001e0312a19604204c00801c021104810003130b0504445c0d070702c0001d0010101480300d1001c01180680309210812001d0700d0300c0401010405105000c1e0205001081105003681402d828017000510f10302d880d01c072a40c21103411031140c51808030301d08100320096200c24011280c50780d0b000c0 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 378844478 1250 378843228 378843247
    0x30c150302040b03060f030a1211070f1a090d0b0c04060f03020a020d05130506040b0c070b0f0a0f0c1506060807020c010c020d0303061703031906120219091a0f0901080a0b0903 77
    0x2c14410022096845054000c4001c105031307414189207030801b001233a04401c0c10000c10500c0e41c200e4030104110000b040e15880c801d80003400b009100140601004c2252046c02440ba001600810843c0d4403a12044004030000c14140e059024440d0b0440150b004200d01008040c007480003458810100d8501c01b000030f8882001686d1900141c02207802c40700007013002000641c0c20031401001e0f001300d0545500700154100520f22034840c08003800b00304071140000c540200c6c00703450902d440f0341c0c0c00f1001c041081d0b40160400c2c010440e82c8103280005441402041c003641c0080340950146d001079441000125080d0288001542158411002c06580e40c00c0081d240d0052208a04140c0340710b0007079a5a410020100d0010310f2490070751a2000d4a004010840d0100140700c0c0b280080e81529001c0090b00849088101015a90320240c00641081c00b01c4207003c19010100c882004104c50b000402e03020740c014007541041c00d02540d042a406500d88401040c400c0d0880c650016402045900d00b24860 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 378845728 1250 378844478 378844493
    0x40602130303050d180b040f032a03081803071106040b0403050303101e060e1801080106051f0207061409030304030b0118051501031109040501030c150302040b03060f030a 75
    0x154416400500b000c5025880700ca8640203071082c0c170311008141540c400141e194920030315130181c030042c40c10255071706070b03010503008681c12015501c01e1840d120110300002c1c3c00891402980390708400082e0a0f0740001c0c2c0c4940d06000c60300b070010518006604142c1036a83d0003003106c26003016941d00680030300c000a4181c8204000704040c40c400c00c055504d80c03d02c042ca00710307020102e41064203d8860101d010003014003588040f411150945003180110b070741c403000302d2019808007080520300d005180021800140540100d4200c0d00c05031841d1301d0f50250410484030340060f0901110058011200811102c2d03c00d601c039040100c071510180d46070213401c00001e499548180e0084911030007240c0104041c50700c45000d000c072141800b006004a1400410046011001018440c1415610038035024109402e000b0341d014400090810401d558603801c1146284445d8441d180700000396885880351640b2074006d40d030032901414002404c685881c400c2140e000c1890140d150140b2441c604a004180e80 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 378846978 1250 378845728 378845767
    0x908030a02011b03020331020d05010e0d030b06040608070513090f11070b0a0c050c07030c03060c02070f14120d08010602010c0e010804060f1415040b040b060909040602 74
    0x558000140703c519039035041c0c20a000003030b814070505205008101320400c1c0142041c013800c8664005005074000250744010b101902000a500030b09002c0340241000015070040700708141c01c004482400160708822000c2d1020340d2540d076001a000e0204008232030160b0f84103a008000f50401a080658686541e070144240d540101e110039114502248810114803c606416a106011a15207d4103496442050300c1c054012045180e80b0720859000c1889601a80c11000e000340a0700c3c40a07a890030f00780300e0001c00d40401e40f14903144c41303440700e1002c0c00040c020301100c501307948401980b4a41114440712030b004071001500b110b06021080c0c1c0d040070030b1001e081802e8061322a0341072541825002401c440e0710b9030700c1106110040b01341001a03a0401c80869015610410201d1070f04445c000709030252414009051070401c02c0402e001e0000508600004890707400e5a003088a106100208015510710750300458200e44200702c800400c2c10504c40e156030160080901600c0c206e9400c0940b18451074 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 378848228 1250 378846978 378846997
    0xc1606020405100e31022b02070c091109060406230307050d02180616140c18060a0e1006031a280504060e1e040809010f090803 56
    0xe00040c24080c501d0604444800e04406140c41d264240300f000102c0c50904001015502c0302c01c0043d60900f8105a0b0b10880e461140070000035522000e880303441550091054001c0a500c100440b10300d1801001842070b03948194110010704141880c140d0070100401d04500c1c0315101c001c08100800a540715800240002c147d150740c0c50704101103c0c114501441c104c1c0d9031103c2180820000d00114130340c41003d54540f8114808016940c03c4521052081421040f403a0f03504031a0218100401c0c18004515943c1180500b400d20741c92003804a505c1d4881d2042c601403a48411007001c8019002588440c03e135100310007a001034042134848a404100c84000c036508094050030890620060f42e250061482d40303a001c5c4030055810040c88000f5000060500032900e140c40f6088440480841e5540c40300010b140c05003041100c6030b00e4251241072080100d90404181c5040802d501540d0030102400b4811b50300a0324241c00c0101c01001100e103441e000305042e0401104000106800200344010060940d = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 378849478 1250 378848228 378848231
    0x1b0d0b0d140105060f10110f1203060109120506070e120a060e010c0c020307050607230a020a06021501050f040f050903090a0503070605040501081801050a0902090c0715050c1606 78
    0xe00c59042e0a6a0300280914052a50090001550781341c1c07440c040c6000140b07081c2a5031107070202000718076007140007014440c0c0d40f15102e81c0b510600451402580940420303600c030428192680744d034130400700c928a001061036121100040c40540f054002c1445440010001f04404103545209403428400c032400350b603090b50301c00c2807441c1720f5000d128034042c0c248c4508000e4110074903500000d40314486441490302504000a1083c100500380700705d9440511808542c0004068000d590f590b038108504049004070003410300410102d000080d4110024843c0f4140d40b001d80c02d21090003060321014203201e41060320348c01d100d06456424040e4070321a9410384000c50321281a0400c210b6016080c0c3c0c00300d402038102050a01a07680d2050498055507000e0034041400d0b00c842414034034003101c2d0018200a03510b06030030f01401001e40d03040501818000c580ca66000e0300e44100144080c0b0030560001c058030000403c20340501901c1e040b0342d42c055403490006040030170520703460000340800c040854003503 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 378850728 1250 378849478 378849503
    0x60d0b03060f010e1006020d1b390308070f11030a030323090615012003090415061b051e0a1a07050a030906020c0124210803060406051201060e0c031b0d0b0d 69
    0x3940c245524100101911501d816112f10310b80f1428100d02c02c107403019207803062069003d0140151207117806030400010303003128940c1c4100c0c00c1c014002c10501e4440c00040a8140124104010301c881d900e0050a44102400e03c9403101d52044001105030b0003110306200d0b01d00300c0d54580b2120100c088101c01c0c20000515520602c98007040229100182d404550b50079030041400003e030301080000e541c00d0051403150481c003003401c08616154a0032060324500d00542141480d5407070104034592154807400302314501c011501107545180004071680c2d000101c0074088005414481c1c0c2108a0392801841e0051030141a074a105003511002c454818021600c40980d0b502c11900d0b41d6428010280c0c0707030384140808607c40408106c000468005450500e011001c100740da5151b0303005c400186402802060300c40d0004c19a00d011b04028800c00d0000c00c00c4400286103070361140c049a108102a404021a107d40c001900c0c655800c41c20700f0707601c6240d50f514000469241c00b8000b001c40c2c0d0040d140341512 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 378851978 1250 378850728 378850793
    0x310050310091e061103040c090509010525170906041e050a0204050406021207030b030708010615050c03040b040b0d061d06060d0b03060f010e1006020d1b 68
    0x91a1040300d10901242c5072440d180042141100c1d4841892201c0d0152802d415443c280b040142041015440c00741800000b03010402c08200f10a10840ba10444c0c00e0080d940c50030341032401c8400031103c403c03103900380b010750980e85201904030046a40d030340d040030f00e1041c090180c103030140842181c0b1a41141e000e2800d1105201c21402e2505075000b00f2800308071000e2140c0c0d03a02e6103d041014000f80920348442c04a020030100341c066860301000414400304500d0024401009040054800b9003e801407a02c080f5a07000180555000c1d2880024000d0f85040b07144411105540207011210b6180401e00c401f10705035008400400007001d512400d55160825000d21004488240c0c0c069140340c0c02c0408000156605c8010459020304220340c1d4540b65041035049030081c216100d0507907454015182000004e800c100c95042c1600d20543d000e1010343d44051100794403c100c1d00030f68001d031784040c0c210241c03544502150300c05100120040d00c1c4001a56030789400e0500c080c100064081403d00c2c6c549107 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 378853228 1250 378851978 378851983
    0x24150301080d1407050c04020f0c0d0806011e080f040c050a0b0307021218010c02010504091d0105060f09131a0103060f05070f09030204020309160b03070e01140412050a060203100503 80
    0xa10f2660181145007010390ba980d1940c03107160f00340050082d5004a0f5100c40504490203540d0245100d0051310f06800b140c10000b046c24500b229103e0108040381640c0341060300880104034000d00c580c032080070740d840b0017490509c030070002841202d5030407098101080c1c580702c4085290040180300e0030780e84c5900308454040d0810030000891100002d081c4102e080c4004a28011845501c0c2802c0c00c420402c05800100e0f44c5106640024165605100c15007448240f242e1070f06c511480e1060080000361140e208010611210304c483c0ca501c0031020001c02d9646080c03030346042a09120f03548034003240c2c408565281e100348099006a80380395882c140101c0c9503065000300703503009010f4035003400c07941d0800d000a040c0111901001c0d00440c1e02100146094404012600c03455118400c0307800e4540d52504000314582c004c0b1468400200890b8800d880c55000b0000b60b10403c4200c0b0f00d45c2c1c181403c10814856000c0c007503406803011f200c0e18641c0d0003c14811320041d401303080140e592410b01400e00c003d01d072 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 378854478 1250 378853228 378853247
    0x3030f07061a0108040201050a1206060c03090e090a0b1911070b0a1b050c01140c04170606130c02010b18070e01020606090c090121090204060e24150301080d 69
    0x390b00501002d98054075a9101c00342d541e01540c242041a1203a130742d0401202c51810f107104034000f40d4500100890400e030000d0100440603c80c0daa00f41c1c40780c0d01d52881c0ca20720300d425150950f4039030110600100140b0046455a8000c030078060303d664080f0301c20058401c0d01c41c01d0207000b015510000d60b0f0814070224401e000d5004c0724040d018006640c80d00e01851040740c0c43c401e4601003150214016118403800c0d0000030049080212200c0c05003002c90030641284d200f48961403261206085142c40c4460211b0303550700c41e800040422880f441d00f2005180a000c2070340001085560b1000c40c000c1559070071142c198003407051580d10095182036803001e041d8105050000d419035018200704405940c448135070903840100000d045494031165001a610303100c000905803050b07800141a41002e51050b8018031445000325420301040740d45103e5407050100680d100c030007084058051a50035940c1c540c0104c0851070203024002c026080d40103030011030304280c200140b90b8104501d0440b0540e4070014030b1 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 378855728 1250 378854478 378854501
    0xe040c14010e060a020f0703050606090f09190804080102130e0a06080316050705060a02010c090e010b0712180e150301050702150c04330201020a0c0215070203030f0706 74
    0x6903910502440060701450a01840a210300c0e030028840c00341d07074400d20039000c24401d000c00300c0d500181c0b60b1801d40d071a85d10485a607409040da4500103481403804041c258028500c1f100030300020150346000c803c542000c40c00544030360031704100014030001d01740300600b41523201c0d00140c01104e040c200c8a41e40c0c040c000d45002e40640c28480240300059001c404c98040c10a000500002a00c041c6011810044203a2003141d100d50042641074a1507019040301c242c000b00750782da2247d0644c540c0c0b0076030440d040a004081c3c0e1070909024070380010341c92051001c142006810179060f0381503c64050704280010750030942d44090104e040c404c214401c50102c00d2001011402130105250041c0004d544030100700a4141841c00c890119501c0e6140b01c088802911104031120301ca4080c08056002d010100364400d04041e00008002800910610941e114607041e03070303640d8180703c43d144c08101c801c0901d890010340e92401004a4401650101b00400d07141c400c043e4955201d21180c00d1141c00c03100140b820 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 378856978 1250 378855728 378855749
    0xf03020c0c010315080a0503072901030204020a030f020d020c06010b0708250203011d1c080c0906090d06050603060f0618090a02090403020c031009120305090a0c0e040c 74
    0x315000d6034008950481c40400078640000c12240042201c810300d0241d41c044001400b64401c0e1909115010005141c107902451400241f0f00382284203000c4006030a001c0d400d01c1500030014001842c0036001014030480902d00842c0142e81001c138441260700c00500f01c4110383c1d0000c0c8803081408140410350060228840c01402c12a00e42c807520454426550109118003049105498451403810800d4585402030020000d14008140460042c082c944802c0d000303216100c1c000c400c0c1110700d1070360162103019699806840c5c40e0384107038079065009919002e60100044c0081da1250701c3e084441c800c240e002e2840401e02d81400001e0508000e00548443d01d4601c808080001c00e80710034101050803004d0000840842d903c07550300a00b4194501402588801e506003172100b40f660004551089500c00c03029585109400500001241c801d404c1c028034110007203414110341e6000303502c92540008003070144c448114003035903520050031194000c400d42035551010f000030b0001c03601c880406000d00714107 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 378858228 1250 378856978 378856987
    0x7050a081f09020a0306020310090b090910020d09050f03040303090f120b07050f1801030605011b0212031303120201060906051f1404030b01030506060306040c0b28030c0f0302 77
    0x7222a1403041d10100110807070380701ca4480d0210b4407004541c0c402550441421901d9051620404900c3c0e4210b01c42d2a03c514109600c90b145c0d49444119a405104004018202c02d52005100c101941041e4000c00010b5980c0095601041c424001c000280b40030034043c50f990703400c40c81c010302a4001c9801114807a030401f41d040c002c00000303e07003812045802140142e540da41c0d000e8112941d100380807010311200404070b26001603000c11000d03903008603401d88090044584600044035075086041041c202d2116040000c009800e1400351304031042601000c1d40e107032100c14484542201c3e90f5a008980700701c0200300000010303a0a00c203a0028140c1c41005110b5035140500055285062294201c42000100d80341c5001d580143e6017041c02c0401914002c1e04c444d601d06102d01902001d100c1076625005020009400e4038020402c6803003140d0000b070180b0a9810128001860341042c40340d8903c1c80704d0305030602a00d40d9250304000603041c0b07a5034003241040328003800424410740307065210241b600600 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 378859478 1250 378858228 378858253
    0x109020303220f080102070b06010305060d0204110405101d0603010e0412121a0a090213180e0102070b07020c0102070b03010b07150507050a1805180c0d060807050a08 73
    0x840c2c1869201607503802914034600144031120348940d111103042d000b0181d00190041c410740143c0790941c002c406200d415a01d5074010341c15581e04480c00d5505c04c0382003a00d43e0040ca420783c444140c1c62921204207041a88400204130600719094004000c80c0383c2900c0c5030f600e0301c00021001135a807002d0311810b0030355240424480c20301e100940002c0204016400c0078600e40d101d03101c2184030580450301848181d16010381c11000d0303604050b5a5000d030800d05000305121000f0300840300840008041d4003036585c5803000c03907214250980580141d86488a03621000f03110240003402c40d42d8014401c0039405e08140350f02038a0081d41100c2c483c155000040d042298503440710903281150040c2103040c0c1d0300e000350700d40600e40150010041003002d1808091140040e03000c0301601c0c40116a85500c103180924100c04400701c0e400e485901d030f0040343d28020b27551001b0032841460700805040c4803542017910200840d000c0c3c44140c0c0191046a0017200d0030003031454003201210040010001070301310455400c = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 378860728 1250 378859478 378859483
    0xe060913110603070201090f0c06020118110603071803050d081312140705010f0e120f040303050d06030203030715050c04030f0b06030a0506090607030c1704030c05070b0a0c021201090203 82
    0x7500d010720070007010000410040c000c0d04181c00060744080b44081c010a41c2c0742200c403030200c0b80a0100150b180418615826281c4000402c4842d0442c0105001d403034618100590741c0c2c402040e07a420400452502c201d81c103110407042c03000e148244058121780428803001048100f0042150720380081118086012030710000703501d0600c0b00c032854040980300d00c10390b12ba15a4469400001c10035880c10002c0000b400c419800760b1140c54400d03003038483c440300b51008500f04d40101c01d01c4122511040004000190195004148070f0601581c00700302c40f070792500002e086801c9800241c0d0240c00b03032040307103103402010301c40c81d135115180c03001c090b00305030450315801d25103041610010548261a80400c207255001c100e0090b82c66840b00880e203882ca4800d123031070749030a004d407000300c0480e00b01080410260701864060924002c9000d41802661300da407400c50760008224400d44443c002d60b0b4011842c14110380040000c0c100d5900e801d00010390a2041c00000700c4510074800036030340b41c0403101c00160b401 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 378861978 1250 378860728 378860753
    0x207030503060d06230604050c0a02060a0e071814010e10050f04330905042d0204050c0a080c070b01051203090a261c0c0314040e060913 60
    0x141c9201c803030000d80d85003010003004020081754840c0040c400c000b80d020301e50751465101d900141c5061200341ca032031b815509503004808040e00560003450019184960319032183c1e100414010803180310aa564102c0e8449450340c0305072000740340d1a2884c80d0410641e609a8500601c0d500d014081186003500c00707081d1948007801510300c41d80414170340078074564803a0405482c5003204040340d440011400c0d01c8010074480410361006055042100081010a6101e100c2c4916080f85030941c3c1c5c4080c2040e09100016415036841058800c42c1d43c81015807201d1207090320401441d4001503036a81c0852006e005854001c0c01340c1c5940108002220014004c100c03094111842503404001500307c501e0b5003400e43c003844000640000400310001444074510202050031840c822a0350342420382180d4080d11282040f0300e45100180314014884040d1007044400e24450103460407a000040d940d061490b036a1241c0e1011098054a505001c130074641080c01c1c9411000c542c001c00300c150019a140b0b00032980c0c = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 378863228 1250 378861978 378861991
    0xa0201050a0c06020906042403090f14100c18090b030705060306010c0501230606030603060402100c0c0801020a0207060215131e031805030d091509080a030914040207030503 76
    0xe0b5075100100300800e50b016039480c203000610203511282c8400449400c01c3c1115291089130808444215200d0300038441c1d0054180c0041c508005001c90383c4070042942d00b011074082c610f1080510000884a082c42a803642e4032440d0b0364a113202540c0d40403e56041926000b18003e58940a4249804e58000806c8411160700b910001d40381d0303441a005070707000000c60320058029400c1201c0b004844130075201d1198017200840e404c10254032001d00340104c50204890710741c0c165100300301050151801e0344800108102c2c2b0315000414107019980c0c942917411a610100341607401081c960400380d01408003201604a0f44014805181c1781200015100ca001e4001513070605910306400c14044000300c40c47c804a44c0e04801c21000c4d0051400411051105c04402c3d0420041d40c404505071902080e101880305c22696440c101c3c3d810109082085001c0881003414025002000620400203000c0708090300c0c001c0d15200d04191401060443c0004d420880d1880f0718410020b64000039040707816170f5000f51 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 378864478 1250 378863228 378863237
    0x40c0807080f150601210f0c050306130b0411121618090e1203040f110a0f061b0b100e0a02030105060f07053405150a111f06170a0201050a 61
    0x458010040c1c0350828200015071544c2410707201010f440000380c107c000105610102008810440142120103000c01d582c2142d004007403084070590b41c42c2c142c0161450120007080040d80409664054020f0f40c40801070050a00000c01000076010000302e062000c0c0001d4101010111a102d1541101c0d04440c050003602c00e590301000100b400c0d003001216030340400140040d5580c00c16080102243c6074214080b20704c1143d5019501c0582842c1d1070820850304158001594a41049000d0311200f6117070216010b41104c020001004c80e141054090141030304c01c00d484500360401d040101401e8005104035a5540100010001d54580f4011108001c8292a00344c2d1100d07107900d000e906040e0102c001c1405004030400260505c0100c040124035413185110074600c5550710f206201c83c02c0d115400c456220384051115818144c0560210520001600c042e2a05040700b00b034420544070038402c4001c500c9503200002d02c000040911f21404007046540140a102c2041e40001c2040c4105d031450780400 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 378865728 1250 378864478 378864481
    0x8070b0c090a06030b031903020705270403080403080702060906070804030c0606230909060105010c08130810061202030a201e180c12040c0e040c0807080f15 69
    0x8551050381d50031040142541c40196585200034090483e0801e414428005c50000c44400214900c4541c0f10740d0b8075801401c811890041003003a9000b0b80303896081da100d81c4501e0341d000c614001b84552302c070b20320a444182c4c1604040c1401400a04000d10441c290740c041c000384003210310001841644010302d0b1518104654651800f01e0300511505030040005041401c04200718100407252805000001e404500c111503c004100c2c03459030603654800c941d0013540c014003495201d10264100c181c018405285411214401c40007522003c0d80310240907000041d0032070080c0e2040c041c000041c500300d00c0aa003180d52640010740c0345c54195000030701110901c03031601c4040c840200c140d4601d50004003a208000800f03201c80701c3d101d201503265071103104e0746610701c0d919184c91090140104032403101c0e142000340c2442e032214010005002520520b802d21000911540150640c522a502c6054200003407480c2490300740c074001d11508045c0300c6402c60210490404800500301c2240003d80308040ca19 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 378866978 1250 378865728 378865741
    0x618060f070c120305150a06050d0216020a03060b01140c03030708102c16020a060c09030605010639110a05030a0506010e07090b040b0903010f0518010f020708070b 72
    0x311154204020034220490f0a120394094240d070100e4400c030b850341c80031015510b1500811090103c140200c00c0492024440b21644d100654003074041c0c03110740b00d0905241c003080d40000c0c041c0100d80d4811290140c640c41c2596007964820800f03507089500f002e503181403c201511082d02c0340030090450040000000008010b20001d0300354600400f42201a003100321010446120f6201010400d901003420740d0012a1141840d603491281d1030386294082c10448013107603102409811000c8203081042800140400881c4287c86654000c02031522201080216801c00c00e0084000c1c0d80320014000c1034280a10604403a00365070304c4400d51146040030240902d00c00105514840d41080384c0501c100c2509008010b00010071905807100710843c029141d84481086881e14010300415000004c14801000301d4641c0c0400740444140040c000b00c0d10200d64030300340007115003c5074031180300b901c0c4501900c0704803400c2c4504103004d5142c0d0401e61506101d519044500d214002d03005040010100c006101e = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 378868228 1250 378866978 378866987
    0x10060e09070810030b0109020403051204120f061e0605030d031118030111181306060e0603041e03030b0a120b0c0304051e0d03050f060904060b010203040f0b030103050618060f07 78
    0xb03540c5c4202500713541e584400b40407009401c02d0004403058424400300c4a0301c003a5043c10368040b9852642140741882c0070f80d403443c91446400d042102c11945602190210707441c21054200400e0900000140803482c03e410103280c00070b2407c1341c2c0701f4185040c0d10030010500d83c10848100e05c110b41c203c40d58283c607610110307005080340e0400840200006c0b1b404650701240440b00c004051040700c0340d846455101d04040100c91720751040380045829981105518100400030b164818000c50f44640480368a0b107241c1300986004a08030002039490560494a14042115001900e10080103404180e12070f0303202d411980001d42003084100d0302200250400c0820043e400e0cd0405000703e0f000708820a038481c96172106407002e0440400d003418000b819645005000a210300001444070b0025251511900c000701000280d041c1107000421000c140f454801c6149030040114603400c80d41c9624505059080500c050a58030079413102a00c80c0e68580400039070b55400c00030b40240b10410f502c5080003980c = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 378869478 1250 378868228 378868261
    0x2030907060e13050109150b0a091a0903010c081b18060f0f07030507060506040e06060103050604061a040905070f020d0f0207030c08010515040209060d11040503011410060e090708 79
    0xc0940303013400000b2807000d4298201a494100c4c81a014a042e0b896920916290007003800c01310000705290000c101c0c00302c40d0611800c0e1213007402a0302d45000021008a42035030315808010000c1041d41042c480340006400c1d0440038641d10208036401c0c090b1070388654040c03254071411240306140101d03149080001010441d06640640803800356914183e284c0507025410901081e91098640b40004100d4140340c000d4500c00d60a84000d03210310355410300150010800030382400c0d00240d0740c500c00b0540c8403c0000e40000101440f9260b42c4551400d40d81900b034030b20040c102400c00c00c50b140c5407140720350002828540d01c4110306100f0120b000d0200100e19104190740302400d41c03002d100001400c900190b01940c001c42c0008000804022140300707000c01d0748910345409400c06400c01a81c02840c0142d8030036411310920f440040c1c0303443da598002030b00b0b40712107885048104041c1802d01c4000c00420050a00500442c01c000e0a03620020303000901118004000406120080c000030f150741c10085000f4 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 378870728 1250 378869478 378869509
    0x3011a011103040f060801090e0d05030c03040c090c0507140d020606060304170f0901020c01021b120a0512090307170706031d0a0c0f120807020d1b03110a0902030907060e 75
    0x100c654a05c40284000c40a10444807154139101d00303040c20480c08a004000c800862700c1d0103184d034440c8946041b180d440140b082c0c0340c40c031102c7d601107100c4c4840e00444004070300030380d140c40d10381c01c00d030810742d804022003c0441400c0d8000c0c03070741c072082640114205500035422501c40381c980c0c1d902d05120ba2224071a00300d2040349000043e0048090b051100503222000c000c0c0c3c01c0b61342c0154003800580c3c0d904c00424050b05550f5130990460103500e448000e070095881c0040585512600c265100c61500c129121840e08192020404c0d4020303080c10403d450080c009142c4030000d801008a8064031400307280201003c01d07840388000022340b205034088103442940308040340c210281c0c60410045035812400341603a01d00f001040021301000c100d038507406240d0807034400c1d490400c080e8200a0701242e14076080700d4a009055420103072003a050b41802c01140030710350031204090100208010b003c6203412030303a480c81c8140103011620360005103a4040c1c44040c248503039000345800c00201112501d2460 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 378871978 1250 378870728 378870749
    0xd0308091c180e090c10020f03031302180c03071815020d02070524031302090a05040b010e13020d080f1b06010617070c0614040302010b030c03011a01110304 69
    0x48a1180303501054600b42000503030300440c0700c0c42c0ca03102e10809480c0242c0d21581e45071702c500c00940f013030700d041d00c1c9504140d06140102c0382e11203410110182150402c407244803102e01040d0350718080d4108895020100c10309402040901d2800c400b030300e0601d0101500820400071205001500c018139122804050251800465604840b4a100039540c107580080500103018020002405082c080f00503444141240c000411411a0b40318030303070031508010180510021045002c1c00940c071020b804034040c40080f5000b00c1c4510302405c224100340f81c1a8000b641790a07c0104000c0410f0b00440713010981c543c1224401200c00513410b107400d00d4040c002c0e111880c03010004030444003003280c1c10700080700404441510290380c0d846005540c0380406540c1c010701d40886500007103a035845542507001c520b105140000744a0030780f51060004200071076044025030b5403030300500c5207032500700891908644110001d111400402c0c000f004044030f80403050307061200101d0000380c8408280241c1d0090201d00d01c0 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 378873228 1250 378871978 378872023
    0x17040e0103110415150c050c0a1805060f0d02060306010c0510020703030e070302031507181202040f06080309060a11010f05100801060b042d091d0307020d030809 71
    0xd120102c59503075004207101d20b1070540071034000c8070f6040c42c020440c4c0944102907003000c5c480e4015120b0b04505807084507640540110f1345016901d24544102602c152009030006065054414007142d901074441d501c9602119904c0c1c003955200381e0b0901c09160705441c0291070791640b0300142c548085400300140b00d8054028900702010041d030103000c0c0607000fa68103016103031500c2c440030f4582c042c41c000650150011940d42100c10300c1d00f00515003284551401c250282c09808007860000d106402c0a02d0407441d508903401076140500810036080e80c0c5800401059140c81882503980c400c9160542c0a00000700d00007814900039501d40c0101c0302e041e0005c0c805514003000c0a8000c2c02d0031100c0c00c8c071380b624144002c40c0341481441070205442900002902d4107040c440005103c0c9280b40303180e126035044510040d601b2811120f0030000700032050011076900861108201ca11103860302c10102a4002e00c8104003685e90340c006030701800e8042c100003006444e641809403e04010840410711044090b2 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 378874478 1250 378873228 378873233
    0x121e0209040b100b040b071e120305041502031003020922050102040905070503040309030f230f0d030e03090f0604121a070309050606130609140108070e01050102060417040e0103 78
    0x40400d11902000541183e0030b0b443c1e003002140c900450003603558460f014020180040c0141d0b0f400040c3d102003000080071a22641d980301d20121408032031400084e20340d030501c81040208183c84001a00c2c040c015411440d020040310b81a13050341c40043e22400c000c07004036072284140f00c000c80480904203512800d0241c2402c015010350721510403817900514001c00074428600c1807041d6805603030306035103600e051032868071080300f000f80e840c0d019075100a4501e00e050720403c1e040380c44422000390030050b0041d034200c0a135060401d50002c003110103150814074403d0f20100c002c011142c5014085549078050b242110100f13a050003540c11075445010700c203808100f403250340001d43e131000303a0000340d103076180c1d0f2108012000d940c0c0801d0024069401040400e4451078004c0c1402d10700c2c038125400040440d074030070803402a40c9211210241c5031607110018400d01c04140042000352880070721081c059403510300000d6890700d0041c00980308544581e00a00d9080c2241c04032001008400384448103940c507030 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 378875728 1250 378874478 378874493
    0x601122004030b06030d051209010b1314061c15060b1b0c0103060e07030203310510140c03070e090c0423061b030912060f070801121e020904 62
    0x1404103549502e02a40024840e05c1c00007112131076082181e0300d0b2801d000076001a01c8176148098100300c610754075055004003a0300c1d0411480b600c00d038001004641000324921040d41121302130708842c01170301c044036003080c4200c0c4801c4070415030b980004c5920f00300b2040141e42000307100d260058140c401c00007841101303181640300004400403e071420340340702d8448080154102c4581c0d00c180e510082c81c02c4001075100f40282e01075a4008140b424520001000c40110000320140980280401110000e00c2d418007508001c05606000f540750100700d00c0d020300d0132140c0b40713a9000b00f81c030401503c0000011403030791140000b1600c0c024054420070b4a410310402c4500c240c0c0090090202442c98244a072009901c8016a50b82080c005400c41c1e20340380f1039046200c649207490601c049144800c118035501500d6014003c1c461100c00d0002c5d11003130a204405449001d00544039004102c0c126006110b1071048d58850309001c3d50201c58085110103003030301c1e140c0000030301c03c0195228045404010070310144 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 378876978 1250 378875728 378875737
    0xe040e0a0303020309190c091e060f0602070602030c061609030606030605070e030102121501030b0306090606030c1f050307030f020a020a110420072d02240306011220 73
    0xb08080d182404000203d4014180c17140e0409840c07c1160201003090041950007100051001000180380541c2111a84255001d544c002582c10b00e11b240100541a8148004006032907e407016600d01034042c00d42c80d0390b50001030107070901010300481050710b01d0300400100303006503400300050100c0c035903a080c44d000a19080300c084000c180070035482d2503185010f03c00c8850b041c601c3c6080d406035403592940c907000410f05441003030515a03103170701c2001c5c165410402a8414030049004111074903107203003454185103512054601400701683c0d0100002090a4110003071012841c1c0943c4994030508102c020303021460203461054400140c0030180f40c0e0108100a41c0390140c2c60703401c1605c40403c03c1c0021595500070b480e2241d500d246801000459044c024403841d0301135008140c3d00c0c110304d0346800c0d6809034010318824490350304200004509014080740c1c520710000d101c44103202d070210603800e00351000600d00c504005800e0b1302808504565403000040d05000710900800000030005000c0d503900 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 378878228 1250 378876978 378876991
    0xf0320030a1b060503090a032f0105060a0b090a06030903020a060c0c0b01051009050f0d060c0801060806090f010603020309070306110d1d031902070305030f09120714010e040e0a03030203 82
    0x10280b6020640d01d00440880f40141c12801c0242000d903402d44089900706580e001003c2a10b200c1d5090000d80000000b807000301c507803014000038141c104441040702c1c8948980c40358040c110103004035030301660344403c118100d642900300801d541c8030a180890400f19900001000e41e07180c04040c0010a501c0842000b03154403403440e80c0e1180c1d803140100f11503020a96543c0740054208902880241000310f004215004003500086540080307540d500181c80b880352510f000140e800d0300400c421580011520f4001c40d041d22084980e041005c039505403454140103003070038542c001011568003071041210381e000b1504103404014007007003503070350107000c0d030180401010b150f090014964030000030418000084004c1300046150100c400c000300c0e418072402608030300b54091070740c00001045041c001002c1503560010f10613502c83e062000c0000c0d41c0303140300a0900d45d50103020f00348070880345540216102403003400c0c1000c0d62060031000901400005040c05040d0003070402c06030415402d174014502407035 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 378879478 1250 378878228 378878273
    0x1003110d06090b01080f0112050a02030706050c2a040c1707020105070f02070807060f050c010203090a060614030706050c010603050a061a090c0a12020921160f0320030a 74
    0x410f0070700460300d101e800d490100401e10740b5030042040c0e2140003070414140d4822400d031080080306d03400090400082c1d51048000c50b40000e04c0c2411742c00107000380b42c1c900c013089802c0ac0c02042c01a0010702c40c80100740300b050103141e82c0c0280b0a0ba050007070752140c0c10703141500391100442ca40801d000b4040d104c250780c91000b2440c034004908056002103840c3e41a65456030080002c2894558210350f0002c15242d4001844010042445607840070700044d403145141da80105550200f0f0301e0f0140450310343d980b004a8403883c4003100c4407a660301150520440b0700c0c41c500607491b05451543c40d03005045039072004020344101d50315102080f0141d0000d1068880380e000440d0501c180a00340080c08004541d010040442004600d03031031401407070300a4145139126001030910b0307205004034803c0220b0400e4a840c9101d9226500003814003001000c0310b414841089801841c41c1090454100c0010301004004243c104110040312605895071010382c140241155440d9241f4100486071a0200800c05d1529 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 378880728 1250 378879478 378879491
    0x313050a03031b2102160c09061406040e06010804080405030a03031413031403131e170a02070302060f0909010f08010e0307021c0303092405090109020f1003110d0609 73
    0x24020541c0d100c8005545074209050044c6800d894002e500504299142c0002014000085450321004d4005044041c80001d00e45082145040103d140d0110045c440c520801c000d021150f007008042e50480c1007820040c810f525079281510440c02150002034062144a07048814150701d0f421045048801c10701681c802d88a044080009000c03840024000c100d6580c0f84099110025000b198040a5002c000795442901d554558240d13070ba00c500304402803000c06461040c40824810015071400d24030445240003d4954041d480e01007510010307100f1240400c90410081c00d00f401c94400f40d90040c107500081d0b0b150070250001e90585d002c0c4181544c0782c030040d0130001da07001003103490340c0340c00805640e0950b009c90f1448003040c0e9040310450030161601258400102c0e90041040d1680402c40d481404491030341412040311001002d500b0640e04201044002d0388603d000070041c11002e445c030621141d4640800e4016104c105070749069500f0000705081c000c20310303070b000000ba0340c024401880b60 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 378881978 1250 378880728 378880781
    0x60f0405130b03030f1308120910080601020c0d03050d0f05090709201c0938180f0d0c03030f0209220b0d06020301090b060a05040306020313050a0303 66
    0x700d44100480e9030f050780c41084113056a030040d0000d400c031000801e180044168807410880c0c189100411510444440816001f14601d00b03c42c04903100e03c0300d417804003401e150440000b50303615002040035000c6c4070034040c401d082c5031181045826510142005104d1460f41d550300400514007241c049a203400360050207d5050500d009020b520800c9074405284003000c14111031503984004180c18800c030300781c1c0c0c501e1b0816400380141120700380a0441d940070f045c481e0b2841c23445047d01070110280d004c04036034174500842114a00d0f0344c0000d4042c005201034580741005070310703281d121100e80c0b540c0d00c00c0020031607505070f105001c3c8011a20030359081c015030105285c07100581c0500b202007584000812903d940164050a0401c401a401140815400702030008600401c0304504181c6019030000018003400c0403a00520110706400e40b20703145005404034004140d80241d01004001d19000404503503404020f03076000c0b08880d0000c00b92014500780e0320b0040c004100381c6e58074040184090198112 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 378883228 1250 378881978 378881981
    0x20706021602121209100314040c140301090b010308090321030103170c0c100201180609021014030a02030417030a020703080f06011b0c0b070f0302012004050108040c05060f040513 79
    0x503132401441820300ca000d83c10024400200b0310180200341c0c2d079440541c8140c1282400d94001e45c01513644009950404200710002d8040e8840030307010303a06060403100003c10101c0f1041c1160303013103151581c443c00408006400c080000038508110083d61944001c6a035108000b181220322070082150043c08c1084091130b2401485aa03002d00e8110309202003181c14204000002d1450a10000418500c10903020b400d26155480a550883c0d484081000318103090460074400e04003814503c12004480301e10882900c8020400341da1250084081410001c060215501b0030415901c441d449107040c618240081d008140d0650006400a004c5462507900c0301c8075074085c0406945403404546007007441c41c0c040f0b5008030115220b2640000000f0b900000401034083c45210340400e01c508070a5003002801e46040e0781c65850038036600e030b14642c0e18246842c00c4900305c41003030811182503074070350070807041c91403540c1d00c01d07604110001400900d004d5400000c00945004540f00f403210144041c1b40300 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 378884478 1250 378883228 378883243
    0xf02040b0a1b02100e04150803180901030209240d0f150902090105150c0601090606090626071b06021327020f0f04120201030f0e06010902030a02070602160212 70
    0x4c1d040400580e00d110b0061048050504010011b030001c83e4416003040150a800000d0b40081d200d600040fa40c11802d110301c540a114550301211903200325411900042c4555101514485180d4120001c5034040a846210a81c9581005100c80104d04050030328034603615114808481ca141c120340c0100001c0300341d2165502040c0c01500c89109a8200000d02140701030086580c40d40350340a00155074410740c00c000241c007134190441c0100d0441d00e881c001400f18030440c6c021030107200080c64840d40e11100c03c0d00d0151a03040504002c20310f42c580c41803d807030000300b584418264282c84ec01203014880e079a002003403554400c58a804145543e50185802c08840030142c240c54007445d0b078540d07074041c002d03000f81c04040c0c81d10f00418905807207401458940d9009521102c800c144c0c5420140c250f68161007007001301004441c5c1840900d103000304c030a444450500034065050740c04404100070700200d5064401003a4402c45c00c5550320b01203101602d591600341c038102c0c0319111040d4500000340000c80e410 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 378885728 1250 378884478 378884483
    0x102120103020f010c23010c02030c100c03060e1003050606011704060207020f0a1203030605060301061e02010f0617010606143406020901030c02210306040f02040b0a1b 74
    0x2580607400e581c200b091040142c95403904214800c08504085107040700804148900b0203001c1d04441e41c034000283c03e540b0744005a030190342041c8200c0d080c03c2d00200705030840f5985044000340003201c0410540080080d03400c40300039461014200140e549200c00c01c035042c3c80c003c004036107142e51240011105c0c0c0c940d0780c1e48015041490408140000e540760094416140300401c406191040300011403803601c281c0d40320443d08085403c0341c409040c1c142c402c0c400901016103c1a11b5507041082c098418500c3c0611881030845209540145038400c3d80031101034001c0c000140541a52040f140001008031000c041c00e95291010000d2580d004022109060f1410802c0360304080c0a0300c94003e8503801d0035803a81501800c0e00031001d414026141021001c0d129000058071000300200050841c0c0040c4102001e43d40249003030300120031400b0b0720401070790140851541d25a50440490090980721600075102800070802055141541c2e021f000100c0090f1f07076456106401480d50300040725004d001 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 378886978 1250 378885728 378885757
    0xe1801110906030a02070f05160e04170a09170c010816200106030605070503150f09011502100e0322180207020103240501090f1802090a21020a080102 66
    0x1400d0b400c00e2405154020440b020041c20000c0c9501e40052105c03100108035019040324492640048110039080301600108062510034601b0759905140607501003c0c80e85035160200e400e400d1303584140340c048054501c2240000d00700e40c000c0c070070b155240c211014103804189558000345074491150200388403094580d4400c80521150b00c90056003525000c042c400303654075000c2c0480403d0007409424010000c0340d0b1000e5607890143c004094440091650078030800c81050581c02e070b079803080d8209054031350800c00c248003500c0c900c605034036240c0c6500e180c030015418402e000c41b02040100c064012041e0410390004080e0244081ca205004113010385500005140e84e201b00c6007403282e010b855440d106041c0011469a0009148042ca94a074400c01c205040d070f60052200e035a0007100e00000f03100c0d00000c00d40050030080c4101e03e040c441c01900c0c0707070281d010654602c55030b0760254441c014084001c030141003a5881448000407400f0f81c006a00400000b000040c2c41001442140c480c031030310818 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 378888228 1250 378886978 378886987
    0x206090120091c0b0705071e120e18012c0106021c120513150e03190c08191b020f011808030c1f0603021c02060409060e180111 56
    0x4002d80c000c180c565000003c040042c0e10303000240810301003030189600e501c0340c82c0c40384124544041464015284182607030017100e098400503100d260385040080b80350408040e43d07030303074400030420116000c00800d00180e03046000040e4248000031600500085800313940c1d0303066082c94000302c108400e1160b000140c1c4105480c12421101109000088034140751001c00503d01916540658809548000300c0e00d004024290401094650205c460a00010f0a020b48021050a103480e40212030044c0c1c00c0f604000008103d071403182c4d000241e00c0c4da1019006803581550540c41d1300e40aa480ca645000c02c400d444074181154209800007009640103180c8240d000400c1c0044540740702014400000f89100d40d03001c0b500080034006400c00d0000d0000400c1222580f11850150381e46a00040080f20f260000600168651000c5158485164603100452031110b10108045109503840065041e203403071004200344103120360440c050549038a01d1070800800482481c200d0f2002c50418189400410 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 378889478 1250 378888228 378888247
    0x513080703050f0d0b0a080c150903030909040803040548150a0215090705100507061805100606120c03061e03031101110f0c16060206090120 62
    0x1400d0191003072a1460505011004164041d00001c10103205651107600010480c1810b60190300101031030700c000c020072000310000c60881071401103103440c200d80c002402810340c0c8040049a852610103460143c2a240a003450801c0780c00c292822036550241c10420710045013522508403100000c2410001042c002100711000c400c400b1a5100000140c101c0250540d40e03410000e0000f64454050341c0e035500c2c80341d5002400c0c80104200707010084140014010403542c0010740c8d00c01c6da40142c50600200b8003038002a40c030340c0100c0100a00c000d0605e600d0386541d00c004c544940c00c0c18480c80031640320035205284035041d940c6601a00c8006281c3d410080910496a0440596410b80e420009246512202542c03000010450f80380c101550000b010801c243d4000c5810740600502c2c0003c10151034526001c4245100300d8003490011302000c9861100303500e0a0146074a80200e03111800503940d0380e988040c1d00c84c4e2048030148815407900303d9515a0701c5284074598014403154401519010101 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 378890728 1250 378889478 378889493
    0x9010b07020f041d0609010e1603050706110703140709140403020a030305061311090a08030a0c110f0918010f0e1c022404020a050609130906111b010507030513 70
    0x42407040440041e00320304c062501c0c10301009000c0e000c01000840c4940031074244515103061000050b03000721a0300001c0001c140003080d070f1010b8801d9072501c000c00c6ca9106001500e001c2d2250000b5181e0401d55512102408001500c24100d454070034061291200d0101e040880043c11103010f000340c2c02421003040040d1080e4000e90707200000a01b001031496040034041c00700c0700054020403081c140000c60304c003030b498100a0324004010b22401103107800c6100c4002400c40c813588400801c0b96601c2c210400c510703510500c42918510300942081078620740b800da00c003662119a032030f21005510b8074601801440050040c100d03151440320043c03440020135041e0403000c6050548907002c500030020440c1d0000d5135502400030141c2a2a040d01c0c890406004000321081103520043c4103ca0801288000341c0700c00c040c0c1e454408180500040d59001340c1061405010f4501842c0e4070104005050000d000b44100841450445d01000f001a03a50b0018250308844c000d0381e4041d0b000026120900000c0c810 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 378891978 1250 378890728 378890741
    0x20c1c020102042103051e0c0f010207060e03040305031c0f140a050105060c03070212030c070608100509041106070204090602030a2703080c0304060b10120e06010609140109032009010b07020f04 85
    0x41c7e105e503d00f4040c0404c00c0e08120740d1030940384039a50001000300a00c10742d8041e40b52550220401b640c178007807a6603200b580d2840384d182041e032034802214400200c122243d100d0482c210b48a01c041c4180720600c500300f040a4022151003d034285010004a42400c10605070340354665401d00840c07a054098080000291004c070890341148802c122100d001c0406200c60b0004110585420f07032107040100c02c41e0310044880d0000c0b4024440e280401010130304911508144c0342c01030310502c2da01c500c58000b09015001460010700b089000105208015200da400346c60030071003410310082e0b016169991059032544028000e0001201c1d500414040340903e4020350708030b445100002403603070b69031000c00c42c0c050800702568042110700b90f0406103420180114400c00d100c01c00500519070405102400e58451401260b2411740750000c101e005901409080003d1500318219a2415002e0034210002e036620240aa004501d820000200c0b0104030003a03800480c0c1c000e10000b6000da80c4021700005002 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 378893228 1250 378891978 378892027
    0x306081015170717010c05040303030b0f0306010f06021b151303150204060f020d231e0901090605120a090f02040519150e0109020c1c02010204210305 66
    0x78180c10005040340700503030400c01403400c070700504203841c98240c0a1354008011040c05420707034104814140c0c144d5019040b1800d0b2989810002001c40020b030100b05000015001c95402d0b00c00c0340c00206080034810054811901180d0840710740b01c401100400300b00460340c2040c0d401c200503071070410800d50190003034043c0007551b60300d04608607500d8647d0507059101105000c055680000c040c0800c80d486020503507281c426000611008680c0e80b4000d0188045150b00d11a01c00200c1d2102090100081110032150101c21000442141041610a5944840d5900d0301107042841c000030302d640a0f1041d5181d07104481406c120076620607038924003030100e0b050f00301c40c0c0c1190180341d01c0050b40c491060364042c0d030b00c0306c0c20302c0d0451304c804252408450403005851501168000c0420210341d0300300e616410740d4070300f05025841c2c91303402036498502803960140005034000803640003d0705605501500403114a070120801d9080d0203040021030f0004180040d001500402420004403007101081d0951003 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 378894478 1250 378893228 378893261
    0xc0d0e040e07060c0b180d0503040b070c051c180905161e0305040f0611070303050a020408030a030b03010f05010b03040606060e1302090111031c05010503070e060d030e1804050d03060810 82
    0x11043d104071b0342040321420300d0074040340e0007100340020300205a803905d51004690074260b40540d1541c581590399031401c4142907085080c41c05140003107220f685902084d0003950460720782ea41d102c000040c09410100c50418000c0005105002014072034507012407504c000107414440c800449104502030700340100255003030b8110789501d900240c0c140c85903560044034410300603103900e000e2800131b054407406040202c13040d00504c0240304400c400320482e80c1c080c24078100040c5c20040d540209015107200c4010f24030003031400000080c004207001c001c500c42c7d446807204100981d10b525043d5411400c0c9000c00750428402030387c180f80541e0f1039000700b620703090504120030450300c4400040c0c0340d580034410389140e030200300c150000000c2d464001d49026040440c0680b0404d820071010a041480080c10076103c1d81c40350f0798050506008408404170750502a20800300404480804a4136031400d50f0111080d00c601044030508504c24482c0b10240c0d0b1680d4003a00c41e0481c4401038401424600031000442c4 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 378895728 1250 378894478 378894511
    0x1f0e030703061a03010e0304051c0c06030c2a32030408010b03010b0303070303051b0307050a1e080402210708240106050403060f020c0d0e040e07060c0b 67
    0x29601000020011071240380042440c100d48285025090800c0d469076029a05000050701035200101c20b55098a03c00d0718441d1005115080c42144058510000f92120701c5040002c034042d5070607008048000020b4480d240880da9444404109200d0080002c13000150b41c0b40d94000144031291160075110745080310384880325103050503d820030307020030740d844980e0001a04000341d280078003038042210700481c020003030040558082a100d203c0c0c080001c08150b900c0e400a081c0759051b00e10030b0070050300da5207107a440c4d1038450300c043d040d03500000c042e0001c101c0e11200046014514100b140c201a045d90340c00e16207444950a05c4544d4000c01003c0c1901645c100c0c440c0d04941e0204a07410007000c58800406100441041d192048441c00410302c03070900441005010b0341e1f410504441c1140c3c0d101000241c1418440c481381c0c000d0007407400c140c255000790b0340da400500313601400301200702c101141d04000880400010f0350369022188944008582e0380c0e42c0c02c4001c1030640b80484c0e407040001510401c01e = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 378896978 1250 378895728 378895757
    0x8180714040b1e10030207110607032a030305010f1203080405071e0e0a020c0601120f02040504061509050601120b0a0806071e080601140903010f0f020414040b1f 71
    0xc3c5240304107040d102d260b8452880a146004180303081003440c00c0c1011481c041094562920341c1d10001149400380c0b0740040d14000701841106417200038038003030600100b0600310740001c401112100000750300103810130001080b0303418170404400441d80c60080d1a540c1d0301982e0b43c1a149004005c006076924018104001492500712600c90300610040491960650400100d1400f084014000341072540c81131100c440b0804d00010700c9030640d070585060b103041c4600c91500b0400300b0280310000750840e040c0000e0004128517604401f90301d840300362850741e0301c80e03c8040c001c01f19074044601c540041c80200070300c08008041d5200d64041c03200500b09405141e101c03a42c06142840940d6041c000421791403400c80a0300301c09469003080c0545190107100303402c21304002401c01c111034844107082c031000900740f0703981d517400d51048002d40b6410380140450510038158900075041489005281c3c4040344c1c4100403483d0a02c28005103110040002d06e164841c1420314001d2801d040310042400302018100e6034 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 378898228 1250 378896978 378896989
    0x3050406060e07050d150501020606060c0a170a031b050f090d060204151d2202090a1e0b030f04060c0212030c0d0b0303090a1520070608180714040b 65
    0x201d0301544d140c2664983c0100480000c564560b5620060780c0340c00c50041c8070984e408039100d82c000900725002d0341c03500401c030f1050381883c1305034600801c0103000c44845101005070070060610314250362401c0081003100c0c102101950040c0326404001241080070401045144d0060b002c8008007030b080c502c410819030b031120102d074030541106200034408100800d806034401b41c0502440c0b45800d85108a00c89000410b4151003504800c0e0080c02e80004041d07400708040c1e041c0c03048d07204009c1140c40c440b81e9072620001c9402e406102c003100790501000103d0010040c1c0f04580c0641c00002d609450b43e40c55031600c2d0004d103c49003410046024068448044070400400396006030f84144400350303a01d41d2001c0d40c400300c402068055009410074812054644d503810038070000c58a0740182c00c1d10081d28204100d030005d0300120074050001004400c0e03400b00300005124404d555003510361390107980302c0b45c182501c07140c44a20010380d82d0340040c01c140501c2100c200d810100703150241c004100040054000f1b42c = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 378899478 1250 378898228 378898231
    0x3070c0308030105090c1e0d091b18060e0a0e03120109020d0c030606360609030605010b040f1401031103130201020c09150f06040b04080709050705090a030303050406060e 75
    0x290035407804030060007240307010341d5031a410681052100f46040d200c2c0400c80603a441d4180340d0262100086840c14641440c0c1c2c00903814958043c0c01d0084e030407006184e1605034851030086a4014803580c0421040012038450001510324407031091600e91303501c20049001e0b00701800075420b980400d010303901940170340b440414044c1010740300145c0c54408004805086030740c0b0440003000c050904204104c020b40100644100703a81550b940340c000002150014041c0403400315090590410860000d40684e22242080075a445500140016681d814200d456809180a1242c0b504803285041081504c0c24214101302c04040c14046a944c3c1c04000064958004031026140040b05050705401c660b814881c001010108841c0c64490341000c4154140f022005028907004568007044045c80f9990a01501d000b0151203000030b070740c0c94595462940f03a50b128415410b0403400c2002240c0c81ca402a025a8036002d40a424001c03000d286480490241c100500241d5145507203244c0440e90814903222603 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 378900728 1250 378899478 378899483
    0x150f06060908010f020304030e12010b031b0406050a050f10030b090c0a0807030c120b030a12020106030209010e061008280c020c010c050c040c022505013e03070c03 72
    0xc000c0350300e842c05050940c0e000400d90310505204204000000c1d8000c0807101e071040c016104c507401c0c82201e8107443c0c01001d18054542c2c0c144980d00500f400007500c0a210842c0100645040c0039460340d5000744412000b040c003501e944040701c0d2880140d9410302502182154046150204c0d01140520106000c100251040003c89400240000c6002e0300180200d4100f02c4500d400c202805142c1c8000b424140300302074460029031a0704046101d6581045109481c1d0b802648a0050324104c80b006070007064140301c101c0c02098900000100504001d620701e00c0341601901ea035088110b41c22085400040050900e1501c0c06d4040019292001404a4681c43c8090003800a01c85189010291404102685050400035444401d80001d007011501d00c54440066402090011400d034050741040240501140052444121150241e0740440380310308444003a20341440361045002501c0309075032500200c0c0c10640b400300e80204540c0040c3c4a0b070208400300c02c2907904000a56031130880c024600e601c00d = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 378901978 1250 378900728 378900737
    0x2031005040503032d06100201060902040b0d05010f080a02190305030c150105030f150402010504031e17070b070f1103070b1503030a020a060c0504121a0609090a150f0606 75
    0x4015403811210800443e441c14980e48400540350170802203100000140440d000c0e204460140500c0c83c003d401510144c241d0340000c0d516141ca07041c01c2c522a03004014094400f50a10000080c800d6244428106403845040503011104594080c0440001403203403040080041d110b0001c0410710901c09070118a0041020b402042039510030407140700b0040e00000c0c8032f138202452071a8540000100f40c0790f605281034111001c2e0303540f400180c0c2c0380d000715030014100210145082000021011403032036841c2c1700d1109500001035200c11000140103000000344800d01035404a00f0940c000c04e43d40b850302d644c034030b4921000910140c8460031764000f0f50f4102c80c0103c00409100140740103829a0a4104060303005605004184d24020f68072100307000090502590380d039118007420b20820854010708440408403918071081d02d41194038540c081441445036100340003181e502e00e800b6185c0c5015190315070007403e168425445640345040c0202089201941d2801040392008a50080000030221030b2078 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 378903228 1250 378901978 378901981
    0x50c0a06021e03340e0103050a02090904140601080a0f1b180608150702030a1b05160503150c0315030a0f05060412050a090b09030f0a060b0a050a0e0c070203100504050303 75
    0x366010a144c0410185080030500041556540c3d00050011251000340380228042c0c562a81c0d140003803043d08209038000480800700070611401000d407a001600075402c548c00c585e41c41542c26151400e0050050034101448014004038940490504010b0a030b45000809160344251140d580007400f59060034403038a8140c1001344160a1202281c520a4070391620091f00c2e001c08000d44910403005e981c014410341c00040000ba03401810220f08240c2d1050855054540100301642c00d03030681e10440f44203101390880b40400010f480d21013402518034003080d03429502c9140703035a52211100f80b465031300b511502c0c04400100d520140c9001440d0b0250011340040d0a10381481c0d09241c848010040a10004008281705903a20000c3c034821101a00d0100391a0740b2a500083c1c01e200d403c05c4c007104a841400d04903001e100040c0c2c046411b1007030440e44004251381d61030510010408a2141c20314100010001507a400c102d00f0007003000c80e02c001c0c20b42e444801d09801c2d45040354015101560b1689c400710 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 378904478 1250 378903228 378903271
    0x507050f1005100b04080d20060106081008010b220f02131703031603090c0803070c0504060f061b020d0c030308150d0b071101021324050c0a06021e03 66
    0x1055600500104d0746064a824242104c0340d5445260031010402c0084041075451000c3c5024601c1901083c004c080d607415507074400300100b00c1e00c002d580c0603c40c000c50610000e1540d01c1486120f02c1e0501c0074012035030300769822601c0c0203280784102441c008191100c0910300c9450792880100340382d2440c0400c009000b814407400c000c08611041000142c0d030310410078016810300c034641c4211102c8451401164085c11840c00814020036035010444c503100100760a410040c0520314082556000d841c10840182c1c1c541c8076003044026803103601c0c0400c24030100d1218240071a00c004505900107850140020401e5407121102404c079841580028401410f20003070f05407140f05556100401c80b0b0b501000360ba075466541703400c10701400440620001c040c000400750350a40640f040c800b800c014610141d0f03940da00500c031f20320780780b03081c4081c140d066204010131030b0252060769043c0110000510764140340340e50705402540010340040c50b000380c5400b00d604d181c20340d00003107221382c2b6a69682d815102905 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 378905728 1250 378904478 378904501
    0x1807180801230703050105090115020a0f0809040b060301050a03030311070c030b0906420909150606030108061f05040207080a0e0906060a03150515040305060906010e04030507050f1005 81
    0x180600f01090300f0000100301c00c0e42c990ba4901e0540e15080080544001c03808406d900e047c001520051000120705605000d00184070058842000151024490915010b08101e5944024001c2e6a4840103841c002e1020a01c01c0e840210400c05011010386045070035126a40c6149550f030084070009582010400340790b1061080355044001d4140b100420000001d00810541002c604105443d048000120548020b60100c02d07004401500c90710341420f0081d50140c580c1950100303400900302040102c1d0460030a031040768102d0320a800038007619110701c882ca440c04060b03011481d440c07041d10140892032382c1e00d610040504d40d1092808035980c24035000064140b0500c50326041c410701c2030742c0c104010b544a8100311451040c01e0700c0c0c00507001e03803c1e181d040c0702e012142d0070031034101d068000c00c1000c0d074000500500c182c9000da01100c01d40d96810400a81d1080d007400385142d540d101d0404a0002070061018180591141c0250b0f84a0500400150724001c5425038a03101030b51510180120003070007 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 378906978 1250 378905728 378905731
    0x180f0c03050603192a180e030910031805031902030c0a020f15031005090a360c030605011d010807030b06120f0619060506040509040203070e09100b180718080123 71
    0x28201c1480b13038580c20f00e441070b224050184800c0c0104041c0010841c0682f081c3d004c600c94504940001440107410f086c4955aa0090740c541c400103081e45d010703490401c0c0004103a8040c89038040090500440d01c0d428898a030000c1c07110b07190007002c090092a101404503001d10f116807039070000c01240900e00300c1080000d040103010708030b915190201c1000c1500c103102000d00c1d00200c505c45800701180c1180302c0100900d40e910302038000020000040204145500801d0403100125444c4090a44943d00004018401e1040703072445e6102d81c0040002035084400e81780d0040707005000b01a40c4424429072828910180c225040c550402c1c1d007000250b10b1400700c000351068548004002aa0410303010174580d01c61400b41c60312981e010f4000808541d010011580a080034417403140c030710f05212280640d00c42d203166407468041e041ca680c1d103c20342004200340220300002c074141c0b2880d84603180c0c1070b24040700400201000d4618003002043d0140c2c00d00444443e00d0b6204c9401d040c00e0752440070141c25a20 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 378908228 1250 378906978 378907019
    0xf0406050606030421020709020d0b09060405090a061109060307170702061012170705030d0608030f0405090411030d0f02070803091018180f0c03050603192a 69
    0x2e0034414000440c8004201040c1c81ca61030303186505421030160141c1c601019640302601e214000500d04084480a0300840a650b1040d075002d08261078201c104400d54031304546981c8290300500040b8041019600141030140f039000d851840c2490b0140400d115510440303040300072035081003921010a101601c59a070050651002c0c05260401410006217150584030340e000707c0b030305c140b141ea00b48401c001128401c5a0083c090f9a40c802103460b0054503a046601105031082c503040001940307c0020085400500c5003540280ca0a41054200508414060405c1e1003c1c0800c100410345600d0402021884032125201c50f50700860382c2c18024a4044c0d20740001c1c0c910340040c0071400707985e00c0d00c050b00c00f02444a800d0003201c520000409102258083d0702822100c2c0e05561030402c00001d9a00a01b102c0502c00024031403084031610a0b002c1d0b0b07005403111601a070269941d07001d100b0704800d4804140780b040390307513150b44004210312290000c960090040101e15a905c200801c6000e8082e0903403105 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 378909478 1250 378908228 378908239
    0x609050f1f06111005100602061f210f0506091213030201050f0c061914090a0b0a1e0507020d08040f02040203040812090a050706030b0916030605090f04060506 70
    0x1405004080c8a000502c240c205000310b84003410403180040c0030340703e52944802c90802036454101124a0384031858803854001d40201e0010030141d04245650b507007244203018800c0c007160315192041c844a40f0300382904002c107a80c42003110020303041c0e0385a440e849000d00004c20003810300e809510b0401801560311000d81c0300c200090a074061841d402102240d80900f0a50340b0340610542e2686079110b11080e00c841409100e04001e16640039092031481c422241d01c0030403100e4a0240d540c0100001980c6201041c2d0056210000281d205400c1e02c0c0d00038600c10300440d001000808030400000692500c0342415101c40410807101c0e8100141306d034045051600703c40720700302030301c50001c00b0b08201e601074080c2d81c0010006045c0f0480200b114001c224042c2c461005140c044500c82e111250241d08450758018901d0002e00c481c464010a00002e60042655a05840d10b02d0742d074043c0c045200e0090305044c1c4410300014160765850101e40310b0a40d0b001d80ea0004e24140ca400002c030388000786243d1107403 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 378910728 1250 378909478 378909511
    0x1b02011401120f112e1e1b0206091c1b031722080f0f010516030207021c0f0c0501050f031501090f06020f0f0118240609050f 55
    0x20461203690f0340322034001004007003c007040c001041603110000408000d2218040d4091030300142000b003c000f03a24941e4400c000c03406550b0305040c00450800f10304001402c034014503c4000d04410644aa10b84002d0070359107488680b03408078003161f20102c08100c4204204005c107040c04040754100501c0d40c0c1080c07500c4403140c2103a4a440c810004030704507520992010995187c9180d031560213055030003921400a4501d81c1c0c03102d085542d140c2c5d00c0154000c43c000c00451040030301050003080e020342600c890785150440203248c118000d4014140076603004043e0124061504084540054900d0280c1d400b60540300c0d0b242085140e1700966401385040100801064600030440025240c12481d19030261108108003001203490000c0d41d00202540342000710002403494000420880c11085070742580c4100300d0860100e400c98000c180b05035001c243c2554818001509022010307201500420a04a0381e00c0a4500d18100c0b4400d0b009500019a90824060500100340086a00c28015420700191 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 378911978 1250 378910728 378910733
    0x15150901091e060513050418020102010e0d020c13021b031306050307020303061512070305070e03150403080c04080d090302011d130203060109050d11040507080c04060e041b0201140112 81
    0x840010b0710a9801304080030034482c2e03400d00342003450710041000500c148591040158000320140c05003008a01641c039003900400a00d8022270021001d0b1441c4d00a011014100700034801c1251490304214405682040601041c100110415111f42e028600450302c81c0f5441400c2603050582c0d4021805001c000d20801034002e81c0081280d90100042d1031001030404280c0c0003803018040d00740300d1814000e6142c10403c040e0ba144d03015130b00c200c2c0e55980c0c040b1940c0b103e0042c543c1360000f80000140c850b19400000e40428080d0501e982c000b1022070700c82e444e0079035450409091543d00003000f00003402010f000c00c10356a104000585422020329003161340000d180008035060f40000b0070805158010000501d05ea0140940700c0007031034060070010001543d171034a003100d82c624103169807003186000041100c841c0300e500725070f10420548505038503080c107010003030b41c5108030300000c640d02903120300b14809201640022030245128640000c0380031072034245949181e000580120503410400c20750b6502 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 378913228 1250 378911978 378912029
    0x2031c17010308030a2d05070306090209010914180f0105031b030309040902010302090a0b07050d0c080f0d06030f0b071d0a0b0d0f06030f0311010b060405091515090109 74
    0xc10403140340740010341100340c0320380d1a42c44810744a00f00711450401181400c1200581082e48101e08d5954100103031074640b10400128040d90305024001002070701c0a2120780000110218844002842e000d840020503501002806003120b4100d0004d010350700401403410100a801d00301d56910f0110540700e848100442d0342c81c0500345200f8822900d841c004015a4040d5040f5052404050300c0c032668551501c8220105a0003801c0445180c4115107141c8240d6100c0c1f13600c41d042550140c0110310b4a14084c031038040d60380003603451135003895071504004001041910241c01503031150640302c00310b01c0c0c0315a01607c1c002c0403201c0fa40d80e1458082c03c91805940d03a0740d1000c2990b19004c0e15580320813510071090024540343d50f03a207a0b100c0c600480802801036850070b80250342e20907076582039901010300f01d030340c02d89100503159500800c00f480107000c60702d0030481183d8804440480411282c1c00b800c00038162880c0300203041740200f8001580401542d000520001030000d8414500800039510240d61 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 378914478 1250 378913228 378913231
    0xa02100f140c070204060f12170a080711010216142a041509050c070c0f12110103090f110a05240c030c030703081e090a03050c030702031c1701030803 66
    0xc1e03101e08000f074900215500c9034800d2002d05055503481c62459141c580180103400c3c82042074440d1202d101c0c1c080005401d07074003142e4510901e651202110f0300e0740c000590721400d0220f4100c49a54007400a2150318444002d01c0c02d606024410482001c440035002c142084640c1041c03040b0040d107030741c1410310042018080150b180050758002980f07682c0480c4203580810681060014030f00703100900003618a25809400c00740e02072400040459500d00d440d80d480107540c402e5030841002c070304010000c642400346604884034181000f143c0f514140d51a0103820f01c170070008441c51202c0c02c12411090920307803984805094182c2c0c50f284100e15044c1d50100c0190014288410110000b400d81a00041801036545074080c0c401100c4d154000303803034098012038040710031040381d820345070100c410803001020711805440b1200203003041200d03644080340c3d26484280740c0120b40c0310070011140141c40402c48003006012030310000c0d003003034001130000700000d11455451404003603150041c00401c100a0071607 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 378915728 1250 378914478 378914491
    0x6030a0b0121050f0703060c081b0d0212040c15030e10020306040e0f01050403030c0f0509010311041a040f0504050906010e090703080705060a050106090f0b1b030a02100f14 76
    0x1000416845915425a074882000090150181c4d060309030a4800000e152800d903807046409000f0480400411180503904503418030300a54078000b41207944800200828400ea80000003502d048494843c40c00414410f8034100c07502034a100007080b4503002d00808084440321894107020500e21054120740d55138a10451941d05607001002c61100d03a19684680b110902c0401626a5002030502550081c03000311800d4010a05080d207044078944274818060045016440d01403c081d00b0b2801100201141184649118020040490000d034134440e199008103c000e40d10390344908040300540f5503802a84894001e13030604041c010fa001000c10011705496800b01d280f0000e0307580c186100e1405485a10103440ca140001e210400d001010a0851188030460024026030740e0324001154040c4103842180c0c401528141e0500480d01a08020b01200060100d82c41e02e1904129000303042da0b05c0400c0708405a40040100344c0821100d0040d0058544140000c0242c503820044c80074425500900305c = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 378916978 1250 378915728 378915749
    0x70906061d0405090a032114090c03150c070c0504020c0a06060f03080405090a0f09120e010c050d050a05071a06100e0607020402031e0a0c110a08091903060c0302090906030a0b01 78
    0x107280c01403414002c4031040d1810340c9040c00403801c80104030751848c0040e1621303103090241103c003100c0e038200050f289060445804031203055681c0c01c0c08010694001c09800c641001e465100014650380740e0000c0c00c00c40181c0c03c060020b0360141d28201048805951040c1e81211030700e801000400c00700000d44044400c10758020015981d410300c490700809203c80300402282c03500c00c1030780c14040002c444450000954840300d045181400054648580840e802000f603404185480c110b00d228001800c22140c0600700942464ac1e01e903260441040c28410b04000303180103000700095858408031313030407a501d06030500700b004088140100f20340d07225005001c1d0095400001007941c2c500c0340ea42003211900982400c00140c106000034001a045019902c03001440045680e21a0f82c0007085005103c0d80c84602c09103031210321400e000315149001059829800350740c1c03001022615038054002c0151550350010303510b40807a810070480c0c00010345428025403100a41038000b69044901c00c0c19904500362 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 378918228 1250 378916978 378916997
    0x10c0503040f0f05041127030c06162d0f082106040b010f0926070e010801110a0c110f0303040909140c0108040f0203070906061d0405090a03 62
    0x2042491846107a00074450320051000002c2c032000710382d05503019604100d4003801084d1800021460034002c7d12861503040403075170189003a81303101c24050707800d04001a0a95445009100018142d40c01c084c4c00702c10b40741185e410784000c10003244011040071074404541c040142819250844030075105000902000001c03085005026105083d512070b00d0254060107814041400481c040b004150b6403940251f040181e0a261503014006400740b881040d80c0f40d410740b918025a00c00311090284405c1680080e4112a10a851051052801400c1e06080c807800d03551600340c81c030742198100c14520149500500a07c0300c2c0641c00301c4c00614154014001898403442c0200148141d4150f404c00d6078144000100012944010342103142c8a0b07000e030323000c0d101c1010303a6210241c5800350360707031198001410000001d000484d09001c3c116240d001504881d03140ea01d85440b4811a2100e400240c0801c0e0707041240d4659801180303000a034040141c03001d102d1800c006050030b955107813400004051050104 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 378919478 1250 378918228 378918233
    0x70b03070905090103030e03060108030f0904020f04080f1c0f050a0f030f06081b06040308070807030219060921050409020c0c1f12060501080613020c0a0302060a06060e030c010c 78
    0x640d10002d094000c1c02007480756580d04d00941031410448005019018101c00000e4420010003a2500c0100400b031032031400701c48c0c2e01000020741c40000f0341d0811301c90920010034040401c08ca195500b03541f1000401000e503020528040e4619019540d80030040e55031071032131010b50f1042c180c0e50500103c1c24203030428032420038240d01501e4051103010300c9c149001c03400905e040300001c644803c4245001402070541049060140a1086001c0500160b41c208100ba001500001c02018560701920590b502c00d401a10900048040038405440e211307110703a8a007040c00003001c990b150102007886540644140b031440500319005510841c40002d5001c507101048000501c1600380000f001014494040389200f0644418045000764000207800c400d040d20310750301c0340e00c6281e041d00d0058444031003c2e40d521007000710320030726200c02c064415000d010200d0b0034542003050040d0036129030041d000c41d1800c5130441c01110003680c400000c21103a2030040380e1540380441c890304011400e1070500c0c200381260 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 378920728 1250 378919478 378919487
    0x60d060b01030e0f250b2b0e06010302011101020c07052205010815060105040f0b0f0c030a0f021c081b1e0702031b0102031204060f06060206060a0602010509070b0307 73
    0x20315102e08074040c0300542e24130007402003011a692001d0040d040c12082e513203240e404a000301c40c001e07106040070802c11400c1966948680041002c9070030030043c44500090b151100365403407490300b401035a0103400144115a00703e9900e02e00c80260380b0086050000807000b0f141e4550003441124001e14001d82140c5014401e80304100310311a5410b030600c01c0303582d40d0b141030b9030320803007100d082c0c00082100012032074030361050040718122001c0e20a15034006003400c0d54016a640041c1040a41581c00c00003802c2024060015110303469413030301c608500611200010742013501c0c8070344100c2e46160b54800f811400d50030031303d05030f008041c0c80403008284e00c5542c2c82c3c0d6601e1207801c95541c2c80d141844c0400650310440c030020404648280c0941d40c1007844842c210801c2107000420a0142e0401d020185141e042c411000354050b02400300454032030042c0c0c140310b00712036240e000140140c01083c2040f03d142040d1403213070f0040c1750f1403008000c10300c1c0c031074406501d80400b0701803080c1082002000c549854442e = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 378921978 1250 378920728 378920741
    0xe010f0c061d0a03080a0507210f060906150201060b21060402092112030f0105010c0f12050a0e0307030203210d0612020102011d07062001020d060806010905060d060b0103 75
    0x100049903030f00d000604010f080603404030f60100c585810a00050b6200b44a001d901c03020400ca0401381044080c515030f00e1001d0100843e01c0802d1741e94920000540f0300c0c19008001c0185601000c65481c0c8240d800000d0039180b45411a030601001080000e0300c0200e658a020148000c005801e04c0c55215500000c010307100303456070240e01200320204211640d48500d9081030b58417030401140c0300039040d48034010680c0012a0380c6040d258000b0010442075014517804a651803045001840111803581c0310513044400c8103542c00090000704004205075080028078180d600210014035140303256600107551402c00c210b408000c08501819241d440b0701820907214003400c0c4103000d002c625101c0c3d0a00c007144084500507801582000385083d100000c10696030304001c04074024103082400c140d020b079503140600c1c0c0040003860300c41041c0303c4642400c2c800303002450580c610200c1c0c010300d80300138603160500c18ac0100031490300c2d02c4188083c507500c14200d4080c007030340032001068410030200160000c00f42d = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 378923228 1250 378921978 378922031
    0xa051303080f1308010b090412170703020901020709060b03060d0f0b0901052403071a040b190e180712090f050109031d03030d020711150403030e010f0c06 68
    0x102003000c025541d00d82d00503003d141002a820f884003a5218102400d079a03d1403840d0b41c1085151000c50041080d00c08200c04001c0503060941d0110110000c12420304c60031149840025408a881c030450340c0c0c1030081e0340c0200241c20381440348a00b4007104c3c01079803102600a40c8514180c10a4604002c42a4100d052154000d070410380c2c42c0c9410102c0901a02045600030f01c581710320902c0303081c107055a000300c20b00044041d000785081410040d203034201000c0d400c1075401e035407030511001800140c0c03000100041d40d01c01c2600007040c58441d001600c130b00035111b1070f10301c0b80d14174800e805251607803030401c107600120a02c1c0c4645401c5404010100034220a00064940c4440c0b420301e03407c1c040c0c15040072449038400e0741e649500d100e9038454954440030070100300354140c100300041e142ca80358a4001e004454010424004008924000a500b5207410490040b0785007000c10108203242d041400c0e505204070a00b441c801c3e005016000424007403021000501582e0f4501d000032002003800d985840a01 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 378924478 1250 378923228 378923243
    0x2010801090b270a112503020f010c0c0c0b0f1603050d1b0e0906130b0a1715010b04050f10140d140a0903020a080315130e010b0103110a051303 63
    0x30040043c42d443c0382c0201c450803141c03410010a05480075840003103440c82291050540032107881d0502e140003180011005800318443c2c0e81100c026068207210f2303101a180b40d500c1343c040d013954918050a400c4600d03401050340d0348050106000d41c0a44608032500101410710350032080500c0e01d815203040c021090160f00442ca070000c0000d20081c4c403202d103810030400c2d4890100350b0a0201c100551000201c806c103030024120340c3c4c00c0802004580101000c1d0034014420b00c0510303103501040380b00180c600da41c6409a40021100003510503441c164601610310411034624290601010501100c20b040c5000d00550705001c0102c5aa07200308aa1400d4814902800341e079001008a5003002d03144050500081820440200d08209410702c2079003c1194142c0141c940031240783c03103010041c3c10051601900c001d12043c1d0440c10750326442a060740c1404c15000150f0000122211421030b1460484541458641001c0514458500c800d41e40424003a280c903668490120b801144503400b02c4c2d10062180 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 378925728 1250 378924478 378924529
    0x1201031416060809190c140f040c030b090702010501030b0c0318070b0d0f020313060905161d060906280503160801180809040c17040b0402041802010801090b 69
    0x1503921200140c02080c40008540a0b61481d041c01c0801c03109445c1c00500a24828404220000440e01100f100d100010710030340301000c1c0607011030281c540c020140c0c000240c0c0c1b030070694524a080540e1a4000d686440204995811a501c600011501034010f0f16183c10100009802181607540f801800c400c80086d5842c540ea01d0301c2e01c1d8201d40140903483e02850820030b0b600019080ca20a4910854188812003103e50300da840d03042c001c28008505449501400701c1010003c40381d4404034006107580c2c59844150700c0000620711598801800342c0f07104441c1c510610140340c2c0c42c9401ea40c1c060407003050304068595880d0300d8581442c842c0d40100d030180501c065450319241e01410540403141c021000780708551921480217048052540001c200120500c40030b40c450405030b1100c0310950b19803d10b68000301d802c0c0e0f107140d10300b001200c044a111411400300001c5007424052a001c1c0e10b04004030f10039500d01c0741d00103446042c0c1405080e8a6039540d816101c0a956407050383c200710761101101c103058 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 378926978 1250 378925728 378925739
    0x1e090307211106160b0f18030306120319080105190501020c091f030326060603010b0904090602040b030901201c06050603010608070905010f0f080403020c0618040609021201031416 79
    0x15541214002d200d035140d01b0010304d00140d5496104c108080e014051455561100204404d0b100314410700000c0d0303c4144944140000c4010485402c0215511400f01c00e42c9008200450101d800700d0b40c803040e03041d048003081030ba41c00080c280740c0b00508595450f46551040d0081c0030b2014124515155a00d54a2000042c141c05c190102c0da44581c02001144101c114445010190300a403070392900310100704010000400743d10064801c1e003000030301c0450410f81d15211482070340c009410a5890840010600008100c00d110b800d4103c40c90361501d410742c00f225103e018030750040d420103420004d8184020030100400c0d84c4048040c00005044549a584469004010034011244c0d54041941c41c0d83c08501c03580640c08420100c88250398510311a2040e0358102c41c01c80c0081e20441c198441c00810b410b050365108003400031041d886050503800c610b02001c00c000d94055920081c0344502c1000071403040044882e0090640b0781028225014036040030005250440704200c514a0703224002d404030300c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 378928228 1250 378926978 378926993
    0x1a01081905070507050609060f1b07060204062604121103090307120c08150106030e0c0306090c13050f060d0c150306060e010e031f021e09030721110616 67
    0x4c207203000e14101e5020380c0c1c48100041c0e90701c0f4140c0300000d00341d62070000035042c080c00c0300c480612402211401403c01c0c515995071000da801c5a0011300100d1503a651407640308580c0301c01031244418592880080f0300f46921000c490b0000404900c082001040d5240181c850030002c83e407613402c01034221001503035030300c08071481449111030440744041c40000019003610300082c1400040944641c00080f64605507040e0000d00440e509a580ca000703a80300b0080903a018802184035090003009424100503030010856007440400780b04c100a4507060601010784400040c50341e11000c207070b44100740d112080c1004400c03840160b010480000c140800c42801d10740c503800c44030403a001511340718501500180155917080240342040e81682c04074101e040314680d8003003103080404680100500d88002d540341c2c001020121802200400d0002034400a07604080008400508401500d8441d0019183e0030341d0807129400c0c0081c1c406ea044144502c070031303a207400c225280020b22280418500070903140030f5a = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 378929478 1250 378928228 378928237
    0xb03071d0a0b03060403020606010c0303090b07170703021204110a0506031806011406090f24190201020c03040e0703060e0a0902010f0f020a061503061d060603011a010819050705 78
    0x7101da003000c2e240c80c03903400e00240c014001e1340d03d0740203032042e0b554a00c011116681c0403541030302056181c5a240340820582c1049034094580365560000580c21100e41c0c40100d040070b0404070415204000b07011344400c40103807841d0003641c040103411800c0c000c0000580700d90b04941285c1d500c410b001052110504200b0b03020040807000806603034680e039039038040e1025111200150342d0024010400c25501c1e1070310301268050100020201d4400806078a03403990700c14414259865001400501440c60f6450001000c08000381480298136203d1440190350b220700807482241c10008006001c580351500a421101c05410060b0121140d4900352001e14050b005020090340498680c200101049204410303036000c01c000340d00180551089a03031003800070141070b1414520285014004000504c2c180591515103420701d40490145200c14241d5040c000081c010703510036071502c504140b580d03011141c0c082c0c6025007401c2c07100656550725002c071080e0b100c00c076544a0304c6290a08121034250810050f0 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 378930728 1250 378929478 378929491
    0x190521060c03160c081b15070c020f2b0602040b030a0f050708060105090d020a05060d0e070b041d06130e030a0e012a0f0b010320030a11040b03071d 65
    0x290218802048140e802200303052002e410303144204000c0f1002031015900600145080e01103034810807005010a0744418123445840001c0d44d03107010f01c415494404000ca0842d401101c0211648076900c4280408980e02d41c000c80824904900b09404e100a0f42e0551b0b0003040045051a6a807a0100140f0010080c030610009454944000302c1d01c514445d41074903208203c180c461500c0c00f8081d8013004840914414120ba000d5242c400c007054a480704c40c0a0041d0440d40ca80101d4a5207150901c075040c16800e40000b14000340c240801c003c01d6801c0c014819041030300400140180e00d421021a150546004058030260706203194009011070000050029124598580340c40000310001110112040040051001e40210004180b27100036181c1e2000503100303200b2136000d81c641da903c1c40b600344003da1055405016210349600d880781d81c07501c958203079030048028100c1c4968030f40e02c07000100c0085400c14016540c554080f030b41c0d500e041015002503e050404808081140d07100c4d08403100c000c0311030 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 378931978 1250 378930728 378930751
    0x30706240b181219140f0d1205060f06070f030806030c0a09020a09031704060207171504050c03010609061503091a060a0b070f060b190521060c03 64
    0x3603030741c2880d0251441d402580b805000384480c1d07101000052140c00c80d118600d0701a9400c1c0c0819001102580d02229100304d134000700c1c02d0300c0c0715202400c10503043c4200210f50000d41c0b1400302a54000c09480c03401149140000d084c1d100d8501050500e050244540e8001c20005409410700c5600e0a16007602482996031443c0c665511003410744a0308091415504010482424804007070300d9000b9110200d55440c00d440e0f0305a894661070408040c0c0e544160541800103030900c000c036810302503000a170200416500000044116180c3d80788580c400646480200700082070421000b80017511032208010000e0144a403210344400041c41c04e13100b032004240c0e0245031511550300900810060942050700840e400000c81c3c8078022100b4024482e50b03010350012008a10043d145004d4080b403800303450303840c0d160917075450201c080b5220b02d01102d101e0718011020494a003001500003055400a40e88443c080203896826a100003940c00e1062840c0900f1041200300c1442d500910301c078007640000c = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 378933228 1250 378931978 378932051
    0xe04081306080a0b10120e033009010207020a0311040609020a110106080f060127020a1223060d061401080a0210111005180d081801020f0912030706 65
    0xc00290081c202401800305a40344c020f0101c900e07043d488981d1075000e51f0709480c90a0350091040f03801c00b50b05200344081188a2140c1030504a14100f113036400410ba8000310724114058001501900081c40010002c001d820862040c54465801860007031020f14800d40d21506107141c0540050744040c00001a0361810744001240540080c42070451104200501078036400e0031990340200000c1c0c018180ca050780d10f0184035405a180c030003402410781d59074804004145012007503041d80c10440c10f00311004480b0150851243e2202c3c00190400c2d003c4649a00c10314940c602400a01000c0a06101481c00500000382d90b03d40880c164044501c2201c2078001001a1042900c8c00d841c1c25084034425488011080b29501c07550703106c55004031140c20403801b82e010740d262541c40c02d407603407181701c1c0020020f4044c04070440001641d0000c40300100d0081d8240312060044000c2401030030358407032107445144195407215400340f0881e0007003034000b441881410711203003080d203c0b865104000c1410796807044 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 378934478 1250 378933228 378933251
    0x406030b060f012303090f0d02030a08090f0d05130506030c0415180e060a0315060f12020306040b1305190b0a050105010c0b040303150806010503120307090e04081306080a 75
    0x341c0e50240503c440f55400004e000b10070800d0550b0700001c100d850079101c3d007090702014000412249602005aa00840c2d803118045001094450b000e80400c4080c2e000c0c1d041b001207000d011074005101481c4d4038203203884800640429101310002da0101d07030403c10020921000c01544c1d4018016206411501c0d0100e41404c182183c0384803041101c403809006040d400c0c0000b60407c03140c0c58001c80000c120a4146d030712030300d0b561404813542d41030210042c0d032100e08000600d00c00311004001c0c051482028110348030382d001310741c8840c0000d0000300340700645000290321540c1400501c010303a030040200e441d20301426842c0328030f2010300300c4184c490100800029490000318003c0c0c605856040e07544942c010504d40d1280f04501010380201c0902d030b2508000c590080305000100d0081c1078903002046954540030030306061464580302c0d07400c104003c03c20485101d801441600441c0c154500d0300ca43c5507100d042c000180e000e40b0a042903a02022800000d0841d0311010441c0902e050882c208662501e50 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 378935728 1250 378934478 378934487
    0x10f080406180f1101080c04031101140a1d06030108030f030a021306020303010815060d060b010e130603020108060916050f070215041805040507150504081912030501060c08090409020406030b060f01 87
    0x21547c980c0d59120030402440092896003003c1d40440042c148401c83d005020345140080e003019155000103401001c7e4034046130344800c04c2c00320244003a101c1c2c51442d41845600c546070b10440b034401c0c01084000010404000d900d81c1110344003420324030414807803a01d54200a403281d10078071403600c071842200c40c00e0b654603e1048031039001c3c41d80100000707402c0c5565650540901000c0400e107061000a4048480e42c1d1184040c0143c41c00740713801c0002c1c130581035100150200304084c140c0760042c006201040820840e0f04580ea588000b2070903c00c0c1c454a03d00c2c8001414818104000c0d0070034031448010391344d4092074015101341e42e0902c0b0000b10210000c0350160854004860207040e66210140070041840d00205034a501d1003a032611078501038680c68403601d003580769130506200785c440900c10310600071a40d012600e1140d00d40780c1800f15525101c00104180504000038141042c0002c40329080c3d0b98aa21628000d80e0141041c08005c0d6241041c10070300100702d60f03650040c40654940403ca6106 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 378936978 1250 378935728 378935731
    0x501050a0c050316080d060b03130230070f060528090504050c0a02011113150c150b0a08071d04060204050603181b010f080406180f110108 61
    0x1a52650300388601403204440382034010301c0590b0b29000820607807040b0100c20005416103401004010f603030f01c1c14610600201c900740e902031090300c0d1041c418401e18501307024004502940448000c0c054000008002c004180c2c5c080b6030681f038440e1035000c507107000c001089143c201c44890b044100a02d0303030b81d1800d8410f840b4100c00c81000b100100702000000b84c2c140c4a0a4020110b032401d2420641c40d54046011a070054600b400300303084c0406c0c80c1031113903424010310301407942903600d0a0800001c010368110390344560240403501c0d54004400c80806114503100c1d1000c80e004402c881403464103064903002001d0300d024460088500600102d001b01e00090307440c1c101ca102140b40140c54894405070180c864010f041103a405808100c0044d0780e40d191303c0510b0103800140d2100880141c04e180c01c45c40c140d140c68105d4141040001074520507070b0000c00c1c180402000b410301d1892943c0c0c62500800800300484503001ca07a5080b038000c002d1103203072069041010310407800c602d040000300c3c005480900c5c0 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 378938228 1250 378936978 378936989
    0x60a05030d1805100507050d170406050717040317180c0402030c04030506010b0d06091e02070609052d0102090d151509020705060601081902070318090603031206 71
    0xc40180c1d2001c032846034401c0c0d16000d810310780c0c44038403d40b900300041e9202010380e40d0400259000c202da4051203402d00c01c1c200050f000b41413042c1e01c001c03c2c8a0702c00e131811004101402c040d641d41c00262501d4040c01038600008840f0386004800c0c90140340c003600d03444c4460414498100100b00159058241c1212100d040c0000801082d00c107541e18201710195000800c0749540c0c0c107040c000000065401c2084074080d00c1d5611500380c41d18981c0602000b101c003154443c405031030810304140d903006026181500e1a00d06c0300401b50340e810103420544050013070101c00030001c0c440c11140003030780d09001030b00c103039a24560307070b600001c41c0f281d20304150a0b400303a412032036400200151900d00060030050b00c0240304202001c007080700300e000740b4403241c1c640480c0e11900b003207a00058100308000303090140c01e40c003c801342007612450030501c0e440030b5124080c1e000002e005900150100905010f81c035050804c46005800d812a59240c021060203030071244000c0700400d20058890388100007034051b044c145c48 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 378939478 1250 378938228 378938233
    0x1021609180203060a20090a12031e080633070201022a012d0815120f0610060507030815040207030e03060601020a0c0504020f0408060a06080105060a0503 68
    0x60900d00000014140c800c445072699907586100c5005031400d005080c401d0001e10b8002031011042d18002d400c006c2a00145000320a00700007020f066a0b408803c0d01c207803410790745150812500c0385416514180c04400c0345510408404129110343d40c402101c0d44a110181d0300407030300c1545030100a91400c036064400c011064031404902540320a0005441410f0051040340ea00000c2030107103403280c0290110181b410403c3c02420700c03480d44c02240c0082c12040602e000c0e019082da258125402d11040c0740c00701c003000041404100380d8001d1003074080204c240142006601c0440f4903409640e40180110000d490061500003041d01d4035400c414030454459854440c0b9040035550201c80c0c4590052961080301050083c4c030315a5115171001c0c051051107512580c8095121800301458001c2c010206c5045602c03042522000408130000038044810550700580c9070601420081c105011359000f050311131160344200941206240c2241049400420080040e9146c04061040d012803502440d901907 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 378940728 1250 378939478 378939523
    0x90605070206190e101e14030601030507020106080f0a0c080703020108070c020a090e10051b0d0f09082206020604080703080621010c0306080105130f05012d0b0102 72
    0x9046146040302008101d2801c04d00c000d05520000700d00030303240710b01c1c8000182e5248007000030100c17180c5146903044444c141540c041041c1507550712503120041000c0e04040d2160007041260b4001d4010002500d54081560316a00c0806821652219040c000b0703540009041400552031202062400681c0e4040c0c0d26441d01d0b940352034094400380110401241c02003c240b10024000c50f03203105600403000ca43c000f400e0340e1000390108409a55005d410b00404010b4901140364040b852012110701500508010803240c21058017140101504c4d0300c05052034600013041c0281c40055044801107085c04000307100081e440c1c0804981e100011a002400710f1030400140020a000300c40a039403012008100840c150180c181d6071540e0410848042926911382c055071008a4041c000c60024050281c0200244d1034814415540302212100107031400a0186100080c04000c1d001010a04540443c40030007403920b142c040910711400354802035003490301390844960761002c00d4082d5079048a07170006819 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 378941978 1250 378940728 378940747
    0xf02040f0e04031209030f2601051201141501020f01060503031b030705103804050c0c06040f02091f030803190504120314131b12050d090605070206 65
    0xa2002d00154244101c0341c1e00508501c18070700a044105e8070a41d20100e00210000e40946184d20419242c0d00070003500c201c0e0581d09070640300807070460b0300481d680400c0780d0391505c0550062421403051850005028100920100d00011043d0320200c01c0e401c40c1c10b00e2174040b01c0c050803034485008695068104200342540011240d1001545024040070b5034980402540c55900c1c14002800d40107045407a591100c81c0c00d01464402d1250140140714a10f0242c0c108150b44c0d0791041030707076500e8803072903451011a03040701c2201c080d6000c0c003122404460039418182011000c00b40c0c1c0301010ad11400301000096100000041407a01d6810744001c0500b00d0348c11070380c5081ca280c000410f8841d030307000d41c5012103445441d14090103008500a400340c0725203040100e0010240c81c1080c030013010b0003102000340103008041d580108c002a40150507440110344030701c0350040b00c443d00e0b482144070342401d45590050107008541c000500551303482e0f1200c0140e0f0761100340e43c45c1c014410040e502410a0141081 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 378943228 1250 378941978 378941999
    0xc060309030a180b0d060e010504060503150928061118010e0f03070906050406050301050103020105120702011d100b09060f04020c0c060f030702152203020715120f02040f 75
    0x40901d12044550f003103035200c66001d42c04c1d8100500552902e030300c4440c2045960889400d46000d4202510144002400c06012030780d02c5030052864019942c900000458411007404010002081041034a0400f040000784004200051205070b03000c80c5040203618103c88000d040352441c1d05000030040c003018003000195488e000141e001070300010080450042990b0a010703c90250281e594001589410902030200316111504040e00980c034190041c00541e03041030542e110140310940301040d59940700d030101e003d005000c06080058142080d101ca4078480400c6036100e19604007030400244000104000e402e500a07a091500b0015141200e0f88508058000b0030380c4c03400c400c0c11150f83d81c0c28040808d259902901c1e07016013403040842880311003a8140001d10b108040421501d480341030507202c8902d034851030488a0807104450b8806020180280b0070b1000a01c1da04000d1080d840c035403100070704007001e5441d640784e80034074200408010800d280700352402e480401424103041e60a00043c802e = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 378944478 1250 378943228 378943247
    0xa0209090c1608030a0914030f121305010c0309060c0207140d03030e07030c0608070305010e06220908040623190203130f0303080618060103180f0b07020c060309030a 73
    0x10000c42c074500c0500007142102004500900b4140c0c0000780c070386040d0502030f25003070224844540e81e03041006400c020340d10b01010b48041c14200a0580d21a490b000380015040c8140d08005005509040117482420b8166000810450090009100c2e11401c844c0490325400301d0700a083c01d080100306050021b040a010404000e84242000500c0e40050b2010a00d00001940211030400710100700b80030150303200e00302c0303504101c0604080c081941041e04c3d0424014005028900030401c1c08007003441d520045055860154120710100140e4503e070506903060b41c864000e031360110360f481600814806861078000c1c2d600340c1c0d8003103982c00d18098275040c0d2000d003112800c180441c40140603c070003098481c02c154000385000f802c80b014107032841c940900704240080072544100c9801e03270011041c6514500003a8020800d10300010105035500e034685040c4c8201b030010308030350f030807070091400c0100940220313014088a408072801d001020007042841c0c4401c0310310304481e4006000005c12240503000d00b2 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 378945728 1250 378944478 378944497
    0x9030320131a160c05010906090602060619050409030801050301051e040b0402030106053c031005060105041206021b010b010c061a091e0105150708090d020d05070e0a0209090c 77
    0x1c0c5800e60740c0036443c4400c1c1d0001e80070f880c00c65002c0b008106568000c0288001407195084c445442480c0030000303034480400404680c0507560f0325099060944000d1109005008009c20070441d0303003102d040060242d0360900030780303000b50310b13040104801d46071908054042c0e00d40d21040310007546e502d0340e8000740b00b100503104036003640d00c41c4c40c08503d0b0360342c0300c107140b2400c2d50b800c0c14502c0002c409a085a41c551044080d500030100080b20780480380c4001c180410901ca006001244544450004071110f200b6035108402e00d0403401c80e41420824540c0041182240c40200e0390030105280e09501e00700c0708400720150100381056031250000e64a9000010000703c6400d038290303038610341c4010079000c5c0000c0395074810a41d280f06400318808072010031580500415503c001d0a144003240851140c840c0380c80181ca02407020850003055518000c6100c0701c141d02a0a500c2000d845192071542c4148030300611564044410001d0a400c017540700345c60042c800100071940e0b945032142180c40c0c55000c1880d1 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 378946978 1250 378945728 378945779
    0x90c1403032b021209060105010315060f0909110c0c0604120b1518010e09060403050307030b03030408030409020c06011a0d020901030b030d020609070b0c1e100903032013 75
    0x1901000d481c603c040d003402c0c4000e215500c800e00d071440c0395508020058124606041c5048501d80341c40030011000020394459041200007070365a440705450000c0c40e64009900700b41420795014541c0e0018003d08039032100e010413540c01901c170000b0000729008600984101419140181c80441d645005142c0c024020f600603003030010959001c184030740d0010004140d65815000104004880d0b00070481d0f0115030301d4040c04090500d0f99008000d0b02c009840b010030180c4995501c440d996051044074010440041203d80c0d480e528054200690400000d000a0b4042d00000040b481490950001c200451250040c0740080710103865000307400040c040c03030405070307641840c0d080b54404111754090400250000e01c41454005280791501c0d0700790f006141045000e12030b030092210b001451404152850120380c0c2e80030207010015103400400d61100c20524149103101c8180758041d40301605a01c10111b14510048408034007041503c40d03180300248840c00c40008200703000c42c0c0d40d05d6a8465040000 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 378948228 1250 378946978 378947047
    0x111b010903060507051c090201140d11031608090d0210020d060b03180c01020a03021e0f0706050a080c04050f0108040602090d05011d0a02150c100f090c140303 70
    0x21001c007200c80842e10380003c2000080d00d580e5043d106c2c2030150301003004d42000c0c48000c0940d030000b01a0088250706290844011402d1400c490b01ea811040d15401607120356902c80c580300c03a5002c500384000b00c0c0782000c5811000810540c100110b804c440d050080d400902c40503400c001420000d510144441e8900b581e6590045001d071400c40056008050500549149008170120340307041806991005066510030b050b9240029008203406104220112600c0781042d07403440e100303090075211a0740307580724000c0c005d0124405030081e005d010b61110741d41d244041980e82c0708a0381c0c1c80e0b220f103000d880e902014a403402000c41d84200e80d05544507210324005402c14103001d0101e405c0300c01a19048482d80d44800460409506811400380c10f1010000101450221070b00403c0928004540c00c0c007c12000184801080350200042e07c0701940c81a001c0002c240c86008101c0140300907202106d0154100038009005110805804010302d40280918600314040610340c0344414513070030b9034480441001 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 378949478 1250 378948228 378948233
    0x608010b22180b030c010e0904050a12080901050f100e09161814130212030f030a05150301110307051b0a03050406230406030c20030c0d111b010903 65
    0x141c0100040005001c0c0101070003041001e070064582da0b04955000e540140c000b100c040e0f9008005480c1210103450f254801c0d202c50414030308080030003402900e290020040c001401e0360104400e8410703072140000300016110081120b100460503a01804906030684003404070107103101c4459084008001203403001c4842c0c5025a1a11000d079020324200c08a4070300c40e6101c00c2d001e00400030741c40c1c003001e044031341840c024075080340380e04070143d02034095400b82e46408441c42041007101c02400740486520b849180c03c0740d041c3c0c0940300488031003100b03401c06601d0704180c0c10140140102d0400d8100380600307603640c0031800c40f80da821620b0341c01d040780d048031080e0030080300510407520200d000c0d6075959a00c50510001408598941c00c40c1e10b0241c0d5a80c0c000b14116a8081c29a000d4402d503180c0800c0d0340001a40403611521041d01180e910144c1e24055040c0120000041904445420958880c0d01207070005035070b1413400c00406400c070b811950113a1100c010700300021031134081c141080c6074415200e4 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 378950728 1250 378949478 378949537
    0x8090609010c150e0f0309030717070e0f0a0b0402070c03141002190305160203070b040201030623040c1d09100308030705070c0906060512040204060b0a0503100e010608010b 76
    0x2200c0403c00c0d0703584081c01405000c05200320051880a040203510b0b000d90000480d503209018800d62908403064981244070010910143e0010a181155000f0a041001d00000c0b00c80c4151034a04860b441c02c42038410505050094402e0340350842d80c103e008900e036031107024501400222000c001e010b1386140103000d2480e8800b4110440d5440800310491003210800b400319000a07062124242d458003e201c442ca9000040f682d005602c80394001540c1c40303d04c01a0007519698001c41008400140000380d090240903106443d11000c0301c050103a00e2807101e050711041241c9c0101d51a540d29041a50f40c0c40c282031011581280510401c0c0011654a844450303181d007040c3c9460b0001035000402505100300c1010b690042d002448041103460303d007000240c4948140314404100ca450200003406541d03503544204014001e40c0d60150769045030440040007603108a41204100304d445070080360081804980354189c0711183c483c9069a400c0031050022a00140c0000e0895442810341b1840200c45 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 378951978 1250 378950728 378950753
    0x606120a0e0f240408040603180609050c01030c030e030412021203031f08061e270c040f110307140903120324010e0112060b070f02150708090609010c 66
    0x2075401401041000c105442c5440a000480c1019018444180320115900b101281c081f19018100020300c00800905801d8518403850064401e91500100e0000d00201007908600304801741e0701001030800c43e900943c2228880c00107007480d41e009100c284282000c0643d10840740340000c1007280d403184100300c1c182ca1640300301c42010103108007040442c40b101c00b00059002400042c009403445160130a603401902080110ba194205952804103040103c0c020b4401c1c1c44c003079112102111408820350050343c1d074958244460141d4646844441401c0840c4078840e2410086105207141d078464080403940171502d9946c0e20400c450030400b5000380d540c1040603000000307040d41d04079142c5c61300e40807503c2342504051010f504440e4150010540f80e034007071201a41020f0074240b204840012840e02c3c401010305401c08041c0500005250041c40110700452081c18406c1340d118407100c45240f000c541d103001e042d078000d10300c1c03400b400441000d180200151004507410314200303e210500340c40e000300740c0301c9 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 378953228 1250 378951978 378952003
    0x2040213090605120a050a0314130f080c040b0a260304081e01050403020d05160b0a09050d05040305060a050c1606090203010501060212030c0a0201290a06080606120a0e 74
    0x180c5081c2007010341444201c000d880d55100020f88000051904c2d1291240f1f1030240060404c40a900703903004110441041c1e07000b101120510300c88403500d4a01c054148042806000018404d5600340071032860103000d417860340c44000e440400c5c1b9518018551241070b001118042e00d8041015210301c1e0800c081000d0b0008000d40001841600701c2c0001003103a00c0c06070110403000d45d040200f00700229800090254415103140740c0580d84006210200c5c05600c10918018214a50072050082555040d00701c08107450040068420754103580000740d9140c45507200040c907907080000054103410440e80560391141c0c41b00c900750f08d0082031180c400030144000030202d42c4290340ba800001541424413440d405019903000400300c0d000c0c5c640c0010124040209041310040780040d14202a074400e401c105182400d2400510220070207003c00b218000740030945900030783c840100051b00510800c510b502400018042c02e00d030604004000d88004002046121100d4035908511600c00003044102c4100c10f = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 378954478 1250 378953228 378953231
    0x1050105060a2712050c0f0109030b0601110c12070e0c04030b07080a0207080f070c0b030606090f040f0519050a140c220f050a171c020c03070f06020c010903120c0204021309 76
    0x20f2070000c1181341e11f03111070540c1c10000b40398070510000c2c1110540581000007403c2c10340e4034440c4510210715142d8040c00d4075400400300f03920322415440001e401015240550341010242e81c07102c0850390140107a03c03000d0440c40c04240428809401054100c0d0080c038540005482d18440e81c846540c541d00c41d00341010004400500c500034084640d020720302030841c50b00c610b4650b003800c10001e50f89026040d00240314110400614040b42e032a031307008200c58203030041c0c2404103150440d8020f414811800025407400e0401000801e800414410144594004424200c00d91200c0711207034000c1d0084000340301d6a91241d907080d12071482005841000707052082200803140c1c01c10050082c1c05080da406140d6030420074604298101c8081142c10b018a411004858400a42070040385003503040200c10740c15008003500030808041c58010794040d00c4c0d0301d400b1160000c00e81070044a9120a078440508011503500b42400c0710b5100d0100800643c1c0010005400c101c0701e8000401e0414090340011f8129 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 378955728 1250 378954478 378954493
    0x42f0706060b0a18050a18021c050402100c1a040503130e010503011a0604060c0203211305090402030a0b330a0f030c0b0a1e09030501050105060a271205 67
    0x1680c0a0100e14994130b00f40040ba00d80e51502e0b012940002c1a4010280c0e0f1054082000001200960695050f0b5000703811192015201d07006101c02072006075030590080010444800e6200d000f17070803900d41c26030700c641c3c100e000e0200345c1c030300014902010b0700c11240c9004c2003003a038100500c032800030400f40184403000c120306c2d45000201401c48898400e03d0210740b1103804850301c5076a4030800e4800321081400c11500301001440001e040c2410403c09912600790540b0041c02810311401400350419410074480c017880c1c480b406c01ca191a01150001d501d0307404170031a80d00007102142d42a40003002044600b0104540c0c03560b03802210300c41d050f81107410b000700b00f10b03c5c12468003031400c800070300084511981960440d1603082c5801d50034007035209070a034001900c192061241d000dc0040c08840c03002040c0246003000024440060f51005641940c2800d0000c05c1d140741c030303904550a40f40940c0700c4030044000e0340c00640c0f950047c1c0400c000316080d0b060300050350120413a4046a1036101d0700117404c40 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 378956834 1106 378955728 378955747
    0x8091b060c010209090a0605091503101116030c0218060603040f030c02040f05191109090612060705030f0c030c0d0b0d020411040311042f0706060b 65
    0x1100b4190104041ea180ca0b031f02041c2612811901c02c040c544500c20444501c0344c5026032298076402250481000511a0b4851030040c1800b040e0b15042c40c0d001641c04e50038141d00c0d030303041d00403d0070360041904524010240500405400030400d4650408402003545070100401c01404c40c0c1d410b807280e900380b42c01001c1d44c5d00911340c0200184659182009001c000e854107580c400c01e41a0380c10720000043c5203d018a101c04245401014286030681c01000700080d00604015041140c90401021a0b0b806104051103400c0e03d032100c50790703424240c2128801000082c8240c0708000e09105014011110030202d804d10030034048082842050100010248940410004d50292900002005202500b009481220b0185084101511212003440305a071011080d030540403d407801e12061b111401c0c417848440001c3c02d000b06042080700da0301d5404039409a0440c4084940100e0150701 = true := by decide +kernel

theorem cover : BRFrame.Cov 378776978 378956834 := by
  have h0 := BRFrame.cov_init 378776978
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378776978 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378776978 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378776978 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378776978 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378776978 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378776978 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378776978 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378776978 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378776978 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378776978 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378776978 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378776978 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378776978 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378776978 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378776978 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378776978 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378776978 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378776978 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378776978 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378776978 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378776978 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378776978 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378776978 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378776978 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378776978 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378776978 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378776978 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378776978 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378776978 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378776978 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378776978 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378776978 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378776978 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378776978 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378776978 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378776978 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378776978 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378776978 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378776978 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378776978 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378776978 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378776978 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378776978 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378776978 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378776978 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378776978 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378776978 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378776978 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378776978 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378776978 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378776978 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378776978 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378776978 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378776978 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378776978 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378776978 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378776978 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378776978 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378776978 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378776978 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378776978 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378776978 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378776978 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378776978 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378776978 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378776978 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378776978 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378776978 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378776978 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378776978 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378776978 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378776978 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378776978 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378776978 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378776978 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378776978 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378776978 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378776978 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378776978 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378776978 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378776978 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378776978 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378776978 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378776978 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378776978 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378776978 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378776978 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378776978 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378776978 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378776978 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378776978 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378776978 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378776978 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378776978 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378776978 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378776978 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378776978 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378776978 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378776978 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378776978 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378776978 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378776978 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378776978 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378776978 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378776978 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378776978 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378776978 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378776978 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378776978 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378776978 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378776978 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378776978 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378776978 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378776978 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378776978 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378776978 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378776978 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378776978 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378776978 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378776978 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378776978 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378776978 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378776978 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378776978 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378776978 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378776978 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378776978 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378776978 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378776978 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378776978 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378776978 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378776978 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378776978 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378776978 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378776978 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378776978 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378776978 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378776978 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378776978 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378776978 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378776978 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378776978 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378776978 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378776978 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 378776978 ≤ n) (h2 : n < 378956834) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
