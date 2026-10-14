-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2841
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T07:53:53.026305+00:00
-- url     : https://prove2.me/submissions/e38a70fa-dffb-4814-8b29-a0c93f7f78e3

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 510791366 ≤ n < 510971223 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 510792616 1250 510791366 510791389
    0x509030315100c170f040f08162610060b070203060604150b0a020f03030a140f0c0f07060207060213080f2b0c121e0e031b010c080a081005 61
    0x50f43c820164005507501c01080f120a00080d070100041072249030344040c00310025200a08078807030b52540c401e181a40ea40d04018400c04130b40d050f1121600184542c111f4420f01400b501e0442d03607820034051501d8402800d00b401a070100e03502a00304840098075950020250950600817001c0d211252556410402190f075114440c52180303801c000f04203c9000072801400c00c00701c140c0181e560030243c4c8121142190b004490407410f55607100405080325000c00c0186030b00c041c82081d940300310300f460400320511340a40d076802804400000b03101010020103030140c1e1351407584900c0c10b5444020090001045000ca80035003035242c80b880700c0080c40c07007100080300800000400d52002103621403160684170720f004110240180700d0040b60f00c4c1c0c0000d0501c0181c1c0c1c841c1000ba50f8920070301d00c1d51080c4d072004001e00319680d010000305e171003a240300750f80110300042d013030039291007103180e100c0c840d4010780300c0f06292030b0054200300c0049400032030113400c810051703c0f503a000160a460680c50364104215584131 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 510793866 1250 510792616 510792649
    0xc0905041e0203060d0b0712060e060a0306020d0f021201080d1b06150806040501090b06030a030e2808031c05040b0f070e0d030e09010f0b03040f02130509030315 71
    0x7001003070500000d4581c01540c0003040030700240107004035034807030305101081070b507503840010382030000310500e03218520920024103a500c1c07206800341031072000152902010f00015240300c1d4000380d440500c8000d90b1000344031504199040d9240c004038007140c040d1080074407515445018070341d4402e10080c804e0a410400c1e409100c2c00000203c00c030780700c0d10300510b000a805410542c641d40d0224001e0030810140c0c4c4154030501c004500d091603454120a1080090071043c000e520040c0c0e0f4000080e046075002c800e11200307845031501e9071084240c01c441040c0c5540d44016894010b280840d00e40f10100007004030301486090a60428564138100c0206d800482e00908840828008100c1e4942001130440d0406498030b801c0c070b5002070b440009280320020180072400b29111703640c1c104050812240c4d40b8010520b1881c140c210920301409940503100081005059452406c03c00045613039480c2c0d82c0c0c601c003030203e00030001d6140802e646560790340700307a81d014010403c4427070114076860146003c410401a = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 510795116 1250 510793866 510793901
    0x1501030e030313060b18060102010b010f020c04050a0b0919060b0403080d0b0307081b090612060720010c0903061a0a2309040507051011060708150d060c090504 70
    0x11800010070b02c0c05241c0e14100c4d11540c0396180c4a4465841003080146410020510f101d1400e11071300190841c0c80c1402218140306603404820b508a4000c00d42078200e500550707000c00c0c3c0d0780e5101100030052503072000c8281c2c00045041030001c513082a140048001074164010000c03223480358031100c59401184401882d000c4200402ca41d003c4154001400e003007400740459680c20345a080980c144035440c080102d42a10ba02c560071060729200c41203035040802075425605c080d1008160503282c010082103442481210501c0b06c00184117591403000f8440b04800030080103181541c024980d00e50b51100303545c1340e4104070a04030140212280340800090040811114030b01c0e103048290001500b2991002219080d200c686040c0c07903010303c1038802d61055018104160600b402c1064007880307580c024081041000032844030120008100da001061410b09200558501540d1110501520141034009a1040f0746a040044541000183c158a6140c480c056503c520600c0304403410f025201c0e0701d818 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 510796366 1250 510795116 510795121
    0xc060813140a060504080c0c09061003240f06031a0310050621030703091a0403030c020609130501080715020703110f06071214030105100807090801060b031501030e0303 74
    0x10030384020540707800e64610544201c0812a190b440490340100e40544c0c04d52400140b00340904030503c403850130000c04681412650800e140800c210a588107038040a1503902d6006807022a00b06450302c5801c2138143c1160703c0151100c100e424502003c1c400c44002c1b03400c5c4012240e0320000720f111a400e900d0042c0c000c0c4925504007500b4409440c0c06400103401c0303109040100202d000c41d007103400a5900b00f00c01990303103500703510340107050001c01d03440404440be441c99040300c0d0b1b002c640b04440403603825140116541c1241c2c0001241407040407049540002032406181c0303003020355005281207031588025980c0c81aa1840e070301000300c203100503120040c1c010000601c000b0316202911144a5809060001503a0360f040211301103920042099641c504c1c800844400203901001c4000054000c0135190708551614010640f607000e56414003003400760840004000380e201311903440062600304002d20489942d0b107400001c9034015940540c0507580200d0000e150b5020b40901d100c401c10100c011491036 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 510797616 1250 510796366 510796373
    0x50c09010e190c0504050a0902120a050c03041b0e07110d02060c0d050c07050a08120601031b030c0212042d030b0c0703020a080307081e0c030c070305040510020a0c060813 75
    0x4083d070003410410b00c201401302080a0b01c5881c0c104d0041c0502d09001643d50282e050200c141000c01456458010709200c1082013041403103066940150f405900b1500c000003103521240c1d02c84071070300803207262070440c804c0121140c0d0000c41c2d8020100785c0d1043e00c1d1103510700b0000300d0310b81d0780844d40119915401c01c9681c0981c040c0d80e01055200510302c0a40742002841c2d41c4035818447c0540050b1005607020515a2090142e160300325000300c82401e04100003200b003810b401d00e01d42040d0f281014955244024042d01d03009000600d40ca034408140c0c50355658807003850165010414540041c05444038203550703042c101c22000034087e0303904030200d07404c26540c241c1c3d0403949178030504080301103010724400380c4006004c20b030255020355050348440400d45000c000c07218202d24001038161f581b0003c1c0050000c9088c3c032204503508050708440940e0795901e5401c00703a81d0391007540c0c00241c0110242240d00641a0701154444e43d90344a10304000c80541d403114200c030010b809440380420b0346d40c04000d00c00003 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 510798866 1250 510797616 510797621
    0x30c2019051018050a06080708100602120306190801151215091b0e0105010806030d0c0b0a090507120201110f25030605090a05010f06300b04050c09010e19 68
    0x1c401d005165110000c3c0c681012445c0000c09500003030201d03039000f090042d19030700481d0030380c0e011070100d0395614914548a80207641e03560209009403c0c08002012071290348071350003032007c0301050006a0460980d103e41c3d03580203020040d00300350210280d010100d5200311500002e101203411411911941070700c013800500038544213004032661094030328050382c00344c1c50000b044010001615050507070340c500380000d007017101e005020b42c0c400c1d004140000305898111078140c10380c1da084401c1d0301c0030b0b0b5100c021482c001d01c095030010b021441908000100c1d41440c4115207c258803e03a2041080d49809a0190303846625a40c181d202d0341000400324512042c4240c0f01c201044c40d65090002c80e55691140001c03640c065801c014a5080340d0400b0007440000d019010349149001c200304005490079036235081941e004c1603001d410000740320b14107602c4200304040c2c5403016008a19401e15017890714105640300030345515280509803001c00005c00c42184a00d9511902841820960110403886038400 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 510800116 1250 510798866 510798887
    0x9090b0303040f260a0c0503120f03042414011a0c070308030c07060e0a050708030a0e09090f39090402060307021501290c07030807030c20190510 64
    0x180104c20f00241c0c84100c008000315080d40b07000d0b21005045504000505d8104180b40310200d902d1841046801c81034072400302103950050b041011990300c814514100405000320b200d1060f031181c14401e80d40c0761607002511030f90403260460344c0e040000610104d01c0c11280680e00c0c0d01201c0d500007610030804900403100071540a05d0b442815403600c1203c0c1e40c1d41c4115403c540241246d0f0744140010030801008125020117015210300450508044030300050007003065946481c0030304010300228402140801044154034461030a448a02c80e400c903030030340f8284015440051500a0380d075014000304a01c1880303c1c200340003030944030b072542d525001e018040e44040c021000314070131f8100000e404600da8a00a019054150501c001e8010b408000010b200904612141029081100c1d0380000000600d480c03c483d4420111038032000507080039100c01110306005858401509200c0c017036040320481c3e5943c0c10500f240e00c0c107110702e002e00414641c0580c50060b1038001042810944072540102d04154 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 510801366 1250 510800116 510800159
    0x150503070b0a120f0908070b06190501031e060303030209090c1e030423010501091410060c05030712032307020a06050613020d0209030c010804030f0f030e010c09090b0303040f 77
    0xd0440200c2d00300108940c05000c01b07442c1403001052842c00c0103980c00c015a0030078012148880001994200401c1a90342882200d041c50b44d11860642d03120100803201d10b0350100710900704403d9a907818040d01035806000c00504c074191700c000291030b11002009551a0004040e80b4100104520085032011352004d00140c440b010000886032643c4080941c40c0424048800003007a07652500d20000e0a070b407610480154012101010080080c1810000904681451820007800c0c0c2d0355082a81c00e40c03186490181902c1403105e07944181d9501500a1307000e0b940640d402050828036a481035100032400d0700c00e040160414034200c0045a42e0350030141c0c0000d0020080d000c001c1040c0c03c0403089034829405044c10f150089800141031030f0a11502c0e2000600b800c4c910264540390342c006100d8002c2000a405008101e8048940988243d1004030303014401c100030440b000030001d0240c4841c046101c0d405500341450710703038010741c02c0c040150ba00703d4180312040303000c0c1c0d17040000c40001d144c101203504 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 510802616 1250 510801366 510801371
    0x310050f1212090a08030706150b070f021314010303020105070806060c030904110405030a110a0f05091605040e010e0f010609060509010c26031006080613020901030608030d150503070b0a12 83
    0x420044414001030488030300c01c080006828400880c44480c00212b0f83c003610242005114000104031901615080d85504444001f504d040900301c3c0c2000303140c0c00c0d000f603c1980b100344c004010550150b105c0e0f0300440e03858035442481e980300001c00c000d45c41b607000001143d0b00240405042410f06822040c0b01e180c0b00070190f400c0540398008240340c400d600d07409940e02e40d20302c0e00085d4282841412080641642c000c000704480c1400081150418040c00f40140180040c60b14050f0b90b1040c070580e0050301d90600c04c0d60040d60360f64031030b620482d02600c500d4402000e500001880394094400300003210541e480d0541406070b0000151780034a0500f40c00d032504d11001d1800251000c2c1d6030109a00c408a44001c141c59042034842c0040100181e0032480038001c1c403c003444015034880102070710709801c0311400340c0c4d42c01c00d4400407405000f19030302c03c110500c00401c40b1618040e0640106c041a102281c2c122003c580d0340c03080680d00c0c04c040c85107040410081002058a500c58201c58140c010b003003802 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 510803866 1250 510802616 510802619
    0xf061e040c020a0203060c04090e0a1110031506030204051206010f140a080f0a050d0e01050f0304260c0f0a08030c2803021309053106020310050f1212090a 68
    0x200341882c5084883c0c00700c80351f002400b48080c02d070714450702c1400700f000001000000d569959031400c4805411009114840107102100754a110744c0000c02d00c403010340d00f030034220385c1d0714803014000c0e400c140a80d6200e500c603c02850100030f00010014129038031302043c0a11145050150b403002d1300c05152240d04100c13441008035644070208404c8410400040c01040800300ca41803180c01c1c203103001199820000300da48400c815a9115080d5031450300880f01c0181d030390311546403000c0030300002070101c8143c84210104142d0540c200c4040c02501c8095400e550501401a44090303d4484110008205003c24004074440d0314506002e001c50720342d00319145503440000702d03601d000419441502c0000076000034640d99003100024403640100010300003030181d403e1100f0302c0c41c00c0c600d0140c800c601c112200101d80040e440d00c0309410301c0c0160420400c41d543e052486c1e800d0120409405071030b000c0c041c92441c0002034100071002403100200390b00a0310381c22a142c0541c0e0220351010001e00d0b841048081c0 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 510805116 1250 510803866 510803869
    0xa03060e03071407141e04180f1a090106030203030d050903092e0e100c05030f0a12050c0c060c03040501091707050601090b0a05010e031002040e0f061e040c020a02 72
    0x3115259022100000d141d40e070301c0e04100c40800c40300e25550341d0058000c0c1c1020481b204622a01900c0301108580100741d005030800350031107015208502a0100e01100718501c03d210300905024064041000002080d0340c680221500780d8000303100003901030f40100060303400d02e102c1d50b00c019001000c2c40300766460105540e00265800000098510040e040d0000511803c02210f686007414010f1342400e444101c1d840300012214000c200011082c006c6a81002c01040130130310842c2c01c3c0b19814400365440350b60300e001c01092661a5034007024480c0c6403c01084000703040001740d609540c0c04900520382c0c0d94841155880c030383c01c05002182ca80d901c8079202c0c80020109910001c46007480800542c40b4011410010b1034080180d1000c1d40070751501845003807545810004400347c1700f007820240361512480001c030303180000c00048954050720108d0003141818100070b0b01c3d8000e00170700349124010b459403c00c0118020711046545001c800610300001e0300d04080d0800d4061441c10b0060b03135000300f803a40 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 510806366 1250 510805116 510805133
    0x1c060e0c03090606040b010c02010c0f050609030901030e010504020603280f021c06060203090d0804080d02010902011e23191e080112030e030a290705090a03060e0307 73
    0x10348011030380102004100b05204100031190744804125005c0c05540d401d200044c083e15650740019040188500d00b400502c0380801c4515001c1e9030000c100d540340c0c54036849880d2242c00404c840742c0046e0900c09040c2010505004140c095a0010a05440d40d00d680d40a0388002c803d084a181030940224400d1480c00e00070300c6182001da03100b0324096900e41505580e41c0221801101e041980751500300244680c03503000064900d83c541c01e40c0c0450b207040f0641400111406190f200c3c860601c10300707014501d445e03810341183c40b440d4403e8840e10b84002030089810200110300c4850000600000142502c044072980d10740071074090114581c0c60001949032400300405140444c10110302d2030034030261440318850503d00e10a1107485c0100340d42d41080c00c906c80055103860003908111151290a409580c00d102860349607500000030030707c1c80c40002c0c000080022500e01079407032603840e9002568440c00785c07003201c1c21803034018136010741c0508680e03502c0014140d030091603842d40310034480c46000a2400 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 510807616 1250 510806366 510806371
    0x9040213050907091b080c090f1908060c0f07030f03182312030406020903070f03140c09070e0d05160f050307090207210c0803070f120b03031c060e 65
    0x2c0000d450320904181034a0240c503e1281400300c44804200c01414003588910000d03000008466030135030710360300040040c41003499503401740c0d404000c0c841903081c040c20503422001213a0f96801600c005a44040f4518990f01501000d0b084161040201d400001c9c0300c0e0110000174041c03428000342d040201c0710788901000140707000300d40c699040c0b0456040c0c9503800e81c1104480340031500800c400f00402d8070040741800040c00082c48950041444d810582d010701000010304180822040c0c042d540e42000341c140c4611211000807030140c0818420103081000c0185e00c81d5019454032651200b00b1410300040d64214041620300d40103518112a20151203c044e000818a2120300343c98241800105402c05540780c1c0080c2030248100403c40000f002c1070000036040c1106140b208044c204140c06032260300411038002c0c1241000820002c00540201521500c036003695180e0070650248001413044a519a2185034513600503c16104140040b103082440d080070301c9008580c46540710715201080006 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 510808866 1250 510807616 510807631
    0xc0c031e07030e04020c0309040902040b060c16090b09191b020106060e0d21032c1b011d030a0503070501050103031416060507030e160f0807080c0904021305 69
    0x3841d80203040d030001c451110080121801c5140c1300092042035038178070410604500032912054150203543d1558080035524a018051640d203c2d00c00186503100c062002c032003a5141c001581c040381c941c0d603d21505100788005000482c00381c03181803c2e84181e549118100400700c0e160030015000c08251410140284003540020400905120014020107401c2411b01d0141c000c803002100031403a01e010b03a60503280301d07140113403890301055000c030041c1283c024034044c4540c0928103a0702550181001113014100001501d01c510340700b50714404041c4201d08107034000b031405490300c004804c05640603040c0c9a00141100c1c11f54869507546421078000c0402661140d640c0d030010414550030900c0c410b89a98451489441c0ca280308040c24020441c104025180607520300c00a00054000c0d4030143c840302e070540072581102648004401c00c50072a0046603e105021040001c80050000f10501070314000d4000c2c0c000e856000c014880c400c00c005001381c0c1e000940000c07010304c0306442d00c035044c050b020 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 510810116 1250 510808866 510808927
    0xd02160506180609030a0c020102030403050102031f150f030e0708071508070804030903030804060605090906040309050301021234030b0301231303050d1e0b0a08060c0c03 75
    0x41c40d0390311078014103038800c00760403035000f0384100509100040110352400c002800c040c0310280642c00104c0ca58040c036040140756620000502600d85030860032058400c600760b2020ba2010744804950040000d803c2c0c2070b90116002ca00300c0030300140242c00c90741031070072203408981010341e907042841c0c5800b5103940070103d15440901d908100a0b80310440c184d000340315003030400e4503050070303034005103400c802d480301508004400f4042400c21860b40c100c48000c080c01440da80303107070401c5101d15444000a507802c4010991035180050a810180244c0d0301c01424000c142280c3d40c0c440c50790050390b6600f8a600300c0000300b42d021244420382e01c1d1411100c010195900040ca40e003011040c142180c01900c0f0743c0c0c1c0711918405410040131054220280d2156200d4461a1030481740c0c0742c1070303031940140780c4520016030a011040480420302407260041c6a005441440700e100504c3c01d1040918150042107040d810950025400b800c4001c000c0c100d4010310011280b0b0040d544182221001008003448031046 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 510811366 1250 510810116 510810121
    0x111e0c090a0b041e2406050c15010b0a02010b010206060a140301111c05011d0a0b030c0402162a1208070c09230c16170d020a080108030c0307080d02160506 68
    0x21302510420a0090700d00105541d042ca603504009100c0c002442410104800020201c81c65103060010440d40481c03049140001d58443e2000866508a250440010740c0703452450718041d880001e0b024000c08006e80040342c000e0429030701070054000092440e415640356211031b00807540e103030000c091602505801a806181c460041e0f0300303032441a40024544d040089206031001d840b0703800c0303603041a454040010420f02c0c02d03011030f0500000720b04259000d840803510080381031483c10090803441c070232520703010200300ca01c80c000c01c29404d95041c40c5c00361001807024802c58541c00320326258907024021a506000080e941d00d0030018454002e4100f0701c8e220f921518403000030140d1011007070300d40c47c0008520701d80302d51003030b071540607101d0021103040070b070710f80f010503c06400740d40404550a860307596540c00340a08240041d5001186407400180c2c03480002031948004003c0d50383c021012400746203050510345545446411804070b204001c1d60030800552040d01c0d2100000b12180b00380c3c054491032 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 510812616 1250 510811366 510811421
    0xd0305070b130b160815190e160503010b04120314040f0f0b0c0d080c0714010e0606010c08070813152d020a12050403080a111e0c090a0b04 61
    0x8102409038050411310700c511030b1000e500710b052580d2050410b070f4501070b07041c403260015000e00302841d115070074220407400114060b001d070404544542d00c002d50030000c1060b110000c8643d44824440e10310075140c14042405020701715024181200d01900c2c004c40c02142d914071325040e560060b03100740440320341c5050070010f0000c402c0e03189004080302003e60f4205442d0000326500e59141e0b03100101000404000a4042c100c080c080d034240760340041210b1103035548001494000c1600001c03170b401d0f510070f000000c0e007039600c10700d42541081e501140c3c2c06d0400445076104003d5030050213540e0000950401c003c54000321710302c0d420590828545d99006113103010301022500c0d00700191800c00c110224182034003820f400003503c1d182039a22861600f01181c1e00c1404a6980c043c0303130801409001d0014403401d102c0d520405102c0100301e00c8042e110a00600c05415102d40c0009652140a0300012901c0740c45143c07001182e40d00810a140109000c0706880000d8119224282c418517010301c214000c1804 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 510813866 1250 510812616 510812633
    0x5060c0c090a02040e0a0507050d0903030e0705030c10030b04060b0a021b0a08030a0804170a09080d0f0905011b0210020a0b0117190c05092508150d0305070b13 70
    0x206160781c0c11132400342000105903110740000c00c9070000ba622100070609440c49003007250414403020608001c40031452400401074035807100f0386440d51160a00c0403419180125401500720b8009206170316001500e0001d6021788442842e00780d01075520080001d148d00c2003002000091115406045860140049040c1020ed40c03030300c49000d50001074042c00781044c00000c86040130070754208a002503880d89000c1e83c0c54545001800000d020100707075045120380102180040e20000e409403050b110030080c080f1a000000c4d101040000d44201e0200840d5025540d5200d40003101c06600e03c88451503004140350400c503010038801a4007400c00e4206005500034207601420303100b4a100d422841302d40c02c00740e460b00d0480140034074120b5035840e80104a907107000c600061070f000d81b4072051803919111b071500060320f0103054906603035244240710003c2d1042c64540c1c4a1010b8401d2a40e000c06040103110001d6500c510032000c4c000100a4000802c109482151260383e54102c2d44401c0d80d00751420095 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 510815116 1250 510813866 510813871
    0xa0f03031a010e0f0409061b0906260601022d01060b091e060c011a040e010b150a11030c030a030e0a0309030215070b150306071d1905060c0c09 63
    0x1540da8203007051038581c1d0044101c1000c220813907021441014800009008241074079006100c540741800000301d0244107001c2601507240c1d511404049c5588203020340340a600ea4810484402d83c0e040030509a01800074400d40200040c070480d40025000d0b100ca6000440101d0034020018400020b01c00c44542400303040c014280c20720745a424200410003180100c0704400040d002c00da07420b0800300c80c9444000c150f4001404800081c000008110b41e400604041e44d68824000ca040601c0c07400780d84014002d001c070a000c040d24032a031007561600f1602050300142c0c412020000c0c1d503011000007100400103810254044809140d5400d2010005021a200c0c0c0000303800c1034004038103c40c08680c2205101d030440760182d03144002d41b0700710480c4481c1d0b48202600207180c1d040341c03024000408082114602280307404d4044443c942c69072441540d80c040300002120700d001903140005a0f81c104070904a00b0340b1a0b1101c2044240d490300001596904004950125a40551200a01c0c0e2903c0e110311038 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 510816366 1250 510815116 510815141
    0x40b090706090602031b0a080a050304020316030213050919060501050f01030903080c09150c0102071a0907050d050106030203010e0607020115050907050c12130f15022d0a0f0303 78
    0x20006450508007071344034000c4070701118404d49600b21955002c4002c3c4810071f006580841c0700d617607590104c800681941c200b902d05a02a01c102c03002c0300c00306070220444009403a0001c0040407400c65150200000c2c00008008072002d00480c1c00d0150b034402050b9808800b5072003460086a658186002d000003800841c12803810141008a0314000c02d40141950380c11200c0c1d80403d503942d40a500c0850780c420003180c19800d20307010000c0d2001c500d501c10741c003070039110b4802c3d1400c1c0b041004400c030100d103449045d14107401623000220104801e142510181c650700307125500200c0d00950706c1d000282150100d00d503117a20340e002442000b030b0140d42849032000100c120480c1c1201c1c5410100441c00c241001881d00003070090000307407013035023080400c00c0c03040c8402c6a00590380d85030380b000e9080b50002d2151007000c50302c0101e1039010a0005140410381c01c1d0080035030041410900d484103008403640601e45403d031030300382c41d509040a0742043c044150300c0e82c050300b4140b280000700c0c9801000c03149003200e680c = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 510817616 1250 510816366 510816377
    0x12a1e020a030311030f07062405031f1803050c0d0906020d141e0d0c03020702090703020f121e070804050c19050a091b090308070f0f060203040b090706 67
    0x90005039905031000c825030b5018500008001d00000c0442d01d1481142d828205512011810808020850304508000c0d0840000440b200320140c02c845880e070050700070030b0381c9034000041c0000120307008444482c0303817084050041100301903194484a9020445130607000a000051145c0c903c9100f04034444010b401403070608000c0d80340a600039220901c0307034213140801410600d00c49130080c4c3e030000d80d64403103070112000e1100304a820381c508280d800f4110b508281030070101e144c00070394043e20940e610300b500589000e085da0b030f841204500a41c860152000c3c103c00620140c2c5000a001084500c50640b00003400018412401d226000d000020320700070402c40300b1000c000014a02080140d414001035502c401e0301c0b0349504140142c01ca007a08048c0c1c020005420000c0c4130056074000c02105050a032400713510007510b00b011108140320340006400f00f10300b08400f400050805404401c101c0c001e5816110080c66a540c0806a900986050b101e056604003802064001403100d507000701901d0614 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 510818866 1250 510817616 510817673
    0x4060906060f0810090504020609091f0603140c09030f1507030b0901060c110f04090507050405150d11060706090605060901081f05040501091b03030909021c0209012a 73
    0x4425031000580101741c0314540301d001040841d00c1e002c00762400c01100801801c268900b845092840718101e4600000940000d000001c54501a21461402294070340c1240380035039914030a40030340c0c1e10102400360140305a90020510101c280020340088605c00710020310350810410081c190b40e00541264480d11240d0010801c4627040824404825030007000c42c2e00c560407450002e403140c402c9086864100e030514480700c0800c00b0204237401514401c032420010b54450300301803600305108202460b004070040303414a0120305105100d0300d40031030041030189001e071203070f1700e40c015600076090031030fa4641c0b58024000c09184c00c10941c1d000d0502e42d80100582a0b0031144900c1081ca40c0311908110b941d590045003e100e003e4021149181d00450f4903007500c0e40342d500e01c45402410744414ac000070584080850b103140340f4021541c00c804d0815240f014a180411544001d40c4550b660074184200070300340d920703401e519030114101c0380c400a4040e02e140c000d5041c0801c0b0310500786c49040005c19040d15 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 510820116 1250 510818866 510818881
    0x30c0c060f0403021306030602160201120e060133120c0c0b220203030c030304140d0207091a133c110d0e030d0606050309151504060906060f08 63
    0x10380b421290100c030740b2907050001c51801c100a050a402c0900460700014101482200380c0b1075100c0254400e07078414164102602d02a03080301c0030215041d2a42c0c21480041081c401c20804e502c0b51050b51810041d540c010704400c0420000e406c120481c08515051581610952280b05040c2d804603103040018040c40c0035512400f8000c0010643c2c0070181170700d0020144036101c035400d03280c0705030f0203000c072075513416125241c80d91f9030422a411650248203e988000c4940b02060b841c242c80001e40040400c10704080c00d000103082110f480740b600e60325031034181809564519801664503c007210014108100d091119042500f080301d440d001c06100b100408014840300c1140642100b00a00084041121418519501c101c840380c00100b400d00807050500b003008070082c030714418080f40800040f0350303455003a00e050004985c210740d03a0b004011640162989171056a80c000354104481e0034490b40a80087c00311040e5030040b5800541d502020710103030790025000411f42d12242409006031601c1103 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 510821366 1250 510820116 510820147
    0x3020619140a053301110105092d0a08070605130309090f1b080403080a020a2003130905010f06030e0c0f0a0512060405010507030605151e0301080105070f03020a0e0f0307030206030405030c0c06 85
    0x40e50310100e103c0d80308501d8500c45501d030066124450ac0280e551000484c00d00702d10302c0c1c010910a0325414a0000860011600307404c1c45981158592142000b46290200400040c10740d141da1151240c0c55100c0011141300700380c4c1c806184140d0341c407030000e00e04050400400b011002425094041e204005c1061100c3c0c02c23142411001c0001000d003143c01c160181141d00754003590501c91191032081c50040b03200d2449070000c0f4144c42c1c00d40b0b80b54031002d5417544c044080d2054035456403915000441100c1c030500b031010121604200c081c0518020f40c1e65103001c0ba041405140c804546604914148000c009081c007415030800c107185030603c0010705081c002412500030300c083c181e000c0d800180d1010704420400d10b404800b00c50f42e400644942e9102c40b040d01920007201c02c2d00c0082c9c11840d9412000e4000d1003a1040080079903a504050800c20741440980114440240e515100f0088000b0050303451400840c4124070801c00745880d8114405980d1030f011901007120302c50310051000305218030044 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 510822616 1250 510821366 510821383
    0x70912080912030307020d030b0603010f0902070516090b03010e011b08071101020406030e1005070e240f0a0906022406060903070303020619140a05330111010509 71
    0x10345040d54541912001802d944000061214940000300800c41d803035801040740a05182180ca00b84001e60740d40b0100483c071b1009005589017240c1c40442809aa113140d4041d000c014401d4044600a00882c4907052200103c7e920200c062034a48640d5003850a00303003d071528106041001744000103030000d005c4880c10480002008211050b0000765485126030318006240b02c0340b100031555507494402c002e01900c02c6158040c62807280c80211280554940300b841d1241c1610394480318145e22032820009605501903210024400c4004075104083c140070080c02c80034040d11044e541d45903c072902410340e17404c0303500c80c8095400401e030001050711100e035200c0c4003a203500212011607545100250441c096000c006405200c0c10202000301030300040d92074061001480318130300b4045550500710030794880e1001140c000180d280880c0b8400c0154004a4100c4591810b02001d011418200803915151840034001c02801c0c0c02e20b003507513503000840840a0203c4000910545c50400b144c50f5943e1500d = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 510823866 1250 510822616 510822623
    0x80303040b091903020d030507020d09150e130f0e030c0c040c1b03081f031a0717041109011505030411060c0d110106050d020307030605071e0c0308070912 68
    0x20400082d980100c2481202101003100030040103914090800941d07134500c034100540482d24203004075030001e0001501003080d58907692001c462174101014820380e50581507404050241009103045141d44000f1a5916000e102d480060300018036035600e000e0f1502202a0301058100f04902000c07240302240040f10b110381134901007150781140404413400d00400000d92260030020501100b095030010700c49000304110300c081c91800445648401c020520740c8802040b982d440c5504024081f102d44405a000c180e030f04000f4134030040c440101d00004411102110100c1400e491042e07103152445480340502420360f05400c0c0c10802c4940a00103100160000d014008403441420695a4010484914030711004c01e644007441031580240c40c04002e000e008481c0d50820a01084034202450791421483d00100200600c903c0e54990000038040a0034110401c07468082200000b640320401b0b4090600741d6070381c0c900140103070400519821019140324100007003c1020050798004005000c141c540 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 510825116 1250 510823866 510823883
    0xc0a06060f0b2d04081005070906050406030e0c0d050d031808040504090f150608011805061915170c0d082709091525050a02011404060617030408030304 67
    0x100500090343c0f030070307589801e640c00074005030105613400e0110340b203804c01004040602483d1985a000d80d4a52610b01500000500c103000c1004040c1c03103904500c89808811050b125a0b004000c0801c0540c0c0c841601920b999001641d03038030910b030345442044441c001038210320303030505146d944403082c611070352041602c100d46038224a000d00c600520001c44d01c03a8000700300c0740400c000520030304c0501001d119010140d4a00f10304c2c1060030300c6544c00010103545c4900949025654403500ca030640c881402013803c7c0c1582c0c1c0503001070f18425202100040c042c4820707d51118800b890b1040e261100580c00c842c000c0d031032240c2142c0080c0b40d580994504209291840d2218005440107a5203100031114044c1d01c2151201446000a40852011221002c62240700103954818040c400551440c10101c01da001c10010031050282c0700314090080d150540c40042a980480358140c281201d056600303071111684c5400c10005c82403200344505094801c2006107042c02d2916104603200c2c000140083c00601 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 510826366 1250 510825116 510825157
    0x30216080c010311220f05040203060603041e0c031a160237060c03050105060a050d1109041a0102011b090504020a031803020703020312122a0c0a06060f0b 68
    0x5400003550340650a40c01c2190400310650f03d00c980d541500d105a0082e06c0b03059501061364102802100d00c99203015012500d941c0355507442e0b01d0000e8800a0f01c40d011001c0c4600a800210403140c880000e60040714030034800c2810160b01078000703201500d501d42201c480c0320360414154020840e204020040b04084e40305003105141c9480101e61041642044000b00282a0402109a226084025103a50200516a02d8209100c0180b01c2d0002e55004248184400c42c51030f0056001500704010709007409052045440c0424240c40d40004e420b03d12806070000c483c150350742446654100d92112510181c0ca07500104003030104080f42c040c0ca40a00e800089288056002c0d40001150003c00041c03500700398003500303000b07403100301c140022881390003140368a4581e40c0c0d1120a0301c5202004208107501e82c6c4544001c2084803100000051050007801100300310044c18134040d00005001d400a44181d07503c6150a9085600340e0b00f01c4082d9051641c3d09000d6a5455020b864602c40c80320002440306 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 510827616 1250 510826366 510826391
    0x30203040c0f05240c1f1407091203030b060a051801081003080318120c100b0a23100906080903030103051c12060906060e090f1302210a030216080c0103 67
    0xe01c105848117900784200101c02c608041d540d9a0341d1605284050b04000041100c0011100c021007600c5510004e01c81c0002400781c40d0b0b103040006c0c08544241000200450316402040c501c0e0002900b0b40d0100c3d6020070030300c101880381806403c40450920b4004601d240c24010214496101d000290881e4408400a21103049001c0542a8041c4002c202c50181c07241c0d614689941e4882c5680c03c9441c050300c541c0081c0d5045178007c1e150005001000b0285c007608001120002c100440600320465181103102005501c90403085113078181c1540c0e441d86030504140026001100141c0b492411b03510402c0100081100880c403c04c1e0199140321340c0d2485000404210390100c50342114000b041d2800c0d8001a0912036170f401b40040b50055107400841088240412440355012900488200003840000b814080350f9000c0c0d080c5148001c24500416002680076581d9490480000045a000740c07484420f0580402103018038010500c01d061b41c0c0c41c200300000351070700c82d64107202d81815110514843c1d80c = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 510828866 1250 510827616 510827689
    0x703150c170117150606070212160801020307030c080f040f0c030b01290a0c0b0a090c08060612191205040312030504110d0b01050607140607030203040c0f05 69
    0x1070110800d208120350f183c8105100992056900c000248110488000c50a111115640c0303c2d00008111505000b00e607002c0c0310210040315481400760082e07140d0801c440c0008480b010103000b500000580303c1c81c103250041c0440da020301e030400074081c0d007a08000c0d810002060090f40194401c1000c0c0003a400e900c0c04c0070704400c603078000070049a1340f1000800c1c988029002001c0c111a003445502c92900c0d01201a03c0c40d00c40d10071401c0000e103069104002042901c855a41c00c1260740c40001610b001e29241c01d4001081504156002d03004a002d000315490200c07007600f01144140042c1000b84000d0403a60103603040480003c003000040c648071042d5034081d200391001150803071100040558041030040040804580448103c00d03244c01486c5242011445030360044d9001c440c8402607401c00c010001250000c002c102c40580c050b04120340458070070720400d40120050b03100541c884c201031500d84821589904889514242c0c0501000a551907845034440c150048070148074180c2c0f0009841d1a = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 510830116 1250 510828866 510828887
    0x1110301090b06070510090c0e09030712020f0a0c0e060114190507120e1302030c0a08220b1b03070c0212160b0a080c040b19020312010f050906030703150c 68
    0x1724000c42a01100d4840b0030740144500f284204482c16200740c03640100c00709200161a5091a5070050208800003414002210303c5029a40103c61662410000c001d180c1540c080041360107240d860130402103000740c02416604403409090040041c8640d207a401c03035601410030b260602e1401e600070744039810300600442d541c00c0d8000c0402e840792061090090a041d10f561822030103081c030500408030500c107510136640551059004903141200c07038282100c000703101400d5041d1040340c0600c0000d10818450683c52164404d00498025240516400c1034855011141c4c8100ca5000c00400c2600c1d907010001540150341243c6443c0d41c0030189508502d0140070b82c805048103c042e0300d001c2030341c0040f03801400c0121000d079500c4905a84451813201d05028911500507518400d101644a03506e0581392289814002c0c8101c9003048140c60400c2952642a03101002102c6030610034081c034107122425a0784044158010400140f4659620345800300c9200000303c56960b070301500010910030503001c01e = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 510831366 1250 510830116 510830123
    0x1902150108250506070f02031c09090b0a0803190206010b0408151f080c03010c02010209030a08280c03030b010c0302101802060705060a051605031b0c1f060801110301090b0607 77
    0x15164591403400c1b010b045010303902170384a4030550124028081d052585902441c4096860040300f0b0b11b00400f54010748415003061354800e040681c013043c2600c0c10005003081d20310708155a0070381c80c44802d019040a4040c0c00c200800c2c0000c110a0052040005100b0081e22940081a10ba5566200d030102c000e0242c2500340c204d140311140014481200140c0109030520480003084800c0d450803050707080f4407072880320942580000100102062441c1d0140c9030b000c0c94205400300250403040c2c45403410030381044241c041a12000aa0185a40342c8103804da40d001c2804d0180003100320361000381d51441101151526141c883c110006002004010881d00640c00b4040d59120902494100d0b1a8001142c0498980303242a001980c034105100d01185100d079076494007403a58450b404484881400104041251601085004040c14082000f0b00311150302c2c0c07055400d00c003c0750800340196101070380b142c0386aa041040810840c01200e08071b0b4111010030344001604a00b071008aa824026618085d = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 510832616 1250 510831366 510831379
    0x16060204172a01110d110c0d0b040f0303150807080c1527040f020318070b0d0b0f09150909010b01050d0209030c0d08071101020703080703050903070b19021501082505 73
    0x4040c5d60803000c404100c1c61994113555a6410b40414880500340620025114803003041c00329010036160b507500703040f190080c030780840d40301c2180c10030040c1401654015006a40071341010020601c1c24084401c1c079046c226007a4801c03c2e00103041492501600c003c0790540209401325400c0703152190800f24003010080d01c28040c0740342c0c40f81080300035001112000450406101a002c1d2000041409800e0b1003615605ca030500170480299801041c5980324150000d40110001ea05540e0b541c0e41c00d48603c0f007045090102c2d044101c2400721652000c2c11801040e810b01020613410ba0304030040da41182c1d101c10b00140c40303010300170000b49402e021420481e00040000b4483c82408141c0004020032401075803180f1440f00c03103030012030780c41002e44000382925406000200000707100d08010508140c0041c1180c6402e921401e0b114216408036003250101001c10442d0b00ca401e4041c000310f0450811000d260581d50b24180c0890344030100e200f160602104000c4e40d06045c241d030010340c40050700014048 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 510833866 1250 510832616 510832633
    0x1005040e030409060b0f030c0711030709052220040f020f03040302070f03050c0d060e010515031b181b030901060315180b0c16060204172a0111 63
    0x3500c1e207960103400b444025608000c3c02080301404d01c012540c4041c01d2036006851071f600c2d024001d0300340e08810400c0310714040401e001c228541d41040401e0107042d40000000d603a0600d90800d6000b8414449800b440b0b110400c0d00502080740c82c4c2e4150030b038104881070854500d00040010300104040019104854408581402c60401b104042e600c00e5109400711410103032508541241403a2a1200601c15400b50040300d015081c440307000eaaa90713109810100d0802c409a00d85030a59601300c81603400000084e0640099207000c102c3e45038088010304400000f2115080031803890f0501c4100c0e6004403010001060f10a440034004030f03039502002c9401d5450b070520580840c080e0400c0e01c001d50380c0d21300d00401207881800310720400c9036083d840441e00c0300e41d82c0c2550798644508002480c02d03d0401d001c3c051020842844540b040d03040e0700c1900016a150700304030809a065807a00c1c071007072843e032080f15801038807625010401c440060407200c0d1941890441d00484601c0008944041c080c01000708 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 510835116 1250 510833866 510833891
    0x302030901020c0a110f010c17090109030501020a030506132007050304030b010b0c120408031b0c04020d0203180c030316020f060a020604142e02040e0c1c02120f100504 74
    0x400d4030017070046403603080d10140e21004591302c0328a90000f6101034a114201502c40c0d40350381c01024032240604020f025036030380f41c54040c2281c200c0e9586030040390f292000c120300c901d82581100e0207283d40e1002001030340c1c0b00383e581811000d140915810142400201790307050020410907500150b5000b20800704a6850b00501746040d001442686218031842c0800d082204000013518140ca07003001c02036080c62a00c51038588180c00040d241000350140d140303450015103a5000404500e4842070b009640c0382802428200800049140034802d600101d044a55617940441191005c0010414444d080030060000881e0609411420f07a400040040e0014140340c02050042c40345000da868148180c003042c02090300e42881860320340c80000c1520594450706004200c09542a5a0400043c206601c458090141c00030650705010b8404010070680d50810031140f2005070544414820340c24502d55a50260f00310f13070085c2515480340880e0700050001d0144081c142d000b4070b0002c0090018500c9003c = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 510836366 1250 510835116 510835133
    0x1c08100f0b04090b0303030114062d0403020a08071217090301090b0403120b0108070f0509120708060915010902070f0b041101021b10180315020901081f060302030901020c0a 76
    0x1003103e0360581010740e042d00b01e15000c070990b412140d4000c40441e115001004000d907542c01412074940005090725064210741640f41d03081c000380e52980006541b1411401044810112984507082c9a80042400d0100302c0030198011038040e84180803003a4020f07007a00c0703c0318174054040d40c280c0642c03070710b4501024440685144c80c01540a6101c468a01113810080e80695a400c4607035030101d01100042015182306d1a54032800d81e003180342203030400441d81d0005480804040a01290760300001e000d1001c11018088241c11060000080686040b0002d00701991041440b4119415034085010003d1003860001c80d8180380c0e0100c01c5400a1902d8a04404150100c80d200d50050ac62001900c1200850948645803160020800d142c08a60188211080b8042c401ca400320b401a5140000005911084551401d01240c101580b01c0381010001802240000d0240f006504200c0348000c94868040d854000c0e1032540c030b0701581e41e650380010030f40a0f2255101546c00342c480c550f0031005004240 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 510837616 1250 510836366 510836369
    0x9030e0915010c29010b03010e10080a06090c03150905010b060403110d02040e030c0a1509020f100912050307050706030b031b01090e071805031c08100f0b04 69
    0x1240c5524480e25003000540d840441c0c9460140802d4a844015020580441c40310b07201d807590f44001121910403007105180ca490a0b4018110048044010b1105014015116903c680c0c1100f81c0d4541516142c0b0060b600c16400e0006000b15070b03549205014040341d510140c02454011000104070605403501d1001003800c0d4105031910f501e0074480002d0340c50410215402c07240c200305050061628541005200c40030038404a034095903500300454035010600152901c003420070040c01c0812890304000f008a414064030700c0e8400d103454400401640c4800a260701c42c00207a44804945040f04026a826000754010b5101819500901010410000300a01401e44500140d4203800d656540580c00e95151244695154019980d07940d83c01580c91800c400702c80c0c0500d400506a6521141c030301100205075103035030004105411403426a50254860002041e058009055410134800d11041c03c0454094031001c00c00300001140440491404031030150038281d04000a559881e051f9003000d601c02d = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 510838866 1250 510837616 510837619
    0x207030b0a0f110901140c0c0105090d0b1807081f0c02070503071e12080306190b070602030f1302030303071805060a0810091503060c03020d0e0d1b0507170f0109030e 73
    0xd40c12130050444000f02601c1f4605600401024422403030b40040d0f501d6009540381e6604805411503100105998001e43c9010380c80350400000d20b8820034801900700001501701130820b50202c28244a110718444000050140d800e03030000d43e000c040301c812428200c3d981c0c0021341c5031042c1c035008507130030703801001c552412503c2c03040780003585646034100c07401a40b0001c409018504184001500307424040c4100f412001003901401c100c5446403003c441c140c21100701502c1180d808010008881001d04403c1c0d085188803040382c5d0303c007042d540001d0b5644001000307401003200c281d00019107010f0798400c644c080e1000400c00d44c1c5900300103800406601040394031074009207a00e0000650071b81c6511500d0004140e100d1120445419521054003034101640c8020070103500708100c2e001240f1a11075003004d00e0070240500380d58040c0d808010003480528620740c804150940c0361400064001906500300d5814007112030941900c2146075013003403962100045a542440e064408144d440503198040300c50 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 510840116 1250 510838866 510838877
    0x10b0904150c180302120304092901050c0c04020921032809050d0f06050406090c0518151c0b0105130905030a0e0a080703030c06110304030207030b0a0f110901 70
    0x2c101140c06039114650040030f10703500c41082c0051300304000c0721420003941c18101c0e4070b41941c643e6942704596036402a9031020200c0c00c54403004030461100801c0c281d409190050500c11303502c000f43d03110f200d0009110b1042d50300060040083e10340c4840900780c04c10290010b51000c40c07041c689a1a68850b40c07030780320641b01000d0b204500e41c0c40710601c1c2d610300040d65a50f540c918189018800c1812440300c0a0355001841400c2e140003903018000c4510851003404080f49280f060b10b4942c0f410003042c0c0000344110f9024503407d5140701400c4006a110010145000301c500b00300d004191450036402c0806900c0140c2c2120409002d10704c0b10150484500350303504141812548040c0003140d241a00040454000b04502d030807191042c40d41482d5200010450346115544940302480e00700240e00807000710b00b041076030809000b410300c0b607e40b40340f02003880d191030b606c0e2941d03000b034440c0d056000c002e14017014440400d4150005500a0082c40d5220000700151808105030b000d81c0e80040000c907000a0 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 510841366 1250 510840116 510840131
    0xf1c050c0102070612020c100903050c060f070c110f150304110a030f12110d180e0124020309030607031d010e0c060f0f0a03240602030304080c010b090415 68
    0x510001e01c03c01110266034500380b816500d031000d003000c1d51240020342e07141e1085c00d001c0382c1c0d0780b40948140c00305103103e920791a80e29086050a642407000c000d0148041300d2000c0200081903800141ca051020780c0084800482d50145000880a20f46030903010b8020b070071002c0071845030444100071405540a05030031015084443c0c1006640e400e10f000080020307034404924800102d00500718480c001e05420b00c1c0944a500c0b5502900d04150051007800142114034403d00a21207401240081c2c940100ba115540d03040260006d8400410070071201468007042514460310320a1050711041e4000506a550b03a003800f150050103810060710303000174604003025900ca1690148102d103a0021208040e2001c2991399080200d150401c22005610386402c00c00d0141c50351a62008240d000360503100007500b2614042114201c1c0c01d0500e014209010421040c0301580d00003050300e901075400b5440950b03d032003600d49c1c94003400c1d040c4242908400100148020000108144561711006501c200143c4 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 510842616 1250 510841366 510841369
    0x60114130b010c0f050c1f030b03030412030f020709020d05151008040b100b0c01061a070b0f0c04090f0e0f210a090e18070518150f1c050c 61
    0x150301040e0860301140f003e00e51840010010000d4411032401a415aa190311604020658a40040248544c01c4101c40d851002041d00b41c0f0504030b98080a6000314205810700400014070304031880d02400f886580b2030400c082603c00c12101c005041703441c0065441d60600c3c005c2c030f0050003013590b10f514000a5000e481c151414003800f54540140140c0d05c20496841b00d44540c00000d0024105407d01c4070103010100c1d03d501050020040748800100024910380303000d0f2707808c1800340340302261500940e0800207400805c245030340f59600800000804505074031041402e243c036202d10f40c481503210b4100300040c03040041e580d20400481824605450983d603e20b070b80140c580c242c1c3e0071000c260700c2c84408150510000b0304041c1005030340c1740c00c1c10820706441d02a420351440040300c62582d03030000401c7d1444150310501c000030040000795552040c2c1e11083c040318401941c000c0c002d607030380c84a070300c41c104681e5500100000034200203001401490030280040d600c2403840b42041e50b0030310403e0b4440405 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 510843866 1250 510842616 510842621
    0xb0a02120a09030905030d20060601080c03070318030e0a050402190818060f160c03080c0702010c140d0306051512071e05040509090d020d0f1106011413 67
    0x4140c90510303800c85540e40d4841d00004003800801601000300000020031a52420030152216418948400c1060b1040c01030104000260002521031500f0007404e010081c1d030403141c02e94100c000340c2170241e01d940d00c580c8200e004040010700c10000c2c007402c001384402c5c1a007101c8449814201036420000d02901c410a0200fa842108000c07100d080301503042044d0785102c0e5201c80d4028200903140582d145500c0c1000d80b82070300a071042c0007809505000d0000e554881079a40405810a017840028407890341c40c007408040d4020140c0300040000201c00045a208000a00a0a5010140748140747c2c0c0440401c1c0d6039800910000042850080003098520b4090240034440c01c03040403451601001800020403807601074640c10510240c02c0c14003580c28203000c074a20780b0b460503030b456a45913441c2c0b1040000c49480038003440881e81010307450300c0507203501080e4104600d119003844080d00142d00b901304d40c80c1c00000b413000014001c41380081880504180348039032000e01107a490980281c0c070079000c400c = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 510845116 1250 510843866 510843877
    0x325020106030c091a09040507050a06020105040209220203071419080c010315032906010305040221031e030a150602030702130605030f0606240f03090304120f0b0a02 73
    0x31108000700204071000032034001207150010172524036820f021034008900045825031302200e107030700030000c00d0069003014001c06d0b00902c6280300038080d50602d9000f00b0f024040251101460444608a02d143c0e80519620400c3c440d43c058110b49480b42d8483c1220b500002100f0300c2c502c034080c078966a141c03903405003c480c0c050b0351064001d040d811402500550007040420b010038000c1e2202100040803400c000c140d204006207260900c00c10189441d500014410001c1051381410302d400b003400701588415100c50807041d0700c0c10a8000005102c40354501d5400f0720346102d00d00d440302400300381c40800700c43c011f180561800343c000c0c010f410800803103840891943c054080140d00034088840036103807080821001030007200c00003801a8407000480d061610000003103184e80d0080c8180079190420020722025050850381072448041800d800b036800780304925682c12220004070103d01017840500840300140b8041161020351032241c03900025210000030242c1d104000f040c0000c4091880d4001c950 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 510846366 1250 510845116 510845123
    0xb0c070f0615050a0f091a150405040506090c1206060d060906030b2d06060403060207050604023307060e0f0a0c091503020d14060705040e0a0903050a050c010b0303032502010603 78
    0x4085c00c14805000400807010a003140d410020380306a2079895236001c006040c2d0703400e00c0710744d40c0350708000901c82a10400344c241c40c001d50001c4200030600300034505844035040d0500004140d03894480000b940380c019005030300751091800b00006040c0800b6400001140d11506200c00650380e0007420707100d0301c00501c10181445003030701e4603201a00885c030081e650100c0c0042c602c034101071f1039840e0a4100c0c1c20065040300c25600c041d090006502c0c02044a818064043c040c0c400350400e0b08003003a00300c030106401c912400a001c980c01040007401c0d001a07550000050442e6480244040070982d0f5400d0b81d0801d0322030605082c0049080702d200d01400c251b02e814040d104401038610350920412860085050f104210b07000c804219242042c800c4c103009400750b59541d0344a50500070041401d49018003d01c8000b454101d2803c0001d801605941c2d072220242000303902c0388c15041105015200b0b410205034580400003c2081d400340710510b0421340140c080c90b1440e05a800030059088401d68040034 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 510847616 1250 510846366 510846389
    0x40905010e041a041505010303050c1c020d03020d0b0607060501031709010e0f060d2d1e09021f1706090f061215010b0a0206100b070b0c070f0615050a 66
    0x103000080c03d5031034068009120740108441c014840290301e00321102a082140020720006103008840320030885507000340078014a140c41e50380c100074003a541c1c442c01802d40c0e06040c0c001c2002074682c00d01760320401182001501540e41c03003078280b40c44402040300f400211003100c1c1d61800441001014000e84824141c10786560010414001c10481d5440d2108445540254100400900c000c01802610303031480300400040140e2540b81002c143e11645920b44800103441c2c41d501e0b02003070001488059070854004000901e4144a0011407a0b40b241e0740552001c001e4000003c1c600c0e96031003a4102c450b0901c0741e140400540790b1074200010620142c6403011208444404100680303071110000340309607c000b00704d80305000480100c0855441c00d83c03103000062408101041200e8043c04142d078094440c05c83c0441080c148092a412030040090140111450703000003404210480c08641e1410f0f004072505603580741034903001c0301400d02100d2141c030200f030700708000540d4140042002c06942000402d17 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 510848866 1250 510847616 510847643
    0x304050616080c0a3c0809100906030f060e1b25061d030708090a0b0d0518030915130b0310031b15030c0e040e03040905010e04 56
    0x800146400c422030700494103882259070000285950000c040381000c50010b0319503501141401da5041c014104a0190351040e0612000c0ca006611902d00381003280d100da0b41c50f42e014905007080e560041c2c405a030303003282c5c910b5500b5000ca60002e4402d42103d00035076062000003106541007058541a200e500d540c8500c4001042000540d102c0321030101d06041711890400b1104501c1c55a40e6100f08a481d19144003c043d843c1031014502031441c4082803192540d00350800c0215283e5280b042c880054100000401d51160541c0d851400c00d008004101e0b460341c503083c1038006000101400c1c2d81c0c110218860071000800d19001205455040600601e0701c11204245407000c000d6038400a24602c080c91050400b10701c215640016501598010b500000554110325011310749a00b0041f041d000600c0301030081041342c040386a040520403143c540410740c94030040055400e03030f80310781c1d0f0a64003506002c52442030140000240045031140c01040c00b69981e194942c0c4050340d4255400b9000c2080d0828 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 510850116 1250 510848866 510848869
    0x80c04090c0302240d09061107120804031715030c010207060203040603090206040504050406050f01061707211d0c010c0f060209060d110904060b0a02070e0c09030f100518030405 78
    0x2800a50b110141008030741c0040300c07244001c40c0d031000000c0f03907415540741b00010510805101d420407411180845034500710540e100c5914081070420b41d40c081001c080005010035109650f03168500c081d10354005194204040b051415100c54001a4060b05c03c519010615610000d40d800850782d0940140d03151605002088000e00901c81c2d003607800c00710400c030010b125291441483d00c61401100c0000f07660820917500040b605d41a03020204104040c010540d4800d000342c034450b04200d282c02d04004041d40e0380501000e0700c0000c0080002503103080388443e071103040c54407080065203100d0280c44c04043d0000056071110903240002d06902000903036100016440c2d03000b010703180d00050149041010901e0b800c400e4500c118098a0b86a8000c900d00240782014020040a00880c110385800c0080f0118000e54030210341c070580703480c000e8190121781441c194400301c030643c1c06d0150907100940c205d02078680d40c91307038407e45e40c6040078a03000000c0c40703905004c0c04803220401304102442c90180380a0 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 510851366 1250 510850116 510850129
    0xb0933060f03010b060f2208030d05070c0b040c050312040b030c0c03070f03030e010c030507080712061e0f060207050a0b030c04120609021516170903070807080c04090c0302 76
    0x3040c1e5425650b25041e40c0305036503848000d02074401201040a98860102d08101040300044040c06c0781001c120342e0902201d038000c0203403003403102c852200241980d2014811036004525a0001d444180080300303100030301425455882c1601d000783c08541c0501d6424450240a1140d84111301300c9880a101040c1c1002044005050120540080b0303410704075507031940c59101c01e6200c821404650740307514a4403400707400c0c0039501482c0c0711800d04005034600518040c021280080c56032007013102175004140c204902d5402080a8543d800c01003a41081c1c00761161110012030013050800744140600080c01440050740760150b450180120710300d03919001c80704210307401c0504110109802807101052424203260f0072400103014403c0828100e0460041c410301c4000400b80c28220b090420404038080c1040c0040048603078400d044100d0b0600200440c2c82c240110402c650b03041c0140500020310450001d04401640d40c050280d503100041c01e41004100e0700c44a00007041c0f2a07480004101524060703 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 510852616 1250 510851366 510851389
    0x313082d1821030a020f0f060606070f0611030c130905130b041406070507021804230a05030a091a03071d0103090611040609050d02090c0f070b093306 66
    0x84040160003807402c201c10381141c2026008400503800384090001002c020410000b110800501410241c20300308003245051050701001740102c52030412900070040d050b4840c049072404031000340d840342010205102240d2102100001d80c030548400070900071000d11407640034010f588440c0002c3c2070300340e40b410500100204266280c0031904000030241d03009100a501c9800b8070703928503607101514030410100c8d205084442140c2d44071030301004005401c1c0c10400400c400d80044000d144661003e26a2a0254610b00202503000101d291440190880da8250903551481c80f600c1c0d080458000c01c140600040303402c4000240d40b180040313034160681c400050421018500071640172a10784800d02039440104000020b200c0000e0304021040c1c1c800080c401503c0c080304c09034607000b0743da00010ba0040c4040c0245000b090001410407103032440da8215a881640f149080c5014540112119151804081400612240900082c407907040c2c502ca4140c003c8041030450355551140b078107102888558 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 510853866 1250 510852616 510852649
    0x170c030d0c0f05060c040512010b130e1f0207060c050a14030709082d0f0c0f061606020403020f0d0308041103030c0a0507050a080705150313082d18 65
    0x142e510a0300416418410729220b40041000e003661a440c1c101400460030a1004d580b086900d44092021140d9500400d0700381800704a1000c1030b0004001c4c6c07041d003000070b00010805c0d50700c4220704260042c0c100350040c1c001140500c100f00302ca05001c4a00303548911a484200000640700031250004031148005180c104c8054031f05080d21946528100345040b00022846040806800b2207004540c0d80440001c00080c03110054540e004552a24903540d4400e42c4101d07200c0ca4070050402c510381c4440741941e07800c9101c0c040005c3c0610b0b090400380000d40c0f040c00b059008651442400701241040c010004200d9032683c1c03500031030381d03e0f41c41303204801c0c8201252540c507020400c11006181070410584281c0c5000340003a04200745040d0410481d0031490b070080c101c5400c401d100708507694820f000401c1012182840960725542c1701c04880a221099130700511900e008a0030001004810040060034441143c507680044080711030061640180c080501540004680100140c00d02e0a0074000314a40c = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 510855116 1250 510853866 510853883
    0x501030615030921110c01020705131a0d0c09230f09101e0b1519090308070c030203010f0b0913020f04020403030c0b0f15090718030309170c030d0c 65
    0x1005001160051501c10003130002846146107400404401d004540010300f00b40010100540740c00c0108082c0c0075194400c034a106d60718802296100da401c290b1264441c1c0041540e10b0400c903500e8501c50310305441c014605003501e007005140ea41250922191414010303901c1c0c2003950b640f20100c110264200070300c0c0c00410b0090100108100c8400e01072400720031003001b800c54110010310190b0040318450740500d8880c0f00e01040358400c803402d07501200d0700c8102d01c101040c01745010703d03c2511203611170b510080a04200140941c184045040900c090324800c400031b00c5548114003584080d40c0c01c160309d071076124000401003040141d20031a00c0380311074806172940c0006914a03002900f02e0300564800e4000c685030300c804108209100e024651b008203501d00007205410000b600300758040700303400d00d1f82c000c03401140070641150207854055002d803143c4059030740854891600070006029840748401c0c50034503090008408002240b036546190707000e0024607200020070740c2150100c00b201020f445050 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 510856366 1250 510855116 510855143
    0x190f120b031906021903060e06011815120c021c080601022404020306070809060112020a0305101505010c1509081216120203070206060f28090605010306150309 70
    0x4990380b01d0300e08200d000d45001601c6120121901100e01038418110007050320f02241070120ba0340d1210900e400070400c0c40d210442e410f41208565242091f40c000c1a0754007400d041e90707103007150310001c0313240240ca41c12001c1c050895520820307a40c40035207104628010250b202d1423652240301e0185d650340050144111203610003007402d0f40664900b42408000e1500c1003008010035818104500750308402507181040c02440c068118584440041c000c00050300350b83c1c010141550b0380c05106002450300f190a07120301003518541d480c000c0a01c4a090a042d0005000002d56580120018075046400405582c0381d42c850303002c403d00400079004110707206c0e04284107001000c2d141400180c400c600040e20011900a83c0300050072507092141c484800078010070810580c0d0b94086075a94100358240c2c3d48505101c81400010b04840c2040c0f0440380903940840e070715584003204030a401c2203d0002804203d04c5842e0701c011000d41358180501051010f5400703090006902c41e41c0250300c0a13001d80c3e030030400c50 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 510857616 1250 510856366 510856393
    0x14040e0106170a020a0e0f0a0504020607230f070b0406050906040b0408150f0c090108091509010902010e150412060603021503040209091606031509050c190f120b03 72
    0x705241006070b0202c2d440300307000d20110305000d80a640607005408890a2901c1d200c40310035401d4030000c2c02c51a1154403180850110349808080d00d041582c03101c80415400321501015801524058155286101d101031005541c0d4011900354243c03000703100b47c0c40c501410710a00b070b505607010850031500460f0400000865103001000f8001500c4c00340b0240c4225602a120700003840d4002c0c162440e180924400d03c5802881c0200f103031240b40081c2001c1125079038921142d42820160b0151240c14225281000040a019070220903914403d881e040c00121000707040c005a004a0728818502140801c818000c00c0610515034513142d20075040420300907143e9000c02d004211840c4540c01000c00400cd020841c0b62010059501159503001000da000c40008134001c0b5003458490316050596642214034550181d241010240c036110609001d9814046d00345a165801103441030101200389210104d0030b8410246403450000d40da0b24015041d41d00c10722000140380072101a0b50603c161b440400c0c40 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 510858866 1250 510857616 510857639
    0x90d020a181b0809070311042301090e0c060a230c01021206120a061a03011a0312030f010b090a031407150e0607170418050403030f0614040e0106 64
    0x60100c071000108601000340c088030420511002c0d8882844070840c10030608000c00101102100d4000c4543d2603a4500c241c0891f0040c0005c0900c20080d9404160402c02e1001120100b41240d80c1103804108600c0d10400b1781c1c4e01d0710070280009920030410020001440c0c07084041d4100d219046c8401c0d424440714040500b0709600c229402070050b500802c849196500810310941d009400380e4030129200d20039021551150b07041c51000b40307180c0d1f8031a940762540c01c90304022446100054020404040340782100000c03d80c03180c80080c864804c401201d03181400c5501503d000e50b048000544e079076428a280301e40d15403c815611034205e82240000000310f0101c000309180c002185001d042a68106401e600303800a04001d62010b010a00c24140d040303031902070071550926001f040d5100001c1c42032101c44040d20455019854048000341d40541c803c005911040c0194031035203040206607410280b00b0241c2d461845852100c3c156110141c444d03081c0342c3c000300384a00340c060000170030a8584a00d10f05 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 510860116 1250 510858866 510858899
    0xb030702070806180a15020904020d052a0a030b042c12040b04060810050406081b03060601050304060c090905070c020103111305150c03070b0a0c030501050303090d020a 74
    0x1079000310340411034a03805101c040d41101c801d041d00340402810b01c412030780d94451450300500207880005186940441035054503000a0020025960303400c5100b4a40090003041c0c45401c0c260b515400c07039070000e40340c03d82c2d0304100d02403203c0e15909103810490260000c19400c10302d541c205444264501003030910b85000c00305194180300d4911403000d008075891425055000c20401d508003044144145020082900c08032155858036194079030b16459000c0b190315195000503001420050f010580d54004207210056504503061280f80030605020195603105c141c0c3d006002c070300104041400305840d504007220900c80b904200c01da1a9480281800b240e03000c071003400015a10425203000c540e45802800700102140b0102400d0021000894590583c2841100d20440018419960341c0e207102042c0c40304242824166500d6210504040a940808581e01007541345407140042005000e88206070507180064021400e258094081c040000c0d003200040c0d9004004c1440001c600045401c1400c = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 510861366 1250 510860116 510860131
    0x8150901030c15020c061602060d060f0519050906010c0305070b010603020406030e0123090a120201020a030f0203040c0509090721120c0312051509040c08060a09110f04060b03 77
    0x190030b4541145142c44600003c0c0c44011034014000c8030390f0982d01c103c1615040c1000720074000ca41c0c1242e10000d00d00d407107503614803204135040100008580500b4200f40040b60b005440d034518002130450b002c0c5414901d801a5030b4007520800100344076503c280028035403d40700b41000c1d4035240103522145001d070002d0340502c0009800250900c40503074036004100b000b41d071000085c4000c808078122017001558561040801da0700310340001304440020401d45d1503094125880d040070302c000c844024040d6011803440408207050003c8240e60704024401c80307118981000fa4183c65a08110030041e14405c080c002e60b40e0342c4684503000c245070403444403151840c000d043c5404001c81d050310f4103d24442c00e40c41004c0030b0025800000000c00d410031090303107164000c0103000480e0755552441c0720000d881001615002001441040200460004003809035105034044620030b54600d0346010907210440001007520044414890071814069a000c0c07068078010030108420780c55038100c1045402c00c8920a = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 510862616 1250 510861366 510861383
    0x1052203120f090f0f12170406020a0e0d0c1d160e010201020c0706020109110d030906080403120915050c0c070306020705070305120d0509030f0a1b0b0a0f0b0306060f010815090103 79
    0x381c204104400706c20341540d502c0c1007074004450400601420b071030700244007070700a64001544c008401e2107003100c0c002c480402499030100401a0a01c1c024103541e0307001d08041e000003149100724186543e030a2030300c0395484850040c1544010b0100701c403c00150118241035640a010612588806209502c0503123083e500004006485007411000042102682d81c003a07a100c2e03c4840102c2d900030401d00030344070319041281040d1154a0122030340e500d000142e00d071003407506d031644040100f0200e4a2854500b10702e400d004c41d48134034800905c20b20072003c900000d030b4130191041001400b180c010b82032590180050715422a40ca8a4081c18440d029036a051510000502e14100d4031048c41200d0b000800c0000450070714081001c401c086101d0707150100c081c090030b48100e00701201c41460002c1ea4641c040041207903400c10b1410f0307002a1629480c0021000e040010341e401c0e500b40011601c0c030404006002d83c600214100064402200141107000b55424645002c07049840c1c200d40b00e8000c5102e848503 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 510863866 1250 510862616 510862643
    0x6110705100f081501080403080c0415080f0610091a07170309120a02070b162a0918080a02070b0304030e15070209060405101701052203120f090f 64
    0x404502c8000e248200111400c0b1382c41c941c9982c0311407a00da010b50b141c02c0c070b81c0c2a074945c804440010300569005c00e01c0b40c0a02036110000303d511030b58440c05491460050344035038a4003c200700c024001c0340654400642e88501c01c0004c070706000380d56002c134500c00c0b110529001d0951586204000541001000054000107200440034100510608140345c0c6003941d042940005000b91607081511540e40f002c50085800f0340a0071883c6509002aa03001f440100084000171404040d03030f0003e0440f1010a80840c000240b40020f80910601003c0303401d0500b00e60380440c0d90303414040d08203040700750071489015001301e14074850300015400b45009480c0c07100c046c001141081514500d40540c0f802000d01400000c005840740c4200c0c5403c10b0702281d0104181d5181c0b02c0a042458056100c60041038001d0004146d03070b581907010300d000307040615108407050214130481c112201440d4009000507502d203001c0044142a40c07000718800c51a00d00414000c2d540e03290441d02400211040d01e0070f0044151 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 510865116 1250 510863866 510863897
    0x905032205010f020d0c0204240905060406080a080d0b030f0304030219050d0201140f0a0c062708031018020310090614190509010e0f09160611070510 66
    0xc0c0c80008050034609a03a4100580000a4541c01103107607035818481002444411907440b80c02090501050203c400700d1110010503d2002508902c10309103045e14001c040340c5103003860b0040300c0075661904014010080c0a43c1c0f03201850788014400d010081d44c901d00007040342d80a0101d400d0307490488006649860840c0100004a4000c01480488400c140020062030701c0d02e641d051442c64090030190b2613001c250980e40028130940c80d040c4612100020491421a004100b1782039181c01101d007081405e8440e101c40d505c00705401b499a070700c81401b5150000180d20440119440b04075001a045082d81d51040042c04115a0707405100a035000310402240e004064a264000d1070380a0092201074540a124400c2e80e40c0143c4070307400b403810580d00c0c44941801041050003000090103120b001c0d82c0d40d0480c10705a103002d0b01c100a54440b444003180342e59000240002d04005c001c030f00f5000e203900d8040141d424070f2000c2c8000286021343d20000074203030f5621384400082d14031a1a2a10340f40b1142e40e = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 510866366 1250 510865116 510865177
    0x63c0504050f07110714011815180e061c1505040f021017190b0603011d090a0c120204090b040302060a060618060f090f1e060503090619090503 63
    0x58407134141c0d620415003000581c200402005142000b0300702500080401d082001c1030a030207030040e22450784807100500f4a00c6c0e000081400070712645400c0308002d6116404080000400c3e40c0f1030707612100904103101c00814071011035090b244030380c0002e01d800d480d40d170307010003618000c035070594522005c0320400041d810322000b003000c00b0182d482d1041d00070b55064416401e2003c050000c44900c480c3c0d5062020f0007501ea8094a026070008214645030360351060b03807107464084c5a88400821603040007080f0030b8400060f45038540c0368048110b50800c1d04042c030389411540e1454041c2c6e409030b01e40d080f5401050100f6a1240128000e030301928461030715100348010b45015910800c20400b204030b10041da018100c5c80e07001540c5642c9440e003900c44102a04840c80d081c0c0b9003081120210514000132002130700e0340c020b031000036001065012141e4540b015a01c2d400b00305e9010986410250003e4a0b50048009046140301803040010700c920603501d40501d19001840c4a603111950002e03000785517840e90 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 510867616 1250 510866366 510866387
    0xd0c09061b03120e030d15080f070621091b0338130c1205060a050105010215041b0f0509090a030903240c030b0103063c0504050f07 58
    0xc0940d016074a8090303030000e01d07880a1a0203681c0c01583d8454440840c00284201c50a07240c458505020b030310400c0e074030380c0c2401d50a8030032020a80b01e1a0381c01848850082915421680c1d19142d004044c5000b1000704500501007078100c1e40b1503601c0140500203420b0502d540c41e211741c1c60300b004001d1400d51502c080b60001000701142171980c01680300010012031740c100403601410220404107501ca0500d018101d40c0c001400400b24400a0804079440c007460420007403e5000340304403403080e00e421107000c00f255028001e003030043c1c1042d1f40e20406290421512a00184982c00d100600040c1809a91104145070130205964000030000c000314038004280302d4004884201522820000740e5018094090364070000b4451100807050312060100c0720b5022100d0304001509100c100b05012005004110142d003550100313140040118440544400d40c4e05031025400c0c000300164440c100700e41c1000d4120501142a41d18100041500d441d80d000351800b903c4859001d403511b040c148005421040417 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 510868866 1250 510867616 510867647
    0x1f150806061c110a0806101e0b030910060909020a0504050c16150f0902090f1006050d09060207050f15061003021c0608061e0103050706030507050d0c0906 68
    0x11080c0146a5149400c040120410100120700b800103454450114280c1030701d100d0740102c0d410b81c000f82c00c1c1c0011070700910a0584091882c500303510b41088184440320b070b640c61107032460f41200500c00340d0380c0000115006904c1c00c0403210800074010416003515500d401030440f02d45c0321048941103051024192018080840d07080c0142d1814042d4104c0d14052640b0803040100c0c1a1016018480000340d041d05c403403464901030000440300d0030000f0150603040340c124050006100014001c1d4100c8030440e0040c022070540d420fa592070110f00700c85680212041000d066911001200041d02074401016064400c8014000300e04400550701e0a0445487d05485100081130411896030340b90024014004043c1c1401602c0f416484520300c001d12608480c0c05e6440d1a0803004504040700083e814132550f92900c2d80300c944c6004c0b150110081800b844020260792003258140708003802a00150313480300327151610354180417130048100300f9608000c00321070221300e02c18070500c1103580c00701541d43c00310030 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 510870116 1250 510868866 510868873
    0x32b0210110306060a050705070b211506030a14040506041b060212030a0902120604120336050607090f05040c0f2a0305190305060d0b04051f1508 64
    0x114080703900500e100052080d071080200107405014140981c0a80348101d410a08079945262107400190301c0f5841009510300003501d1f04212110804404d81d182c1c402c0e0a000c0411000d61011805c3c020603400162601500c5a01d4075102e0010b06030961005105d54083c1d030007402c1070b04250400024070360760340c41c0c442150f811521027803200b55000121003500f00e0704240700380e0f513039a0350607003040061501d0040254081c54800702e0380210280040e019003d2806540d40800300b0005150580441d810006902c00520708505442102c10f13442001407840800000c100103240001e03501c846c02c006c0103d4a007400305a55407014401d080000104602412003030b03904011806c07400b040548100b440002003400c00407400c2149a0045507001600c05010700140144c05c10f030350b281740182c0660020100300ea0400c004c499010202403190240d54042c9a01a2484582813600c0d00c80320000100100140d032184240c1ea04000846d041c4501501002800f0600003504109110080122469580800350991 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 510871366 1250 510870116 510870131
    0x110a060906022e0e010e010b0913060f0207120206041e020a14010201110d060513060509040209091606081509040302030a0c051006060e13060602060c09032b0210 71
    0x10b40010310111031031180b581002c25000005030050040601c02c0c40110b0070b906240f1008401441500880318003a0084001c6c07204003410401e005000700b0840e01c1100201d5400f642d400801c01035030002941c522920409441c00f011034440005440d00030a1300c100503403060703003000103010031182c003440200c90804103600502c010f6000250440324901607003144c0901c2030540509a8004d500100f041030500783c04daa01d6085041013040200711724420a070064040c5020440104068800c0314142c43d00203004a41c0e070f40ba13039024000746850041c040030840c071030130f03004000c820104154076008065035a1742a44616054a409501414106c4624000d88409040c04002030b0040213880e0014080e00d0300e4481c14296080180c5800d6480c00a41c000620301200450a103511131b6512294540944913007190300c44c0004c0e0f041c01c4078503511402005030001c00204880000c640024030003290f0040458004101000c2c0e000d00202c12081d211541d84c864035030b091880c0d901407111014652050b0f10400580 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 510872616 1250 510871366 510871379
    0x70c021302090d0b06312022030c030c03030e0402070c051002070308030a0b0f060406020c0f060d02030906160c050c06030402010309050d0207030501200703031512110a0609 76
    0x11081c003c000301190080c0c400241661600c000c5d8400c80a010000840d400c03402d030901c0607920007020001090641800500386c4030907840c10101c01607405140501e03140c400c0c130003440c201c444005495591010203020300080460070402040303010394040c00b0260310803440c524001d045541e0b4900c040380102d00501415011504141d00f5030300b2510f054400744940c01d0070450490600605800007421144013000344a0101000e0307000d0707034680c00300761043c80c44445a181003140c20b001c4c510132170f00141d00c80b2580c000e5505120120403030b05d0801400c05400c011a40c1183c00c1680c0003240c250185600040400c0403c48194921204003d06070411301d241d24a00e80f00c21340c0311000c403118180a640000041411a44207520591503207400c1416580031020680d402501c0b500e051005503055070070a0380b004000f240d1010301c03c80c50300842042600e0900c540d58160040c0034542d01c04029602c3c00200061503210341d01c40b0484036071082c40790f000701c4a140d008020320715101e0b401c084c1c00c100c001d10041c0040d = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 510873866 1250 510872616 510872629
    0x3100e0a23131202070527061203030a11090a06020f0c1504090519050915070306210f0b0a0c09080106060503070c080903010c08010608160818070e070c02130209 71
    0xc68000c030b843d9194507690700041e0710b403180f6540020f400c0b60340b1a241020700d603152226a074840c000d0349100c01d002d88a000421017080304440c0c5080d0260400c00102c0c10242c01a400209604080030440d420202400000344c00c1022550010000d0b8000860301c0521803018441c042d0759090482d451000504d01c1c000c81c1542d0b01071400344a410a95550105041c602424a0703040e805854003020700031403400c040000c3e00d40200040c10320a009114006c030350101c4c042d01901003039034012010b451210029018510724104911000d8920b8000c80f001d6030040342c90360040e14400e9412010201d402019600300400200a552190703c490745805020320160f0350105c01c880e04800c80d45400c1000d00528240740300303180710700780400b030f070541c030b00708440000c1500195820304941640e02c03010b1172666440000180f080810a41d4000584600d000400f6070440400001000d04001d00303e5500c9a1030350340010000206070b8071200814141e054400452504802a0840c002d10f0302e4158200321054011564 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 510875116 1250 510873866 510873901
    0x203040b0a1a100c0606080d0f0201290f0301061412070315090812010f03060c0c0201080414030403050102040e04110d03020604020d02040b1c02100c05100203100e0a23 74
    0xf08480408012000900c542800319a4030740003e801c10809985881c516a00c1d408107101e20042810300f0b08410340c030b600622403400d007135103020803a00402c0316903a01d19518491840000c0c0d401690301401283c87d44007442118060040d8080d000c035841032072401c00c051444000d90031a100e41c82480c1c24000135003920003500e6540e414a201080d40070451800c2e2485026070740041c142207205000008241c0d580c1c0847d5411640a91000c00601c560128112854400c0800181c04606d1340350110300010b100d150414a409000c40c16207050603107035960f69099a105a004415489507031051006001d84810707801c900007801c40e142c68034800940d0f00691200f80060019205100b15000042992140d8100040d2884010075503040020403042c8000344188283c010380c01703412100c0900d00c04901613004890f000c0c0d0044010080450203e81c01c0c40a50b0004000780080e510171b545c00650820340c00030050044181200104000b2610f007010140b00051448165400e01c050080c004880c429080001 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 510876366 1250 510875116 510875119
    0x14060106180308120a111204020103110c0613081309060302030705060a09090506010512190518150901090c0e070f020303010b19090b0d09020a0e070206071d10030203040b0a1a 77
    0x10f0b44c2d5500c2844220041400381d8460104420000b885e04a66400071a1540b04074400d0702d04001c04030aa141c08a01c034080c00340c400c00190700420120b0035140a81050290103845544114076020400f9003d5085801a5000b0402181ca40905004628050109001400040d60121f08050b501000200300780382c030344907032140280e0300c2c00800c44c20b9103e42c1c115500c0e071411034407201080c1003151090400e51200c524220956281001140d550000302e140c200c13100060380000c04503490340c3e944207051980701609a103410741da03410b940c80009040b640440d00400c0500d504941500c1e02d035401a0450b40c0ca14591070031034004100501003a108a8295858094a034031804481c0010680c161141d52854210a540503808500ca041405407900012155803081e10a03420550b601c1800c010f8122085d6070f1440903070402c10020300480e224143c0c44500c03180c03e06100a200000c0e001151623035100b030700e50100107170b00081000240800140050b4021a18031020001110055011000e4001d19282c03e03 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 510877616 1250 510876366 510876397
    0x303010e0c0c010501320f06090415080604031214281a100305010302030d080c0714030910020a05150702010209030321010e100b070c0314060106180308 67
    0x20380030045101c1500ca20107020002008156100c4118401550580c2c1c9120707082d1500181e0000104041c07030844001c0ea01c09000c1d000407080d01020041183c01c070100994025560b50141450b62015003004001020000041d00d06400d060400402ca030000405554102e0300b40300d1524460100c64204580c0715200c0c01a02800801000309044610340e0011881046814401c00040c1d00103000c001c000d10240889a441302040486000d509807802403201940c10380100d0360018056000c0c0b01d0003907004034010314151a00341c031036590b000b011208440400040e400815021080e04207601680102041c030b0008044000d0709541d55981e803070400000904008130300d030101e44a00d000350140c1d03808010041c140c03a150551541513030000c2c00c690350302c0c4841010f0345000142d8074581d01f01d0540a441060800002203003081002041a88081002c03107031681910400804a04e06081e01701c00e20010798040c0103035500d0314a0042c42c11008210010368006243e10401c0010006000c0b142c6158150440 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 510878866 1250 510877616 510877621
    0x3121b0f0b190207050d09091e020c07030f03030f0b0913171e030609180a03030207110a060c11010f020a030e04060312020d300506041e060513020702030303010e 71
    0xc1507490715142c4250300035a030022450108110b4089180d411002c01561612041070b5280001d074141d402e110f5860a440b0350251034805428403980060460201e02c1d004c80d503000d90340b0b54608212440741c0c4000c1e40081e94600d040070a100b500c0c010713103140c1e40c0111402e904078113211041e0b84d450320140500400b15146003907010010708640003030724103034111441c184030504c4030401d6484c4c3c42d40c021100e80d4443d07481c800010b184c0022040c01d03068001032a00c01802285455a002c0d0b0080d40b00c003c0556495a0b0345072484102d0340d804041c00c0240c102955103055240d01491b181844da21101c207801e050103d520780b4124071640c0000d840c000c0941510349014048410307070103d4010304481d040030304501e02a8041040443d000030720040c070300083c1c1e691040707a001c8490201400000c543c080e0300289040c1001c0c4d00c0d5a00140e0440c0743c010a0052000401e0300c9001002d8000c02079007011208a5611020708100790301c0c10314510180841d1144095181210035800a170f20391005025003400020360001 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 510880116 1250 510878866 510878881
    0x11d0705070c0b04120b060405091f110d0b10090e0a0b040b040507180608011203030c1704150c03050c2212030c0611130620010603121b0f0b 62
    0xc2c10002402c806400c04d980d10307240c52513a21440c840701415102e41d04208045070040c00c2c01d03c00c0780c0c800d03040c20001e4042000000384151192941c0d107050990140c640315101c412006800041c00e0480341207000103000c00c814424003d80605c01450f41e810700c0b0391410100a254010f030303a0b45a20a249285c0040c910558a0008005052502250340c000b0b26007820080c10315040002850705244084500e03200c00c3d070314401100c40000034007902000c0d0900c006141d000034080d40103102c0120b036a04025050111040380f104010390222002e556200c0752140c0700100d02c44a11076180e0780c19846c0790170701031f9240ca0320403580180b1409152184040140815410b280c2040900340080d104000d6003000700c14003402d000b480b4141c5044103a4001c1e00c0d082d115216800740e030086588249012503044051071400344256441501051049610000c11440100d011428071401000d503104100904070540c80c2840180a0394420702c0029440828800e5400030840115004030041d51106414249075165034 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 510881366 1250 510880116 510880133
    0xb06060903030f1305181003060b0402070212070f06030b0108130323030406060e060f0904060b03070303080907060903021f05091521061c02031e070e011d070507 71
    0xb414052200c0860b04c01040e030f190350540300489004449403440e14040c5c684001070480d09541d100d500c040d85050800015542d83c01c0402008001480141810360a0700450352046225554034119001818144045040070341000c010f40214a0200451344644c00064650040503200702c806d1000c4c00325440404d072040c1c40500d85041d900c225003080007244414640326800581d000c84200382000c03004a1703140b2400f44041e01c0364070002d2034004003e051005108888d40050400d458090311980c0110958138100074110085109640705615031400748100ea0414000342c1100b802c114450300204056640c8101c0c006400404a00c0e880300e000340c1038401d0341c542c030803038810b01d03044030400800b400003003081d0000e040e00c003081010600703c404049446402a11040383da50b5445030b81c1e580c5c2c0d01d00042030340d07030725030105480942184e1003078040011b030180c03840601c43c2c03030f03075140d0700c4540e090140380d40f00c1040354014455498506040181c40c018100c13802401046030f002c120700411820140290003 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 510882616 1250 510881366 510881377
    0x130318090612141c030504140106080a0b0105040504030807050c0f0a0c0311041512081e03091e030f0906070215190504030507090c020f0601060e1206040b0606090303 73
    0x994040000c641e842e0b40710755100c00201c009903807070341c8096000340c49140086540101000d24500e07102042c00c008000790001c0a011300295014055040c000007000804d02c906406024031000800c10005075282080c000d0390140c002500031424082404006074104855940208050072304c6519454103c1c1032170f103013510f409a00300c00c1e88180302425042c800c030305c203da2050745d002d001083c4c041c4040c0002e02040d1851038648800c0c52a5200b1b0402c00c2c0c5010910318480c80e0322414884d0310302980074407409410200ca0a200c05a4032000050000b281000c000c008a01051004012031140034510440d481c2d0080502c41044404002007015855940b10101e64145a004206895007141150301d0805500306901b40e40c03098401643e440c86030390042c800e44040300d034002c00401c281c505000130f00028102582c400d10551050072000002448207120844c064040761380c40f202c0c1d0b00c1c0c040003003000102183c441120583c220405100104a400300083d501940a886066407005220003192452044 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 510883866 1250 510882616 510882629
    0xc1e1e1206010e0115030b090402060a020a0209010e0126100507090308190e0109050a03260d0c0f030216030c030216140405011e1401031b12050f130318 67
    0x1c41c40041a43c100016040381a11030b02d403107071805440380e907500341c040b0341440302d0340340d44101c4050028006180400c01070104168510646900444560204540d00c4080e0004891000078400500a4070384010058020344985d40881146004102c1d101d521340c030503185a0f0040b140c942d0f0014640d03900030080364004650209880d661810810342082c0301400700c5a240000410710000110998481c100e000c0a80e90010b0218a0703481c0345a495803405280f55400048101c41008003030358080e207460140c101e07a9078030b00010441070200c103070060102101130041e2050620511070110980d88525015030303c3d5900d1301b40f030b8900031000e040991070b02c5280e46d0907068400701c0d2180450b50083c0342c5c04040d140d00c4180c8007030001e6602d6440d00100d1602e491244003488000c0c1ca4100881190f540d510503034144107040004921410f02c0d109a80c21902203007000120300400e5607002100d03040e1203450790000342c0c014018114113010030450006585010040c00300408461b040d12129504c2020000821a = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 510885116 1250 510883866 510883873
    0x70b0405010b0f03010b010912060f0e0a1b0605030c1308030a20030424090506040b03040203060f0103080f0a030f050406050415091205030901090b0103050c1e1e12 72
    0x50624000d80a07090351516140122102c00d065069070405001d40c042100d8161a103801d000e0078002310f059202c00442066402c15141d2035007001000b402d1040b800d0703081c01000038109180543c20702c0381d07030006200307942017035040c81180400c000743c0c0c0001641d4001360352281056503880895203180008049800000c0c0c14040000c1c0c032410142c2103102604515a199101c0e54540c0d8400c448540302d008a109038902d1400c8119a000c0964020344c0300824400c1504141e40f8030354841020400b02e821580110b0010600081400305502d8100415a481000403180340c41660540d550304c1030718054144604905540414a0000d450181d0420340c0c9200e05000308004501d007a0400d0310240c0301c169810b4900300e4403121103030b8050100780500990240c0003040c02c030301344556200440c1c46900041c60705046543c2c1c0d07450500010443c40c41980218000c0009020070484035003000185000496080c0d4070480681ca0304016450b9902184194024a85115541c102e00000301350511300c1030903c0b128600 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 510886366 1250 510885116 510885121
    0x14030103140a15060f050909030f0c0f03030a02030f180c010e061c02040614070b060d3207050a080c15070c03140c0a2d090609290603010e0a02070b 65
    0x20500e911803802c503002120261000e607911b00900c890040300b5180007065400400c401c80105505d41c1c01800c2010004e011a4401e410a002990541d002610b2120b01d5603000401d01400c04030b40030481d40c00c070307040c06007161a100c4422100c0341c1d03984410641c58180080540c95009031743e01c01094840a440000c0b0090324000b040111f003000b944140295004581d018458101714981e07841920b4901d5449416810103803030781000c00c80c1c0380c98185803c483c82010309410412a00185881020449920083c000c00d83e081b040468240701164000d039014095aa1007000940f4000903180900c100507114400c0c16048906003910501c030365480076004000500c0b00104005907401152b514a000f40d0036511105c59800400005504510400720b0000c0416040ca109561940701825031086c2000502e0049540c0c1d052001541c48950040c0081c59450103428030011039007800c10800250340790139000440304440041d5590006000350b010000410002484025042d411501825040f446070040751 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 510887616 1250 510886366 510886403
    0x3112d040305100e060601141804020705030d0b010206060a060e0a031703100906030f0204050702100527120f1e072004062103090f1401020d14030103140a 68
    0x2090283c240c215814644404000b43c2035000c42d0060160405075030b840c078200002802031002c0c0c0c0040b80c070003d400c260b02502020b15a50791004040d1580301e4400323140c451110a002404458143c12079a0640d0014000c103c010b99420304840240c402c80c1c00e08801800c0503101003003291819420081640e11888400002400d154014611640920703612001c92901c2c0c009031000ea0380300e44401051120080281d40040c034050300882c0e8010242e104550107198195040011f07160140d440040c421a060305203602c0070b1114503200d990380d00110040400000f00820715485100349054041c0170100070480b109595803c008800e0f004901d004050348490340341c1081c560004c44100d00392301281c0c82030703240c41580c10f00d03006071000c5a125803a043c22007000c07001200c0548100b81022010010a1040030803c0d855601000010f07102e451001810350724610006032501815418100601200c00e03500140712031880101c0e4156603110b010900c0d02411005080e2802c1c85c0e1050007813a009142c1c0382d08010 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 510888866 1250 510887616 510887623
    0x2013e0d02130b0702010207050108132f01022b0c0602040e060f010e01020c0f060d1406030105070908120d06030b090c0301060b0403020307140604030b0108060a0c03112d040305 78
    0x220500300880140b040e9544821266078426140000d0140e081520100070640c0600d0f1070aa125684006486100d011596100741440071205265000c407015581c02c05200caa80c8103024180d81d0a00003800d0070440088510110124441c907281a8280400004812803081018039803169220905644490720ba5100f0094200c0031111140114466041c0011030742c1303c1d1001c442c3ca4a0107070003900c80084c004050210a500c082e480d143c00c0340d0101325880060b0418401c1034101c00050785000c1c2c050074154105404d44402812510800a048030288140e100200f5441100c016640800d6645c100703010480c0050052548080c1400c0344400c2082105800800d00e1500b4140c110000c10001d506c41d080c0b8038041c011741c00302175007561040c081400040c0130002c410b40d0010000b031a59060550340d80c1d0b2605130040903040001d807130700200b0a02c001d1000031700611100b2005400c0c1813000d0350003035140030001d000f40d0440106181e0b01d43c1c0f5440344448100110340b0714103c02c2002d5a81d55440382040741e90b = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 510890116 1250 510888866 510888877
    0x13506041217041106190305090d0c0c14031911090c2b020706050405100e071d2a040512160308130e01060c1202013e0d02 54
    0x41801d04503800368a0300b449030424692400e401e402001d00c41d2580e4541c2c440c071229244461350801000c0001c081d01c101c020071141248245a540401c01d8501014070341d0030030a200e0340120034040d80c1d07000c1c0c0b80090300d1600c5074015504000d0545c1b48900749030f400a46007076100e08140107203000f0440314000780701110340140c0f40f6000954400103151100e084440c024850f6120902050303020300b4450010004c0040c4107071148080741c0001d4185526600da5004a80f8103850489003035020303600d09000341d60701c0d0080c1c950b45a14280540242e40c5480700c0c0e800210066140760b0b503407004039000603100400d81e107041c0c000c0030466a100d001201e0309255074110b070341c045e0142d903100300001c90300d92101c032200040c40140003001e41040760201d40b969840440d5a0882600a0035198400c400451072502c20b01846009050725500c0414021207070030000013000c9d2452018003103905080e0007011100c0c2c003018045030341e010800065020171a6003283d1405c3c040921064101c82070014a12010b1126030700a440c = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 510891366 1250 510890116 510890123
    0x311070b04060e0c03190f120806010807030c08040f02010c0b101440141009020901020c09060f0618010f020f1507050909040f03110309060301350604 66
    0x201c3c1c64100692981c80030358080c90b983c15401030142c004d14281044c0090321845c132842900000c3d140301d545a80f540e4000d0001341c000030306000d080000ba5a030101c401500503901d424100071008a8480050034000001c0c000781c82c04251001110869204981d0785005e550484100b07000780c14803600407460640b0a00c03030801c0d01c804e403480e540410710f000e41e042d081c03d141c030103c07030316079445803003a002040b4504802c00c0c0003204800b4040200040c40c0e004641c42c0100013080300300b192400720f00280c3c004003a1f8020f581c542c0c0c4140726030070b13807a600092107501402080303030f0301c20165441c80002258202d6a040381b0f500104049420090307031079407200303050a400007601c9050704144015012aa9440701c10700009075507120b402c2034440c0003074010800c2e41101e0070345021482c0c081d00700e0125461410541d0203c400c641c42c18025003e160b1300032142c2160540040146107002c00d1040014107a0206005403c8075001d81c21009201c0311000e10b80203041c0d00642c001c805540e141c0e1400c962036070011201034 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 510892616 1250 510891366 510891371
    0x613060f091d0106030c172a0c0a031b051b0402190302030f01150215091006170601090501061d040e012c01140c0c210a0207050616080a0311070b0406 66
    0x400d880c00780c0c11580500414405c7e0b21003a41d5070032414005122000a580a42030195060055001c3e9000090079450f044c8401494003051624009102c02d0100074000c0c09080745c40d541d00c0004002007021000b8520141d10743d40c1814910000034001d200e02c1c603032544081811400c0c426a01d42540240d8801d4090074111300d0543c0c0ea840903508540301001117140141c0002d261804c1d5210101c03560f60300b05512004581e4001011494030045400c80d402c02d24a102c03145880c851078840400901d0301402c4404018001940341c050064040c3c801c48103501c00940300d1061000468031039900410800c1e1001c0005d02c10400b00100341801944410252004c81035081034101066030140181b0041070680c0904610580d28024501c1c7e281e007088410085a014610400240da0300c82c03402d42d004541e4001542e5076910482c000a4904489548503d01800b028000041424031007249000c2d400d400002c0c980e916040b03072070120000d0403210700c16414020007154000038003a07080b600ba48106d1141404 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 510893866 1250 510892616 510892631
    0x40c0905091e1501081f052e0f0206180f07090507021b0105040e090c030f0606010225090207150501030c030209011d0105130f24050613060f091d010603 67
    0x959100010f468201d80441c4941002c20341d184100c640340c00407000403480c03181c1901e484900141c81031017020760b5081c042d40341e203807071411010107410b084500680e64100740100b1401b0b9031000e500c6120040980440541d603000d100d0301c8810602841301d0284229042d28280d42d100c2d48a04002c00003603603040014403440c88a0848200542c68440d0311190584509007414a0410044803c0384002c1054000c1c3c09542d07401e8200c2d4800300800e0b48161f04450203000d041c60030400081c504182402102e078840007104501c0b110f9900c0194101c2558010035015940301114140700030303a02d00d01d4400c58401440d040c000400e0011440c1a50b0136207200b00e0740d844180c0d03a078407848131880c0030030300d03405960301d001c100100a54a0031200841c1c600b02000001f107a042e20f007400d200e0440d0640703041441e101c504040c414050b00700c40c444482c085d0200710b80351400c0c400100e00002d908101d07402540c1c18008808100c480c500d0264821383d00030015502101007640d4541048201840b0071b220325004030341840d14 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 510895116 1250 510893866 510893881
    0x30f071b05070e0402040204081501050411070b0109091e03050c1002091f030b0a0e06040e0a120c0309180f05090105070c110a05090c03070e0f060405040c0905091e 72
    0x60304206030060700400318039040c1090300b0f00c690405402242e015900b00800190b410b8144100d801071603c80c3c0021340158500024081036910300348525140c0da07010014200001d1420707403100e055030020080000e090711140341207a1200e41100f6030904014003190b1910400d86e00400501100c03581c1002c0d40c0c0d420007401c103410300364042d0240555102c0540100380e18900d03016824001c0c034243c0d40c076003ca2007040ca2004119010700641010520241d80300400038541494050508030798200001040e007100c080d00d0342808001c1c2c1690810811142c507504009252044c0c3e8010060304660400b40798400140c8000b0000323114011804071440d045c07200041048006100d0303140f02d02d026403620100014155100c2b0b0303030404070410f05580510028408036560300c0d584145c5200e02c61224205640e420507600283c0020031003294030b03200341e007980c81d682056100d107000d480444905503008103070512031410035100c440054110031b4004284404005918134901021020645440e8000b81103445e00c00 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 510896366 1250 510895116 510895157
    0x115060e0907140307120c020d1e0507020607170d3c0c090806042f0f1c05010f0213050a0e0c0901110304030c050117090c060a0311030f07 61
    0x1550000030800d160200f03036024507008029030744100546005804400a501300100319400c00e00d00340c005038841c01203143c04a03001115041e800030102041c0d8050a00b1120080c114866000024052070020403210200440401c2d96040c18425901c1c054035190851042001003200808601d1003074190750f0308041d007200c2001c500150902c880c006410000a249445000c1c0101c880814200040803a00040400c01404041c0c0142e108403901c41140200c0140c4a43e08102039010030242515203030081266600c03c4000c4860010644079010b4a1400d1081c0c4035141c96100805002942230090364a064281507008001c4800110143e80703035141c9442c1406140d000301e001d4034a411031408041101289560058004e1400c14503092425480900e40f160860f00654001c0f01c010100c054103200c1513030004020801400c6100343d5144900c2c00a28865946240c81f60701401140002a4a40c01521a411028083e4a0800855501c2c208040c802c0d182c00d8040702c0c0c4200040703415100503031501c60030 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 510897616 1250 510896366 510896371
    0x7051507030f02070c0e0705091215010e10031101030e06040b270a060b0a080a060f0c0503090c040902060d230606070203150c070210170a0b0607080711030115060e09 73
    0x80410500c500303020b40e03000d2400c8050280022300c0411f000b5802e1545c1c5800610b201c410b03620b406403642c400700e9441489800702c10780104010000902c100090941c0461011085980149420501d0250400141c004010414010005001d08000c00003401450003019005813842000d80d1100010f03040b00041001d40d1012144e403a42100d5419008616541c00950314400c004140340252540d03185400c0c80c0c20314031303c07088038100c1d00c07280d030780303c11803d5407103242034800c241e041040c41c61400a41c3c3c581c80e0021042424811699401940d0640d1104000c0c1e0341000c43d224807c200000d0f4940a80151503400300d00d0396001a50303440092a1130030214241c406072076000e07009080c51403c041e641481c14030b008152000f60b50046c842100580d0340c00d1440804c00c030311742e1140003003011204403029003070000905c0001114284a1501c28a45507641151407040d00050690b072210514a0b018685000c102c09107641503081035201148414000f1880048464076110a210702088070140031010008 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 510898866 1250 510897616 510897623
    0x6020309010f050309120c010e03040e09161409042a08010e150f0c070629030607120b06090604090b0a141c06090b07110f0a0b06040b010507051507030f0207 69
    0x299a141c0c412200b46c085c2c608070380b8000c0003103031f401e107442030103841d6800c075500c09002c0e0380c0000140540303550b0500c0701501c86070000d600346000700d061100701a840002d0200503400f800309140020f051140c1c03800c01a0000e5400000c400803c401c035202c21011420a0184000ca03510785590416035850000c1d140141828010215826030742c0c05285083c464402400300780c844804000240c0020014819621001c02040c0303140380f44191540c5100c0305a0b008814103019a0000301841381b00f6400a100301900f10f01030300c0c086446001d80e40818080e0064440c0160040d60100300461035001c260424a0816070543c0c010783d48643d100d50001d10025880b242c039030008012940740c0700940c1500c42d40780c3d00c1c0b4058900801c0704016503459a0310910220343c0140025403009120164503024444d000c0c500c040100105000d08131904c804019406c00360429104503510301200d081d690007a81038450f034039040700580310045134490710588024422100c00d00020f1a040d000720780011148266040303142c0 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 510900116 1250 510898866 510898873
    0x5120a0342230a09060e0a06060503090a060c020705120106082e05102105070803070302031b0a05030d0204060f142a0a0c080115030f12090f06020309010f050309 71
    0x14018a2005a90281c2da801600403184100100d2000e601d406120000c0240052150443c6000c80c0000304a840b00d40018081105c108113100c24000c0c0040c00140302d90700030314001480d12081380c0030380c0307003400503400140c002410182e00021143c042d40254200e03515101038800301e690009606034a280800d040c16480d180c003000c2e132100315a07a03901142d8016050405807600d0398a038030a004400650a41114120300c2081c0d6070030400c0401c1c4401c200401c0010011410300d0300555000e502d80c05040b4000000050f20407031a5424281041100d5103143c10009880c0d951510b00485000ba41c400c0c01a0070215001d420204440c5101c1c642c14120303a850044164200150300c40d03581d04650a800f0020074666000780c0742c0900c0c10050168081d01d6201c0e04060510724500501d881c203548890420400c44c80014004101180590380f102c0a03856020004801c0f5000b40e00058803207030381640cc4070310b01d164403a0f000f00750141c00000409140c0c000342c1b5070084080c1c00250860340d0344802c48168410382c0 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 510901366 1250 510900116 510900149
    0x2060c0403030c051908090102070906120b04020a0b0721020d0518030a021c0312110f0a0311130305060a05450307140a05120a0342 58
    0xd2090f14821800c1c2d00c90710546465803081044201992040b55041d0751a003170000f64068150313010050a0001c005102007801142d20304030202011a01c00a00a0005641138001030110356448c00420080e042c20790683d0340f110210700342000c4045e031030085004504468005030f19a40d00001d015009000d450751032900d801c1c0c598078014074805650380000d40510466518200680c2c82d5841c14900081c081031000d2440e1482c2401001c3d40e203003d040e42401450214515021b84c240d0301103c0d00b201c0c50000c419600c1d88030325000c4004041c0c403204c200740303002c0102c0c851095400a201d440d007264060030884604e5265170300c0000890f00140d40c0c080b400c0c5c400c81d80265040d1000d13582581901440c102401402c20030140307520710600382e102c0200103a0030005103442005090946501e0801100703004010040081d903500b95209101d0f0380108104101040502c08503119411140700180812080541c00c480f8114100350124601d00300700c1e003101000d00382c011069804c901700040301c1080c6281031104 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 510902616 1250 510901366 510901373
    0x90706171909020d08030a14060a17070e0405010504060501080c0a1505040e16030c050a0503010608222301200304020102010e03190f1e110102041505180102060c0403 73
    0x403030640004581072074855401c100543d0b101c1d000d1400f40c6006860340d540e40e14002140710b040741c4c0c05420300411032500758240410b5840f1201114140c4015094201d0504100c0400514000c4968403001842c5c05050420041001c1908004e004034801c2000b4071050362a203205a4480e044a440581c0003042c0c12401c0044884c410a180110b42c01410300c40c0c0303031a0700e45114110103002100d4180480c550540d07200301496251080c07008030a121324109060443c0e00e50018428801071003032100b000041c5c0003044082100e100c08074521143c5c02002d0010034001d00d400c40d01440320400041911a8051102d280d0710010b020b103200450380103902541da071000c00140758440d0806441a41159030b5010360881250042006211034480d111802101030f182400017041782540114a404200c6036441d03405000c500d004540051f400c05042010f04040343c280745a0081c00343e030384055440a02c091070f941180e600880200422013145042003420420240166552907096a030740540510401080010 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 510903866 1250 510902616 510902641
    0x11060609060d0b0a1b032003010506030a0b0402090414102108160203060106091401021b040b030a1e02040b1905060307120c0806190501050f070303020f07060509070617 74
    0x80110003e0010b4100810460002120350101711900801c2d0384149032203024408005184408042c0e042461641d810540030071030301d0101a20424400d030300c0d5040804180d44d13076010307601c0c824005030080092007501000c54803500d00a545098400caa182c1d8007149586140c101d1410b0001b83d240c40c881c500c8050303524a207103940500076880c0c205c402520804010303030f01448494020001941c0c2c0982c500d0400c202c1c1e40c0104101e184003030540d1310042100000303000905070702d03500040c21a40081c404039440c0100303051090383c0c000100054204a08060854111445410ba0074000d03101042110403c900f40708501e4071a20080341c440781d00d220200300625000e802103502290714a040c8481e0489034015005840d80405404c000c500024100a2213040565903155200b200d00c40c1c51189174a4100081c0641c418418654180c0030005140c00070b041c02078048031907901d0f5944145990309040d00b0b01400500d01500d8010b8140142d500014030f0724482e6107136048031f00310343c0d4602241352245640c0404 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 510905116 1250 510903866 510903871
    0x1207120f0f230310030b010b030601020a06090f0213021306031401031209030503030703020405040e1c080a020f040915060f020309010c06140f04022412071e11060609060d0b 76
    0x112181c442e200c224492010800303140202c50441d01d0860a900794544026581d0303050300181d803960014810428981e0b400608140a55045a800550b1a07514100402101502c100280d00110a6914a0b0300c120b40e031350044c41054140d140b03621503075850f424124241d411203640802d0000e401d50051000c51440d032600c0e10040c0d56414000306803a0f480d41c40c42c0c2190811265000841e070301007020407103800c0c1400380703003034030f400740006440c040030654a80d00d61200b0491a680030008084d000030b06000381d99048450700008541083d0302c4980d01c040c0d400140c00408a03c1c200c1c1010f588002070a140103481c500201441e64018609141d503d4004541c20f640c1000241c071b0040d240d481c0091790b2405012207a009031010704401e0000d1426005215841100e049140b00e48420091064001e21200c1c06940000b2644400c610094884650071504ca11140ca040072040b08501116030146801509080c0101d0001043c2c8143c0d80d140e408001d03d2410403140d69403c580194032920000ba4943c060b542d = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 510906366 1250 510905116 510905147
    0x30a0b090304030c08030c06060a080a0311010b06040f29030f06130606030504020411030106020c040b040608061f09020406080105191511150c0702060705010603051207120f0f 77
    0x90802d5500e484242c6003c102c1d030f00c0580c15400020303142403a51f10034001c144d840401a91000040351500400c0365403440d90002c09010450300e11000d1002c01001c2d0000696139100a29083d00c540d25809084642800c5200e8070541801495122540c40100032108818a080048050071540ca5000141c41280000c003400d0b0f0080600089480e0b107409489004007400705a41c00041ea03241910600003203802c00b03818040042c0052004204c0b01e507000480411540060360301080030001d203008600030300307801e8200000c940a0a000c0103131604001c00c01a8007040351079510025150707502c040c3c0d4120300c10350241c140001c907003400500c44c1d4101030318100d24841003480403c2015a50300340c580008803100765440005401c66044514400003045072080002c01c1203692030690070990780201c100d01c140b6000038010000468598244142940600300440d004000e40d11148800456084c041e4485070b0308850525220701c0c0110340d6841500006411403450725014040440ca2000340c510b881303840b0901 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 510907616 1250 510906366 510906373
    0x60705161b0303030203070f0e0f0f1f08061314043207050f011b0212030d110702130e100509010b04110406030e0d0804060c05070618050d020c030a0b09 67
    0x100452600700c81040002c50081c0c0d40103860382440302000b0440e42c1040d248a0420440c034407500d0095480303031a010a41d40040381e41c20f44804078040030400440da41452051a0040d0024501c206a00082c03814404c1c070301155140c0e00d480c03000c5824011611604030a21110b00c03000d00203000030700c00269034841040c4850308000762113040c0341403110106007010443c12a1304100300c2048242001c1000105011007400d200340c50301194a10501071000e0b840b0b0103403103421140783e030003268001841101d03594207103c6014480d01200d902d80400c0c9520400b000c82c0142410920184500d846125403175400329940094940300300351011100c0645005802c1d545155030719011741495030754a100b41c11104419024068032070785029406412038600b8620015950040040030f03113603560240b416a48140d005400050000c1103041c203c03140e011f801d000400b190f20706820b0350404401c80103841410752050084400110352a9001c81e199460704011507055486844903c00003214034448540c00b003140e800b00c = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 510908866 1250 510907616 510907643
    0xe010309020603240303040e06061633020c0303070f020f0d2c09161202031312030e0d080402030c0d0c031416030605060d1b051206070516 61
    0x35803958415601d038490204e0010500c0d965081d40004142c10b5041100518141440c0c840c2c09500644000c146078402d1000180c0c2c00f0b50480c0712100c56001d950041b09903600743d4400700011100445401410b6001356500803042c184111034000c0751214180c8401840c11600c0d42d05040d41c803103082d80302d042e09600507103040c4507145004000038014413036165200e86803121107109420144080040b46483c0c80321803103600b07001d234590500590b080204403400888040c1d84800c02c8640c0d4006a540c203c80600010a01c1001050460044013180c0502d0b00c007400c11840b204250221040e007140d047c0130750000c0c100703c0101d5000e1810268090b00240589c0c90100340100080c20704c100c1c04508852820a0034420b00600a08462440048100c40024507401d100f00c03004034442a024480140b419855034009081c584620040002082d480749500e144c0030181c6071701c043c2e43e0805000d050b00640030b841d1070341d1085200044590294820741ca50394504050290700c1c40100140e81c0d0142c482c1c1d80110746 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 510910116 1250 510908866 510908869
    0x5010f0f052403091f0b0a1a130609031a040201080a1e0f0507080112080f0309010e0709020901020f060c120c04031401020a0f020a030f031509020c0a02040522030e01030902 76
    0x83d4844e41030140507000b100c1500d880161900152113110074103914001e200d042070b0f207440046c070041da01e103240c0108500750000304505051103025000c6000450b600c00008180341c0100d1040141c9114171110241520000725030b00390501c0c1110040d00007410031021030450340c819401402248103554010f803440381c5030416041038031055901c80d080c0356070343e104121100340d0007402030f405070421a024401407100380d1210016030046040c181d904140003c04600d90000075406049411020004c0e0303003542e070391520004000d40001c840c0d907002d40105a24205c4c103142c00b00e0740d00c0c400e204803c0940d0411741300382031003540124001e2080002d01000c200100100790b0b83c01d1303041c000172102c50002d695104607800080c2061104440d070025503003c0392040c800a40c000c521126120704900d8002054021000700300c20407491a40f080c0c202a04c0050000c5590501181c4500307d81d000b502c0512098a81101d04601050708006c01c4c4006060b5484038000030b482604a00e014040515010410803000d40 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 510911366 1250 510910116 510910189
    0x70e0307030803100f1a0901120605100804330b060f0f0913050402011205040201030b1221031303110c1507060c02030a020d080402060706020c07080105010f0f05 71
    0x114407080741342c0c14100030020740d150640c054000d00f81d54449402c01103600c81c035042942c0240307001681400442c8406220041c0240c0c82580102401806c0e084180c0c00f5180c00342807254260f07010341f580c0c000d056240c0030000048411941d2015110510781ea080000c4404030020311115046a501442c1003000f0358201001d10094003c100c502111310350303643d100504100070090f8484401903028202002c010140c0c3c1c2040c0341d00c028001e940d1010403a40c4d583d1004030000d00005994950003450442d49070311030040080c104000e010903a204118040081e0480e00050008850402080000108090020340300b20669901480400308554414102400290340030344141740c4402e450074042640010700c0758501582d035a11010380007562400400840c029100c0040d029001c1c10702000b000810f086458001c1110820754200c103085486500000c8026120700080c4100d040e20360824001040e030824921404045076500c44031088007626020511950038030101201d800010000300f40c401036400903 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 510912616 1250 510911366 510911371
    0x4050112060e06273409092409050319030f1b0507080913091a0403051806090603040303050f0907080d030f0f0e0c10030605181f1e060f08070e0307030803 68
    0x590b680a05c2c0c0e4458001d20000070613408440c49a040201400c0810350342d01d01c0d54200300901c40965264203e607403d0170090017040200504074880042ea5000045d480c1901c0e26045e4a141d4052144200e40c480102c142d403268424407490007110188000740c5409a402004081d110350743c0d80e4104a0000002690612070038401910542c80d80c46510400143c82c21442e880218110002180d003015100240755025001e07550304c021083c070a200c83d007a40c030740d8155803500d04020105a90f0789003070b150050280406480400d10240b650001c10781000006c201304c000d45596034024080000d500400f1000341802096440344596580e50459407441240245801c400078100180921104502441424048000b07003e04141c0341882c10321040c1d89440c8070b010000c505544180c0c49880300a11b00c404225083d401d008850001100001d0840d4008910021140005200c0e000c081c0e4800c0c054401288403140c000010740d1200000b410140070702c07501d80c05020042c0c11a4549a125034490300294800e = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 510913866 1250 510912616 510912673
    0x40b450106050405100314070f0507060603140c0109180b01091220270c04180c1d030312090c0a0902180a0506120c0904050112060e0627 60
    0x40c148205d0030a4903140100c600945000c00660150080341480a40c028007131000b045290351043c90554803440686244c1c0fa0050000c0142c240d503071410b402001c100690043c01409a0441d035602c660117000224110f400c0e50501000b83c910020201c4018904500b80d181400070000001c00c10540d4100302180c458416a0074203000800b6010b0360b4009642a40f8440c030881e01e88410009800301b01c0c84401070070541e0600c240b21a252503040e81140d00440d0490000008800c541800308000d980101d41c01441a490b0b5003041c014408405100d05030090364141c242d0703c10826440e1018030084003a60118900c1d041d00c060004150000344808482e034440c40406d600030444400804050107803c0cc14081207442d10245450040443d059000c0d409009030345c180c5650005038072415280c1102c0600b17500800c108a5982c42c0c01002501507540782050b95541c1c54500b5500328280d0005a49025482000451410328815402300003081c14515405035640109481c4401c00c0c8034410403406580030 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 510915116 1250 510913866 510913877
    0x80a0309031e0e01051c1506080105310b15040608010e04020a170a020402070305030916051e011101140910140105040b0102031e0306040b450106 64
    0x405050082400c00c1c190030707000e2500c0d00c00c8081000b00780c1100400d10a541c00b030a1843d15020b24400354a0710120b40085080060f0034000410407256074a05a603080d21200c0d20ba104e102c2c1d0300d4200b800854407a01d4500341c10042c8500d902d5405c0c0c030350030a50b007542c0c02130084003050030f40317071031001c1402c0703103c0442c1c0140840c10105017030000980001d03640d405002c4101c0c14a0940c501a00011031032a940e00c00c086001c40e140580c031385c9510302070001c81695600603006550398409413600800903842110103010a00030f01e80c0302c1c00200c044114100440741c1c01001c12910b51219003410440981a01841d4140140c00b20521100c0c01d080c05940d010b00c8600c803883c0403624200381441c1c00c10401c814407070341503890880e05901d10484c8480307081c1518400e540014400c082080140d01c3e510800407000e06c10780c482c8c0361450384444d010300114400d43c410b680a022050502c41400660240a030000200000c800c0210740203400c501d05009803401a509004071240382c21131a081843c1e401e03006180043d4 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 510916366 1250 510915116 510915131
    0x2061c060f050406090b0310020703021c021c050c0a020f010903142413030e060912010606030f0b011b03090314061e010819051c050c0705010f0822080a03 68
    0x741c2882160000c10038a4400c0c8800f071a5540003d48074000462010484d42d0301003462b0f01410301c00c011f5034850342e41c2c04502211003054804042d507034110440814120070078661005010a1096065032480800103001b420104415420090400c2d108008641001713164280080482c66074154141c49607420006001e105440841d1046640142a01d010010010205102d0041103005240d40240e4041c60003042c5c3e00c0d0444c0c0065418800d40d4070072540031220b408441c40b540010b500c114101c49503901d04002090250b1344500c1a00c841120460100302c02c0b0003010603808000404140951092a18503141e680ba5520b07880006020031010003d503010204000e0403501400c00d8500c04170b111070fa00442903144c1290a40d031082200c50300d0710304c1040110a0030070000100128075510920400ca00c106422401009126411000101441e48202130000032194002e800601c1c254415940c1c41c4010740d540310f004000030000c002c620b050441407240082c041000c142c058203240055070313004035041 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 510917616 1250 510916366 510916369
    0x901030c050d09060e060604020406210f050f090d2610090c0801080c0406030c1403010b10020a05060f040c052b0803011e083c060603071703030402061c060f05 70
    0x10f00000c00c02c43c0030b09c2c410030040c440c068201440d002c000751100c0c140c005442c80e01e10404d02520a9042020b4070368140014400840c18025007244a04140703400c581741b04080d80f000312601c0d0504004010b140c061850016514800c040d1950741c00300d1000f5280700312542c0e420f0506c04990504000740c000503a035100601c90444288800e02903103404450521026040d0746500e20002018400e0306600d02d160f004e082c8864174290007400c0404401818550300300004100a5110042c1c01e500702c03220301405000851407030790b51040c036024a8202c41c4054a480c2404c00703000752070707800703010903d4003000041540100b030700f61404400d2602c0c4200511502c0354901492103500c014044207084030504208400c2c0194200004c4c06900c0d44007028542d80791440b90201400d00070398955458000c15120500700d00c81c1d55001070040c2c0180001c1e0b01b128040d0313546031801840b00080c03e841d41c0d02030b0410400705015260110242c03101894040718082001d01c81480c40702203402c80da1000d00030b5242101c040042c6e = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 510918866 1250 510917616 510917623
    0x1a07050706020f030f0c0a0f05070501020c040e0703060c11011505040501060f0f0810050604080607022404080913050703050601030b040c05030a15030c08030c0d0c05030901030c050d09060e 83
    0x1007600d400284201e440c1d011800c0c0d124010300007203501103a40071812030301858040050000d00f5400442112004200b81000d988603003a82c000c3c10b0141c400c003180000c240c2440e11583c1000203c09015040040c1140d03948005002c10044079001c110601400c0c540c012402c0c4154001c41203814540f000141c03a140a21043d110305901210601c0b90403000071141c10f800a0740d03490555000c3c64841041c2d42c4a03094020a0081c80d00855000b110100f004a07070090001800742c09040c1540886641c1524007802080c9414520b01c0c0071007543e04600804c0000c0c024070007510b6041e030020480d0f1051401281000c0c226101207a080c0c00280c3c5072000c2c0300c03941d6058031074660744d400280c9090000301410b01026009110282155000590b5003442c20080039500c5240b102943c1c0c4034003c01101a07072490515560740110f44001014002d0781a542c00a0307005c1c1d0100290305500c031000d54244260500150010511005110240038080001415101640c403d2980f10b900c50760000911390700e4100484d18 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 510920116 1250 510918866 510918869
    0xa030902030105062e050f07060905150108031b0a0209090c01110105090d0e0a0e01030c0f050306061c020f0928050106091217030703020415030b0609040f061a070507 73
    0x1c0c440220103030800312490100c10381a0a0031121305c900d650f40e80401280c40d407160f4502d00c1c43c21f1001147c00401c10206400814919025a0480d41c50028850300300c41c07011021b100d0541d851340104080e50b448003001030044d03807088030282903900f200d41c1c98000c0381c407190045900100700d401c85900c80e4902d40e040103001403030b8844100200040d10f01504001d5980c0c07561a03c460610403a085200d0960b0b59049428001d0410220104148d595a1404600c0c1c02c0660040310710964481c50b000c02c01d81000a00940300d030100404030b40c0c0042e0060b000c1034003018020801d84e00210b00f00441c2c01d95442e10300d01d40340100d0808029000d40c54844202482284016400030350b0341d030070000100029544242d520040d16201c81508107210040d00c0e01440090340240100c2a100020007040031558055004d4411074a2021020f264601d007600128111559400042e5002206000404541c200766008003a200c4154200040080c0c0302c0c046168404020b602c1c000c00343d180010000c4c200700c4203000910 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 510921366 1250 510920116 510920119
    0x70504030618300e03070f0905010e15030601060c0f0b10090c05040e04030f02030d15050f120601060809030c030708030a0c230a0e0402222918060a03090203010506 72
    0x3c0303200d03209410701000407003041d01c3e8004218008104540543e01800010000d0000c007601080c201da84088000141c4801d02c00c051a0b480301c0c000181c1c900c01c41c2c80e0305180d49000140900850382c00d007501a182804200c000b03441130b0503080071040000f0790b1840820b000700b840c0c28039203441a1178180346a040ea190301014208204050104103c02c41e0b81d004629045945400c0200022101840880c954060517034101c00041c00c1620007070b003180d0040303000d03401c4d90415221310501e5840a01809006100c0c5a01c0ea07015600040040006921070310080d600701c2c0d0b07048103036031a100c0807104440c03440d04840300c00d8034284230020900901e02e075144105003d42d03419007481c3d000c88180800e420341e1611401ca160006510004080107094400c015101d003090b0f0040086444100180c0c40070081840d8059245280d08104c202081a07418810084540c102d4245050b408404131030700350f4616009030624a1098502c80340f0002c10741c1d2100080e0030640c810382c0e40018064420300425003074035005080765 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 510922616 1250 510921366 510921413
    0x706050d331806030f02090612070603060510030e0d0e120a050c090f0402090c1804050103120908161a04151115011505090f19090e03040501090608070504030618 71
    0x4c0001851030582c0d603980c1d9404507904081c503900e503400f0403030310840030858040c1800341c03640100c0c94540540c4041c0540d002560035035022015510190200da0b004203001c1c8050303001102c80515584941e0f0710055040019101c80507180301003180f94900b441418040302e9603040100c90100c00e007401c60040780d02109070007181003070f420150045440b032030014024954251002403086d2101a00315040185144080e008110941e0340e810140031864150410b40c0c00120380400c00603130b111000030410642c80104c0348030481d481c6031040300c190b0401c00058003030041a00303120000308413100f140400f10410f820344030006001014100c00e81080346d503500001201c01040c00502900c44011600c40c0400c8040c00d041e81e883c0c00c45400582480700c4144296401580c44105889501c0300f2003102c02214110310080c0100450041000e8907030040b8050700e8009000c02c0b01c100701092081c00c440b0b401400c6c43c14000d1526859841e120256000070400c000501c0402c1c51400c20003000d9000d4042e54131412818 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 510923866 1250 510922616 510922619
    0xa0603030509130b030303070e09090601051e0a0801110301031703070219051009080a0210110f0307110a080712210b030111030906010303030606020706050d331806 72
    0x7915030700401810b5070154141da00107005401450344140c0c0c50102c0101125264500b9280041056407404a4a80104c2d1694089039080e07000280c00c1d410780c1e600525003174855000510741d0b02914101017996038048a0301d000058144420301c5244851481000034594942c11810010301a80340700c81c200084070810000c00000e264085407080714420005803800b0031240f9401c000d45040785003507141a01c545400c07880720811041000602500d80245c0a40f2403c070040080b141c02c03194a401c001502e094204014610440200c1c02550b05c03404078104000c241c030258021500d401603401c0c1c00c8404080005160061166090204142d11283c1c68005060400c06c00000d2046d00f8010f2000c8c4c0842d15000003410a0b038003900660012006c07140415201c0c036005074038595980082c8010341c0421302d80200420f00f20720101d00a8103071201502d40910b0500e00c451784000074006040c0031620850300140c481801a403103a01811030a0080c2c181000085c1003c090310111000540443c8460307241450 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 510925116 1250 510923866 510923873
    0xa1505010614040e060f12030c01090b061203160f0b1003020108161b080f0a090e010b190e0103140106021e06150108060301020714101b05180d1205120a0603 69
    0x40103a0002c3e007902e1130581c21007806c0101d058101d080e011440540800320355081807000c158800a165401007030f400710035407600414403407404848614560396800804c800c01d40408118039900400d40701c0c50240c3c08100164585500c824030944000c200201551700c10401c1d980d1000e515504180f142c00028045008400060448680780002510605009010600b40002d41e03007030301c40b0282413560080c2d542655040040c2001910701404100a0391000041882c2042105440c5202070404504c1690400740c00c0a641c404d0b84032130700d1030405d030f100c10020351307200e100004d00303402459160004e002c4200760741950034900c00707600114070706070b4001020800b00c4400004c3c003603440d9800b1f003000f030b52584540d000302c1e003e8868484003074145280c01c00076507140b49000402c1405900c020004100542e800640405022610404000015018003495811810b4103200801d80000180819503411150b641c099852500e50f0b0306001040011441080000c80001801e42c04110070a04000c3c0ca401e665 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 510926366 1250 510925116 510925139
    0x806040501120f150c030603020316030519171602180f0703020d1121130f080a1b0b09071413051f03060b0f090610110a150501061404 59
    0xa006040c83c148205901d080c03180e0900c510f03006101080080c050001882409000340c003042c44200e000344507107a01e18242c901540000420b895004003d03041001c06135031800002258400e06440d81c2404c168403201003030b0320600406248038106505041d0006500411400319080700300304440600c25407c02400003a0940450b510003600e05005071183c814005c3d03030009003612512444103410004440d41490b00f00c544100c80404010140d1881e95550784241d50b1500004c90018280c003038031540d9100150460700505681c62580c1740102c0c0025901c800b1100c1000001800d98006031120f05001c0b0310030050000101808914021140f401501c101240007000c04868400189a650000c90342d0b9a440a1954403d10300ca1004d4000464480c00c1c184000c00d0140d0b00c20344511075646030740c0018180182c01d0b81c4680c4006241d000b600c1103603803007647c000300030317000461a50281000100014001c00c0b8082c0f44a005840c0005440d130624038007910440180d82091140c01090104009005904 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 510927616 1250 510926366 510926399
    0xb04020313030503070e090c041a04140d150920010207120f0f0f050303160e03030a080406020417060a0609270203031308030d0605012309060d020a050a0806040501 72
    0x501d00140d80c0c4e40c4003032049034074184103441c0591212400d0305102c600c9023140054402e89000341622000303100d80740702003003c0388118400c0c01c0508008141000c440d05d0300700e2440b00194010018406020034000084089440e109801c07100ba0160442404444000500d01182032000380000d11425040001c0c00880702072180004140d0541c441c243c50402800003900c211040d8004044c10000c64117292480e102d400890b103400c18510b5002c100c1400074401c1100e00414600500030310300d0031044030001c5911000040c01502e03841e400b04400203011350072201031801030f102100580342905205222500340e034099840140506d040c5002c00c90380c10450703c1801c60b91700c106c414150010b00700703101007825030182405c4640e440d00c5120001030009400320042041d1001c00a042108540310700041d10404042c01100501303203029190a9440c1f0002c00080004050044c05142001c02e80e08410b13003641d0007500c40324000b49010506400326504403e1a0750401802c0740c0500040d1304000c841e607001c2e10310 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 510928866 1250 510927616 510927623
    0xd0c14030d02070b1503011107082209060f230607050a05060a02040303020f0f1e07050a060c020306070309050c131407110f010615050307021203040c090b04020313 72
    0x16450454001020421070760000e450300010740d1586500e080924007060304803281c4842c0c07540310400c00c540d850103100385250403284000d544d003040400e88030000d540d003000c0042c442d6a641d00c6280d104018040201600801401d080402c0150505299541c1444158042c00850303488400b171220100070803201c4100e88806450050310348100c0e003000c624110800801801d20300070b40050240b4000c4036001002600d0107602103503d09244980f9031660703000c0c0000d6411072904404080d050b41550802020340041c02032003280d45003525800000d02070056544000046842c44c80c46030210304040c03011a50115441c102044082403540f1340360f40b9964040070052003001203031107000040386290312102c0151102880c1901601d03107901c02400c140c080b2103d0051500c104c00040c15842c0d4140a05015121102c20050b251350040500740d560350400360a1106601410140d182080c0c04200a144a0703030040980343c141c0f501d0441d640045820440308603014034010410003020b22909000714104e00d90 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 510930116 1250 510928866 510928883
    0xa11010b030a060e100c08040b0f16030f0e06090a05070602030427020403060513201f050c150f060105090d02090601050903010212041202010b0312030a15060518030d0c 74
    0x20200859062465901c5081c41862524801c001b03281e40c09103100c0c0c0304034800c0c2810415601c6030040701c0c5064108071000007003c21204640d00b0035611076001200004010000460a000c0c81e00206041c04812902410b0640c8845510003d00004000b0b00b0003e104500246240608000301c0301505002c071103100c8550814031842c0200090654129002960030260420080c28402010141407040100694068118107041c2903810100b91108030141001400441e083c5014441400c0c4d41c0100c0b200d0f442400030501601c03074241000e0040c40700e0703160849603110700b80c40c22080201e1160809041141004400d024002c0203031a08014000e4542d01103542c60141ea0f1070a004850078440e010074141c155002144050740ca0f0ba01e1006a80a1441140100001880300004900722a03d5460341981079100c0ec0302543e00c45004401584c0040300050b020400c48a40082c0c03421072840c0b0303400034001400c00a0074060003161100c213460511021406000c003140002001801c4070040140a8030145 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 510931366 1250 510930116 510930131
    0x32101030807080c03090913020301060605041d100504090b0a0615080c1612112a090a0f060e011e030c150c05190b0109050105010804030318020d080a11010b030a06 72
    0x90100145c1b155044003c0954100307203001104d02d05000f14280d0100d000e982800c0005c1111400385041c7c40940d004283e81848080074540c82d810700c8400035107840c4540610b80004243c2c0c3d240c9000c1d0f08581c9009210510031400d00301d424034122580c03644000241481000c1020446511080098000025200d140c0d120b0f03100302d102208503600e40800810380058001946543e5030031400d40b914050103c01035074003422031403039100b450107401c408400e030400b05046101e1041ca02444000c0c0c0000d425040056009040b000450403541280c002c42034412030031004009203039000b546502406060154040b0701850341e07881c0080040d450194490103005000503144661203030404d400c0705500407084608007501482ca105000c458850280e5910340309500104000206010b428101d49040e541d40032550341c0d40d20110010040e01c280e5201c003501c00340d0000c01695602e1415000d00c0c0c01684543d030307111081c0d10048c00d90040c2e03255190107a410096075465a90700450003100442d00080003007040c4 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 510932616 1250 510931366 510931387
    0x4170c030f0a17040507080f030412240f090b011211040b03030d0f050906180d0c020a08010504151a221b030b1c0b0604150807030503210103080708 65
    0x40c0000142c000000f482d10308000603c00005078400894482001f5101a081000503407600c9104074000c1421602400e140074001448034110454a502500030091940046140440c247d917110001d001c1980e0300c030704e03900060204c0440020300604104600059401c1d181e03603907611030816a0b400500c12903954810804503181441201d01e4071885d000d0421204c0c5000071000300510083c0d0701580e0a202d2a80012080d02c80581c0145c42d68230014001c100c001d0402500b20340700c65400070101d03007191201c07030000b402580900401e40500d2040344540ea903c0c050312490300455071103a0f01900c80710b600303400800854403250f0104590614100c40c00c0b40344421012000044c1c8036070040c0d40140c00700080c40b0004158960301008810100715050b05003410781011b480303030900fa2014050300d800543d801140c00c42c0b800c1d9200301105101500070307210f1155146142b9007040140e81c802c0d00d158200041d0fa510400280c01c9000c10003411517900700f01541580c407130044030b001d100c1c401000000c001440000d00c = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 510933866 1250 510932616 510932627
    0x11401120b060c150a2301290c0a051213120203010e15040b010b03041703070c060f0902010801091b08100503071401080a0e030a1d0301021204170c030f0a 68
    0xf081030b00c070115840c500b062240c021903540d003103440c142c02d145000c09580c0780d1030302642803007021581c4400d8071185900b0070310181014100840758580e1070f184100a4414a1400006050f4620060002c2e007442011804d2450030010303030100841113582c0420658494940c030103544400e6810118007100892464800700c0c1c01044030084200891080f0041814081140241c042c4594402c040020199070788000440c664001900c004050710049840340d00c90300e0300c5002442d405031140c0390024120440762515000c581c0b0100603005c0b1191644860829941c108030610f0061020840400140848004900405940f4039601c0304208500000c109e1070400311410381d001c3e040043c207517100c0c19030350403180c001d003c803901c0100c0c08a2207074400580110082d104050802c840c2c00040c600d80310380140c044031030010000300241800c0340400000c11503242480a0f1000a00b010b1800d0303000c1c02d080c01c0c6440051444007807001c024004104081c0341da140807081d035000c1706250408584619000105458 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 510935116 1250 510933866 510933877
    0x71d10030e010609050a0e070e040f030c020303121f051c0609031211030f1806062218051501060909110408010e010c110a1106071406130209011401120b06 68
    0x8055040205118440c0c1b0705910014500f00f402c421655510740d10f00c1c02c0303400300b90104c0e0081c00b00c1c00d01d00841800701303000d103001100407880241a6858880134180200c8000c3c0d05403030412031100310102018404003581705d44000740400b02c0d212146020030300d180c101e92f84000034008010545900a540405001300d001a01418010b43c0a110848040b5600a080d4004880c116105080103000c036089c1c000100104c1201c507180e00c05820345603101003e0165140147c0c110001070205049031100c6070b03481d0300c01d00d504001d0800040d8100903c0c0c0c20141c0c54403002e015071180c0e00c4101401004225040356490089030460100820583c0151030b031a006800b466102580a508082d1180c40c10913040d84a440302c0c107115186e141c0b1110500c100300351f0740c11440e003000740000c0b81d0703991045d030610b480300140c0100c2d4851007032100d4904001001c1410004203448005140703c0010289003140303000c50403140980417402018a4070001140000d01c0f1910b00d0200129440e07881c2404941601c03414100d51 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 510936366 1250 510935116 510935129
    0x20d140f12030403031d0a0201080c210115111504050a080d0b09150d0b1f08070e09120d0c0e0a06050706050c0903030a08130f03030203071d10030e0106 67
    0x3400d891100c40761108603407080381c2c1140068038001242c41c1402903405c40c034040b050400001c0548885641c01503814000c0a4019011071000340142006400111031501c220f04140902220f03135450110310b112000706a00e0344d0302c24895084c0040c8624100046c207440080003407030322800c2e9a101d50510a00f85141c1c5400a071418100290160070681190091181d26100717584903803895888001d29040c0c007000c44103203507000c1070030205080417820020f0403642004a02001d40740000c2006c0c241842401c2640c030803042500031070002c100b02e64075083d440c0c2e030052165024050440007074000140a00c0f4000848621541c1d03240e0002d410303031280c2400d1090f002c0c0548400da64a80b0341c04082c017160070441086849a0606001071500b024940136901d6440c1d0260055040500890f801d0364075080040080c2c042c03542020042012900d8240c407a01581e01940b0010380c0d0341003443c0000d0190070442844407003034041c0404c9100640b584080460710780c2c1c0b54500090b00da040180f2282c0507004aa0089 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 510937616 1250 510936366 510936373
    0x603010e1603110306151201080a02090903030f0106050a11120c0f0a1101032007060f06090504050604061a0a030510060f061211040806070206040302010c0c020d140f 73
    0x204400ca00300102600903468074520805040d03040404400340c2c0e80b60711003400018000d201180c064205100300b4503550300b13201d1042e42040c64003074001d00c87c120700344e100203140d42c000310521041d414001e450344d4100c407120020351700e140360000d20407101d00c41c10f2040b0001c0081c00681a880c45203c0c00000310305e21b05250030f6404074680b0007441003540e0041202038241340507101031000054000a040701c1c047d9444035080650000001c0150014070520140c040c001d00d81040e451241c01104004004180c8a02c50000b103180c00103601100312806900109055850142400301281d0009406c03a0b0081e4441c0c0003150744070740d00050a0340c0f402c0203102e554000c141c40401004010f40420f1a000d820301d10135040001a030707644801c40f9402c3e054030401e40890350b1605030483c980120340040c1ca101544101c0e861034135070303101280791500c44112031840050300800c003440100359080c002c0306c403001c10307078070f840005100c0940000b818614a200700810b42500020485107140050190311810320032a4140e = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 510938866 1250 510937616 510937619
    0x2042909060d061a01090b0c1e2401061706010e040506030f01060605030402030d050322020a030f110a080309010e01051809041505060301090c1809020909010c170c031b09060301 78
    0x131010343d52158400c0e010803541503000c12445807180a90700b0701440e0358000c008081c0d075038040b140c5003011042d101800703014201e444088104400c0740045080c041240d550f14035071401c40000c084250080391101c40d021101c00b40001d80c3c2c0d2014640550440c1250005000d840f220002450301c02e440640094650074010700091a0340c0010185201e035000b034040d501191000c41007240c942c031003111107200c8010140f0103004144002c03030b1811a5284044c05400c0440e442c0e40310b640d00c90000b10801c4440005400d0304504508102e004031005010701001141000806d9001901511720751054034100600800c0b00f40c24405a00c01c00d0b03144031030240503560f5074282401c14088000355002103d02c12800c00000c2816818140300c2d2542803500300c1c6075048030701e090083c80510841203000040043c0e8840b0b01c01000340e6a14010580200c101d60300000c0e039640d280030040c00000a4040f00c0900c03030182010041e0b082c00e100308807644404504042d404410071582e004805010b0031204a8121102000 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 510940116 1250 510938866 510938891
    0xa03060513141806130602040803030c04080d030b10050c010f090b04440903061008010b031b12070b070501020304062f0313150902042909060d06 64
    0x81092015041110207a003036441d03c100303d403a0b5100002c0306034240d128034005001500c41c801c119008078410680540790a81d6882e00c07918540040d50495240e16000608102e0914100840c000000d1181010310042c00c40744000381d80b4174070300515102405000500110849029404002d4056405008104001791810220140801150111164186002603a0890513040c440300c1c052030001488100c01509440c00980c080b082500301c0c1003c090500282c01280d8051040d603210f49107110414030351601d080110350035150780440ea1402a0003003140001059281100e5069a000c20b880781690414140e02861400c2c0c26a4404042c051000c40e000c0d040182c103400035400380c1d00445052000203c1105100318103003020020301c207059400324000c40c0d9103001c41c01442c1e1100c041840350004100716100e03140c03c40102c001c601d101d1aa1032960404528140c815481e1000c1041ca41c0000c01c03000b02c11107081404121062480f80c4849400205c5550b0380c0c03040550b281d54042d0062010008615 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 510941366 1250 510940116 510940121
    0xa300e041814031803031201090903030608010e0c150a0210020c160f0f050a06050a03091b0605040e0f0c0d0f18140d18060309020d0b010b0a0f0201061a0a03060513 72
    0x40304c603803ea0707100c04e0b01e1046a10b000019204241040f44190b0f040c0d9203482102e400908604504070140b5840f00f05c0006c80c60820f00c1201400541500a01010410a010800c00200300340f09511072080c1803141c01140d950026504c101c1d00900b020043c1d030340d40780c0382080745801c002c040103026120784240301048410700c00d000e8000311056000c0d07603216551503c5c02c1002c00850b500802c000101d0500c40391134028802d412550310203016684000042030307142c0092005086503082030012450001d0100310108030f035030303031581d0010000f0103892181c2413541103810395200c0c07000049083c44e16a0040200052160320950b201031150514058180651510466211a440c005c5805010344090440018002d00b00c80c0040d20309074000303900380c90600c0b030198010514003100b030383c012801d400d01c0c10009448000c400d01810740c1091003a211411054000c000f98074440e4030108590421004203d103540d42241550780c40401201d541c0c80d0f07404100b003140240794691019a02020b03001880c5485600355 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 510942616 1250 510941366 510941377
    0x807060f020111040e0c030a0603080d0b0901050d0302060403140f0301030f0b0f0106051b010b100c021e01090b0906090d0602130b0f04050907110a300e04181403 71
    0x1074009000e4681d900e00500014021481013030700e8444a000003070002c4104400a5034050309404000410039203a40324070b04660068104148890340d10340d4405003503c0c22041c0507004010841b81d1854504855078029101d50001c0c0000f030502c01a00c035501108074110003a1001d0b445211250390312917950781071400c0301e61907180c41500c031403e0900108040241d1401410b042e07803581e4490b2440c06800c0070441c0020078800c03a502c481da550343c0c0203000065660400c0000040140c0c3d584140e11030780c42c010031902c0440015041d01104000c0303562680f5980000002045070002c8401c20344404005010a01501c14400050347c880000302000d0100010350380030381040e101c650300715024147c4850742c0702001c1c4a1002d8215115000b4402005a03140450309140c1c400d1203407404d10141c0c420001901c0ca416004a000c480078501183c01a19005841c4200c040c000d05281040310711f80c000c42c10203001d0000502d429030040b80c0350b8400342d120302c401038075021725641d00c0981481c1c0050411041500c94219 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 510943866 1250 510942616 510942647
    0x41214120709230102070b0c01060503070f05100c030c02010c0c270506030a1109060a0e0412141602121c03020903060109090c0e040215180102010506061303110a080706 74
    0x2000c501440912030503000344031201178000f0007480f418951883d803180c1103641600182e40d00c036100814a0b490901500000345900340c01000c1302801c0c5400c00000e43c0000f05a03070200701c0411306040100b40d02c034414480240c0c081c01e04061b41e84a07410055058111900403030f504080503005041d4041c00510145039507904010100601d4072801c04068a5151301c071005402c00340a113a0301c2d003452400b01409604104010301200c06183d41e09a03003001610300300c4058500e003407260b0a00001c1030308100524400071409100c0c0e85004124120b016402c645003034003900403000c2501039202c0761400c011001c01404001440f248454030414000c0286d4040c20361140a4010f400000403514003a0242c550203503840740280c1265403c1641079058040300a01c160780c06002006101061842c0000a042c1c6240311022041002d02d44000a030035100041c000074000c4508000842844101000301d9090340da0026068081085c8640011280c1c44c864000a6860081c0f00c40042d8054000c000f203000c1e0f80380c = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 510945116 1250 510943866 510943889
    0x2102010914030a15060f080d020f0705010813060f0509100b060403020303070b15180f181b040f0608071d0c1603120f0209040b030105041214120709 65
    0x31604060700224288101c00394140d0312500007000060085030021000301c10703c4a0020b1250b60340c14110303103100203d91200309180c1120310a600c020b54148016010201d140c001464440e20b80720000f021803000408a171000d01d80c4008500c100030081e00071070450800740030b0500580c10402c2400341c80705101000041c5032031078500001807605021003542c04980d00280610704150160f104c1000d10380e00101140700520240038035516503520b144501c0004410080381011602c0c3c2400c020460b075201400003031107101c41d8130200132912000500441c0c81e8070040d0583d82d44820805c08070303003d00403641d4003041c598105080170440540c0050000c01710340d2614800c1089c480503190120284006403441000102d040084032101c800c0b41e1050341741c1610038501070010566400038001140c580200320f410094001030032000b1403510780500c01d01c0c907200710000c01a0303040655600350010785500d11881882a00c0c07140c80310079944c0a0a592135030306a04401d40c00e03864200700007062001203010361040e600 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 510946366 1250 510945116 510945119
    0x10f0509010305030d2c0114060d0c061d040e010b0f190501030c052107110c030a020405040821090d05042706090f0506030708011112040c21020109 65
    0x14003184103604803a000400b6500c0e12190811002c06401000c0c03806000c540c0c49241010f242920200440d0000719640001520304008150740300c0c14070002d04428840d00000d44644045100440c410007103400d98185400e04c0036600180703840529000d10704a9208e4500f01070306100304010341001021000459495500341c04441c104840302c40102e05094140c0400c04081c4420350080e88014814a9542480390508051a0004807800c40300c03034004010301c019005010545410180c100004440701010b40180d0001501096540b12012000303486152510041004d00030742d581199a0101c01200a85544d201a002642900c01c2030720714425500c5410700352400ca6101d802a00c00b540c0220068403031140202e1405a0260200080d008505565541c00a80080b0178480c614400404034401b00786031604408241c05d104ca80c1d4000c52090b4141104918030b214050211868003000782c02e48441e40d2250b003800c804414064000c0d19a007490712400001c0322411120400c20640700b43d03143d07070205 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 510947616 1250 510946366 510946369
    0x110a0309050d181401030f0e100c0e1305060409020a0609030c0b031306020702040f0c090f0b0403030f050703030608071818020a1401030e011d06091516050c01060608010f05 76
    0xd0002e072030025141012442e0138003402070000300b10400040140740120b02c18035848000000c40d01c0b403005031100341c0e0000714284840c846500801e00a4486824042440242100860406138011501ea045645c0c0c2c0da000811035079865218850361a005000260b100780c5450002c1c1c918400d0b40000e40d09085104000034098241d0760032a0300c5448030192482c04488156210b01c003a400c000000c0380d02540f10316000e11300842500c1084440c0425664442c04e840c5483c900d641400410741040d000741c0c008101c1880440e40280d01c0d5405c0000034a04159a080241000c8000340415003115815001d42d040000f1940c1c0e408820385610385507210208402da00c41000c921071030020702d1009422602120040110445810700302c08000c0040c11f000c1600d40001340800e08603509500c8100c40c4030f1213030780c0403001c1e0301c820060994050712a81c02000c00d806580f43d14940000f00410b0010342041f50b070301d603e0003280b0a0f026102d66144400003030017000c2e19444054101102401221120030a6103000a40c0d0b = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 510948866 1250 510947616 510947627
    0xd090906060e090405151f06050f0301031b0b0705031b0a11091003020405010803041401080108060f07050f030a0b270414030903070806040606090911090a110a0309050d 74
    0x8640c05074840503403855060092065410740148195554050482d14450b481ca44000300f907c03c960005e41e82c0301c0e4141404006207030100c0c5411100411100f8881001e0020320038003202c0c1901d410241310695020031122440a09050b504050030070030010840340108103001001d00074070700110f0034030303c440c1810902c05a51000d40e03807000341030002c6a000c1c20265080c0a04c030036801c102c851041c07034010341c1c903500800c003651000c5c0e102980c1640001001c001c402d10100660110700700c00d10b0304114551400200d0740e40c0b4080a001030401440c80004100c155000340100c1d5018504c6403a915241d280c80c528010042c429924114054002e10b0302082120200e06503000a0140905890b03e40b42c4941c5c56900e803400c0e5149004d88140307c10000d0015541c2c04004041c010310801d0300804d0310380381500c0d1840654245503c200f0041d4102101080010b40403481040110802c0e40c1c4a41141d441c1e5103080050b1070340e99054035114a00080c00c1c911594960400020076000d54101d644060708500120b40 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 510950116 1250 510948866 510948869
    0x130b150d05370b030f0a050f071706010905150a0e0415060f1806090608030a030608030f04090b010c0c06050a021507080402130f050c04030506240409020d140d090906 73
    0x4903014070030504003100265103c003241c1c01c4040c04542840328400489490298101301c1071380c0c00e903c0600c51b0310020404214140c040c100301c1d0240300b856054201d40a6031040c06010b107905090f107a1001400c098101d100d5090041802000c1140d55507070707490000c2c9100401d80d0292404026000c200704105000c0c0507200480301103110358152a40b07032a40e1641840380c4a450450781c0c6858282c0003880b0203e901612029251a50140da0f50707101e160006012a809a4000c01c07042d00140965504d18407064140c40490388100c40104074614034600484403900307070400041c8038030418140440d40b6035004000d80b031040f15035022501d0701800c14070b20318000e400031034403100002c80850008005040402000741003052a000200340c0b2000380c004001034800c1144c01d281c000380c002c2010030600000b041982e8000c180000d0b40704d0144921003080d07480203041e0300868000c0d51186007110440d11003400c0c3e002529082400c1d04810700d1080380054882d2034654458000802c00c01c4041045a0b80c2d104020 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 510951366 1250 510950116 510950191
    0x9050f0c0301090c090302060304050c13110409020901030b12011a0414010b0c0321060a050d05120c070302030a120f09080715090b0a0c03020615130b150d05 69
    0x242543e2801c400c00000d009040501ea0400c02511300000040c1c8a90005e0b41c0214481c402412003070114030706100d625550b0f4441c4224050401005180c1c80d12082c04a50507075140100c0969541c2080005030003a04004451540105901c02000b9010304c0651224040c0461180c024015030030510402081e201c00a510b2003071031000c04010004a11980000e0903100c1c0303110300303480c148542e24182d11b0080244200040e60075505008008031807030620840701c007400d011035991080c80c142d900d0300d695449040043d60ba0320b020000d0580e414020801508004650040403031392800d003945003144912000c1160358000c240010f0008400704d0040d02608203503410200101211480e0007031607528401002242c0060106405000c0344402c201d030020107101140c2d0b101d41051400504c0d0080c81c00d07500814aa054010b032030524155555845403840082050000100c0c0005400c0001245610310414031840803000040721078131124680c0003e403089980035000b04905201802460194a49a6041 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 510952616 1250 510951366 510951391
    0x9060515030a18020d0302010510091b0807110d050702040b0405010501140a03090b010303020f0d0203040f05060d0b04140406110a05070b07020106051c0b09070302030d230f0409050f 80
    0x14a654a00e0380075001c03000590f0549100c0700195000300d2429061854103a00503515001004140003208160000400111204100d8425004814404080c0404041c000c000120004c5801c0300d100e80b8002d41100800410389464420030800500305601c0664228000c034100f0f00740e4170b000c0c0392521800b4103c1d101a180d1100307a032454a5144002c1d071004842e801850b9076400319402085902d41e90b50b028510030780040c840401d18840e96031501e0030b56200c0c9800c650080006200200b422a00d15046403c141c1e583d07a124001c0300f4030640035107402c940c010380252a20403200324aa01c1c40e081c9900581c000c1008002e03074804050005000d1203402a0788011560820075031000644901c0c2456210324544000a2843c1e00c401c005080064805003074114489148000014421140006500b15030f81c0b1004010740d62841d40400d848003c40315040082c0962043352001c406c1050a507014120058400b0a0740c900c01901c0601c1680c005000302da44040c503002c0010034144414102c14020148030f10304 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 510953866 1250 510952616 510952621
    0xc04112701140f0c011805160f05010c050111120403110703051e1005040605070e0306061005031909050a41070e15010e0312030a05130f0302070906051503 68
    0x4036507100107003c1c101c5610412012006200c280704001c0c103e42c0f2540c0502969000c1c2c140035141030b444055072410580f10920400c001c0000410b8202291000e082c030134642811410300300d005000d0b40702d10740c1c24513000040c80802c07051032080d118403d61290321480c50b0f08107a007040c0b558582d02c1c0d0100615581c0034048503803040c1c0102100607000f108810071140b43d403040f07005060548400341d030111000c940324020f2244a64010030001c02410003a00100058640710b800216442c0c030400f9220248000080852294294642800071041040344240419926071410710f558841c1d0f448141e54120300c2c140904401603c0c1c41203801050307040c0720b91002d0034020720400584e42900d406504158402e2010000f4110028000d40e8400d40d00ca69210b680314143c08009405100f506100d10310a03044000b041c03011001c040192600032200040014040e43c1e1140c50300c41d80144030310301400404040542e8001c055001542d40c0c140c0d405c1c841c1c2400450398401c10302071052042c0d801f0001c01c66040c0300 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 510955116 1250 510953866 510953897
    0x303090d0e04090812042001020a0b0705120723040503060402040f0e0a061e0e100c030908042c060102151b0f0301060e1009090b030c04112701 63
    0x9000d80d086004000041800c250755400c01e1950042d0103000c17034116070030308100c14801c17450154403441c0d01540005215044510000392103440b80403008100700c0c000e80c040348509100d001038400611403180401c0ca982402e4802400451070310f800782d030300341004440410102d0100c1c400c5e20b08451000c2c1c000c0006480f1a42004058075080014207601d640e60000c0d105443c0742007100a45803809448001880380040d02d00c2c00a40801c4c0010005450038059a9100514006640e00540800d001c0020303590300c82010440142203101009084e01a0200d804104500905100d004c1c108105600070a9002d00140c140b42160088400a02580016416905042041c1036403684115040200b00c90103801c0c00028210383c124039000c40d40800040700500c004d941043d0b006011440071240203441e103503100c1d4010400981d90142b140000c2d243c00f15461a40c13810400513900842c002d205010103041300700c2c84881e170307002135504506018004a036440d64410b0427948030711840e4180d5403190f2401441c0c1 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 510956366 1250 510955116 510955127
    0xf0803150109360c050d0b09010605070321050a0e0f070f05010c051903020c1302030402060405060d0b040f0b010201110301080312090f07080304031a090c0f13060e0402120303090d 79
    0x806819a0b403d01c3d110110400106100300c480240b182c0e181c058560a5000b90394044440c0c1101071805980c0701401031060b41e410800341c0e9401035040c50308000e2003074144044d40400242d10100c5c0b20301403e02c410f2007039629154104c031b01140051401c580c0c0b00c0c00700380e100947c1c3d119144140d008a070300c9510144211751090070b80303154090240c0101c508014100e002109403980300001038006800c039a0050f00300e450010301c038465580c9605003c0d421404c050b000602248980c0c480c4a200b82000681400295090740240340f6041004008010110803a407140025002c0d600042d401540f07800f100060901e015000e0340d0680b0b80b050002e40c240103003c042030380a8071300a0400d0009201b805074200184000b0801017000d04040c0c0040c64480e071a40c908a004100c050780300d41035014000080124000c400105688606000c1703403c034144860030408594417500c241d204210050810402103003401d40c00a159014500c01d8030084d030b18469800d074198481c08103031070010258100c10307207205c08540300d0f1 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 510957616 1250 510956366 510956429
    0x524090c13030503031b0c060a021c0f05040c2907030306031203090308100b07110a09181101030b0102060103140c061218120f03130f0803150109 64
    0x41181074079140703841000900c845229402110b60f82c0c000010030400c555080704c503003c0d41d03151551240c185120241c0c8180c903070b01c000388032403105a408203c0e900c10a0801c10f035210841c13643e000401011a000851402030482200c0a41307182c0441480004e5400c103950307155554032407070200342452400021410341c03e40e000340c2c0203404042d11618040040761607415800c03039084150320002100030759440c0180082c44018484200302d40c80700e000b0080040c0c030780101c9a0803540710f03584459540070b000004001c03401541052180e0380c5001d003003000106013140700401050040c04850200781c001401181526440d40840740140c100e0001080000c480b141c0e0814081074140035541c0c1c5ca0081c4000c40c0d8503800c12501a91440203400c00d1024200000c40105208040c0e140946460680700c8210801d501c81c01003102240310001000038680d020014a10300c203154030402c80301c2e0b580d8040c1458003043e001a50031410491207a4500a01c0e5800344407010100d400090700080c0300503442d201603409084c40c = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 510958866 1250 510957616 510957631
    0x2161a070f0f0506011211040504020f040e011b02010c0801140a0e0703060305010c030902011b0804350d0801170d0509180403020d0e01030213090b130c0c020103052409 74
    0x1000c107880c001030040c06060302800c05015000d203071000e47e00708070300711085500985001e07501d0301080c8030250312580c0018881034015240411092a000501030041c0000500c9642050007a1000005070f80d040d00411a26800395556080690b00c03030000b00c00c0f10462a00c40c50b40001040b00420039007091007543d40c0d00c10b5240c18002880c035600d0301c540d82904d01d0002c041d00041e9598400d00119a003013016111400e1864800c103826007540d540705002803186004130b0041c20b1000b030b1403a03650300314080100c0c0001c041c071103590400c0b990a426190b4400c0b0110281c0049012200007081620104144210801d80b4a00810442040349025281ea62110440c1c03508800020b09510500c52640141c6001d40c1c031030360049c200e6a400c4034000308054600e5102a0406004010700e4010051070b00400c0240c803001400010684900c2000890300c0c401c2c5821812454104000b031807800d5002402c005205000780ca080c0704580e10600300c01d00f219001380a0f401a10f04103180401b240c20140c0310150300540703 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 510960116 1250 510958866 510958883
    0x509061002030f0403080301050a1d040b22060207050114040c0504050a0f0e0f19020d02120708071e0b16110109050604030f02031005070f050703091502161a070f 71
    0x3c10740f019280720b6000c0d800540c1e00d680c00100402c99410411814070042c2180d004009089045040a0741068400341000d0030191190011070014500f11f0034a031080440c204c0180c040c0103084c90882d0180d000314006940b40d510b050700b280d04100c00422002d1107a03500500000703032141003a04210040c100a041c112946070360311450000161035116084034400510024207401d204100e2040c6411003654240d05014840c403140e8006803641044480110f074112426014080f481460701d00d0804140d0013842c0740c0c400d4180000d60000034034070100000040a10a0f8134550701e0b2080c0c1d0394148070744c2c5143da1244201c11701c2c4c0c10220712216580700c000c4c0c10500d0b20a040c00c1c0d45000186594225400c1507482020840c070fa482185003c2000c03c1d1150394000c0248818a86a8800b802610b1855100000d1200004959080520507584480542001031000c0040088150000d545410841070341d00f0341c0381c8400001c14500d85845403200c0344681802c520345001e00c0d958583d2807410f010141111001c4 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 510961366 1250 510960116 510960127
    0x201120f140103060213050f0d02120c0405100305070b07030807030203060d080d150509040c0611010e01150509091b01032f091302030130120225050906100203 70
    0x18515007064001c6005080140e250001e070140780204200c150f000520407a2218071400407a100c1485080005d038040701c000c60240c00e204443d9080110b00c0700741a502514005c10401d10008004036807003500e008004803142140c40d490f1007805441400c03800b5003c910940002060b252180c1c00859102d203010f80080e80d00110340c2e8846e083d6800c44890801800d03219200c0802e00560341d203452006020485146a680c10203855800c0384040030701400b41040018000b215410100b5040000c80c1003034440200706900c2580200703981c0c0303a440d0042510564190300440c4d001c50300001c4076400d4240c0c010f040c0321030b040d08000660041460040101454480240841c03402062401c680d846146100c8855aa04c545000b080302c1030b4620306c5658049441400184a5512128890b03080c21005106000c0b005032140082c5080341e606210080420280088545110398041140321a0101580d15040080000fa4005140c20303050301a1681110708880010740615144040c0018001d540c01607908e801d = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 510962616 1250 510961366 510961391
    0x1140f0405012406030f0b150f120109050a0f02030402031c09050301050108060a180f170408060a06050906120a020603100320030d0525050c030a050604140a0201120f 73
    0x2150540000d0800701c004001001350f540c0500418140500c0604100050804400082d0202015051040f501c0c0000b00d41c008d500d0b102c2104443e144008641249402e607034503814000504400c1b50003140080c142001101400e2050003902e001c1e43d8024040e02d042d000c0d501d1100d039200c903904540c008001010000003940d8400b841014003901c08440a81410710b0800c0002007034440c0c2000311013901c1c0f0518a004007180300400350008030b60313010b0910700001807604251a0a8091500850010b000d60802c2c890745c1a41540403c003210b505035110502d0f5942c2800f04000c10342240f03641c84c07461700110034007001460b110b80199030242001d008184010380320b80b62310954807084c0032003521600c80c40c1040e4480b03140c10403047c1d6403454036183c16803400b502140c00041074422220403605805640a042c01000000c0c001c80c81a280c01804a40000b986800d11558511050310180d881c0750000d810248c40640c0030800007182c98040e102c5031801894207002c0740040081c60030002d040c0750341e031031104d100 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 510963866 1250 510962616 510962651
    0x150609040c171b0f0c01020f1b06071d0607050115170c1f0c020d02060307031e0204120b07030608011416181509090c2001140f040501 59
    0x5161540c1c0c1c410b0062442c064a403480010080d000401c590718104000c41614040b00880d0381d0f29100000d155143d0b000d9220306806405078102e00081c28030007190141c09161040c41018002c0c00315000c94405880d20383c015242c1c5900070410001e00c240c007071860216801d048000300005c0703110b6000026195007108c050b4080d013100303801420041450341034164120030100144404100100c5035901641c03101c006204050400000b41030a02c8000c44811013550b540c1e1000c034515503000390134035a903403400f01c200074000c110804204240304e040c01d40381115200303039100795015140123000c058821030058a602c411050010020410541ca841c1d0104183e442070003200c50b5002d15160701c0c0b100d81800f088132008060305141080c00c111f014004511410300882580d02140c80040c543d11400ca05c402d8100e940c0700c00d81d000015074908113171000402c41e40c06210003011014005c0f2420f0089100e401040c20707100b400355804201c0b40e54101003003215404418076600140b141d800042c10208000300f0004 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 510965116 1250 510963866 510963881
    0xf140906030901091a15120a05060a0617010e0307020f1c060218091612140c04050102070f030f170405040c02060a1d060412200c0102010c05030c0315060904 69
    0x10b02c0c0d4540781503100304094110390f20106407900d03290520510b0f00f982c401c2c08040118100307174440c011340014a00d81400c00c1c020300c0c22203601300c400c2d50700d54500054404054550340c428020700314140c40380f07102da088040c402c4818000d5958051481c00b0001d40801c000c10f04407214040d4454001808950303042c128003240b000c0c07284a0800540c40d0040742c031001d10400748801029015040c1c070000c2082a81c400100070740c012241c5d04000d0310f4496148030150003418080441c1e09191f41c403c0c240040c0070703101c0c8003178422030b03200b60f007107582c1180c032140000f84041d41d038840200007524100c00c0200107010031103035800440c1088510350610341d032800042d00340d0380d040e00c0c200c026030001317001c0c000d920140c0e02a80c01240b11200301c044070308800c20b140a40e42c0307200410140038041400e40d1101124401c8029900c443d0080d88480003113911741011a464411440e01c140c09580703056403007003402e40544140c5c1e04c60b0b06a000c40c43e04680c2e8101c480001c902d4650b103d1540003600300454843d40e5140e124450 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 510966366 1250 510965116 510965131
    0x20a090f0e0a0605100504060e070f0e0d0b040b100312050c03090612040b06060306030a03050d0204170f010c03060b0a20010f06170714011d1011010b040c0f14090603 73
    0x7402d0700b01001c5e54494040e29420450145080804c180011a986080a60040c6c10382c9040c0d0101c0061903411a0007801d80c60800d81d1280711802c0c00810700801641d42c0d03018600030032406c4a662102507070402407500d2881f0046c01c128002c6244100c680c0104083c1100ba4508010b8901c0c0c25404000100e00ea8400c2504900c9581203809020902c0b0318004165401b050507120940b071810f0540002c0d40e5458226002000c01000041d6880302da0001d805913401010141d80f00c2c81d0350b006810307400f9164206800b03451303442d40c60845c0005406219000c0e4174200c071180f002641c60420808000c4130300c140543d540c6141c101c40c841c4540030b075039000d1141d0300000410440020761036003020351149100500101c00d441c05e50100d48107011300174003800c50b102000c0f000d00f44414044100c5c019044c5080c0d00707c1c1820b83c000d6142c0c036000d00b03081e000507081c8080901a8002c001e0554850b08200494290003100302c0003c1c0d20b0600c11211030b0040048080d62200c1952281c24080c2c11000a0030a610440d05030 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 510967616 1250 510966366 510966371
    0x1803060501060809010c1d0d02090f04030f02030403030801030b090102070b01060e1009080601120510020d090b061002061f2706060c420c110307020a090f0e0a06 71
    0x4021441e44440d1290700076980d413000307001d0002d042c0c2c1e000300034041c0681c242030032083c036000441c1c1d00d5460a80d11b5000940c0644850214035200d08010501d40007160181c010030400c0303640c256030718400710172681603942c9a22244100c1e421a01d074007000280060850040c6e41d403c001080100d0b00400043c0e000302680c0e07440b0303114288203c050000d01101980d064040c4140310341c007445050000b00b001419941c3d000300c003080c440f0721402e01c2494200c240300e5065940384001114600304201d42c0000c1c0201d4010440c59005032100c1c005d200d0886a0307055014010380000340820a071848480000440e0454400c0841c10725440e00742001e41c0450400c00c0c1002a480c800d00980d0540142c0031307680086c070b581e0400009043c0145c03149054101051408205444447c030328400100800c203058401c180c000c0ca00264220111024100411400c5080f00c0850002000510f04000000131038621070780c06040d03000c05510300b4104201404240c4200e1401ba0303210351001c08404010000c4000e164040d0801 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 510968866 1250 510967616 510967619
    0xf20090a09020a0501031401210b0703050601140c0a02040504050c03120304021002010608190203010f061d012102040506150c0607120213030305070228051804031e1803060501 77
    0x108050f000080d8085418103003042d203daa80440c2c15040139044864000d82010052003000140500c840208002861035510350203104103941d06034403c1d48600720a80b2100d03824449103000314041d0089401c40d00299201450071300c010f080c0381c0c01840e00540b05408680034032480c40006410004c0554a25080304400b1041000758900074000d138a043c00180000c100d100d0a0041141d141c0088140460281c2d41c07080502d0f0440d1000d5200440c4400519001c000c01503c502da005406000c40034408401141c1400109a030002d4600c2c00940b401c10788208510042203a00303210280c50028040b6501c90083c0c490000d041c11650018000c642407000902414070340b051002e0100325407040740072199031040c04440c601415504c1c942d010340b501810003684554803403000a52001040c080e00e206910b98680e6a211010000d40c00c3c029a0301c22202004031381070070802150070700e40881e0003030000348800074907442c1005051700f02c50505c82e00d031805d1100c00184001005c0501d09a50049072002e03030381d100 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 510970116 1250 510968866 510968869
    0xc020d02121204082101090c030f05071b0602040f17070f0503030a080a020c0714151c0b01200a060509030a08071d15040305060f040f20090a0902 64
    0x1d80030141400622003814a26091900c1211001c0140002c002d010006801e00d51241c52608507103140032000110507031036840c1c2013090040c110311140c00307011034100b2089500c01d80c02d07802032903c2a1102d559060780002d0703420403401010011603094402d994200300104210640c18440300c0504009540b68011041d094491071520310a40d200040c42130313003035400744600e83c2c000c4111070400b07905203484849c586801002c1d00080c8252115410140b01d8140001580170758030700020b40040c0210765022030461800e5113540daa03c41d1a00d894048042c00c2149600c8100c0c95118410544043c540b44911200b0480c1c292009000c15807503a40740c1e8030000a070703005c02c80c1d01e0156680c48515100590300704103880001500c0a140a843d02c024004c55548403a4404964030b24107000320300c01402818805204120907225a0040c0000d40700d87c060f41000800c3c10b003522700594001c45c1c2c800c561103020314040d16200258174083c000503a01c3e6981c0010142c003079982c000500e01401001344001141c008520 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 510971223 1107 510970116 510970123
    0x30506130c09061103040503120705010b0d03170a020702090612010e16081e030403060519020705031315120e070527070c0f0807030e040c020d02 64
    0x40302020400342e114000300100c401c1d83d00c92080801010f003840741c8138400d5004e4690107511802000d0034111001006055883c054000020114014000a0207503044100150000707080a6040d001100f5030303441c1d01d6089242084110f1800600c0e0740403855100b4000c0c00548120001034151403038250030341100c0e00d00110304054030392003600880010100c2d0707040d0084040758070800113581d22640c0d103090001c42c2038032142d008500305803a640d62034024100080c8030304151111010000541c800d5400030b0401c1d40c0c4110051038441c0d8410f4072103d24610b40c1d60000da511507801018000f40c542015060b4000f40081e2008030382da5040c125018501900ca070310181d0068100110003040c0d40340d4500d60808030510002d0080c858591900071500406114009000810b6201d10b071000603103c0b00040035aa03119050403000e1500e2040003c1c1110000d41c2e40c513001da00008070007150a503050 = true := by decide +kernel

theorem cover : BRFrame.Cov 510791366 510971223 := by
  have h0 := BRFrame.cov_init 510791366
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510791366 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510791366 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510791366 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510791366 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510791366 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510791366 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510791366 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510791366 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510791366 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510791366 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510791366 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510791366 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510791366 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510791366 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510791366 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510791366 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510791366 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510791366 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510791366 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510791366 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510791366 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510791366 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510791366 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510791366 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510791366 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510791366 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510791366 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510791366 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510791366 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510791366 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510791366 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510791366 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510791366 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510791366 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510791366 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510791366 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510791366 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510791366 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510791366 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510791366 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510791366 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510791366 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510791366 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510791366 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510791366 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510791366 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510791366 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510791366 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510791366 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510791366 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510791366 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510791366 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510791366 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510791366 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510791366 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510791366 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510791366 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510791366 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510791366 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510791366 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510791366 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510791366 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510791366 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510791366 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510791366 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510791366 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510791366 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510791366 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510791366 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510791366 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510791366 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510791366 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510791366 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510791366 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510791366 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510791366 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510791366 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510791366 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510791366 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510791366 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510791366 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510791366 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510791366 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510791366 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510791366 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510791366 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510791366 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510791366 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510791366 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510791366 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510791366 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510791366 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510791366 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510791366 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510791366 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510791366 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510791366 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510791366 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510791366 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510791366 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510791366 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510791366 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510791366 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510791366 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510791366 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510791366 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510791366 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510791366 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510791366 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510791366 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510791366 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510791366 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510791366 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510791366 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510791366 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510791366 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510791366 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510791366 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510791366 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510791366 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510791366 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510791366 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510791366 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510791366 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510791366 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510791366 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510791366 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510791366 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510791366 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510791366 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510791366 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510791366 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510791366 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510791366 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510791366 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510791366 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510791366 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510791366 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510791366 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510791366 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510791366 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510791366 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510791366 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510791366 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 510791366 ≤ n) (h2 : n < 510971223) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
