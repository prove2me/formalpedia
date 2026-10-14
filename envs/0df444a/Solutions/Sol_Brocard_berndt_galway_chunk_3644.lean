-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3644
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T10:16:08.977733+00:00
-- url     : https://prove2.me/submissions/18672c76-db77-42d2-bb96-3e7b4511663e

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 655215827 ≤ n < 655395683 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 655217077 1250 655215827 655215851
    0x4060b0105041d07110f0607030b0d060f0e0d0c02090a0209031c0807021c120b0a09020a090f14030d0f05040e01030503030910060503070605160b04150605010905010e0d06 75
    0x2107a5201441d4011070f00450500c040018080140e405420302903a20440c40e9010240f800141d4550101c001e141c001580c950703010001c0d403e1002003e01401040c10000c02c3c1c1c600018540c07260812480750012032300020100e80c419106000074000107548411360f00b000a0711813940360028201c42c1d4000701130f95040240345145902e00c01c2c40c5aa04800245031608202c40301e6010031407009003e84104031040e8640c0a18001000032007072a011140198a4003620405501c40020b61000b17441c40480954540340108002040a18144200e10507000703211400952900c0c6510143c804900c0940038119107070781801c0035104800e004800008105003040002440a888400980031f1441389015540e0790800d044d90520b4011102e80c1d900f0f40c0340c81d03d03408118558000600300202d4284d0b04105441d420443d440c0d10444011a40140201d0002e400308030420040c07200441070f01c521110200000b50f190001100c42d12418003600f40490714501c2e9004181c80c0480902441d140300340c01c08100d00c48223403 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 655218327 1250 655217077 655217099
    0x5090604030605090f07091b0e01090e010611120a08040f0c091104091b020c121501080c01270509091f0203071b0b010b0307050c010e0c09130b04060b010504 69
    0xa800b008145c0055055200c044010b1004100900301040305100309201d40329403c03c003560f050507000a1042d0550003580990042621500400041d0a0710b6410b607510000038140c100416010a100d0142d90712110f40740c9441710580c2c0001083e40d498440765a5183d0f60f115031030803101c00c03d03174000300304001c0040c11140074007a8000d030a02c039030301064680340340c004043c0035907100050440c0c0362241c00f000403260f942c1c00130766060000e1080754510308104210146d6810408103c0109115810130000070940d24400100908802020b03600c03030040b8008a04101c00008402c11258035013001080200700e00d20340050490342124050301a9203005c1014004170403000b40100ca03d080068003c0b00b0080e0080d00600c4641540d0720200310030301e54423004d51396440040b905028a1010450100109045e10b200f00140c5440140039002001444098403e107a0f54070b550011551041380c404000429425112160901250b4448a200c070180c0381daa841101901203001068100441404005400a046 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 655219577 1250 655218327 655218331
    0x20061e13080403050a12030203041106160203010213081504030516141603020901210209090307050601080604020a140d110303250507060f20070522050a050c040605090604030605 78
    0x301300800810605140114200c01c500301c0345070070315106000300004039100891502c0b9a10f02250501c0d07507030b01e40d078195000d8120260030107174043d880800c0200842d4561000304040c2c0d201e0404603400307e141a1901c0c03041110440380100082c3c002c2c041c900c591100f07440300c40da44500c01e80d0900c40000d203906d84240781924981202c0c0f01400f1044040095080c800359842c050400800e100c95059007046c2608401140004000d00410150300020003d141c280180c5004c50303841419100c0307550396030b40141d6460405480a0344910b034001c0c000070f805003009030300b01c00102001c1c200e000512150b440703d03204000c10240c02e9400d4042040302a401c100103905400300e41001c484800c004e03140030304116141803200c0e0008014000100607150704c5a070800004001c044200440d000318070103c1000c9402d02c840d650007a900711f070704d0f000f00740d440228111030050960080e4504102c01da9802c40303000242d50381501c0140c1101c1040206220340c0340309800428030303c580506500c0c0341942c0c80e51110704661003 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 655220827 1250 655219577 655219583
    0x609020a050619081b180d0c180b18040f150e030703030b0f0105090910030f060518010606080a02070c0b0f040e0c0405060409050703140720061e13080403 68
    0x125003002990540100c101074004a200c01503617940c1c807a1103422000d51007074a11442810b00c403d100030780265101030840203007582c0300390341500403276443c5c0e01d0616030070101c0c2c09000620305054007000c2e41c1c280301c0c0c8020a14048011070455030727142d03600e5012040a20715000d4440c011504407601200000c0c0c02039001004082000f103980d43c44a0400130304031034403180710601c03402e080340ba83ca28130381c2c4c041c3c103492500c0c404a03a0f00b400d50702c0710620111070b074090740c1c0000c0c014100b40c0d440c135040c018240d00040c031510800d400b240c403901c00d082d01107088540d60b00601d03002c02d600102140f800040d0741e019000c00e40c030440c4101e45650b2107480114241c2c0101c8101c100f000d8001906005000b480c000c20368100b40a01706290034182080d0001e2158081d40c02784140031503a03600001d80480c403070b0f0420a040000c40004c0070560030182001401020a45442e080710308580510000104002901500c07071814004814041c0c003003504d04140c8094040d1403e80c0c070410b0002c03064080380f010002071004500c = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 655222077 1250 655220827 655220857
    0xa050105101707030809010503071116060306082a030f2d1b19030b0403030603021c020d12140a02030705060c0406300618060902070f0609020a0506 65
    0xc98a060030000b110b020361101920307001090100002514030742a03540c29942401d00c29126079030440100c8024046041e45681c47c03107440d01321a2030720400c082e070409070340065a060080c20b44451510b661042101040d0124070101100c48070540d4803080302901400e0000c050f40e444c000d010f200310f883c0003100700038650b5055a9941d0113003005203603600c26441a8805000c1c3c65000c81c108149101e0140d01c50a10340168428851180b15140921450014503409402072401d402c16090090041500340012030068503054110340c440c810a04944000310341c020068100081c07280d80300c85e145c0e150700c240c0c0024403c030b6030300c414016404100948845c101c244e00071900c0f40c01c50f04045150040249c4448006076040106011a42c1c0c882e20340d100d50380d00c40040050352449081304520b40e090850b00d45450518280010442c0480075443c0301803040404014007003551110128404c9214400000380f19091400d01000028810342040040600052401c11180d6a480c04140c02e98805200211442 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 655223327 1250 655222077 655222079
    0x303092a08060f10030321140402040f180213060506030405060907050f0a0b03040c05031e070905010620120f0702040e1614030c0402040b0316030b0d060e0a05010510 73
    0x4404205441d030049407050940704a040203028100130403024000a0b0802c44000402c200c5181102c10003d00010303e0b6004100b01c001c0048218a01e01d000e0310220f20032400d06125074105580c90042103201c0d0244820082526a25400c11104589800041c614181c0320040066241e42b130300040d40c4034038090400340101c0d151007a40340742400620b0300042d104004030440fa5840f0348901c07001e40203031000c1c03c548540c0c07611142002c09251107164811507040c422103410364003030420702c5284440a04080100c07402503454449c0203041d50001d0041100240c4a60756400055001002205010b003034041030714006580c146014060354840181e640f102c40000078180110304261051084103011040139003000380031516800a034400c2481f0380e00011903a14000c0e000c1c1c2c2c0c0c003805180c0e08003100800c115501c56039030104021070340003291344095040e40d00000c280458003c2c006d0f4600802c0084c42e566441403259034a04c010802a40444401d00ca100340c442d000036000d104076030180302880a600300c09 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 655224577 1250 655223327 655223339
    0x311203090b010b03010308070627030908071a1603050d0c260411010e042c07060c03020c060d1824090803010e0601020a0803040303020405100c0f0303092a 68
    0x480781a4405140d0315000c00c010008900d44c08140d860b40c90b4804804680e40201d5940c0f810112520146202d034501815417480c101038002c07490b042120016000c1d240460713911013203100112480c0701c1d40e034401602080300c425041040402d5610091090a08508215101c16044101c0c1da0705040ad8000c121452041d044034001c440b10007280c1402840c00c1c0e229898517554011084421410280c1408003121584441c2d1340c45421085003100203035840380b000c500007070116005410901c0d83c3c3c565400f400344049419481494103c51207074060700200b030030800ca1f60500545610100800e6411680c6d201c03918011502c109180b245d031400b65100d0323461220140700c0b01e80b87e064a0300d8652030701840c1c0000d0800190094054030b0445800c92100e0702a55a03800042c1d0928410810040401c1000410007080641507405002900c00545005444045003901a51501450320001d08116601c81c00800000d100e500403400480c400e140c2d50f0842103440780c9802c00860140019408010300070410b01c86 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 655225827 1250 655224577 655224593
    0x8190614071d060301030203190804120501020304061d19061803121407170901090f0b010e01080303100e0a0b06040b0a17100302010c1b06030c0206090631120309 71
    0x21150a1300c1c5500d59030010750b030b524010f90340c40e0021409111000078401101705441c0103207110058002c00030f44515225000b07520407103045400c545400d014a2301025000300740d2450741d2255000348150b54800044004c025241d82080f5010342d282c0d5140001403441e190040d08041c4207840e182069a55581c2c0c000a94480100d620429912142040f220356804000340101e03003643c80b0a0025512414222405010306603030140c04268143c40c00341c1084200118141281ca01948000041e600c8020640e100e100c150785501103c40341c0b0704103200e412121900250081760b1301000051903400200802c100c0e41069005207608003000c01c0d5080b48a80210340c0024207500107075030038224503200442c1c1c040c0000c07d00010b410014154608010410003078289607200a64509403000d80d5030fa0741000b0041d103441c401180041c0103400114000100c0040c031180610b51810710301d200380c200701203003010300300d0480340c08000b00c030820f000c180c0070401454003146c10300440e59010070001018144501 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 655227077 1250 655225827 655225877
    0x921040315050f011203050702090103080c0d090506070305030603150702031902071a03100f0f14040c022e060803030906010f1202010503100503010e1e03040819061407 74
    0x1c1ca00e0404007005481c1c000030300e240f415121812503112000046040c00c070307100d00801d40d000750072080503400071051101d188082c1038102110303003c0b184a001c51401c00c60307040301300d4411076070840c0c3c5c240600d0300000d004101a6901500c00743c12600407100c00315900e0040ca40a40d000d80c09a04001543c01c88401000f10260840328917000070852140f41240701e80c06610034001c8210000c40100124070b481c400324060b68001e011050559044a403504020040c1d180c003403140d030101e80841a5918071030706184c000c4106400c099009844480e026040c041d100c58008103201d42d1800114500b91480d83c1c003031241380003401c0d102000b1502d070728000161510b89201030704a122020b40f1407100b000002d0707800040c90700d8154280703000c540740c1c0c860700b443c000311a4054001c0c40d819420f200c1c24480c07001001075407014440d86d40c0300d99003124144500c0c035500e0348980e025a00140d04442d07001314034074564070f1040720828030520740010846a103540e0506d0340c240c1a00c0c00000030b0400d8003031074600241c0b0750860b1 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 655228327 1250 655227077 655227113
    0x18030305040b22060515090712060e0c0d090501060816053f0a15020306010212031e04050c04020a02150912030a231608090714010809210403 62
    0x41460f40d0364409645510420b40c07001018552901e0000d5904061a03049800801024201d80303414240040042c001c0e1001e40002c40c1c506103400c5002401014901c6011300842d000c2c4466071410698103d030002410354100d00b0780b19507488120000b81000100b049080c01403030340c0548001d09040c44104034481d0805110418444183c20090018000c0c440c81403009030003420724080140400d902c89820a89401c00160562000c0a201140400c203a001103100301026401d5803a0188140e001d0101c0340010380c0c01400c400915400103101d49009006280c00c5030040048482401c810800581680d00031504240143c0294201040c1c4001341c2d51000c0d08240c1c003402a0000440c241c91500c1940001840d10303041c02d85400c843c2c0c03100140d80c600303800c1c1c04540c4403032140140313804030840c5024680b00d01184005110701001401e08d1a0100311501030f5040c542c220a090701d0310400442e00007801030884880ba008034004c17954008c0d6071900001141c40810300450f01d46141d400c149004074002d06d03502c = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 655229577 1250 655228327 655228351
    0xb1804060806180c090717070c030e011101021b0a030210090b0f070c020a031202100e060106180b0406030b120d3f0603230705040b0418030305040b 65
    0xe0103400000726a550b84201056035500c0d605890343c940c50301d8040c2c902e04d01900035840728244405594072100d80c004110500d81d9a205c10348880c001180e40d013680d55030280009104982ca0749180d0701c19006a01d0b8499040005410b001d1401240c031028036210300200706941c803810550302003540607c00d01c911000380c18000c1000034a69191100f00c96001040b80101940003000075001e140141144060183c0103001c2c00e0700c050301c92a00c40c01c866010f81c11b0001522900c400c402a00c03516000e0280001840d20207403c0b01e9107040e1082d00c1443d544104c2d440620502100481d00c180c43c1c3d8062300007000260f80216040b5841401e0040303028815070a14217035080600d0300031806822007602c40401740c0c1d4000940c10883c000380c10401d03072034040307a4000e0030798000b2044802c151055001030040d64050b400760782105142070720418482d00c0203203414040d504803d104100f00d103000e52005034000000781c000309072154201e8801d00300e1051104100c0c0465900c1c010700090040302d210b00c5a000840b4944 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 655230827 1250 655229577 655229579
    0x216380a0207061b0609022215050d030507062c070e010b0c0a030e031c030509070f1a090a03020909100b0604050f04021c05010e040b090303060904020f0a0f0b180406 73
    0x1400000104050000e8542901c0b400848215181c0e2007090034800000c050031080446000c0702030016040b4090052740307c0c80e40c0c0e0390100d404e1400b0500e01d5801039042c0c035654a4001d0760766491014091503940e9070342019142c404861086400d0f0306d0420088078040c00b50038600d0420b07140c03120017041a00404810700050150030b02081c00011010340d45605401c1c00d2030040040d00000b40f42c506200c0c0021803402c8030000400d21150540c00c01406009079030b090721420398480d003560368050300c140700704845d0701a06c201500e41c001c1c40b1070003804207060140002c0d010603165000305030524025549140c181e4840c40300b249802e9443c0c07044206401c01281c580c3d10345441c0c000080c40303165070035480d103104036030020710058000880041030030504c4102406104030f40e13560000740c218020844003600c80c40036080000321514404400c80b4410440103000302d010b515560207103d4000000e200700f903041700303032035201003003c40b40c13402105c000b050485121340c4d40d160b41c00000d040c0c00c0408001c150085003003d030 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 655232077 1250 655230827 655230857
    0xa030b16050301030c05040e010b04110901020105160206010608040302160e0f150105030c0a1101090309152c03030d050a0e1002070803060f0607080301090f0c0216380a020706 77
    0x101c1750044400444011950161410815004251626002c0d0748a46898061902d10b0a401c2c00b034181581c00360020880e5640d8604000c1109081200e1200182c010800511215010b03071020b6401c03034042c1c0304440032083c0304001131840b03080c150042c080503c0704004001142000d01401c56001c40440156601100d2900002e0700c1800043c00910800da008220142014810244242809001802030288241c98100500305208600400d5030b404807a1485101c0780740183d90381140e40d1005c40c00035016898041c01200000c010b211002c0e0b240c00108013034107900c4124000c0c80e00441481600061130030074490709614091981443c1100c0a0051040c3c00220b0300c42ca055940c00b410640341000002048000500c40c2d01c00e16000802c0188080004959242240d00400c8051681103041022140303100b0140d0762004c2c040740075101c000b038541050250059180342085c01b81c01ea104012419081c0c1a494031542c1c00780e01b80b0540c020380214405100550400001303004000070b04280340140c02c40a = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 655233327 1250 655232077 655232093
    0x207150c0c170a080a1404030b01060905090c030a0908072306100e010e070302071a01030b1005061603020c0319021e130b03190f02090106031b120b0a030b1605030103 73
    0x143c003402c0c90b40c000c1625007005000d81001c2c80f0040b0803440440c0c0d115207e18011084110078080c80b0300050880c1c40100d800e00f4811103050107030380120092030542d980c010410010b00035101c13080b100c050040c0004000203070021907443e80100c840003103045010318184858a40300004021030303030554074150204a01d446500d00c160564a10102891080d92130080c25000f82c8101c4100526000c050348145880000c460320717141c166031160032481c165480f0292460b5501080e4003900350700c5181086450303000d5005409524180d80b10780180d4801d0050040003a041c2552500c2c062544080d454252f011841c108855018000b1100c407150f8407550040c0104030003401d5220313804075060b034510b4010074903502006244100c40c42010803260705900d82c075250f00746101c404c904030301500e220030001c83c40758013034014400c803010350119503481e06111540850740c0700c1035103588a03c1241c1c2e40100c803681d074484030350740e01c061800b80034000ca030f0742010440c0303603032110a50614a040000620041c00010851 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 655234577 1250 655233327 655233343
    0x70201080603031303050d0e010221030a090203060108010207021c030207211203060501030c0804030206070c0f080403050f071e0b1c06081b0301110405100207150c0c17 74
    0x20329001003035a41e1040400e1540c800d100f0004010300c260b00e400020805d0000320303050b0581c281c2d9500b8215142200c01a41d8480c0c226140c0c0005a4108160403070122122014540c4003099a4022a102c450303a000300341424800c0e08144400e13500010040f0550412040c45540110344001c3c2c40200c000301d850081d1240ea42e03002e0b9003190344803418644205564003840c210466003200e21411140b131102c078054010f249a100c3e541c080b90902511500070390080c201140300d160140c0151240b6030380c00908880e050120001212050079a500c102d01050821024201961145004000c81007a2001070f9241003165072081804090f5441c0300c1c072000704403501010444884403007150311420501d0310480618004140b16000502c0c1210004242c8800030318403403134000301000d6144643d043d07030500d426520000e4210300e404c00c0400040001d42007401040310300c4149881551221500c8050251341c0e12442050b03200051080d407a0322040c03205c1d4001803402400741d40b03a11b0312409415080c0f02d480e00c1d00 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 655235827 1250 655234577 655234579
    0x3030307050a02150109051801201b030403060203060a0e070207141305070216080c0d0212010209060706090b01060302070b070c03020c19090c020303040f0b0a0f1805061b0702 77
    0xb0440c0d100d003500030009401c149070500850b50715903846452034401801c00300e031880810503821404c2070b400c0f581846030051024008040400940040940f041190303c4680510f1040350705102030341c0d60607030500c00f400182d88603100c050796070b051060411582c03491981001004080b076600f804a040d8000900800311040000f41380fa07070109850008440a203000e808204036420601000000340d80414080c40a1101c0b00c0e030500060785070990141d4402507100502d8010300640c3d00200540b501e000200c040c01c0503580003501d130002250200700c0c00c2c0c1141604413135103505d40c00041c041214401e001405010f19203030840c03e040c1d0315103400c0c80164000d08081c0510116100120500d0720901000c80e0355600030348400310b43e491510702c84400c03455a01c00e81d142e0901d00440710019030b1020049a0050303030002141c4052250684508030301d444090150303014241c3e039140c0e013401000c00d4020900340140d18010080d8403545e03424801e003010360080003207840080e0480943c03103250014095416141d0 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 655237077 1250 655235827 655235837
    0x1050f0d090f080f1e0313080906250314160602071b06050a030b04050402010903121e031e1103161b0503091f0801090506030c180a0b010e03030307 65
    0x3600d04150b9120640201c016203070b0301d00082c9004103102c02d44010402c1000c0050080720103031240e00f17a40d41d54001a10b100400d4048030316080e01148180c0041c061155006000c0341c603280d41c4000c1040b00c5000f51b41d40c104c041100070709010615030000c4081504550000c0c0d11480c003200d13817144a030310340040303a001004141c0c042045028400d400055480310101c0507840740e0603586850018206800103284d101c0080e00740f10845555040c01e000c1c09010340d5042e1200c500300740c155940d1000d0024003889002c100310005003403001b0100b00c00312201d8032213025180019014005000c524541e03080c1c102c1e03545541c3c05c16055031004e2011404681d441030021061a60080d04110f00700c5950540d00b6107500e80318188201030007807000104c02080c0c203190440d04109040854000c03007580d030498642c0740d4041814840100b064000d980c0000d903000d0740c0103055501720702400d00046d14600801c0d030701c43c2d0078000031401c00205012600c11702181e00d900b4201850110009400690b90344001045102041 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 655238327 1250 655237077 655237091
    0x20324010614071b05190b040306020912011820010207030602090301090501020d02190f020a0605041a09010e0708031312231b040c0206060409080f0414030c01050f0d 73
    0x404070b50b0a803025194000701c008a00300003003600300340d42c5141c0d00486224040d240038001c69030240425000440d03900c12000d50519145440e118003c6d08440c0c091508900082e5112914820a2088501c08010045001c1c2d01c2600d50810302da12600e156001c1c5044182c5082200b5140e80001d400c1e82100e40c02103001d40c0d20120400070074003602c40300c1320040c0315600101e031107401c41400f900a011615010207001520f000004412074000089184541c09a00098030034008241e060700070b158480d014100d002c0030101000d4000ba000d80b411108507009940d110b540040c0e0a005005400c020300c2000011810031425181a440341101c40c821125116a01041001041610100022190651010f0000c40302520240c20385920303031594200c0021710800080181490a842000d6000220340c0c000d0210b5500c0c0c0d4107000050804141c1640c403d0b900b40845800b00300c0c42c130028405040426000c050304c101101c2810700d400010606141400424401581c840c03400e0000c2e64402201c507074000c200c0e5 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 655239577 1250 655238327 655238357
    0x30506041413021f0c021503070c030503090c0901150f080601020c090a110307020307060c020307030804150905120406020606033c0304090e060a3804050106020601030203240106 78
    0x1069070310003003407055182c07400d00c200e400350884145c0041034000c0d40d10202e0182940c00b1081c26200844d03400340841c0d20304402101007803081c1c1c06180e00460440440f03201e0b40038600001d011050980c441041421b421aa46800542c000d942e18030b11070580c2080740b03032400c0010001c0e44504001d4800c90155000000044085440f508449503d12003c07509aa4034109110000e440b544030880c1980c0081c03d056642494510000440742c41c15023642d540e0059403540e5a07044140d40600240480c00d0303845103402d1000c50170030710004010081c80c854441d45d40d45007107800780c1002c4004145900c0f98001d0b140c1001c01c4024030700c85070310743e102c40312403aa482e2044542c6800e440b07440c006030190612000c18081694074080c0e112041145810781103840b80e541c1c0c00317402c01c2036400381c402a030780310b24600c00065101000000c1080004891159005030740e44813002140440d8426403245005070b02150040041d810240011218070303160265080546202ca001c8401c1101c0611600041040981402c510 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 655240827 1250 655239577 655239589
    0x31503160b07020a091a0a0b0c0d050c0c04050f0a0b03030c1c02070e0f0106090816090c141603170c030112080408060406060602010b03030408060a0203071b050102070303050604141302 81
    0xa407052400030011080c0003929001014240700086001f5a014440490311710030007010380ea030303c40c1c00500800301d042c0c2d47d031400c81c1d13580c1040c5881c0000e4495845d0742c2c141b940e138034050300744948440c141c9030104d40b40104160064400d9100caa6009420820014402c008007040e07510f0340500b41c03000540c0c20031031404201d2610100ea4890741c00342c9080800c2c003800304401c480381412181150350300c0750403d440b0b100c026259003c5041c5188800c44c1c617001046100300540008014054900700701507004600c0100582950219081140e078007220b024035810190000609824403510000441980c43c01d2000d090642c071041c050205809240700082080140c3c110072540a000528203480041c189488e20401070015800380c1030155003048515003080c14004141c8046070590030040942d80c035900c0c541002540090829401c2025015010428100750510030040920540c0016524100c90400500f1104003a00e581e1180d814090f034040c110071101c0007a50030030804451034007040e5a40c80000c107 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 655242077 1250 655240827 655240829
    0xb0402040803121e07020d1713020909011d1005100e0121060207030c0c1703040612181406060f060406050c0109060507090f0b0c061612090602031503160b07020a 71
    0x400c00754000104100e40d6400f10369441c81f40c909031161120385408141c201c0c080d000c11204607114a0b18064080094909030004503045502c038400007842c0c44021f8846000c50042c0c003404450f81d0301201c154a02054140300300d590241c00001c0b1029007a040402e09003040030306204408044040681044600309200d802c11079040c0e00a0003107544191038070740507200609083c016a440032500b40000360452442c180a8508040072020714589410300005a4240503031121031f484041e61400c8410b603441100d6071110409000d00450740141111404103071420348014011402041d040010600c1922231005460595016042040c1c68140c958102c5005000402010b4550750600050194058010034500107491741d005070301503165299018005a489010740c041084c3e0b00c100005004411340843d48201840300e860b00b001c8901d0743c0140482603c0000105440c540c1e800000e0000600400441da4844d2600f58040c00c8406605045a20358000324819a01c00b10400103541c0219650814410 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 655243327 1250 655242077 655242121
    0x803030f27070f0504050702010b030319020a02032d01090c0501080a090c231512070504090c080f060d0b0c160f0b0601020c0603100b0f0705011a03010b040204080312 73
    0x3032055a030340c3d03968400c03030301d00752084c40c0c01a8501804036007400d01c10f014041000c10042d0041d45010301881d9650724007000c421483e404c5024280540300107a034244000304c0c0080080110203c280c40c000e45100403240000d00d500c0070b507894064080c000458450000c011240c007401c114044c0d60712545001c0141052403001804031410800208101c0c0e81071450f000702411454180c00c802d400003007400f071803040041100010000511080c2404091002c125902c440c140c1380060600b6940d08902041d80c1202082c84081001841000124044542403641c00042140c035440c0182c484c0c2c8450007151006072400d00c071103600040381d418410440500306030b11580316003c0b1060710018108550b000e81cac01d40c3c407030340140968548201c1525200003a02d0042e00031030800e207181d0346041032620480d0310030300d071040c02e002c1d080c4200008541c003849034042d840c400341400c84145848a00705800c4440c4501418402c42c8180400e11a40304e00006540b004840c803c0e020b030b081d4403200300c0c0c0c20241071281510303 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 655244577 1250 655243327 655243333
    0xa0b0709050d05010e0606030d050d2f04080114061008070311070507050a0f0509130609061404030801170c011206210605010f230d06050c070c0803030f27 68
    0x202c01080301c1584540c0304060306030305440482c1c8800040649503034681018000084061240005030940c0b9400305000c5101c84040301000304002c0004040d256140c0c021148070b803030200d0300300000503080c0550b8010382400b09a1821515045001800d422026020318040011401c0040d003854000e0707002a0041105c11600d40d158542450001c1e41c0d0403103406400d006100c100c0d0700107101d85040d0520300640e100145000c800d5501ca20b10340b81d03441600d04040d5a000c1c1c68002c0c401c08507002e031180d07800e0503840a800c0506803829040c09001d03010181e0210b101112060440c40712001c010482c0c1954100901c3e2441e030081a9050b2704014081ca50803004004000c102128240740700c24600084403845160284516070b40d517603902580c0c801603c109208098040b114890650a0568414030184002c1481c0188051a1500c1b02260022180d1242c8017400299000500c40304003001d000601c06240110300d1460421110904214054084584030812200007035038292986d001c800004100c00c00c03 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 655245827 1250 655244577 655244599
    0x71a040222020403051e0d0c24020304141b0d052103090601210b19050408041404180b190c05091f2106090f05090613050a0b070905 58
    0x4400c002e52207413008a0303051084600080c04200316110060a00c014407010b0500c01c42280b0050341c0e95511410102c17202115500c1072101c0d501025090001041c1c038030b0340141ca9140ca480c01c503a0288103e0b109034100e5001c010030080001c00729101540d2810140e6260001c0d400500e8003a2901c0340d1060810302d040c405026548800c1c4803e00914840e03805501216281d036070b510019204d60000d44107140600304440307942808200103050482c0c1040e4132060f49607011400d92440400c40d603041d201211901c100081c1003005024044c0d00003442e2104560810116075003402180c10ba044a0344020580c1c0c42c18000100e038070103101a20000c3d940c1071002071041d0b03149600d00900650040c08a18440c542c02c1580c600e00302203180440b942600d1540710202d0b80001c100c24a40306030134907200144601d03123400c004500c855184c014004090980e240124503414181c40781070604c1d038000c00001945455070704040204500080c680145074000300c050805444200c0201d0b0010483c0d0403030f075004943c0f659 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 655247077 1250 655245827 655245889
    0x1404021e13090b0c030f1f120f0c0b040f1217040806010303080a09050c04090204150b04090612120507020118080c0a08030a0f050d0e0d090e090102071a0402 69
    0x108002d68462240c0c04020390b90b0514202082c00269202d5003030281c1480021404c0040d078940420450004802c1c5803142ea0340e203800642885c840204581400007010740c613003000310719034404001e0800031960a007001d00b0002810042040c6115a0600305e54010140f0b0070310030404807840d40090b80e10030070707a40c0302d454140ea19602c19080c0f00c21400211040009400621a4403855050940c01805851503100801c100305c045c1000c00d505a078000d5484841124481c02c07500080010810320603030946071751402c1c3c00d841c215003007540102207041d02d9200442c001444644422044044c40c20322503210580c07400100c0e00021140c5141c1e2001807205004242c580000407801015601202d009840729103d11388213440780540e940d84008036030b03540d510f0391020380036501401c9640c9204000044580d05022542c0c43d004284c8003140200351020424024000701400640c2d201c081c2e00001d5242c480160b43d1412401243d0150854894140c0b011604642d42e0a8491100712800294200f924801d00 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 655248327 1250 655247077 655247081
    0xf02030f0115020a03090620060114010801090e070e130c23010201091707080c1e12030c03041713090209010f02011a04152409091404021e13 62
    0x801030b505202060192150701d2840001c3c0403103d03a501d6034a5010b15440c1140986600140a142011a4017801c403070140810007084414024654002051003580d840300000d082d150041c1c00a02c3c0a60801605c030740460400183c075001c903010400d0000702982c0e01c250440c03038210150801040006c01000019103005100b08462070050148641178400c40518016402c0f00c0301608002c4c5003030000c2c454180314017101c10161803594007030b800d05413900c540c400c10141800401101c1c3e51a90070045c00300d0417403940c01c000341500840d03900341c914614149124114982d010041000300070414880c0e00314000010309055464145e1208200404141c40c2c44250020390450200e99000401ea021489542ea10502540c003510050880c404244e0001c00c00b07210245c02040318020316420003020004411030042a45a0b1404000c2c00d207a032a050a541c008000c2c2c4240d510081341e01e0b00701b88410b481d2001022103290031650469110050440c0c8200b1023001c0300c0401903040c1d000c80c801c3da4100c01c841c1c140d = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 655249577 1250 655248327 655248329
    0x15020f030c060415050f010b090d1a250203040504020f0d09050c130c050906130302100203040f060f0e01030f06080102160c0e010e0705070201021501060323060d03030f0f02030f01 79
    0x50704d40c04510720070100700c0000311603040390303895003103680003004200048810004003091440644041e800940c0c0341c59101d1411004000001351070200c03c00c000c2c4050301e0100303034449480d1441c068420ba466240c0300940d240281e00440e0701c81d5500254001c00e01004104491442c0280d02c4180064a80c0d414625140c10708401e0060083d8074030300180011400c5442514403c2c2429103a8070f0420691a0521540350002241c0011400d05403001001503902c0c950524840d0f030150340115030781d80c04d200c2c0d14400c005081e4040c509021a04030750f5012150002c4060442040a10f80083e00d40300c92517a000142040340d11807036881d4400a4003440c0f80c400d9540c0100e07003a0007240850300181e0390380b030b0b54650410b0074814654007030a90000b240c2c0d100d206a004004041c01441100c80041c4503181d1140d10f400300703900100100b552144011035400d80d003408001c092400040380295480c0c10400300e5400800310034002e00b016500c0214141006140c1c0c0034a01c40c031182e1104644a1902d0040c00c01000d100f = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 655250827 1250 655249577 655249583
    0x9031c051207020f01200a120204090213080c0108040f020105070228060215010b16060b0913020f010c030e06310e090705060403060b010e03062a09030715020f030c0604 74
    0x34031081c01c500c5207903001c2c041856080c0b07006e594a0b1030070081301103560b80ca0143c4640403443d02004005002806800070304419061000110b10f400d1030f010f441d5151007015028035050050003000c000c081000c0d4080e99000790303020700b029540c3d4505440000d501d1240034010b031410b03c0840d01c00c410306140022401d001c0d01c81035006c482002c6426510184e480c2c600744560b6a442c0e2003040100034210042c010030080501c2483e0102d03a2581160001b680750000b1a0185503500a410f00c0c3c900f5441c0249640b01c0d4941e082c01c0a0000100e40d44008102d29030224499010b040000f6000ea0142140036046002d40c6248071940820200114401003041032445072001818408000c50400f80021400c01c003281c10040042d07150070304e15612180585030240c0711905000d0308900c4405641c4091080d548141070380c9900d04640012440764861070001034904041070001405140d2040d00e00140081c1030310805120001a000900c0b03040b031a010040c5038406c51400b002ca0300d16901c000c0003411501841c8 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 655252077 1250 655250827 655250831
    0x4022b0b0a060c110d05100f050a051825050307080d090b120112020f0405070804021f051b0109081308072102040509010f020c030d1109031c051207020f01 68
    0x780e81e84040303400500c80c03500544404c3c1e103283c501801e49000211008020b00c102e0a96401001e0685807100301c5001d50f60481419842d2030401407d0320851103810351103a0321220110481c1050942103598020005140c2da01041c600760040180b20800406002080018116100350741c84a90b9681c41d1210b400c004400300340c0030840851450f04030f400340c42074400841001080350380780000004000d22130000503038000d00c0d015200550b61f10f460050b24804c540a481d03540040c20648180f0040d41d441004030198684048110303100030394032a0480d4084040c58104c075049083c40c0c81070f1401080d260200034001800062840402c044420724041298020360903a400d1523940d804401c5103c0c00a80c1210440d50500080d20040c58a03034850b41e00000c0b000d000044a4441205803012a4440c0540440030760010038441c0c0c40c200b41c0c0c080c2145189404400d582008051400f10b96141e134200247c80b080020691400d4071280f103401a1540000024004892402c2080020703480d1b20304d2112411481d4 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 655253327 1250 655252077 655252079
    0x60605160c05061b1b01170712060b181507020402030603070815090c01031802270c12150a0b070528050c030c0901090e120403030302030f13050a0204022b0b0a 70
    0x5c207030075011000e030034060316405c0c0640070340c5600c0c160206000f40304600740071500741c4c003021024903842407102600006c2c07407141d03481d26401c94048000c001242c07100d1082d000040c180034202e11b8a01910400c980c103941c003503202c2c0c660000107410900135801175203141c400c0c40c2e03045068100c2c4601081c0211840c80030780b0303d80088003004500760f07010814007201482e20380210000506160b20a40030440d81f500b0b0350b0311041c0044d00034184400d026121084652404a00318110140c0c1c4288242c01c046001c021591400c2c00c03c020840c1c844a92180c911980342c080b6a040c00d1040c2445400e4402840c54044050b1000700d480540300d6858140d0f0070fa4861059056000756400c00160f200b1b188a0001c002021681c6801401e40c050500c020208602c1c1c040e4441001070443e045015101071071194401503240e02d00120360180d09500113050b802640b88800b41c03c0c002c50404242c01700200d4069070056035500e07528007602681c4103400700089100030008000e040302c5000c0d030f001c004184400c0350b40520131 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 655254577 1250 655253327 655253353
    0x20417010903021b1f020303090d03180f03090b070320030717030a1401080109060e1c12021209010504032714010e03030d0c02010b04060605160c05061b 67
    0x1c4500c0040240540e010140da40030f105902c501c0c02134180c1c001058041d650212401821840c07a007140040090303031001c0700b8030102c8402403001113840c040b245410010004074900a180500d464080644030080c000c3d014806d244c4038041070b0300907004415000d961a013041c9002810034407200c2041074200c0c84418417120540d0007004407a90560050b82901c0491141800c4a5480d4006001040700d555034041c0e00d074917070204440c070500030040300000241100c19030038220245c0c0c0d401c00014031141c01c8540404108007032010311051860862400c0100200184284c80081c421603030011074a141c0002049910281500a54400c0d88a0303900d51403500704018840085415004c0c02e800305006140c0d0520003203a103054411446641403520700207040681d00440d017580d121b5440a81100d4135500c0c01164150240240280c0c1442aa41040030514100004115008110390750b4000b0a580740f41e901131001c500d50b00005048010103561340c1c0c010101718401d80d1a07640801d950382e03010310040400d0b4 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 655255827 1250 655254577 655254581
    0x30705010f170606040906060e100305010b0a0c0305120c0c10020a051644070309150e031b04060909021804171b0c0a080d1808030d02041701 62
    0x12060381e90301c480180034000e0b05481041a002840c0f0340d080501480002110900d81c041d4200410306500c4a1aa000444040c803002c0c03500c601c00181414104001005240400c4003183e021440c68139081c07003004041d1038122164440c0205141d000c0c4160028000840d1424005240041011084501e07a10300210004180d014129031342c0081501440121030403541200e6800c28544140000e204802c0381e0250481040000c42d1103500c00705000c80c0c08500c8282003200141e03102c1303541c0c0c4070900340380d0540e40007459125a40110b03011508141c072004112030060f4410204c0e01c40007425200c0301007a110303016414000701c2c4070310b03485182408000145910540320380d079280c46e0048c10048588d10708440d01c0c1c84464019108941d40342040100030383e55904c00019000c4001412a0b0a40340c0e545002020300d040d0058140314822000b04404025004000622141d903220358200000708100c4911700282810b9140e014400c240400030740c0c45200d4005500600c10755400a0034164868001002982 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 655257077 1250 655255827 655255847
    0x903090504150501050d1508034302120a0c03080c120301030206040b09010210020f0304020111060709140a09060f090c1b02090606040302180f07022409120310030203070501 76
    0x804504d0820a071804030f03445800205a008410034010200303513582486a2855100d83c0e2009260070641a00b0301c4510300ad40c0c10143ea00c0080c0080d01c10074401e0074044100c05105090007071280007442e240c031801c490107016440303000b5081214045130b10340c0c2c0c3c107003000d4039400052400146d000f80d0403100c1951001e82c003641d060741e402420b001e0038282800c00b44015680614001c50552080c00c014104040c0c00d0700003445001c111008641c2c60341414400504030182030b5104d0b5085401620410004d99131060000c030480d6a100d04a0341403003008400f003008a41150000b480e20390800c800403d180c603075440b10400b110508903003040491031a8030201d8161261071492031802d0300101450001d450311810701504110010030103883c1559980c0001d426840981854861b4002c4c101088001d000c2801901c0d40000c0a00160020607046802e12654401c4140c0010049003003401282d0321030010040780076003c41d070101840d9a41041c00b9102c00401e424402244030f441021000300b159482004640 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 655258327 1250 655257077 655257079
    0x501021207080c0309030307050a0b0609070e040b040b1c11091006120f02120703060b03010f030609110d0507080c060f041205011b180b03160f050d09030905041505 72
    0x20703040091541da04205a488030741e22041c41c0c401030119008039502030005000e032504c11801800241c0c407030b150601c6038910003060103101e010b101c41040056900007410141c4a80f0841b0001100241c1d030001500402c0594039140d0482500c0c45444407a456035803901400301e0281041c81000040b6104220301000c2c1207600d0406c0b1544114200120b5015040700e80c10002c543d074011070f101080c0d4049030b040360444040381d81450b00d51014440c080d601481150060a03081905929544c1021008200b580c0c95120080a49a6510700784091200c1c2112840b10340c10b005005003020017403070502a40d180c4013805810568003d10321000380d103140403400ca40300540100411030910703140c00c1200d811003c0040081d01c465495030090807803a0320b19400c3d5240f020268550114200c03001c0900f15650071075403c0027007200760400c01d000078414034031182c2503101c0081c07078102002071114a00b201c180c011050354002035130624030404201034110b140841915003c0d1420030039903801c01000e10200c5c41a100380e07 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 655259577 1250 655258327 655258363
    0x15090501061716050a0503130b13030e040506100e06070602030a021e030f06040e0f0a0303060612060506192303071119020907200714030d082a190306050102 69
    0x5a1782d82c900400c05558090340340e9101d04007002c441c0c0c55540360741204841101d000115007903000704058005c1401c08ca0408281e60422103894203a0216084401c05d0100806025802c8400c0308207503643d0044480284e4030400964590030800c80d00f00180d005812986254600700e410a400c56190324103076840380d801581a400c5a882d06070501009054070005c9644500401070540044030041200c109000e100381e500050035440c00d03000810340108900320300c54031802c00034200131a640f04001e445443c034103a01400040700c40c444054480961030080f00c00380c0741455156240310804800594030805035512060000f40e0100c41454517507524042c90800914000300c60ba01500b0314008aa5201c100c0f820f0054840310b0344600244031034400c0b056044140c2c0074050502602503404039840c070709407055004050700206020068814200180503030807403800c3c1c011400701e90215400e0001041c0c09c0c100c4480d41e0740c56a06210100d0000701e4807040c08a41050400159035100081b40f2511240280310 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 655260827 1250 655259577 655259587
    0x30304030606170331050301050411010306050d051002030702030415180b090907210f091509030503130204021308061b030c0409050405070905191a060901031509050106171605 77
    0x505e200118086070701d0304542c20398101250743d480901c91540a00c1c084e0060310b219125400004082c2c41c07041d04040c0c01012407000c00800210001a141c1203440c0c0082d0240e10703991080012441d6006540c0001d09004200d0f5801c003e8581048114650055032610701003800c0d1106d046208910510b10129040a02800003800c1e041c03069038070314400041d41c0e070700000800c0d155001c00305031220410b0303260383d1681d80c01c0c2007010007111403001800c042417610140000c04450320083d0003400f000300441c2da01c20607008c6003011544c5a5048481c580c60f508050b400c130580b640e11740d5584032030486010b1010012110490705d40140740060364410055120400c2c074140c18280000090311018000301d44c14842c0d0340f030104204c11507005161294555151420101042c004c0c118180c406501640044041c01141e1020740c1e12620b0446200031000e003004a4054813201c1ca03041d50b4006039118400e80c0c3e00e04800803840702da0240d1202090110a280d0003030b0b5448240801e180002620030a07404940c007044 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 655262077 1250 655260827 655260877
    0x2030406090e10030219061b0b04170408100f0c1e051303050607081e070c0f05150a0f0c0504050d0303091e080a03061409011e050303040306061703 65
    0x82c5501100740300d80a507440f030341d131344c0410f0b886c2111601e4451340808600c02400100d0b80461500000c03840d426222820381d4840e00d40e95a20700380500003500384015840c4107900c40e108501100d00400303012040310188030810306120001e00d841d060202c40541004c058031682481103a0740365080e81d840031405040b0501442c00c1d9a9640941406540031882c02e5000010035001c5c81954420081c1d6119021180303400c00c11a014014020394100400700d504050116640c1e101c01504072481c1cbc00701c44030304041251704080e45464a03d88043c5e80c18907c0d0030070071100352450340100580800d0400113010054084030140c9850203130340205904031080ba1240f0012a20907000001068054010b280032011540c200300360489a0207025102c0c0c0e00c0004030010b4555061049100801c0c240510300c101900a00c00101c0e010300610a281411002c41c0101000301e003160078900050000030304407640e9554034680305001d010305100d0410426040c04841321624008000c840d41c0452031140a8100c1030815 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 655263327 1250 655262077 655262099
    0x907061d03100b0a0f0b0c060c0c10051305030c07050108060406083c01150e01030b0f060a0914160305061c03020705040501060e130c020c090615040b0414010203040609 74
    0x4040f41d405005524009002107072081c9640c050441d40242d20794810360700da070551510f84003a21901aa070420080c5100c1001c1c0803c4080350b031904201c0104080d102c1050305c200c3c02a01c040050801e000c0041d04180080e000030b5401c00300d807020b0301c52a8450ba2418108012907119125200c015003204400030081e042c42041c030011140e1800114a441a80c8603d99401c51003101050000d80e545188001c2039900b90072101d4002c10703210744100020340c1941e035840e09003075000c0c00c030b40d00c4206020080758042d514500503c02902d9880410803600a072599440d600600c240d4504404c1e003002c0303108118581c400e0140500c9901c001d0070007582c14040520b00b110102034840150114042c0315400b25495a80303004136070080045541d11a125000c40c41004030343d1581060480303041345001c2a040701030350041442981c020044071180750564403000868040b2081d0400784911020005000c5268905400540241c6500e10040202c04601c0300043ea074910a031300418020495819081003141421 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 655264577 1250 655263327 655263341
    0xf0706080606040b030403170a09020d033006030b0901050402030c090c0408010501060f0f02061b0c010209030f16080d0801090903120c350112020111060907061d0310 73
    0x70b0a51850642d50344100e80854105036421000a00e655421070203020210034482d0700010800300400000b0b030140d00040070030701318840c010148907020403900790703400103110810301300700d45000c00c007401c0802014000010b048500041300c081c40810040345a4a10510813107225030ba000d40140203e450010801212120003801445419400c0102040c840428010503000307200f03a1710707100c4444040d2800981207a100f445076a0440d030221003000800071015030032000e1078080003e0503a503810f1f038254082c0680700707a42e20340d07802d440b59038800011040d0000700b11050309014541542d00e10b4981849a885200085010001840b00801405a03280580c04044014843e0804543c001514122039040d503800c06016004145014807a94a014003000340e9991500c8002c0802500c040c041441e550303170541030042e036444c4900541d120045901600402c1d0b40d00900b83c044980607e0041111540c944840c041c007070009605040e110b1410201030300f08086008001e020300092030588410000801e04 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 655265827 1250 655264577 655264579
    0x4030f080306120a0b100602031e0a09210611030108030d270c0618060804061d1e0706050a050d0b0f0d031d09041208070e1c140f07060806 61
    0x30070140408070701070810209540611552512005c1d2514202d9600344203559804041503400410071026001e901442007941e030485003040a03111452101c044410f0043c0390055420610070680510800f5541003c0c0c1041d540305080c10301803042c400c1b27000c0181e40420302c030307405965106004400340700c4203540141c0300501c400504022000704078010031404000840003901c50700b00c00c40d03060002542c0310060310217a178000c0d42c031140c02078a0000000c00101c4020f0015109560ba0480064540107030400800f840600b8811200c1303450181a0030f000398188010401c92a1013512000146030b401030064406c0005181c44803400d1038410040e001c040c21411401545c000e403210122030703040e43c0d00e50075407100300d000b56030b0580307400111001c1da480c41401881c02da10401e440020000040c0c010700d51518088141c8c41c0c003403001d444010041c1c44a041000d5a03550000301c0d4030f012042c18181400c81d2400500404002c10900c080311015a140c3c00300070311450701c81e080480f080c0401809000e00a8101c0c00c = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 655267077 1250 655265827 655265839
    0x24071b0f031701090504300c080403230138030a0510020901021506030a0f0602120112060b1e060901050912010204050316261e010b0102010c030204030f080306 70
    0x201d804250310b00c0c81003600401d4005039a03009000c14440144030544140d100303a20742c045800c0c07e5040100c0c5041c1043c412204002c1d142d4000c2080002c4201070ba0011544041e03040e800e62412405c0c01d03039800c22408140c0c81c8c3d41c60030151040d89603401c08040c00702c6003011804011008078075159040d00d02d23183c44d541c0e0188518000580050780404c030306115603030f03255401621001641d000a041c40c41c00d8002c4162030019009004042d0b80100d110941c3c03903408241a6803404aa240c071030f010303002e6080c41040f60b0060200026914100403010070004d440766008100c0217003484204205036240d44000901143d0100e841c148508000005201c00c1c4414117050342000f50110002e1080d620001080250380d401103400c001c141070070401440501c6041c081c640689092081c3c2c400348080405103a00e0a041d030601356184c58105101c580005000b40e036224101201d26029907005c3c2c01450045030056187c820700079080c6205c1c0c420340b0260b0740c1c040035080c19481c403a10344880d1030300080c0089900203 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 655268327 1250 655267077 655267097
    0xa050f0130060c0e030c0618012601050405091b0f03010908040f030b0907031a0601030e060f0f0106050406090909031419090b031603110c24071b0f03 66
    0x41034100001d26280700310004210007806140052108000301c1100b40a9444120040ca842d0340365000c0d07a542c800c02d41c4140000726004070040f00d10240f20401820410443e0784000c52012202ca0341e68103895060386d090103213031116820035603640d00e00d021030a100c4035030024070792280c50041d00300901c3c11402400420034000546952107258070941c42060201070280e03042040082c1a105a5403040311231020b40140d900d1a101c7d2801e1510700d0105601000c00c00b000500740b60300a034480d10611301c100c01107911078640400c1c4a1320116003036800d110801c1c140000022070912800854060740d01d141d5842c14042c0c41d001c0400050300395410f04409209005008003c45c213820000791094015254000042458014024041844c190802c0e904507004000700700c18040b1000450903001000d01e000108103d411506850a014003a500c3c50540960b514007000d003468642e41030f0840c1c01061401d2011345603c2c4041d1281c2030f0306040769842820082000004c00c0d1400d251805560003428145250 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 655269577 1250 655268327 655268399
    0x10c0b09011e0f1a0307030602090d080d0c18141201021605030a0e010c021e0102120d06051906140f040b0d2c03041401020c03150601080a050f01 64
    0x4a00d4180491601c1a529038000c3c10300c9105014a06003058031800e01c5440081050119854080d140005010700341c00140b1552a030311411400072802c0e411040032a201e410807100900036100d404410070000326110303250140180c0003014841110400c0c00c1c21600010b14100b800900b01174143c0601442d542030100040144600f0702100b00030303108901079540c40043c407402a10700c504070907041d81000710701d0540c0c0c001030b2a107802c0d41d0410b052030814a07500c19080b00040f0324101060015080d00c0e180401d507000b0710720b00ca410070f4003507403404c03070340d1098807115008200c3c44669140b15400024000c540c0240c900c41c402402884480c00341114035140c1511444a0940c03548807e400d10041960307003680c210601e00d654912102c00280c03003003581d0b0300682001202d90313034026400b512140e40f9900c219500c50ba80208509541501c3c00350540d8980348144c90801c1e80854102c0340a80811091000281090076520555118051650800b60245d0901420a405403400c48550207092002094a480 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 655270827 1250 655269577 655269611
    0x2130602070e0108070b04050f0f0a062109050a02280b0406080105120c060310031b14010c051015051806040b1215040c050d0b0a0c050306010c0b0901 66
    0x640400e80051010720b14010040c140d400c4140c0c00350b46039402111040c80250342c0b00003128111002210148201c066000001e079040b4a20101c9950041a02c84001002a080501781403100000f801c050307000c21341032255a0544a04401c024900d42010712514014034211f049030250300c0c80c0342411a000d0302450701800002c00207401c6103100c880b005c41c007005001d034031001e2540501416034010720f0725000c1c0240240d440044000d000c0c441e004c040300041c1013140192801c1c00540e04880c1c880d403203c0803141d1103490920280180741321105d1000b1021040e5015a0f2148480c5500000404403042070a09402c0145907e20a900b10f071103568100155070350b034017082c104c5803c80320514a0501c3c1002d03810001101e07103650f0f000340079280810601d19400380115400d001042c0d0848a00a56501c5113016070603100a03401c0039901160b60000c0d0005c0c400c0707600350b0728405e41c07440c1c40800050703501c2a0251040c0c04101c5480340007442440c400c0c00002da1001d038440c1c1003c418030000c142c1540d03000903200 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 655272077 1250 655270827 655270829
    0x307090f14041b14060d110d0617070906051507211205011a041a072108070302180d02040e0304060c020306061806011103070f0605040327060f030213 66
    0x30300464001e00092894030f43c411510b00815621080315414101d0401248103400b80080c2684059698155403200c0302c981ca080322a25180c81c9803c2103203035102d03010080c68129030000085070303120305100410007003c42d00c5040240e540080c0740314012104400d0b1030030742d54090402107410201015034605c80e00014145103804030301688903107605540301e06000d81250816845091802d41588402003074200840445050310605441903810441e11500307a45e9900c01c50300c00074492211800d4507941905241510344ca2281e1503035072108680c90300304044059000e030403030f50541203060404240143c681201d01d00c41042c40600301182e180030110056003035400542c000d030081800088104210310b0240000c60b8851000ca8291032003441e8290208402c0c1001003029050008402002c0b910342c108200740c5002680c090170403154202c07a8600500580815103044003c2021600d041c0007480e20124a0300d06103c5000d4074410303082c6009030850b10200c0071070329403080c5642048428210812a40040 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 655273327 1250 655272077 655272083
    0x1b0f1c050105040311010c0e1005130e0c070b0901060303090e0402190b0a0e0d0b012c070528120b150301121106030f0412030f020a090801060506090307090f1404 71
    0x1308400740142c003517609503880314854600300f14102e03010003440c3e500e1805890706c0c90781c28270b45a030b10740c840c000e240d9440101d2030f04001d5452540d032040181c03403403850000308401ca00c04d083c100d04945440c442c2c01d01b61a00d9000080118140580130301c540c41e488940b5a0740a8001030140b106503030100301c840380c0307420b2541100400c242c00061594440703410007404442c0002c1903401c01c0c140380b43c5894204039401d06000b1143c100c140d0201000704055003071004200e900005d18444010700348241c01410300c0c0e0001c0841e900a0301c400314188a510800f1892a89807100d0b80c83e14441c64521080380300007483d143c1ca4140c1c0c04035001068824215100303002e140a082c03c0c103081c028146040c02d241d200450401203440c8941010801c018101c400d000402e50803070b5000b100003284000e042e2080c0c003d40070b202c0e82229024800f0460464280e030100201048400c0c441c020841c098588007032115a20440200a0701640407240402002c41540d1011040b2210b40000040c0321113402052030340c01c1801d50382a = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 655274577 1250 655273327 655273337
    0x5030406021902280b16031b0c03260f060316090209030613080406030b150a1d0406080d0513080114011e03030903080a11010501080a051b0f1c0501050403 68
    0x92000c4045410404481d206241000200c01c12070ba41d640c0e20008000708641c016496000c190040d00f8000d404c03e41c182c2d4164809016400e805090041100700744027020f40c0065026a000c3c0a2a927001c07010348034003030380f04039250240d5482c451800150480035140c1c0d6098450901c51480c01c42c0455400000741112110240e40c030011801010b14042c030142c09040d203020802c0480c2c0004030400106ea00b12040e60401180004118001070044e0300c0c000a41004013800044080d462903214080403c42410f21562094101c0100184401c9501d24011154190301140c00c0c0c040c02c500500140203004481440b132481e00d500d4030b00060a556500aa01001c0310400300107001c41c00a2805403c2d80360411260266080e03e1a20020b120103894800500f80250020b11008920b1280700c00c0491079520200074401035940300f64a43e070310403201ea010396003170003440081702d001e0680034142440c1650040141e16090b02c2e6004008078003541c0216480050100701034100022803e000d0644a24002c2d210 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 655275827 1250 655274577 655274593
    0x60807050a2f013204030504091103071d0f0f0604030f0302071502030a1704060216050f0d0203120103020907050c07060305010512030a3908070c0e040506060105030406021902 77
    0x4114299034103900416a150301c6903211410008900c0c20032002c01d01c13000030700089a121414191114450fa400112115080c1604071100030017940080d40030380c2c0340351307140c229607070009484c1940702002c41001c99015410182d86030a034940803c00d0359482c076006103100c0c42d0640d613a441c40c02081c2459402c901607001030004003e4106040d46a0030001d0050001c0c51822901800c000e14444102d1100288606034802040c1800001e505980181400c881c481500002c1404c00542c1c4400646140104c0e01c21600000d035410b2001c01036031400004002100c2259003580c0c20003c0c015002000c240810000f07118003c0d140c841003088034002c0426480c0002c495050038184240444440024242070b402000035583c500d50140310301600d0090400900484d600c54002822550201c4004605d8000d48500200a10001600810001c0d00c59070000e070003c0e580383c031081d0445c001110082d040f5085000003901550080000716070051092030f0041c0342c0b00c84405442e0031490811030304801a8407041c4 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 655277077 1250 655275827 655275917
    0x6120411101b081803030c0f0d0318080a020a0f0b190e060a15090905072303030418180302060f01060806131d1203040c090204060807050a 61
    0x241c000c04141d030301e03210151801c8000c035564842d449910040c00444001582d0012900c0e12004403a100e030003d00340c070343c1ca00340d80a989554018902004c07060380200216020340501902c03403201010040d030180d010010320307512141166000002d40c8000e502401d502e500000e20100440040d5910030710708a00503081184a10418100100180409505c0c140740b080b00c0d440c0000c0c2490384440307100c2c001f00b0f60041c5403c046c260300728a603100e40006414100080100180880c6a8081c0e5110103040c4c0300c00b650100c01102034220b0f102e42030b030301504100018000385840321000d411a00c04030303a01156881038038400c448005c140b58019001a0407400a20a83c004204126401400301d8070b000e4080d8180000014600301001d0216481d055540115180180719003603041c1250701800141e40710240740c12980480c540c41124201d0b8241100d49001c210100503100b91001d075041d0740d90f6800d0a98440303805440642c400350508080c0090142441106400313050320080390319480490048600780c0300 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 655278327 1250 655277077 655277089
    0x80a0506010503061005120c031b090c0a05040302011b0818011b1101051309060923130201050304021309030e040f0e121c02030405160e060f06030606120411 69
    0x1c2c004034420307040b2509002d1907002c500700b450140d94080344d542440b41c40c0441c03005d1500b5440001d85805014200c0c98a0b2080903186000d02011030907520783d8111b1f034411107429403d1003918510001700c2c0007408140b002d54410410b1004d404030101c00c0756101c20103511000c480b40c2000488131183d0340000304903601035074814042980f910310703511a60080c0141c1d44d112240c2c45000308215040100101e142c040210601c00c0940040001420400c00c0c242c9800316103001e403040140f4000c42c00740e03148811100b1810b40041d5841400d84020b64120104241d0044405510160042ea400070030b4001c00600301005100d1269030520035110b9a41280400080c00140c034040c50b03c0c3c005c0203192080114140c4400f24840725078008811120f962020110b2a03142040100c800d052041e620100c100010440700050207848850100c2c40c1140060742e1352901566101e044406a402000264080c12141086009180c0101f4024281c43c00c194624074502d15245003241c054035200300400a540d0f06003044 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 655279577 1250 655278327 655278329
    0x60d0c240314070e04021c0608060f0709060804140610050a090b09040b0901090f05031e0405100309050c03150103060605120a0b06030703020a0909030305060a05011709030d0501080a050601 83
    0x2400c0c240003040c00c00001d05070300b8400030080c005200c102c500d6400e10f0796983d41107901000f4100803903003c4811001e21400204900c0c0502ca14610030704021039040549031079007a00c20302c00703643d90070071641c10310108880c507420140048416070788032403c0030019074003440728174481c0803a001c00c498028a8201004800000e5601105d240c03407805940f80000c0e2500b8036919801a0005940781243d00c529010600420f480760307010b400d808156040400f040130210003040e1005e2180c4007482007544100c0d400c0118170492003119400702d080d400c40040140240c1028081ca80200255822859242c2c0401d0401462006901c0260021b07001803040040c1032058a001c0c1c1000d94440c0000611582c0c1e150303560b00352200151440fa00800017486a40e410480c64002d9980640000040d40d036680141d406868404002c07000300382802e00042c05400c00414801c00c880050396650401c01c12001c4502e40e03184094150390584c04104608001c1241345c0c0242402040d601000340000141405c115041c4001 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 655280827 1250 655279577 655279649
    0x21121109090a0b180402151308010b0609180613020408030a02010e01020f07081308070603020a020d020d0e19050a0f080f0601030b010504180b09030307230a08060d0c 73
    0xa0a0f0080e4159140c0008103c244062000c0b81c08194840f800040ca001e00600c96601004100044410044a101020341d080b22080780003400408031b41d03410131003203000380441c1642002d9004440704280c0d0700c0b074403003540044002e4038504502102d0220032003a43c0c02900040810f500c0011039074031a542c24494680c83d10881002141000405076450607a031203908801780c00441d000c00c01c080305581c81107105008011607811914607a5483c4805000b03504203441c228054045c82005101650000c07400f00c8440c138087c0d17501c200c4413059034100a030400c0d03805410000000c0c1900e007c146c40e151200184e01070311641c0d450300350032440d2564403450078082020340c0145410050042001603600111141035401c04c64000c01c8000d00002e0030004030040003405004407800da024070402c880e01200560140645a0f11048001c00c0124119904030300c055a0303909506041000c0c1801c40c3c814480a40c010740000e02c2000e604440d601d0394440034180d608504e4040b18440c0005c00c800001d11711800020035 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 655282077 1250 655280827 655280831
    0x711060712271d0705040f0e060117040b04020103020a05090d0f0615060f050f0f0706060906060f12020315091006020105061516290103051921121109090a 68
    0x1081000741039514100c10f0040380f10340603280102e403009015070142c40140c440900202e5003265035020b24058200203643d004d010403281d0500c40c800c06049800148115040001c0c00704036200da0340118002c0d80700300720040c20000103000300941c03a41c60580c1514224080d51060ba9628594145441160714511545a407084416001c110321178000350310351b0b000d4940e070030001d48807404090031001900c131300c8132155040c003000212902000095440801950b0400008100a0707484810170369201ca41002000d021485008014200e940c054005583c01801c9003e05640c0701c03400408a0800c41c010740b00c0d82c0030359400c40d005000c801e909216003039000c901103824801250b0b050344c03010310500c11040410080107403080581d050004030260040c5401c103030b501c0c0303048030482040280b04194007800111201d001e4441c0143c461025108000c45940c4c10100042418040e0b00ca0002c4900140441c0000c0c0807001071014100842881a640ca040201610a0380d80600008100c44142d0003841d10700454 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 655283327 1250 655282077 655282079
    0x6041502040501080c0304050a060e0a060c0206010b0702041a0a06020a060f1a0103050921040303030501050402040b09131e090b061203030a020d09020616051e03071106071227 77
    0xb82e80420142e170003001c0192107955035221810142c1c14004410302c05020b140c28210f00b5241640c00007244500c20f800780130100003000203548100c0e201d0600307100785001102e082c840407001d8545a4043c0604132422080c10345007034061000315887d00744907841030340940c000001880c148200c500402c814294040000c1100d80701d0100c80b5800944081d1049042641e203000040c07614904005c80d0a0307410807040001c8810f1040f000b2028154814041140007038100320002070319040500079035017682c0040b142981000664801c0c098142c14044da8003034125100c802040b4809030609110103003010149010583c0d90550408441000010300014040e00030b101c1405004280441501c0c3c01c120303007140c050f9940800040a01c060511084041e5200c600007a02c6001c01441000740e404842c401e100b61019001100c11107003031400c4804905100350403c0150100143c0c000c0e250550180c002030045080001545075105c00f09110b0709481d022030148400060700000700d50f003c042403624841058021 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 655284577 1250 655283327 655283329
    0x12050c01090209040f0c32060d09050d11070b041203210501090c0c0308190908280914010c0312020d0504170c0c0405070c0f030e0f010c020117040303150602060415020405 75
    0x4114550f00b41c01040e00c860f11030b0a15584113011100f662741a880c0500c410724903802c059071191041410000800c1d034020120f0038900380462120100d6a0401c243c3c0d0070280703440c0c004050505001c00440070400d80341800c8114000030f580c041c00d0b1321810b9200190341d6042000c0b00080f00d0303a4030081000c0c800008004030000358041003061b44000e0501460401c5645c00704510094070000100410720103010482207c02214548030184200a8a01420100311340200540b1803903aa4050350701995040752000102c1d50003003800340c6d403252282c9400080301d004160050101e070400c51034440c1058658040c4000c0c088840c1d410401d203038402015034038181c0c42480050b03444018030451030066841da00014050307405000300f00a0b054100c182c201d944206468003c208850700d0306040d11840c80041a00d400b54800c03d4060050396060710f0b141d40b081900301103c1550400103204401b09071304e4410200301f20341720420700c500509164000740070b60b0405180000751a118014102c05861040c00308010b5 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 655285827 1250 655284577 655284629
    0x62604020d02040905030c010903051201050a060212280216060207060e0405190507082d041103161e09180803040503071a060f01020a12050c01090209040f0c 69
    0x110360485002070b01601c0d928143e1b0850040e440300b2001c079403a0071703203074401d0641110050801007130400030f404c0e83c3da80b1442003080703161403070050500581c03000c8032040c155403000300109041c45002d82200a00d910345590040c0c1140c0307400a80c1d0042c1c200382404040700351a00c0c9120040e01560010341680c42c1010700040c9001d0542c440c05201e21344840104110021299224141110070002807150b4903000101902d0307080c09846c500794100c100226080c82007907408058001d0b0380c1801e06d940720750311f079034a40040c1030603250001503050140c170007400c8010601516607401030000c9414045020904c0145a540032096441400400c0c14040b5012042d08900c48515029030300481d42510381e101c03403c1144c590300031984000d055007141d24a00440f00c4560030790703511411040b15a031f845e050440004a0722903202200080a2811612461103c0350203040a403240305042400029654102e4001810544003954181c440295480d00801846100c2036500060b001801906407840361010008d03072 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 655287077 1250 655285827 655285849
    0x302012c0112020d2c0c09180c031c030605060c0c120703140303040c1202030d1b020405040b09010b0a0f060c06090b09011407300608030406260402 65
    0x10400241206282403075620b0f40c1079a2500c095403200b08501c00380c2d00c8038908091950445100c0d1120103001a11510000148001c40d8880150241d1031544950414981d64160000c2100d50303400742c004040740a8030100003480d6030b0002d4506008040f800710101404894031508403a0048000300070710505114005054811224140c4000003800810759006040400b0758100070044d003801030b62551003002c0003000c2d5000d1030140100141c480c6d075070000034840c500c0c2000020f4040d00710154080c202c500656000302c0030300c0e2070340541d5000906507000904913131049a049925007019818800b2502c024480c081500505032044000103040407200380c4910503d100d11780401400d1a8060200300d556002840704981c0418000708904084410300d010303140c00c1e080e44501e4002c1300700054145100300b00d5a15481c42c0c0903200d9500001c00061241590f4420350720460468a0381c00c0060200c81c204000c0c00100b11990701c400d17814000d051030b10651440260f00d68854588002030201682e2440134000c = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 655288327 1250 655287077 655287079
    0x314090d051c060f06090504050c090d11040609020a08090d0f0207030b070203070807050319050414040506030a0b04120f020a030e090601020c09010b1b0109080915220302012c 77
    0x2e82c02003800416800b0302803d8100d03107842c04c04140000380050700091010190ba00c1180c06200f81d90304d002e03220034517002e5200b1041e40561002610804502c008007a0461408003903c00725a00303880300c0c20743e41030b688032640850000303110760208481000184031308201c4000a01c3c10604508000c00025910340b9503001c00740410300c804000c61a658001c10407140c860740c0c8485020b446000b02d0805075100c0c3c10544a00c4642c005418000407540d1140e001c45003958850b20305a41400d4500c4140030043c4002411150503104458580020a40444109106074403840c15034104081c031510050104541100080c01d40d401400100002508200d4010690740140d07121100c030340e24440104e29082c4051400740c0c026401c0f00c0003055014010008004550304001d42900c90350000e2142e41c02c8a1040070003034100c1c04144031400d210325110841d000450082c80a0504040c00d50030540f41d54161100d51b010b281c142c1403020411941c20611031242e110312200c0d594800d10316440b1410602010030069 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 655289577 1250 655288327 655288357
    0x101104230315101d07020f06160318020409210f0e09060616080405010318020d0809060705071412060601080c03100b041e080715030b0a080d0314090d05 67
    0x404030f541944042c402049a0030500c6031007071041142c850280c10507211000107005550410b00c184c01e00003072280c000c0108101c800281c0c080244110b0040055100e134810003000301c450000540d440b030203100a024002c9000c5141c000d03540314404070921800400c60240009040007080c855005814024040d00c1620541e901c4c0e51045d0000300944904180e04901141c2e03480500d007441102400b50041e0b0303400380c8040140b10400b40c689140316a07500002984010300d4410b030130003d140c00010740240e0314050456401c5c103402d0383c1c82a00b01803060700109079260601c5102c14143c40c00050758000400400b010704114101000001c1c000c51004012900b10b080c0003003c602ca84803a604a10000e244a034181c50302c95490f48440380004040b400348070145a451000860488008501c0e5400c03605900501158940074000a13005002214282e6601036440d0740000341401d02805030300100c0409030fa00154150006403000341200c030207481541c1a9100141000741ca90300075080b0307208100a2082 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 655290827 1250 655289577 655289581
    0xb070f03140a020601050a08120f0c03070212030903161d0c0d020c0705120105010803180d0602030c0d27140106030203010c211406010c0302101104230315 68
    0x3098682000d0340110041c1d408000880e21070300783d40840d1150581c2c80440305003078215614540a507071030104028800b001c2c00c2c10000c00751a0504d09000b410303580c2c04901601e00b000420f40008070041d1024540c141c0b5500f00107910007461a0500040c08040085003071401d01a04113622000201651034801ca55036942102041704401d40005035218686021410756494a8000c080c54984080340326060140d6441c13030401c1c4c0292010300410b81a40e0a44004605011040e030308802c90540c2c54106c00e400400700c030022000b1600500003148030381004d40145039246080150301044812040c01c103602001050f41070080c2c00c208201c51078900350420181031903000d148007007600402c42c613400254158601000442100d41000008040681002028000441500c4208260f86407840d09640540001001800740e60240944808240c040d1040710300f500d0101c06442c0c110b070503808103d4079a45000c1020080c1c40310901d440e03202c80031242d41218003040000e001c01d0344c5000e56001501503248940c0 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 655292077 1250 655290827 655290833
    0x30304170607180b03070c0c0909031103070f020d240606020f0c060301060e01050d05011412160605030a14010e06030c0402091302031b0414091e1602010e010e0c01030b03070b070f 79
    0x4200d41f840c40d003100451314040d980702c404800030303c043c540880105c5c0700843d003c600c441001c016200701030b4000c0052011025654200000303810080401c442311143d0181a1904000c80780d1442050b52491000042003402c01001034030f07100e000c1d090907000f43d0140ac01c240b00d60716a079068030f04407031803410041c0503045100700599440c001c210b415101a803418000051507050050005003100d02915441446a441d04a0640b20346500c410000000715a24003005028404c0005551041c8082d4001840038140b040b61150072400707a101d914041084000d000e42c2c0d2506102a22034010111411072420b1800008a00e00d80c900c128102606540800050800d882d0340d1101e8041c00d1004134910b6455849504c1c502d802e10300c0c40c007810300488803440054151084944498045c000344510080c0568590a00006410021040c00115500c80400c20745500f024000d5041804107400604100140d540c001011610680b1826100c0c1c0d001507020440c0101e007404031800150801009642610380381 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 655293327 1250 655292077 655292087
    0x606051f0318021302070b011d010308070206120906010f06020a030e040f02090303040b030708060a05012016060c05010e0705090a0c0c0b04030c1b06200c030304170607180b0307 78
    0x121003c0d4214410039080714000c0d1a0303900500ca820f1044d000888240d80300c0918405802010090505021005d001400410314080107480614070042c40c0314035003503020000b030030740100c107644600c400e0748564010700800c07a500c004200035005500c0100714466031514010404252904a1401180ea8000b407842340c0e80369030103c4941040c042c00320395407160340c1c1c40c03480e00c6a44112104400556044080b5100b480c0002e041400c03100140e407070341500302200160460200340e00803d40d28034825509254490141182d05c40010981910340380d00741c910314207141b0b0035108603030000703c600c0c1c1041c1d600f40415036030021100e403c01500c4038001507903510002c00780c510102d612006005000c410f42040b08056000103050b807000d1182440040d94141020704074441011409040c01241c002c20308988020b02e0704495140ca58040400c8078598100b007000f190555206800a0f64440c00c020151454030f04100030a54000c441c0f0710708501c83c4e594041e034a010640017805121103200c40007001c141068850 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 655294577 1250 655293327 655293371
    0x12040f0506091b010318061802040f020a02011401031208042924010e28030501050708090f03070210020f12190806091303021c0c0606051f03 62
    0x222084807054180800429a40d81d8102c03021070701000505035502042d44280280d1042c1000e504103c126850140e60700005445601c09070360f03c0d01d069100744d50260f81c07240501040ca0003100b80c0103946003c0c08800a09550151807914100804c1c0c00040000a445800c11164400a17203030001003604c85240c0356a4031061100407580400b1085464040f8240448821340502ea8208810646010052501c0b00c2c065882c80c40901244100c2e21090440c100008100321000326070031075010009042035440d2071140b180d001922aa9510010440740d160404509030f00000200c00a00349541402001c070f90324030803020024000c3d42c0c50001540c5040c000c104a00b00c0c03104d1241900c0d081d41540451039443c0e04924002422480140301c00384c030342400351164501882000d80580c0382d80d41d03444169212100d0a120860443c81400049080e4104100c1091110030003030f0703600300d401c41035810100b080d21142e410440c403e40200d081d8641304040170040b404c1ca10303d642004101101007100ca8000ca02c0e00c = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 655295827 1250 655294577 655294583
    0x110a1403041124072d0c090209061606020306040b1c0809060d0c21020a020304050f0d0506070e10091202010c031b260705120732100506030312040f 65
    0x108044c02004010841d128900020300000e160005200f543e00c8068210010082d0010059000600c140b105a4000700a800f40180c000c1d85042d80740042041c402c60034810942e003075980401400014a02402000d50b40c0c10221615103190542c0e01901218600c03105000748803010001d400c00464444100351b481140251341c1c10002681e07400c20117800726940c4504a8200100d4000f540d0b440d0040c1e00c291980c00c2090360055081c28100400d00c4818840c82c0724060344001c0c0d060104c0c0003d4807c0000e64411303411680c6848401d42c03d00c00b40035298041901407824480c145806211760f1050341524110690240f900c106054401c0c20152054030300088200380d040004c1d221403061144050000080c01010440030011402a4141d0401b034001c2c220000c007150440d004100310380c1c01040c00740c01201d00032140e50b581e800c0e81c1c0c440071800c009010f0081034000d0051040ba020102c0a200a506400480ca801d011500c1c010001a40701d1040307a2080b008400054041828441b1022840e00e80b658 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 655297077 1250 655295827 655295899
    0x10060e01151218080703020a03020d1d0d05010e010c120e0105071b0f021018081524040c0314090a1115190503162c0112110a14030411 59
    0x114501b002500c0f21a03d01c003c1c0e01520402040f400c0c498801c040bc00080044a484c10340355207110420041d00c0201100709680c0d641d211004952103940c20b00c40c0d15803070032503505c4100e031603114000d0480071b0300e0f505040003003603901d054100b103416500310b11400c20300a044503690b0002407652400d40740c008000b11010f074100c94601d000c014080d40084020b81000044290905401d59511980d581c0e4902100c840c0341c1c599034800400d550901810080039894141028001407000f01e13804138080360b080c400ba040019440c0d1110f04618040440792642101c501405401032104648540c181250030075483c6010f244055031941000c100101a03550341d0175400c085c03804100c0b500000802680055600b4180e1201c90645440c410b40222510b400c5004500f0400b56038100221003030010b11280050281800241200d003a039000c1c0c035100d2041071940700321207036031a0b074002200200074803002c450b500031030301080051001040941c850310740300c11b4084844115440c080d00003924080340c0c1940100d901a = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 655298327 1250 655297077 655297087
    0x907031b05030a14010b09010c020a080d0e0942090114030c0306041110031d0607020f030406020c041512060c0e100c061a0310060e0115121808 63
    0x1551107030085008080490b003d0060f560304803103251005000388074855421700208455003055000c0c0085000f00783c0024240f5600c10b0344c0361082c2e0700740340c0071440100002c0e200c2070740d01c1da640c03404c1d40100d90800d190781d80301a140064940b500820103501c100c550a40000c01260342c0c0d1094002c3c090b2450076074003410504507542d4804110641d5912403039017520030300504d00041058100010104d200b160440706081500100000380000300001d107442008160f01c80d40318007400070b241904001da09501c8001050245452000207007008480c582d560392641040008020141c0c0c0004c0415800030203c80c00103000003000743c501c01a4a80d0341c0310a0148480d80850f0040c0546940b2a160301d0007035480d180c40d085441030400500000ba0070601003c12100050034010854581c030044e440d404000400340021049400246054000010007640945810040c41081030041550b801060104100c10394005a1400644020840c1e6440300c0400d80c0c1d4401c01c0c50711034003d0340c52100180c000340c11660311 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 655299577 1250 655298327 655298381
    0x15111608010203150603041a0415020a0206060111120f130504050c070506070f1d03010b040f0204050a0815010b1e0f09030607140f0a030e06130c0e0c09090703 70
    0x20f904210b80c040060884d01140b201310b03007007413011a071040d0380c4031a04400c03003206208400f9000c00c01134401e0f500382d6000ba190b02204a5144020030b4001d0f06a0000e154515000d40010305d042e400300141c07d11908018060004407100301d090b02d41d810303c20070802e5140c460b110381e4488404070360fa00c8503500ca8100303414040f5410900c0c000f001154028000c0c0c4c0c1d126640d19000303603004400b0390500c80004000e02200e408215241d06075080920000b400462500c80d40c41c009000c6d03841c64020300c2ca8441d8001020020341c60110b48501c01000c009026009050720030703c10003c1041c0500c05c0a22108002443d5240c446d004100544c011030303000d45154a404200801ca051608001d403150f000703104031008240d145000f0744003903181d0020714411b20b240c01410560080389400c4101c0d2201031649644003403801030414460244501035001040d0311100882c285065054503d500c00303101000910203000d50191b5250481d40d801c14103607440c151a0703d0341d9400310000d10f0140120031005c05110401c0b060 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 655300827 1250 655299577 655299581
    0xa0c0521011517010204050102190204180b190504051e0a21080c1303060c0e060304120e10020c010c080d0f0c02010608010e0705130608070b07050607091511160801 72
    0x59510f181404400d40c1c4400b1005800c03803182c0d00905001d60701400405400c040c640110074120361000e000400c4074207420000407001e220b160310071a44249058100105d000a0082c0144c2001203010144100d0609890345070310341400900c1415805002c0c001400182d0003042001c00c441c0c1e00034044c4001041c1d60042e01f21244400d11420700146090001c51044000d18064540c20303440141c042040524550301e0350010120b1508900500c1541420b51025680d0200918812806550450780c600c0c80608000c18454032401130a1190482c0e010f0307008020307800245c4c8035400c0001c2c244404050031a040c007070b060707000380e0a001120a04188681d48922015041242c11103a81e800a02c03003503896201907400d035040d44000032800ea00400c81044076250071201041a030010101c001140b903215801241048001c0e04006918400007849100304501000055440f541da40b400e20565401c0000b0364005041c0c19401c1800c01c421309902d407419103010b101c61815003404150400c1041d954104140c0 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 655302077 1250 655300827 655300829
    0x19030e060a0e031b0c0d2414130314030c07170301061d04020f1303110103020414012016031b0b030601081003240b030a0c05210115 58
    0x140d01820300864004a001d00686010030607050140d81800d8600340c102c6220302c40d46558031118418109901c90b2900d030003e100106601954120641c13a00641d4810309103800210030080840c6400c030b9400c0b01407211300c480340c2c2040000c045071095800d0750404841104204d100d07031000130800800e010341505041c00504010744502c8004030013150114888000e0301091013048040f456110304200713408001c2058510800004000500b44540300c2075485003900080c44003100850151420704c188028180c01c90ba24100c00d00c2c0c2903182a00340340035082c07020100c80c10641130010b813025021441003041d9150030840300703c000b01c9040d280604604030360b5980c0d501c020b071200d01d44220050010740b2070801c403001382c84115094625607100e040044070400d030000c06044a114030b040e400700015155210381007900c1c900207541e1411100410100c81140c19550034a40701c0d9102c50100000140c6503139800040340c50444040001075098141c0022189060300c510307581d5441c14402400e80c10322280030070 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 655303327 1250 655302077 655302101
    0x605090f030606010f1214090106031707111c0212010c0f03091110090e0a0204170309030c010323010f0311030f060613020f0a030b01122f1903 63
    0x9510a40c640c001c0c10746850056a406000035201a26000b8250080c80d01c96001c844502c0c0c0020030058071000c19104203001e488a800c1c136511480d0810601112000c10328150340b440040b9440c1c200d035991409602002c03404002c2c0600c004440051400a0480c4480c1c0810780203040c08405140312220a802054422400b40c0815103070900152624841d120b02e4450550028420040c003886038100001e0201c0652020304118140801084001101c0442c1e40901c00f018405610f03142000b0701d2030140348412900701440da000784003c001c40e680000305079110a1003801d00081c0c2c503601e8502601c0c0c118a403018040701c80e4815000042c1c111044299208484c00340751380002034220070b0109a256000c4000460340366000c0c2c00810154505040540ca00f1007017880c0061a1a81c01203c41c0075a030407403e596404690b892035900302035600000062001803141c0c40400041002d00161080007003554054042c0c0040d118403000103051405c11500c044d03070102d49440446054803401000792134010001 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 655304577 1250 655303327 655303339
    0x10609211a100906150c0809060405150301030b18060412020708120702100315094a0303010b0a0c14070e07090914010e341d061614030301060509 64
    0x116408a2402c4160b901e4650782c1707201c1d111b10b00307403100950781e04442081c4e0b40c0b18804010010f583da0322084c4000b001e21742c540d034094503036146062140c03400030001c11008902142019904020f200420065400703035000206548181956008900d420843c0d00032a60520880c00b085042854010191a0311482100d2441a08240765811003d65050a5001140c081d11960a0002e081c175500843c80f80000c10794900814885004180b100d480700002002c0342540309282c00403d049c4000080d0b20007002c000040d4070750b51505c40201094403c000c813038001c003d0801041c40c00c0100d16006100300403011400ca40946845018181c056001a242e03000800c03070081f00000c03029081d0190360100d07015484c000b4900d81ca81103100640803c0100421f003200b848520403403810842408007100c03a041d40c442c6200c1a28815005041142d440900c4007001ca03106085020650b5288101c03591075451041c01802c0501c40e00c0c003e017645603480004511070102000215507258414080d00515200325a1 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 655305827 1250 655304577 655304579
    0x3022a01090b09210d0b0603010f090c08071b050307020405010b0405102c0d02041406130501230111010c050d060905042f0607050d08010609211a100906 67
    0x1070300e50700d84c00d14652903041d032045400107a51a5100002e085001400302c40441d03800c030500000f50542d403007600300550852083c0024868001c091140082804140c2040c7d40d1070309206001424a4030f50382051106031348140281e0080000c244180c4490680c058418015541c51f1413201d000382d0414010540180a2008511251032080703284003a012180030481074143c1d0030b6401410100c0148680b130340c00100c1d4200340d100581382d61050010004420046e0300940c140001048281203480284c58401c40c05d210040c03104420f80c03c0040080d2400d005a2204064480d0060310303510f120340a44180b43d40b1b020184054242c0003002404906580d000070850346803100000001c6603001c4c1d401606800d04d150b505c07141d0b01151101c2d80000340340c000e441c0c00107108902c0050055030040d4000c0342c9580000000d2a20613800c4500e49000d8451401d001d14040d007014030020b41030311000130821811042c80e28100c02d102000145038001d10156400c1000f914061084120810091103041d40991030b00380 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 655307077 1250 655305827 655305841
    0x13170901110304031a0c16033f090f080406021b060711010e010207181a030601031e030912030e010f0516081c060e0a05010614070303022a01090b 64
    0x4840943e84d201e9030003000c2c045e08080034442840000d0515110640401c4000410000d45400343c0115203c0e41e61042c00300c10001d10243e490f02000364400d00c41403280d0301c100d01d50410032802c0c1c2c200da01c00c9100061a40c03c80c103268080300264a400380140d000060085007480d4003080c41600f80000010444011542100744102880b88007405821080780c02c248412541c0305044d4001100814070465400d01d40361035000728801c40c01d0000500b201da0f580400c040b11061030601009103070007100034181961542d00c5200100425441d8080c0c0240880540e00415002d903440e0805029103107901c102c045505d02c1c025041912101d0342c98040b03044541c2050225107c0d40c2126402404074030040c61a51a0f82d60790440780e0030282083c0c0300c0305180b85200d5811a132a01c0b0344401450b81900d2401241001d1060804445040e0001c00400800c062040d2001c0d40500031102c04d80d40c94900140c1e6207204103800804103140160415081c40b0241d91106a80c0b81508184002d500410081c640e03529a04 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 655308327 1250 655307077 655307083
    0xf06090316110f03070b042108030705070804090203100303030f0603020f0d020a03052b03020c0303071b0203010e01020c010c03050613020309070e09070e090a0b010302091317090111 80
    0x18440a8420404908007000104110800d6640c04030140007402c16040ba0760020341045a20f0304201400400494100808100e04400503041d170307400259040d940440b03449031380d43e81c4802070200080c8070000520f8410003141c6000c0710000c00d400e8108646a0810f40006800310780780d88001c0d40040c1c01c0103a910382801940c800c50048a07801082000c4104031041031182c0d204527060b00366800705440c080000401c50910050340341141c0c500f511280c44034072003240c0c41c000103030139001e0f400c041c03060003e80b50300703540041241e421403210709113403650403000c03880402000d4001d48001d4041d420041c02040c4200150081e00600ca4460024484450034a4003142140c4085503100e038030802c40d00d01d1201d510758540c011501b00c081c80d02914421911803109401072801030341d003e80d4551001204004130b01002c2c401da41c1098508014001028942c0c40e09202c899040c00b02038401c0500c07a0128490301c0c001ca1444003480d600c41c000f098040740c41050050f090704000c01490100328000b405000313880c004 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 655309577 1250 655308327 655308337
    0x1c06051f0807050c03070506071e0512040c1d060420040302060904090c0608010504050a06080307150b040617070504020333060d0504030e0609030d111e0f060903 71
    0x800005100010a034904a948403005000c6000f481030400540c01c00302001d000034090035000c0c4000b00b0560501110041c43c1c1850ba0340504010003c40c06602005680003080b84d280004910b04801d81e52a28101001551000c0e80011a20320000301e00d006240000107190344540c01c12a13041203506e011208100703034400304843c0f0003424041007009200524101c030242448840191001400640307a42c0c0320b60b241c00a0760401da0108461134010003451a081c0103d035400007045a01f800300b00c0c03504010940d68041c0d4a0b00602030f0703030112040754260125030301c0511000002001400078980d21114007020040b000500c841e94003905d800030819003002d000301c9002e24202510748d809600900e04070141511014800000e100c0f80122909a640d190700180c00006e0740ca110004290400f450040c04000d00904240d0040c07005200f4800309a40204140c00103e8842c1030800640d42444c880c1410170905403a9081c1403000140440c007100d50000304108904186400c40c0e100d91903001019030349002d4 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 655310827 1250 655309577 655309609
    0xa051b040e0f0115020c1c050a0b0906090a020f2101050a090507050d03020a03080a021207050a02100903050406120f02040602011509020403111203070609031125090203100b1c0605 79
    0x1000e201d06c900360030f09025014104c004c00907000e032030058a6540a05003000c0f00c4042d25030074201404d000c8501c00038454943c120300e8000040002c0055a400304045030800f11b0b01e0b52041640300440303c0b03e16061040044d1b404a007000801131803604202c2c0f0300061882c0d1400750380e1486501404275107400c107544440c180c0c5416400078403e6641950703080340e0818005215489943e000d0040740180d0918128070350042d60161125502c0e0340800e44004c2c07603c2160218449070505007550200881c1e0010b00300c1d803e890551500c131640d1400c1282d48800307008601c0f500152984009030001d1304543c198051a034820701d0b0504080710310782da8001d9000343d0140f400040d2881881528280d032520340070080c0489501c14401352800c141454550000f02c65920070160040741c40c1c00c00652404c2e10502004500080c010300c400780030102042006400001d5010715031440d680000818882c0340c107848500001e001d810f9606680c0d41d9541608040149800c4030303400310a052500114051414506200031046 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 655312077 1250 655310827 655310833
    0xf0706020d0809120f070b130b0c0304020f0f01050705060f01030b090f07150e092401090303050d0902041806020c06010605040b07170f0403060603050c0301140a051b040e0f011502 79
    0x60000c503441303035510000c107140606004024210000c2d090f910300b240710b286182c2c41803224507a11f0502d801c040700004c015a00764002041000300603a101c9010850103482500c94000d1034802e80c0040e65580b055101c054514884c110400100e10300095070203050b41c0c4280c04c034130103540b2090300c42555100703000b0741c3c02125003062806100c190280c41d095003826915103080640c800e00c2d000440d8030203105651040980310f43c1c1081660440d0a4407145d007142c14281703020142907103191801000e90181c42944201c980d1210314070b0095685580050150202c1c852081c0c152210a14120000b0761043c241a48a030080c0000041c070300c1e0003181543c0031a40307a402850b240100c1d55071207010740c0ca00e00b400c0000c0c4020500144613581e032482c0103080a07500c2341e40c000411a0540c10304038500080b081307a0600c682c2c1081814015410041d1801d0303040794621401007001d8075206c2d401c084581452600341e61101d40844c00041020b10421464002c1c8092441018107980301c6400f60300b820003140c62180564 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 655313327 1250 655312077 655312093
    0x2030105040f0c350705070303111806160501110304110406030b010512100f0b04060e0709050d032607030c080105010f0f1b111315090f0e0f0706020d0809 68
    0x40104450040301303a04003070340d50441d5070700c10460f0182600741d07030070000100040390390310802d60540301e0b00f00c00414006440d07003403084040e0000003c00302000003034051040070560140e5440821201d12a4a43c084000e0251113071502c2e1042c0c00d03410456043d544901400c010041d1030410348a401c0583e0b41189010038682c1c2040c0a2000b040c1203c440891944285c440781405a00207204500d40b6040307450021502e0303051a010001560304c00e8200c010100c5640052141003a040103804048070025150440e0756906401d0a0740c0030301c4900b0019401801c1d10201442c1110900c5210b4890111364034208984500c2d05c50881746140300340509408640c0e0030928100703050040000c48200e08003440c290009501c06c1803500100307480301100311002c4840c662580754914103c003031107001c00c2000800f04620300d0b01802072000c1d81c0c0b503440340c0aa80382c1c1d6000882443c1405800003890516182c040700e0101440d40011680d4030050b10810006008a0804104091250000d42c0c01a42d00360020318802d = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 655314577 1250 655313327 655313357
    0x15030304090c020a02030d0e03071d040201030b13020a080f090d0e091807030606090c110703151107050a0201030e032106010219030203041a071e0c0504060902030105040f0c 76
    0x34000c84030040d00350310404030113000607a420082c0c102401250340c3d03103100d651340c0b140c1490300e0091950003000c500c800201d003d030800040030801c43c0c0c1c0141c0904c0c001c10454400008266040c081c0000000503500026841d8145034020041070700542a01e200c0035141d980784500c0e02c1c0c82c2c4200c9800d0000154070002101200c0c602004843d0b0022419100105500041e4210a1400c0b045034000c07a851034070f80008000c0312000c1c0c0f107800e1614a060510f02c0d03102c51200788031912203145000c028401022030581e040514207540c4041201c40c010201c06a41e400d05080c2113503030b41b07660001240000d0a200842d4514040803042d522081d4024002203020900c403c1204660f4400506081c1148116078029100c0f05101501818141c06500a59910760500701100c130104440d0801000c0d488042000e04c0020741c01954060000000000c00750341d0318164075201401103516800706030310900308000841c0000c030590046040b1241264200620307400d680d142415515038840920214085aa1407212 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 655315827 1250 655314577 655314581
    0x150e071202070f0b0c0f070f050c03150712181506050307050607021219080315030c01050d0b12010219020105100308030f0a091b18060f121a1501081503030409 70
    0x10540a039113a40c02c1046c0c0301c0040034035030416030050b11001c41c440780c00000e100090107114621402500030b072a00d0203443c002d0030f45400019160f2000c00140d42c1d91014122116130191306402c07680803110b4a01c0c8110308000211001c4410005001c0b85041c50000e01454009140d07022a44060300942c108030040d000c02c9240490f516900c4064066440074031080f00c2c11400d5070b040b02d0301c03412965441303051041c0075006080155144e1406a4401d1419840030b80c0c01c82d0a850403241c5100021441c04480f2020540301701281483e45142c0d0f001040c440480243d020f4030880c1d00e0090f9000b0400d503076600381c035002150403610016080c80800c10205903142102503a0a40c000c50b00030000c40c08100503a00c4050351004031041d98400d00d0724000c203012141990040c50035074031302002c2c00d10030b141c14403000c3c0701c02d40100e02c079044d150104813610400b04408145d0a210b803103103400f02c1c10300074a0403545401400c0c0c141c042c40c500103070842e00001c03840c030040b0408816900d030280c003d60a041c01c012460b40 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 655317077 1250 655315827 655315831
    0xc091e0f1a010f09080a14060708041a060316080d0f021c0320040f0e16020d0e030f1203060a050a0e0613020903030a030b01020f0c0f0607020103150e071202070f0b 72
    0x10800c04e110f04049030740742e020809800340038401c100e100701c81e4011111203420030300c000c1d050307608001c5108180310100d075a100c285003e03801760307552031059510360320006450030f1030704907030090f100e00f0a032800200054042681c24940c1942d131104103c15903010022070711003182c000651091069400e00c4c04030f040c0f0991100c0c2031103640d207401041c2c0c1ca403500c06060203500a40e120000a5091030b6042c0800f10b40c1241ea140c200c0d400103103044282d852810044d480d848508400e5040200110040b1a196010081e040c5400320000503240c0c620303030b81403c2e075a5a50007107a49074040c403072191000031030381000d084c054110344080194000070b88400c0c042200c82d0b8249a0420482c0c4e40901c00f40000342d0303090005100b14041070b00e001074000c0e104030019003806140c508400081d0000199207115488400c2d0203510414115041e544c1c801c601d1006a0050001c803c014132542100c0002042241a81401c07902500380b039121408403444055081c1d0503440703122002000e000480e88443e0001c0c0421282903 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 655318327 1250 655317077 655317107
    0xc040513021311090a08030403030207050925030b1008041e0302150a020432040213120203100204030c0e060d031437111203010608040c091e0f1a01 65
    0xd0b01e041d0340d8100086588030646c0119015400000b0708104050301001408003d120035102038a03a407078a102503802940810392440d04600d500103d81c0000b500c41d90003c540403000818080610107924001088904c003210201d0341c40300060809500c142d000c2c4c15080303c05a055000300440040c0300702ca00c043d000d001e04040c084a400780800302315001c206c0401041210900c0742210310102e10713007841659540f030047c50b41c0101d204215519040c0302e040e01c07090a41e240b46040c0603420050784042468074501440c0245040d20200d030200400c00003100d8841111b403103c11888054a4000400944103d40d501c000d002ca01c0303540b40340c501001c02d80060300900010401214036a1007070305415003143e05e201c41500c1190780c001413009240790400b2300540c011040303000a180e210340121921281d4030060080310280010748000801300002542e11230050180204144100d421284124030341d41583c1c801701c25102d00740701104c1d0700c2841c14420040700e0380d5146803128440000744010349d000c1101c1c003099 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 655319577 1250 655318327 655318361
    0xc420a0c0507051809010b01091a09060708040b0a20060121020d0809120307080d09080706060b09180f01060f030204031b03050c0307030f060b0406050405090c0405130213 75
    0x141a5803001c1c04c442103030710500102c0160745010b0784010700311501003255605010111206208441c8603800d1495a84040c01416547d03c4540001514500800c0d50003000550300080105810381d00c240900340f00c02d0303030b40c070b840b100090b4450400c0c0740700b11202030000840d40708c0d0004200c981c3d0061031000f14000304103640b940000203600854883c02103600d06a91070b0f4000241b1a0807030500c0c4a41e103185004c04405541041e250741e840e2030440c81041400c4030200d441d003601e101404511b1003254402944001e0401981e80d4130f03000c4045540245071814450750401d4613403207500031983c480600c40c80d110804900c0c182c1c01c0c6402603442a50020381032040640c01d120220002e640305801031b190100c21480044c6041c03641c58800d00d080509803649010342c1181e001003000810710304640880c82c4d888400420101c07120400b2070f00400d81940625032203814001172080b80c0c0004103401e94182000c2d101401160748100341c3c3d1001c1c0c01070500094104003020209620074840c1e40c89502d004c4691310b05 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 655320827 1250 655319577 655319579
    0x7030c02040c1d0307060903080a09050d031e090e0708220506100801090309090e030f030703050f0109270804080a0b01090c09050109060507050c420a0c0507 69
    0x42800c485144002a0100c1d180d8141000500d42c0418200400f010032002080242c0c02c0004c02010b0014600c4010402400401c0741e0341c116010740306010207400040e00b80c40d500b40440c1801440552800c105020400354a00200c0d005485042404160b4951070002c00f0346444070581242c130048003c00f5422205000c0100202e0039020041c0842c0460140300180194104240c014044448a0780322400f1170789400d0101c00003c1d0014000c03406c46211441c0000d82d03070107640030380c3d0851085102a092502c00002044120b540680c007941c005c50101500f94516030b29464100100c0b080c90804044150980d440582c1e0602480140e01c81d2500c076a00c0c1908069454120b245425401f29044650f041e0f208018042402c3c94820003c41c4c151a141010740540344c4030000e40004420f0140c8010070000003031a070140300d0200301d410a20400982048003109511100c3e0f28100d80d0110700548220000700c0085443c90191404291001030714441c5240c03c0b9004d00540b201000e0b0f11b011201405041c0f0 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 655322077 1250 655320827 655320829
    0x80910030605210606030109020d120c0f0309080616050415110a031e1701030b0703090b0c031806190509070801020a02013e2a0d081012060207030c02 66
    0x1041c00d50040c142c00d0f14040c0d800095451420180010b2002e03000740c2c034001800015948100082403001e4020090301d00308403410130304450441106001501e80d041190410042542c0001020101ea4100c02070b1402904d4400f07140302101e40c0c81c600180007440a00052021040b034900c082c019101d00e041503110910718400c141d040c0b000c121000d8011406100417560100800d1001403941103c6203004802011000881c2c000800c0600010300301400701c20001e480c50f80690320075520250010b095240038600080030f00901e52085902195000c1841c0343d01d03092510000c0c03414000d00401940d024007950528142c401044000c16007901072040301c0001610322801c2c4010110540300e54004546844000c0d030641088216224442d004400489924041034402103185403020008080507910b004e19110303c11801e03103450041d4902070750b001052500000015484a001b009a110312180f0317594075811175030384801c174412400d40284080c0100002010f550050800303034824142079501c00c0082d0 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 655323327 1250 655322077 655322089
    0xb13031112152d19091e02010909020403200f0901081b06040302100f09080f071d0919060212010914061f03021e0f0d0506090103080910030605 63
    0x25030240402c141d214144620b20150410040c0c2004569151901a2005680e042629035000300003038840d140781d400d644001c0300307503801191701e1781c1d0002c2c4501e6114201120001d0302d502044422408902510070020700c010407402503504880c3c00650f0400302c3c801c19064a41c1c508031030222072380d12147c811480161640c500f145a4060040702d4000d00c8480854800b140825010805041c8500300511003040107079528624034807041c0461400901500c3d55600035078103085250814806406505210f0031010384c0010001c007250301c5440480e00d0340b05190120201a14247e0300546a608101e07690b03070480694090b05041144507200c0103180000510007890702250a03085044250745070704020740c070362844d000041d402032801c076440710100141400b80b4180701d480c0c4130800107054010034009a00910070440641c1d0114140000d50340d20240d5001644991144800c00c601078075040c00b09510b814080d00c01c034181c075441410716141407040d81c10480f00d041450900ca04140e203075072000c10903071030390 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 655324577 1250 655323327 655323343
    0xa2408040809061309060909080d15080d0210050a0203011a1b070b0702010336080d020705010b10020c010e090a0e0703110a140901050402070807060e06040c0b13031112 74
    0x107050708104d410b08001c140429200141e000d140745074240000e200101d00306100302c44030b080c2035000000300e40c240d40020808804042d401010540600f08680003070580100d10620740b80350582007041203a407156810070883c0000e019904403242140180c4000070f900d1001002c004481c01d81480a020125500034640b451680055890b0403011501a00315601070007200c0100321140a03442e0007402c003100c1d035110300c0070401c803507110002140304800600424000721a819100c03aa000d5540d6003481c00c200f03000c2c1001c815800d01600000c245040b0051004c100403040c404140e652112a1a04004000c0100070151119480036074034046203441e003100700310490041d0300c500d07021400c62044a04108200440751b11891134018900350f00b40749a5119030070340741503ca0403200180c88130a00d04100074540201c00005060900c0c00b01c10600508001a00900c940c0c440d00001104a813590045200c5000d0b2802d00108130f09844c0382400000d00c0000c088000304005401e095004440c402c1a071b1070b11000c = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 655325827 1250 655324577 655324597
    0x70201050a021612300f0e13020a080105190b07082812020408060a0f0b061305030106060e3007030b0114010201050c1e270a240804080906 61
    0x2800c00741341c003002200e20300e801021104a0b441041304003142d10818080c1e100304040c4d0b0800c443c20a0000c80c20340150b601486684025043d01c104100c41c0154000a5000c3c0b6034010110300b0030000062035103404681020104050034180c071480b40b03407160481058000d801c0480301600c0070702c041c521210900306030110040210340011151700010501034802c0280007600245140100010b01c02c10b80e000610a0b0424501d501c00189070f480740300008014401192000ea10000001e044183e808850324620709603141140204003440d61400150b501c1070303000d1006900b00c2c00742805200181070b0764003110708000300244035940984200076a5030078404550022500f132942a0014000324210269038440114280000c00035420711050f04405070007200e00e4110080708a080c60f11444580406032003a0101c1d950107150a046c09200005611681d131813281c0c014079403c00002039200341c0c200c45000170011507081d80c0d01c040b82c601d0201d50b1810010001e81c5d03d01001c010342d00c2e4980b180303c000c10501c13070 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 655327077 1250 655325827 655325849
    0x30c020607060e0c0f04021801080c0f031f080a030c08130f08101a0f150f0a0302070203010f060b09060a05071a16080106021c0210090501151a070201050a0216 70
    0x2910801c000b04180441007044c02a48140422230301280c40e03118540c950042420f008070256603e410019052280d01001200c442000c024030642c02c07144041c0c09000c00c0c03140c98807022a0346840700301d03980c1c2c202c0c80d401600142002c62503a01103a4914000c1512090003220311145544440034142c105800b940302442c10341c40610340700c0d204030882c458640c0d2001c1c0001100b400b119003600080071401d800c1107080c800c0241e00005001400c010040303500303203910403105d41e44845a0200103002900004410fa001303500b400c075410003000180c800e60090f600c0302018541440c4503401441450f401c0340182e1410300c0400c0040b400030440f01000c003450075410341131441462900201e181d03685500515a98240007400c401402070b03540200c0c041000030454040010103407020310040703190004800500d000d0700e16000301e0005214064100100484207000c00303000c480d80d80d50f40d108414925620445000100740301d080015849140207180103041e07407040b44c04080c0d4403a402201c0001c96489245401 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 655328327 1250 655327077 655327093
    0x1906080c0411040510141204050303070932010c05030403060e1603080d0515270702070501090902160209091b040c050702240d050603060a0603030507030c020607060e 73
    0x31906000b6014000801c11038a4201032508004c103d14043c00002d040500401ca03c0b02140c40495105540348400a07090080707160829040c0961290700654404000400c464008034800414540380450012035080e10354207124001004030301ca1624400480c1000700310b452f21404914100003500143d40100c60000d8241114641c0c141780034060f2035040c8420130707402c400b0804180d40c941070b1000025101008182d0f40d0320245400300819203c20728560060342c80c44552548129808107140c003c2d035103207118210b600c44940a0ba0b4035a59842141c0c0000d1112170184007044141d00500a000c4d050702c3d0039846500e01d91300203242c0390800c81b0358005640c8000048240f8240084c0c0c90107026034199400c002480a0090003022071103000070180c01b0301468034600211401c001d1802458901d602002510360b00c00c400030704040c15060380d0f054403d00c030b03c80200b122024244507607000c8941c151a02031030541683d03401d640d400c03584203050764006001d00050b404605140074110740e10402001400100e = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 655329577 1250 655328327 655328329
    0x3010e070e06040f091b1133070309150e03040302011d032a0f0d0b041403270906010207150c2003060708151e03011b020f12040603051906080c 63
    0x1060f8040f080344104a104240202c4c40c140c04115640e10f000c8240d03201c104980f14044882e80c8d00051840d01014890301010010352a03407660220103041d2185250b43c415102510242e41624200012081d56070030070002040152b02800304201c140102c0d958056080c211200068100300303402c4001d10341c3c004611500007800c00d2030103030340001d10710884d1a8081c0b004000301050002110200040c4071000300004181400f00b806461221071080f941202c0e65110f201c4040b16030300c642c4206d00228044990254105880c20f1100a481104180e00030709505140a10b45d12522040341800070138032003115554000b0408207040c0b451090100d200800260040030b090615040d4014049010003041c00c0500c16003000c581054070010390300301d51055010f41c41c200c800c0c01101410180c1d55056280c0f003401000d0b044d20450202540015400340c0c0d0b0002da8000700aa206e080d10044001e8491040100303101103070290340426005064861107585202058220100b258000c4e00036240c41e501001d1a5009 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 655330827 1250 655329577 655329611
    0xc0b0903070b0106210c030b150409060906080604021c0c08070e071d010f0306231c0b040f03050c010f29130c0e0306100303020d0503010e070e06040f09 67
    0x400302e80c03514003405000000d000392107817109001d52081c0d03601e640740c01421900ca03401020081000600320610100c3c9a1000c0c4815841132180d50300b502e05003d000241210544a05003c0364445000381009940d50780c00c101050021100381120240402402800b00707030311135000d00240200c10000c158040c1861060301d5028070007040b0804020a0804110602501c8141080d440100703082c003085c074181d10036042e4041d042d10780001500303504a01c0d20001c01c0d46000e03808003c1000a60f1498409513040d1280340141c802c0b000042c0c088e620140104001840c10400044030a00a152031400e140003402c0c50b0317081d1925030012000a5842e900d00e611004211046002e050319040b1008840c3c3c07403008081001e1351001d00d155040e541d5a000362541e0a401204800c40e01d80004050303400d5854a103034038100082d0302e070105800621030751141001700d601030070403203061341d5280081011964801e002100e8001207003c6880c0c0000e002c0c0030000d6541440904040900000100131450340e00000403424 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 655332077 1250 655330827 655330829
    0x612010612080903330a02040b0703031b0813080304030e120303091c0f08061f120507031509092406050321030106260115122a0c0b0903070b01 63
    0xe040c03035140170f010300d20900324003188a00b0500032040c0030860391140f00031340082c040ea600404020b0340010b5800d0815a1661004c0c086d11804034040d0080601c2030309c2154032a4080700c480c01100265120040890b0b41903000e107920910031300d0b0480705a0348103800b10ba82040c000b0900c0004d03034808000c2c04800310060044040d0b45611144180e4030310142d03900184800710b4200b0580a00c40c007007000c183c498a13070103640d528100b40d80b100703442d440006950040038101c503010a81506c034581000705048920038000d121075100d08001a03580389003401111001054501d80484000780e000b0104041e481031032603aa008015424400a2a185000c05041c140030342401c1c2d01c203044c1d220341f08100707080c0303849400d6a064404070314010710b03280c1c000100030000c80e905107460b10701c100040340000754041205000040d01c80484c0e4035804442d440100e100c06441a03082e20503000c0095020a4400070142014a03c1e14015442d201c03050007910340f200740c0c0444007526480b140d5000020418184860944203c1c = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 655333327 1250 655332077 655332103
    0xc080c0306091e010b1503070f050702030a120320041703210c04090906050601090b07050c09060409020a0b18061920030313030e030a0302060612010612080903 70
    0x40c0c81c5490765a00b601c80c009038820340d4228007411404540e00f0000d501a4003101e40140c170140e00300110804c619196001150103d001804d507210600d140d92184040c0c40110707a01400416aa18207950303121480c00c031240d1803900305542c4218018259102e0b090210f04021810750360340da101e05100c04035003940110a030065540d0300800400c41704802c9016002203a10000c01c662416445050b02804030f84038680c03101041c04d08249141c01440381a80c407032070180e2401d0301c0f4941c019070785400e505004e008608020300242c1140b0140b14550030801010380c3c0c01103000b4000110510711380c1c000340700c06030103801a41081102040c010003494030801e201c0b02c0e01c0b100301c030301e0b070b082421700000b4660a035000d007075843c104180c0303440c1c0c0c03000040b03502c0b11007150418400581ea203d2400c1c01c44903464140315142500000c2c1610350fa000f00b030070045601c4816036051b901400d026901e08003070107014580221030068542d41c030302c80000c4207600a883c1000c0c89216084407903a9190f030404061400078901c00f80 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 655334577 1250 655333327 655333333
    0x6290102010b06040f05040209030a15060510090303021c020102130e1e010e010303050a030b0a06020c09010905091b0a03060219030b0a0501410a0201112b020c0a0c080c03 75
    0x1788002c020000c51041186d00c1150056622401c1101281c14802c001000030030b0b848040743c003803142052541281091f55000c2d94000084114140100c4100130300748009405a0880c82242d8a41b8000d20070050741220580005890045840401b00c8582c116a22010400804d030040c0514024a60044098103040441d054500e50502001d0028601c0c188001030510070300041c2c48060300d00a4200c241e58a600900e01402540e0782d18000e901d5001010400348a405038000120717000c1080d1060f40c0c040c0d034901c0002c00070301a10401c01015002c09541240d80080e03400e90000010341503000503c414000c60302000f40390074850750080c0c2651000d1000c1d610505c0c1c005020320040c1d0b40011030300c0c40d502405524004104084c083c802205500d10444505079003000d200400030200310000b8014035038168000c01454080b01d8800c2803e01a001602001c0e080e0520305182e01c408890b01503503503040064005142841d081c20142c6010080c0c90111008a40c0003420805140306003c1d81d011a1015005 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 655335827 1250 655334577 655334579
    0x1c0207081b060a0e06030a021213120c03090504050702031b0a021c06231b03060f0925021e060f0403031107060e1b150403030302030406290102010b0604 67
    0x1114510103900303401d060040700007294401c0e0151042075a22001d40380a44565502c0c1400040c09019620440503821104501000b0580c04d20840d80403500d202e80194041020004802084503040441c00d130940c1003040c03036240820b2960740e070310481e80608281e800541d95580c42c0403000207100e05e0301c0c964213995000902c00c01c0142c2c542078160345040502c2c3c4920310b42c01000c0e240040040c045840d018004e80c1019400041c50b292035a0458007407403891941900c402d4031828203118034403007110032030b41105c402c10340500141041221580c000040d00200190444651080742c0020b1464000c1c4005900a0400001180003003020030512071034200980380340d11340603884500d00b85015100a04060762a24000d2000031002d0a403080c05a10039010321600c90340422456645d0154030710701d006c2030f01203040c8800514040c562150314005100701181414a1034505074000d400082003903901c0c2d81c803448088440800043c07940c400e5814280540c070304819010009086800d400c00960241c202004 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 655337077 1250 655335827 655335853
    0x50102150c040b0d0612050703020112090515040201032316030203042004020d0c090905090313090e1c0f0206013212060103150c0807050a08060a05031c020708 70
    0x101c2e02602c0003401c00c50381d941641da1030f210042100e54442410701c6440d486040c104400400e45400b101d000340d13608904600b18444c081c040751155080101203500104c915011625402d540b43d46c018014100010000c520307944400070f20300303800c2c86c0c500c00619103820401407003007420039004001901e01d400c504518080d5070f010081408200364480008103030a0031480756503a9011140d000c0d1460806200b00050014044c207041d80785d0284111036810000001c1c410034002051f180060074607991075200b0351420316200c0042000d8182c2c45070a004281056101ca0025000b0b003e48040d250348041d07030b00c0c0c0384810080c100798040e0403040c864000c9064100340c40c1c01c441048201050310043c4041c0791240c00707000403641300714170440c3c1d00c1c00c0c02144d00010502c4020403110b26000d482450520ad05d03100c400c0200c60340e00007114150302184c010700414880500c03480c40c0540c0080042d180c0f10754561035800080c540b0200d1400d49410b03140000000d0074040d81440000c0c01400150000c2543c0c00c0001 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 655338327 1250 655337077 655337101
    0x909050c180a1a06160f060e070f1e03030819060b0306030c0904020f060a0c05070e041518030305040206310806040506060108041a040609020109060e01081501260105010215 76
    0x5c043e401e001500e24032031406101504609140769540050100221000d441d6020f841d07203d10300c10030041c3c1901840005034000b20700851444495143c00001c0e5075415960306484915000e0b060600e041c01c80c00b81041d03680c2c0c072841000080c00202c0c00564403480c0c41002c141c9410b502c144114040c00144c000d000050311903c2003058250030880c0c0c40750312025807a004031102014001c002d401c51040704800106028801d100034000c03805500c0c0340002a5074200d017174080d1103c1a5403904040010240350003c41d2207940300380d412901c01407000c0e00d0b0142e0070307540b03404013540783d03030400c000c02d8046029010280211003401c00601541c0c016000368501a00e8098440328000c224a0601400344001020401260380641801c1d204142c454003604003410940c0050034101c2c4102c0c08a003104801141c0300f0300904150400c004140d44000301030b81c40302d01d0702c0004880131810a050141c241103440904041c40c00396413602c0421501a00c81d0b61401c0b000a282c820741c0c8038529042c05042c400d000064030380d0 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 655339577 1250 655338327 655338337
    0x9040617070b18031b030705030307170906070209100e061909050919120f09050306151c06050f0c0406050d0c1803080a020106080303010f0909050c180a1a06 69
    0x205100c1502d0b8440180301c051818943c0b9452581405402501080d031003800700028981941941200d05203622101815528032030840c020313042e500b40f4556141440c0180c401000e0007030001d031549041082c1a80071030501d1405881d1014552048001849050782d04c0c00031a9005500301da030b608a00a107100c0720941074505000e94076010741c46000140c804503003000070800c20441c5182c109007001c0d542c206070307c00f44c850720710550000720982164034440740304805a0307040e140002d001d8034568403020840711504110340d54058000340506650581c1c6a0b00855800d9090b002d41c101044620300191151001c400050101c440084103000038840c075a0b205c0181c031048040501c001407440c01c400301c01d0390810801804044a003074003407404403c00411001501058a0700d80090080c25141c280080d2640801d0061000e08841440108080000c0b40c000000030350090301503c4030070300703020040307041c28203c0504410103000b0507084c04200c480510620b90b810116240010681400c640000c400d0b10138 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 655340827 1250 655339577 655339589
    0x10509030f09090a0b060c1b010309032010020a0903050f150c0304080715091b0303120f0605150a091a04091d06090106050114190f05070510020904061707 68
    0x24400000e60304c3d000300e5010148000008101d142c4450310b480c44030b60340b000214101c1c0c680d1039034030088110790b5000740940c805266068560862008520031361044000082c07040b5003052240d8050344006180c103100801d414181c0e503407144180c43c11030030118900110252164482c1e4064a9400c1c2c1c0220710300c2140d07400c00e0340340e643ca56480c0c40b18100341003203005002c00074004034040e00c4c0780c20120680e07078072485019200b00340000e42803900e00d180c0c100e1002e05100280104d403907001144003d85440e48500c8001500a00c000b820503141c5000c1a4a6680c451f441606007400203140550b00e40c00103d404020a0b11085581c60816101c1440e085401139104550304c20340c980c0c8184040c0041485c04110046072036045400a00c1c0c9000d01d24017800682c45110302081d0855103514503520034400302d8580f2100d1800086080c1d4007204100ca101c0101480c1d8420032031306200240019805200d205d4003008001000340e250001a420441294510f03400140c055084040595500e03002082200c12222 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 655342077 1250 655340827 655340839
    0x3150b121605071202011406030604110603060315010806040b180309040209010302160c14010c08030612161e0501050a021b1c080c15131b0b03010305030c010509030f09 74
    0x7281e50003500c15000701d0800030001d80a071404440b1441d415480301481640d0041160f4060315100145900c902007a41c0243c020403a20021000a0800c0001560403000c060100ca0452001c0c20026815050a820030b007220303048001400213205090701403580181149901d00d100a600981c0c082daa44601000f050040c0e40220f22203e00ea0300070740c103682052961108012514000340b410220603200d6010307140005a810090b0b0056505c2007181a0499a10442040c40c1d030304c500e003c018051a0940c1144824490341103041001000360310710b44011f2030441c0141081e1020940c5041d01c2103601e410450411209010781406a9400a00c0900060b40c03d103500b02111615008206c90400c02c0b200c1e05030500d15408200108480e510061154100c10815a04001d10080840344801d0301680d56100005400d2a01d00c00300c0c090f403000e24040000002c1c1c1c4151507503101405e1403e03800990003503941d5003021409403403052080c01510750002400c1c014521707100f1000c01501840c0a0341d00700da80521 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 655343327 1250 655342077 655342111
    0x90f0c0a12060f0204140310020c0a0609050111160b010914071215061706040903090b03090106081207050105070e0306010b0a2105061306120204181203150b12 70
    0x41010b60181d0032043d10140155500da840d0290703001c0803065901c4490180c401c200e0042c046410a1098905401c8020040d04251405031904006840034010aa64035580c8d8000f21840b160390900412030500316161108104089051400071711740168081c4010303608252180c060210b003a007e440c1c0c03185883c10448501131900403008000c141c000c00040400d02000004203d50360088222100702d00b59038010f031903a5a4034400d0000380c0b100301c1030042c08a1f0040900788840c41035180a980c0c13008548000054155031034094500c0c0582d19003995480c038400007501001d2080c2802000c1e84099941030200d4100960303404079540c0e4a051041e000d40e0800450b01c1381d02130344a00c240090300355540d5003080700380e010041c2000040900780c400d9403191222051440c0e91403018042d1388200d45941c00040901c0ba810340901c0301420054614103440c81461008200141144410140c0c11800d5030300064903030a01003400c00c0280071030300440d8200f001403200880d01080300300141c0d400000403c2908080c = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 655344577 1250 655343327 655343333
    0x260a02100813023003040b0f0714010507050304060e011b050d0b030303010b0d0c080c0f0310030803040c030b0711031617041d01050a03020612060f040c08090f0c0a12 73
    0x103040025841301840760190401600101c42405140e50400420742d1640d081c2142036492085204569105405100c07a02e8035046e0240030305503041c0201d04840e00354044c0d4418608484040316508003080011003400107102461140c0d0282c6d4002c00020400e401c2140c6801540c1c0c5503180d0741c02e041140c0010b4016010580b41c11010304080f0190407641c4035611010700541d1030304410031304802980fa20b183c0c043c03281d00c1211400d0088048a100e40d29000603011900c000b603000a20365034441420300700000000d001c540066108600803284406031500390f00d864140408040c0c031440c2040254180001201e0000c4100ea03c15802481e081022854514041a280301100c3c1d55050340071000c500002c6501403200c0d1254a1164813003080c0031683c94001b013041009441c04042d411080920075540005031104400740c02110045c419204400400000b0342a40c032031000900000d4211003e1001c0c00e40f00302f00c0101030ba01c100300600010340140011078118a05d500c100450750b00b10403949424 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 655345827 1250 655344577 655344601
    0xf12170f070b0610020d050a080907180903031415090603150408040303030c1701030b07020a150605010e1503060607060e030403141006180903030209040204260a021008 74
    0x9031040080000e4562015040c04007181400b01c46050107200c64410300d05626101041105a03003180c2d86900742402080c040c00c41d540c0d0030050450096200e0b208c0c0110301c000c0710340c2c0c40c1062040171510100d0000d0545c0f40040656080d0b030724a001a42c0c2510038404440d1800e403075011411410b40f0340344500d9a45000007407038142d40c0b0721409007190054081c0405c0c0005036000b4010399009032401d0191840c200003c880e41e626001d00e6590500301c0000600008003110b000c50f42186440c411900402010303100c52201d641d400040104040da210340800455801c80d500245195007219041d17400440c03483c485095100c024000d521900000a0a03001c02030745902030200040d00e00c2c1102d031220388a01d0440032241c00c0100e1071902d482019055104060320f0301400095640592107040c40030244806c81020b40040e0404606058081c403010100d81c031103102a100070000c841c55000004180d03003581111442d2408004140d42007140b8940144c1c80b4404400d082009034903020030299a44440010 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 655347077 1250 655345827 655345837
    0x403260112020d1e0519050c2e02010f1508030703050a2c1302090315100503010f0605090106110a02062b0c0e06041208070201020a0510020408070f1217 67
    0xa01810800ca24145a004d228050344481c46442103e40d030b003202044d2210007130b400500c0200981e00c08030b040c02003070414580c6401aa468099012150b8401c0b000d10300d1210b0461300410b0041c1c1d52203866200c1d0940b2805440d00218000c1c4960b80c0d0701c1e040101e425200e00c10404082c1c01c0c0000080d101c44078520070465041076040103032003102c40c0ba00b00d24440e00c0207604411a20311900c2c020290713a00b0b101300d9100719034081c10b005005255040f803942c41c10b002d101d0f00800481943ca454040000c2c1a2000e00a841000700d6140c80000c0e150b0601080184040040c0c025004100808640001102002038014900c580460321142c45245160400b4042615003c54442001017030080c1080300c1e50b00c0d00142c500841940702c2e042884100e03001e00025014900c503840500b25404281c80202c0e903400010101140184181c55041e039498490500d4001e0b60b03038981d18a950b00050030440c0c1201800b07000040d081f0360040b046076900e00142d175001010390440280c41c180b1960860b00c014003400c0104c3d4 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 655348327 1250 655347077 655347083
    0xa0c020708160e010b0324040605060703020a020a0b07020109030b1f0b090a0b0c030a0311130e010e01090903050307030c020115080a0312060e0c0c0106050a0e0403260112020d 77
    0x240240206620003140b0820a11460300c80440040010603d003100300b00341c038881c0903481c4520003c0340c154464600c9945500c0c10719604282c1d03030100030072583c58070001024190b0181c1c00414410f010f620610900b5002588600c036030281c24030003480142c0c1e004c2140c5084036080302d8070088035203540d1003441580d0801c10805005006443c000100c20340320070041c1c0080c0d0f4088441d20300329070796200c000215106046181c0c0349030f00100442aa024040c0e840b60346680003105009080c0300403d003502c0e5040d11250890800b41c24400c0c01002080e11449501d8090601c0e000140820500742d03a0103004e90201910708000e05441e0981c0440ba14800d50000c02841051101d46a845a881403640d8840d220b185003a00022540c0441401d10341103402084122005540c1e405020354425901e02481e070800c044410f0300307540b03500c40060980d4414264002901071403140e088282418640034201c01d0081440300002004000d103420a01c90b1000494111806800c5902d032258407880014ac000004038002 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 655349577 1250 655348327 655348333
    0x6240d0b030a060e19021c030324030203120a0509040b0f040c03020a2606011b0b070512070e030604020603061201020f0a0215040b0a110c0a030804021c0b0a0c020708 73
    0x7602401000c0c0c02191918a04a066942d60605100e569000c150301c1200a50000c82c814512002c2e40c008011900003a07000c1d2274001510148200344030044500c00300d040844001403581030040d07190521856122910b245211894440d030f084002e80365001d00c03008103229a68840004243e61507140b8903a064800040c01004a11000d001c064000c0d00148480c50000b4a5035585a41e00b6010300c908507054804030f041030a0341c0d6916001124030404000c102d811012060480c100018003074020140100c440d902d1f00d43d101d1116503c00ca4100314028104810401121240515510b000c250150810340540340295241d50700d40105103292140481001c15600c0081e607000c000080d400503010181d196801c0c0c40c400c410142e030721a0021400d46010705010380c12000314030120003e900101114220350703074144c1001c00545101c1d0505410b03250075030209245008000852174489201c0300920400041041c40180e6038842e0305009038003d00340c5a905642c0d0f850a800d440c001c00035172000740980f40c11 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 655350827 1250 655349577 655349593
    0x10e04050703050f0601020a0201051902120a09060e012a170a020c0a0504061505130f030b1801050907050d060209040510170105010605070201030b04060b030109060e06240d0b03 78
    0x70050041c0320031030715078900c400481c001c074030385620104241c0c107143d4059650300e0800d44010503003007224031080b0070380e0158811a04801d0a800444014000c3d0300c0560b01d59801c41460420043d00c0c1451490f9000c0c100000840c0008450365049802c403884989401c201c00350703142c3e5142c44c01401e06030800401125034042200c4440640c00105443d02100c01d44107031651b1903544023440182d80c01802921500400d1044c014801c6101d9000707802494120360b0360203491a03484074221010b40303180d04255a81c01d0f10304100700845615a840000c50042c0c84c2c0200010700e0f02902241d1190114068244120342e0742a001c414440150141e8881c0312005108200c18188141d10400e0700c80b40b0300c64240c008080c1c18450003404010b02c21141254482c1c0c40711840e104180d80114010100c00c1700711a0701c242c0c1c071903004c1000448903000d035000c3e000b00c0d44005000c40c10000541c2807620028161172140e230700344080c05a60014007040c040789620710b002c0c190300d545002d03901d00090414140455018418058 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 655352077 1250 655350827 655350841
    0x81614030c0402040816092a0e0402030c03012303060c090103090b0a05040212010b0108012c07030e0f01050c0d0915020a050a110c010c23010513030311120a0b010e0405 74
    0xa41d038800f0100711b200241069543d4210300c0141d801c1080100c0c80107425001d040510031251002110390320a80c42d103512609800c2000a00300d07001a40c00509000010006101148075000340b00990601002100700740103400740025a1030000511003101900c000c2602041a4029002002c00c180c1c000c0317a07149185072038805540104411034090348640c0d641811030241107410b100b0710b02e2005040c1c1d01c0300707456170030042c03441100100400503000c0c2d220f076112412506504d404031740340200c0082d07038046840b10501103503501c0c008000c017403039215034501418401b2411445003105e100c06d159840c0030844141c9410f02000070300784500740a00581c00001d1000c0301c154401c0089c11101340a40303442d080c01e041d288006646141c01c4032840d0101e05049490008030701e1b4140400c81e4140c055006d002c180008848003404d441d02030f1594404641d20780c82400805030507006540c40a0541410b0074104100c4a190f10b4420030040c20100445035500c0f411481c0364880d12914030080c10180003404a030030009 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 655353327 1250 655352077 655352083
    0x3060b03100e10110c0a02040504140102030f010806010504060e01050d17040f0e0c0406020a140c030f101109010c06020f070611070c0b0f0a0327030810081614030c04020408 76
    0xd11a074003042c0303031544011021303040304190350b5480155030040c190a0718581c2840300070600038000340d44c5549144038001c2c82440900096205d520071a51655081d450454658901101a0003482c400d07030170104103005469000d038106044400880c0d004030500d0705d41c100300750f201400500c40c12000740c1c00240070601c0f420040c8000100c0d0f42c0c58007042d942e40d0f1042d00400c00307401103024143c016000204001c0210781c07079955442da00000801901c00c0070b8982c6000a1501410701d107240040e4003c600010780b000d0051041402942510900600d021050300000307069074040c42c0014821603001c5000486800ca010990f488103511407010494442c8001140700550441c020480e14100c0900c0c0c042060039400c030540d080c02031401c0b40d1724280583e0b1b030010780140c11018840c0408011000c190091100c0e5042060f072840d00a07200c2d9411820807003581e1103800e0030798005174666401181d400d044901a40b810500b29210104840d00c011000f800180c18040908440d40e8064008031340458000408 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 655354577 1250 655353327 655353343
    0x1409061314041404060902120105010f06110105010302030d0c0302031c02222315030c0903061f0308210103050c01120b060405060702060d02070b070305060603090703060b03100e 78
    0x865400607a041001c4100000c0c3c51401490801580b4804081000110150070024490344010407544000c0c0d0111100340c02c4900980c803100100b03443c0e15080241c0c44c0c000d0041c80c610071507200280070960640e000700c1c0d0b42c1c0a410045c4400c10800996400c2403510a0090704c102c1d000d142c503a00140510703000c9000c040c3d00310102d92680340f004035440e01055000d4104035000c85e41d0011f4002e540c07e5695940b18a0542c44c4a43d613908600d05501d03d00c51955020021807040b503075440710035160314a140034507141050050021818181203100012102c200814142c200d035800032100d82c0d26951410418402105040d010032948504000402002030202d4500c280b000300382d88176111045440d124000365800080c0860308a50304000c180b000d42031450080032514009030400b45401345040c1d03e80e0480c0c1c030008040d581c8040311024031070a254075024680d081807007200e02c24114180381000d19240c3c2d0716484002d219a948144065142c0c80c244014110602c515008114040060721015111044 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 655355827 1250 655354577 655354589
    0x20d080f0f07241b110304030206040e0a05060a030c0b0d0207051507080a180206130b040306090b0f09190204060b0408071805100e0a151d060102010b0102030a14090613 74
    0x1091203843d1807240e1602c0f4903c18254a0000d40d0600c0d64900000d540120102c420350380d0354001040301101584a51300240024420308005a00798079245291800f190400381c085c80c4640c1040c4801c00108000b201240b06071424442c0003a40c844070704480400030301c903174003004103203001f000c0c074480c070316600040981e10a02845c0c485001c295520b00840007100c030301d810303048031000813400f501003d8140f100203840520303010006410160b0300d0382400e0000380c00950048803019101d200d081d00b000f640420258100d00d8a203544112401c052080a440b80360140415803100340c008485000d40d0354a401c244c2c01000c1e0100003d41d52b03901c0341840da448040314000c03541c01c031103d0706001a8030400c900c40c031442074070603114480e807550400c01020911030000d00380c120280e4851071980c2c04206410fa224004050510440d0344001605040c103643d5040204880c2c10359142104051090f600401140c4103a5120b240415500c6560b1444c0d0407903016051000750400030101d00400000c0c0308007075a00c16161 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 655357077 1250 655355827 655355873
    0xc030412050c1e071a03070207150c0f050c060d14061e090702070906060507030e03280c080609011d06160e060d0e0c01030605010c020d080f0f07 64
    0x2046482919188101d080800c40c9500a0909038012042400011010048042600c4d843e55658425040e1a0705610b1458407403000007080c42061901004940002c1c1420300c0300c80404d0140e4100504258120701015240000d81c0f21b81004004c014400500c0c1b4000041c5001d0300e0b005018680e800805000c0c0c030403010920a203003ca5071502e03082c0f22110301000c4510b010b103c00301e41f18052110a410103040a01540300d002e60110711203940340038020160041ea0754198603003866080080114142d0f0f68018003d4010414000c220f80352244000180c01c08903030811090912884c0c046081d19842e4886001030040f5400e00c01c48403010b411a8030005910240c0104024900520301c1d200c1c18243c56060010010703651001c0058003403005c4a0a400d001004181028011980c51065885088229095801078001c004c101c0d07800d03100380310142100386401c210f50100c07540030500040c810f0070f000d86031240110300c42000010340c20840d08a40c1014411a444055600e01590f11455503501c05080ba4 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 655358327 1250 655357077 655357103
    0x1030608060603060a020c0a0b0f06010f0512010b0a0e04141e0108030901180b0d061e051e040207080706020c150f0a0c110d081602010b15030a0f050c0304 68
    0x1403000555500070369005000d02055103403611450001e601c660460601401405074901c081a03a445041d07110311060040034500d8600180018820a0702489000900c05d0500c02105014081518241940c000702819990394044070000d43e00403194417100c80e44103007400c0c00d1268405d031588542c0d0003800c0c00c40181c410ba103000017042841040c01d020b02045a0b00c00c1c0103442c00e03136100341101040d2031000901c1e09401600c038030440c00141d000d00e0300750090503100e0030200007900c0711608402044c501c28420189007800d01c0000381c040c2001c44520148045e01c040d8603007c0d075540707604030340031294413040c0a6910780080c03a101c0041d400450f010b8802d801143c13401ca03843c40c0d0188001e4480c00b05199600c0196840c1054039004194107003440d030400558104c2902e0a16041001c00c110b03401075180c2525501e811614800401030540c1c6400859042c01118421034903200800c0d0580c08c2c440705560313240d0383c904060300024003441c080c46420a00300300c14841d0003c002d5000314003850155450314044 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 655359577 1250 655358327 655358339
    0xf0f020903160b0a080a0f110702030708070510050309031b1b0a060c021e13060e0c07032001150b09010e0108040b0a1805060f071808030a0c11040c0e010306 69
    0x5542c0901ca00181e001080220703401e020f110f5071589038881d009007400100d41c01814075003002c89001c4085184e69010020b18141540340c10481c11000b0310040c4001d11350a400c10f808640754000c0c0204400900c00b002c0085028000b003823058461050680c4c21404801d420040c40c0c60b030713403001100100005150000c12120783d007403d01c416415125541c40d0f0303180f00322041d428462f54144401c0c00080307800c250f14103166a642c81d0030300701081d160001c1010820031b0429a20003003200002e030180440342010000c940000b40c0100501d40c4aa62141d0f004650004e201e160070701505061805640000b80d1a10114071192482c01402c6d90000030385e2011040d00c04200103450340c0c00103540150408043c440020b825a40e160020303c1308145d0b6006440000040d13540d030178580034098801c0000c01c1440f00802c03400702d500a4041e1114410541200c41c20351901d00c800d81c80b40f0504034040300b08080c510030301c1c00f403101c20410004840c0000e84200802c4060b00001400012410710450000741402c02c00285 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 655360827 1250 655359577 655359613
    0x30909050601020703150207021806031018022404150912020d061113080303041103031204110f03100501050a060309030203390c0102101803120f0f020903 68
    0x2041c4010b0700200016411a10341041405000f400c004016030204881e00c010b0300ca100b80302c404400c0301d6011121500317140081505004084050b01c500314a040c0c0b8032401500303103410030b41c1902d405555200003961440415641d1040c0e1110f9165182000100010140c414512a075103400b6540e886840b9603403111180c08040b0138446001e94442078040104010803465071000c0140c801030240b60f85408100c50042004841d80c0e07001c031040c0d400100030801440f003162035605c0d0154007280030b9483c1000303414288020110140c005040d40c1e00345000000c3c60b0301d606211402d01304008045a001c07131010019900581802d003c0c1900560003803400045081c041d0050f050030301d6140d00a58102070040150300c1020203807208044203118002e940070700b2210103045d00b0445018041c041c011a4000030000391030180d40d00200e001c2c071403a181035070710114050b42c000740c052607143c0b0f400010f10107003455000c0a450322040c1e00c19100d10305181e010441c4032030350041007895001d130300f0741c2e144003041c4a083e14 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 655362077 1250 655360827 655360831
    0xd17030702010b0a14151e07060e010b18190203090c040b0111030a1404150c050c01080c09010c0312181b080c090a0e0a0f0218190905010204150c03090905 68
    0x851701e030300104145d07060301d4144e040203100c1c07040114150030f0401c009442d10012104102c0101881c03800a042030511059005505001c00c44000074004010190302089944400c560101c5401000d0070104103000d56104036950002c20f0600e042d500d90030301116a0780c5401800240601c5a40b4103a1009030550280c040c60502d0440c2101450030010701e1a019603600443d84841d182900013040040707207407401c000d54904900703025a1881e965003200d01c1c000380740003400519141401181c0c01041000507000b000c40c3c100c4a8207280110011001d0724090300d440c4484034813000c0c05410310b01080721714044210100c142c14000e9074801c03551282c141d07041c80d8508440c020101030360080807228006013070240c400358000c00d01a600080c0c142d1510b1030707281003001380b481c2200d8100d8101c49040940c540704801c10041c141051903c9820b0034000c14001d084080014101901902c07203141c20140082903054400400381e0000d5000610003204008040d400b881204801107400e5010103d09646075114484c = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 655363327 1250 655362077 655362089
    0x61e0306050f0d170316020f120a2f0325051b012102030a05150f1003060e0906010602010e0303092e020c0a02010e010c03050906090d17030702010b0a 66
    0xc80b80d19103040612500001c601410b6500541000c0e0325029041030f01d00451184104100284071007004d4003000341400000c2620b44299800060b81c2024605800111b40702c41c1f1041c00e04102d004580d10040040c03003107001030f00b000c440410b062150010300100081100700c449600e5014612611000a08616100f22000d4555840f08421030425071000803141030130391050500308280d20466146c1c50801091401c02d0a02c140c0203c2400030000b6130340521500010f49258220306403003144082407003c44170103909031084902108c040040d0b03020760700602c0a40b1142c01001c0251420002a86d90380000b88aa03200644c80c2280c11072940c080401501d00070000301c809090030081c0b82401c80d40b0890b0000c03000b1100686036881d1080340c0c0c0c0710310091414100d140d02a0030b80501c1400003401080445040c076050120303207298803001981c00740489001100031a1704503129001c90b0701151060072400c10082c02d00c42d11640e0158216050b201462003408580d000344190007607602840050b00c070512442c = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 655364577 1250 655363327 655363339
    0x60605130e0402010e06033c0a0507050d0c03050f0c0309030f07170a0804170316140c0703030c06051b030105091321090b1206060a050c0106061e030605 67
    0x280719942059030701542003801407402c07100c011035140001c0c10f154000c0d2102e04800011224080b000c45006d402c84901080705010780c0e44100b5105a294068100100706151259540700003490450045041d44d280c000b80050801000c06403650150040c04251020110000c2900018905903641d40440c0c0c4242c0080c4095400d008001384080b10941010004446c2c07802c1805a40018203400d40107000ba080f030694a1031721900301401c01d040441560080760000c41c004100300f142400c8005504d1134000784502e400424000085002c0140d0702800c0c100c4100d900412800005140d8040034400801c0d00400c02040783d5103500204109100840d403000245240520041000d45040598154007212910011100c01d241d0341e1140c0b1580c20b094080c4145103800020382c07800a612107081d801030301030f04404901c1d0607411a5460480600208140c1c401c4800241c45015603119205440b68800201d00a124094a0703007005016103401c030401c1081e80a03001e2410006503c02d02824044070000381c07032 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 655365827 1250 655364577 655364579
    0x1080f0105060a030f080a141911010c1e020a0b0106020f06090c03120d090b0420090f060d020112141e13030e0d050a080a020c01020a170703030f0f06080106060513 72
    0xa07068150804491f61080c41240c0c5880300302d0021800c0181500c0031407a2403016100f405440141c0326131403031040c5500582c50b120961441d03503000043d070081941801c2c02c41d01e9120035148105d190280707120008104c48075110000556a40010355213503c0ea02d580e064403181d60b070720b802213660785003050300482d03144e4803201c0c0740c1103107480303100080c41045c240101c00701d2464030544901070242400d03503040350255818008402030b980500038440c040ca20403185510740d400e00407004641080050b16192007001c100c0b0700402107a000345403850060303180350350900076443c403c0f800c1c01544401f1100d80c80052400c00505283e4521102558420204508454610030301600e04462500c200044075070090b2401c80741c400814820445900403900c107a8590380e840800020003030030000309080182c15503115032001d0340010290304201c40a134041c03d0351a03480d2041420100c5c09458603075055000300c0d00e0460300803040c648540245d010345050704001e0003001d5440703000310f03103d101e0820110060090200 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 655367077 1250 655365827 655365833
    0x8120708100915032114161515141309050322080f060103020a0504140a1109041a09070801052b02061c0509060f0f041a01080f0105060a030f 62
    0x80158400203c54004450003900c80d80d51502105e1031040d038100a0284140c2e05e41c490354400c0c2000403410101d01182d0810302c0b0319030200000c0704410001130400800c40381222005079598072244050f00c00c098184035581c0c0d41c54200c000c0c1e041c440f0446000f4203410080041c10981805082149540b01d80110303d007441c010519240c10f5041e070b40c00e00741e10001c01400a10102c003040160191181600545001d51446c41044007101459103e14041d504001540b1220000c00721107a500020040d808200c0c4240b0146c1d807110f42c8200008613600514144400030150004820a401000180d4041c00c00d0380b6046000e0f1104c80c1c00b4800c0d103612120004250a881111049a540d0340010a11034901000707640c0c0040c0c01504410342c003248410100c2036104250a00780100340c0c10040490251155081c03200c400c1d600300c00000c05108a03017600c58085410000103550f0100219002e55510589503181c941d0107032101c3c400303107243d841e0b50301303080115243d403805011010403a82d006a0218803210350323079 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 655368327 1250 655367077 655367081
    0xf0c0604090c200f010506030c0102031606020412150b03011b21020a05090a0b03100b1b061627062019060f1a040b03010902030a081207081009 63
    0x340070504201c1c44503000ca032488404000f85400440c2d03600902a80015406464212100141003d1003680400703072000c0140d8001c07045031080400218802e20007105070030010041e102e0b941c00701e040d41c06d03404404001c3c4140311010002a0070081414414444a10300f050300342e804000180010b121594030030040980281e41084064159070344914103801b08180560032a08241001e40200b0000190440309203801480080680550741a403401c50818a20540b0013544c81e00804c103c14200042c1c1c41c1540105115941c4402c0e043d808a4440385001c00380182000c40030301560300411050044100070024103148201600c041c1070103000c0043c40c00c142225082800300c0c901c030710364042d1540190900e50500002080c083c500e10104000d40b00c500d0640100c07a0b280382225034051030104036200260403140440707008001180c0118142e940c4000090040480410083d41072280480c420b040044030760240000390341011600d42d8a035160101a02c036042c046070b000e20000c81604040c00081c88507 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 655369577 1250 655368327 655368341
    0xb030c01050c100608010c020c09011a090409050a03020c131406040c0915020a120801060c110102030f120103020f03070305120c01110f03250c0b04021516050f0c060409 74
    0x55401c850f81d6514050b0702c1401c4625039044084680d458080b02e070a2031303070100403d2100c5c003c16200544290326140c0140d21856a45c81600b001c00000620256990390780e8000e0302c00d8581200550300d00c14135078507010f541e0350403130018540180007081d1268a00d0089204404640704603100b22401507442104000040c41a40200070a01c41c40c0c4002244221510020b0f013400600303500148081003d5003080c100074500c820005041200240040c4050760344108001350300d42c1c0c004030b68904a048040141c3c25402040c0214040800204072007404580ce80d941c11b040324000e0f5000714101d40c0d0403040c140ca4a881c1c2c040604603501110b40e03541c11b22990001001d41400e1800000390b240000e03660464194400000203448910120500640c00c04004203078162490462000c4154030005c070000d81410000320004d1304442d0040001010344d01c2e83c0d0020383c2c40c4040d015420f0303910380c08428604103502d4507a105907198403e04844210030700b00003070300d403143d01c00c010300860070f127841c000c1540b000c2e00316 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 655370827 1250 655369577 655369597
    0x32802040f110403031704030c08070317151201020f03040f050a0803150906010c0b0703020a020102040b03070201091a040f0f0302010b090405010e010c052a0703120807120b030c0105 80
    0x500c01101c400c0c00d240b84034550048252804403551103142d030400178000280c4801c03000742944550140000240c01ca80300e210030940c44002c0b140c403081c0509058030800c0d900702414a2180f492410842e0760003e16400d601c07413003002c589000356104107841141c00c13405200d4080560020400c081030104040d4042d82400b02d200320119800d51189948018881d041038405660558000760340c0310861904c952120b41c0080207180c0f40e0a01c031495290400d9403038026004d0b1052581c005003488034180300303404490140120710301e0135507241000e1070000c2c028010392030241d40c807060b5012182d41c050aa0900c06000d5900300300c41c1041400d85403945024003004030030417400d5641e94081011980c0780c0303c1c503031031040d800b6600021302180243d0089007500d44020000081040c200308001c6c0010342c8104841d010510301040700400d0041061280c604011303500050212009003c41440c0d00798000c1009100e03610070395a443c01c030050030070000300f034500c0d800300954103812a0031000043e502c01c030060003102074 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 655372077 1250 655370827 655370831
    0x18080d0e060c0a05010501060305060d0c0504020f0c0a12300f0b0d440d150306050a1b0509121e07080c1c030c1a1f0503280204 56
    0x40390b02d4001e40340510040c000c0703c00b40d45500c010000607030075110f60ba034881300c160fa200c480d000f0703542e440c400561450f0058500c00c82d4089550002d002c11081600c1422200b80125030700c280b014100024042c03503040d90107001815030740c03455147e4030420b20b8a80801d40c00705014940c0800460000016085960b010300380c440d0340701072804040e641c0c01046c3d290903005464800092500d8240c90003a0352805552003440c4107041400c11441c00514126640c00c0c4062040381e0301e60781c521035160086c20714088020001110400d0120a0004070391003107000f40e1b0100810842c6050001500100e11a10309008000c82c20620038030307844d401c24200a41c40c04000c001038528441e8442d01e1031144514400010000f50f1000502f4021a282045031400004040700d0704140300d4010030b40c4000ba484580401002c0000c403001000412a01000c403c41c0a001c00d0720300001c41c0382042402c0c3c6820b80c003001100414698140002d010b040101704500285000001d01c4400044800c00440905c680c96040303802503 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 655373327 1250 655372077 655372087
    0x4030308041442071403040c081c03050703061805070915050c10050105061606060510080618090d110f01090b0601080114060a0e0d0b011518080d0e06 66
    0x4403c030501c10701e05022031890721079800e400c002541c3c40607090303400c0310f400c2020000c2c0205241c0080050810401c2c1204080d43c0303903103502c0c000d841944503a00c108460304c82c90140401e40c0070800031881001c0111740d01040142ea9600d021000d4800c6445210180c800d2401d141c1106406500300e03542c0483d407424051050b554660300700d510400711403403810004a000c1600300c0f00400c144040910303500c0b6410148469418a030000780c5600c5942d001d20841d03640d440b4150100300d0550054402040d00402c0207030400c260381c001400c07400c5d085610038840d55070011001b00c1500d6400a443c000d44200000307007152640380d134096800e0b42d0070360030318003080c4184043c02e00b181c0e000340101825207104007201141d0341050000035041041c1a000036071190a002d00d0700a060f141e460541d40884030391b2070101344040504011030182c580d000e0740501494920070001c55008040340b024000c070056a514003004043d45c04101910100f05c2c05914103a0b000a1940301c0c01500c590300c0c00300c156100821a614013 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 655374577 1250 655373327 655373353
    0xd050102070b090f0f1c030b010c081303330b0d02090c0a11060702190204021c1b052a150103030806030c150702011404120501050912040303080414 65
    0x2c420495a50740715600c11264111040014044c182100009070010104440d81344503103940030640f0304c4081c0405956881403091684030b640340000f1a60000100d598030950600c0d0415899454001500c0b44092040151082070144030354408a0030b00c100c0c201640080d20054502824003c001d281d03000480003110b00150751089030342401a90304104031036850f0b4180e507014200041131004105540c0006040090b126000304441c0b01303a544159660074240e005100043c0203004010341c2c04041d80c65201c18a01c900415801022008a11459a403c81020801c02c95413441580e0035034500c0c0c246003204001c9840354000024011000000f51009072907007669002900da0b00341c0c030a8002580300c5062050505086c4200b10203402e00740c03000c40c0c224080e030b0f80c445128811580003c1c10068040d84134040310007e9000d4901a00c00103040d614601c032181401030107001d0540e5010040d0180c0b0651840c1c00061000704c1c1c040700d6142e103403000c3c1035560b615421400c105122008960b805960713004440 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 655375827 1250 655374577 655374593
    0x204060f0b1909030b16020304090e01020d0e0c1e12010504050a060e070b030c030603070503030a030e0c0d121b06060617090d021902150a020a1a150d05010207 70
    0xd014040c0005403500005082203064803014948401440740d031420900221741c002c0d0003158001e03c1201c00484440f5420f004a146200300d40c46074884e1864905440301c00380064005102c807252044007406184070b034116154440c1e07104a01c8130b03406030040240c180c441d01c0c903081d002c1081400401d010b0340180000616420754008030350480d1143c00494440c5c00300302851151440707030240c0c60010000d082c100700b0b4403021440050640d4032881000f1001800e255001c020700006000041c080d20b80b84c840d8020f016002d0701001205c810706005a040340d09044c10102e801d82e140700e400510950307801c20103907000c2d034043c60003040ea0729803d804244800c01060303580c040d000081c0110343d01c105040b401d4937400da40300300303001d4184161508140c4107181460350000d0141c500424880c059910310440784006104041c0310081c0c00c1707010070302207552586260042080c8254074040c1c5010011f407034100c41480150501181e451802189440c0d404c6014103041200d040901d01c144001850101c4d15262901 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 655377077 1250 655375827 655375829
    0xc1b06170105030d12141e0703020304031b1b0605031e241306032d03121d060406021810050a0315030203030c1f0c020c0d0303060f080604020a06080c160204060f 71
    0x8011402c54201d5044640ca84850300d43c0640c2302e02c1e0443c110b0600784c0d40107007207690300b803a25104040d11908104c02e03c00d00848070202030b2500100b11541c84e0307580d20050451380045400714041c1da455225000000740d1743d0309640c07086450f40c52019010003d0f442040c2c05846440c04a5004042001c4a500800b1a4801c050155000300c035000c0c003070140150003800502000c800d980c0301045990152002907002801c444c5510405000030034440c0305841c584c502007101d50003c00c0b071752041e4001d11040c402c656004020504000120070b02d07814480e800d0006c0f200c03024031042d0024004020324048184a6840300040448044a10303149036a41c2d00020325640183d950105142c0040e0443c05030151603140c14544000050070a01405015407800781d243c00d40707891068050701c0203078440e41c1014031a900c85005820178079088100340d42c58959590b0f40e1402110101d004800c2c040e000306107940a6450035100341c0c1003030360ba5031420106006d00c00e000c9050304022600130b40c4407000411014210449a8 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 655378327 1250 655377077 655377091
    0x10f091d04030e0604090b041b39031d0628030f02400501200a0c1505030114130f02042306070302060c0a0c1b06170105030d1214 57
    0x42400c031f000344100411a0f107803003061582c80b8800d01c1c0200c00c56420611400c1180f001c1b01440040421074030a00c0117034161040c0000081c40d20301c05c0300c2c04154101e19141040c2c4030802d40d04045610205c10b00c1114401c48403500d80c40a08410001001580060000c00140451030041165022106000240d8014214414403001454442d29101c8040361401032001e00c040701c403034015407854154001034551400b0b124104440382600b410203030b050390211110340d11400100c445070511400c080d0f405881602034014003c1684600c2c0118610400a036810394404110480040b940c030420420f48454420108452940398200c1954407120f51024000400030f0400018003200124003862201d0104480b03244110014010400403982c00264954001141d561a580e105114103094603066040f020080c03d4070440d9440303007a40040c20180d0002c4881c0f03a1528804000e00f44c60b503125840b0f00740a1180c141d80031054140049100c9c2c0c2c6012005101e0720300004001d8914080104011001c036054 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 655379577 1250 655378327 655378331
    0x30608030d0903030506040b1003020d0603020a1d0c091c0f0f08030106090617010303031808030a1406010512040312090b130c170706030504060605030615010f091d04030e060409 78
    0x2c105040d0107004141d84018129002c01c500c3c600d980024942d840f081c0c0c5402c0c101036011940420002c0c965102e03c02035a0014503043c2c4003566103048091203414803110341d002e9001003000ca0101e01c0c4107001d07164601d000070180da005899182000c241c01160045c25100e0800c207030012008039030049184d0707032200d010f04092540c80d81840e20151070000c042c3e02034400c100030142c0d0118151403401390507040d00e07410f14011604801140300781400300002030019010700000002c2c030180110550004241400401c6500e03803e949000042d11940100c14904090010403c0040c002038032070703c04000c000044440c0000c420400381c4034040035560841d641850302814240700401d006c000a0160010204520b880900f0b001c4003000c0364807000f0a2150905142e02c8802060170804650840805040003408880d4a440c081a02d0fa000001c000600c0e80450329403807504425501c9101020203948241ca50f0500041b1549003c0c610b100c401403098042040251449029030380d400020700c001c000742900 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 655380827 1250 655379577 655379591
    0x1311030717010501090e0406020f070c06050301181a04090302250e100602031206180406050f01050405150613090e030c300a090506160b130f0f03030608030d 69
    0x1d402940041a00568180002c0304030800046a0344041c0e55030180d480140035031a10703291b200048142c040d407040105010f5007000c012036903661050185040313801001490385505d60083d0140b00300d404e030310410080d4058010808401e400cdc41c1d044801001d02c41d00c12165200040103030340310f8040350000001c1c44511040010000c1010405806401c40580c921004149160601c041e50745d1041004e42810852a00c000407500d81c0c468501d0302c0740d444021703450085071809180c5140245421a021452070000380000704070f80c106481060310404003d541c100440c11a132041040680182009180c0d5000d02500860fa00c0314501401540005c0c8100440e15113141d07040107420000c022015140e61000304103007505265402492403c08441403034182e07900c00c0c51a9003110042201e802040e0090f50005a40d401280703000301c000c03000c0380500d035900d1041d11030401190303000034070110140400a0814003240407907110095051007501c60b0400050082d5141c00080c195000b0030041000e0b1950307280 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 655382077 1250 655380827 655380857
    0x510050f0903150a151a07030c0804090203040b01210c05131b08040201121505010c020d06110a020c0102070b0405010e120601060e040b03010509060703020c150a0b031603030c0213110307 82
    0x5e018051720580c1840b1a00c804024000303200d074094010081c1c01c02070241a02d0040c01200e204450140c20820801e564034501418541c1c00c08000b07200d0603940403545200040600f40e09000750401035402203c6034811454070040180c003800700602d0514040d40c5458103419144d00041c20103022225480d81c1180e481c1a00002d481200d02400a40340d07182003c0c1011a03c0d0f20f0550791a0655000b402c11b4040c00c00c003400071400a03c54040c1c010300203841c1c20180c0c40030009800c0a086011920340c00c641028040d03070012600d030800d42c8600195413070248014030413580140c010310b40b42c42c80541400040c0304022801454154203a11007000300381002d1100d20642271501030341c40000c9094000340650300705620f5880c2e403168020819020182c2c041080f0804200611585120500750320b40e149940c2001181040144540500148070740f064005050390410700990581c01c4a0b0580c81d0301241d0503854007807001c1024190007000c40d9a0796a90030094105010700594020740c01b0380c0d600c44a2036a01d031 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 655383327 1250 655382077 655382111
    0x1052d0c15061813060c14070c03140d0503060f030c0a060906080a0c020a0b070e030d02160e0f071b0c091d03163f02070510050f0903150a 61
    0x8043c0c07614000008040000041080d01440007256001d84006600e07440b954084510712540314603c0701c0210f00041040a0044030100c2a09490255071501e03198250300308400e54601c0c020550340301250003440060b505140c60740702107401e0040036069518111010b00020b0700420184c00240c049045001c040c004982d0010310240e0045202904100303202903888040d550b00d0320000e004084030402c4000880451151500f00781300d8401030107e4054400c2c07030740042c1d2102a083c1031500c032040c40781030020b04c0380328901500d8060040d500d0403039202d85400904031440b641e501c1c0c100769070012414011000808600d61230f0300410500d0700004030880320094030700503144044c50588031a8000e0000d01c80710b2664607010800c2681c0082c00441145003072900c40c1044041d01702e60003a00000e0a4484040700c1303050034200780d1006a600b3740c4c6020f9202c0c4104540d4102c8103c19000282c81800004007800c060030041100203c01012144141940789110b9100030046903000398040c2c0752417490100c10210 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 655384577 1250 655383327 655383349
    0x9090b0f04151422020a1404170f2b170109290303030a020711100806120d021c030f060602010f11030f1315090506041101052d0c1506 59
    0x1c440200c00784659030000b003e811219413601c040369600140341581180a94000169613500d030500c10344499840351800200005011600c82c00e00555103040d000d04408901c2043d4600d0200780ea8211014041c0c1000d208151000781da410300589107034241580c0343e84030300341c0d000b40704150002c40c0184154110805080e40001040d06d203000c80700360400740d41d4020088d2507004c0300300741e001030300d484503410b040507420036103012a6003000c4c400c90814441ca0780444000d1003507005a03905600403d0002005a4038180303820381d8401a08030403410401545500550f52040c5031074580070642407028015641180c90507440f820140c3c3d0b40f03151480b40d0340794601640b08041882e040313842c10362610942c01090100d00074000100304100c2a0f0003c10000310b01e1498030404c07682403007000b90301124035215684000a550a45101802482d00c640e0382d841802102c00d01442410540d000c0d0000c861068000e1005074080143d1020078400440d2080c820044620109507000800c0c0050900b1802d0003403910740 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 655385827 1250 655384577 655384579
    0x3070b16110706120204090906050714030103030905010507080c0f0a050105180a23070b03101410030b0a0b0a1d011b0321140601020c040c09090b0f041514 68
    0x44604100705901000c00e240d001c44074a0304015003440d000038400c400910940d000900e0561604115200340720300c96000360b1060b0f5451702c408141c50450340d0f1218130360000b40b000a00040403c3c0052180e544110007400742c0a11511450303060014000c07549041000320a000381c19644000252400d01009009a0760441407448400203099200d8071096208d280711071000e40a1200645100a104007408911505411134015104101d40321000c1100360380c820b44098100503100c48001c20422499910041f45020060504940482c00030060300507150040c0e003c1c0e44086060720000305010500b0080400c0c5007107a80f101e604000c0085070301c000407a02e6951a0420100c40170160903940d009071002000754250500401d6016018030481541001d81107501d0107030b00742a1240d82c9080c5084005010b81e03030036000e54404000c0d0806020445445824002c000744c03003604108030300c1d500342c1e1011840f100098071450f0428041404a820381d0140000b4402c0c15401500411030081010020003500c04 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 655387077 1250 655385827 655385837
    0x61e19050325200f010204062d0e040905010f020d091e032003090a15022517030415020618060103151a19060906050f19020f03070b16 59
    0x14004000a042c2d550b21000301443c04800720f071140f25400700b0098100001c0050b4025591036403103590060490000607802c085990840d400ca02401505443d460856282580c40c1001503120310104000341400c260141c030b113950307038141420044c003050005002448103110041103419091a11900e02c80b42125540b0160046010f948006a801894801c00304d8540c05016101d20000d20150f081d0f00c610928243e000d201c160000400c003400d800c203403402c2c04464080d128020b400130901903c1d9000c0584004042055007420701c2504e410341c80c15003609410f074080700d0070683c42c3c4a58001c14800303031040b040964802000c004c0b20700c07030852100c01100185c1015140700c0d455540d0342c180c42080f5003020340a540e210400d10b107014006a0201803000360040c54011a0003406031840f42e6640140074070360000b4804500450014000d2040f1006a0440c110440ca012815141c800007650200300801c2107028031410602a0802003001c0e120440c040d6052440e1820300b460120f4134882c00b5203072102408 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 655388327 1250 655387077 655387141
    0x170303010b030c130e090d1d010819020f030a0203010807230d060902090a140c071707170c061909111210061e05010905061e190503 58
    0x1010000da9401c641071241080d16a01e100c20290b11021280e04100d11030785117003040107460000065081420212a1a00c1c0f502c05550401a444070b4860085940454104004100400710400109a254844803001030416140140a5515a0040d1060400242c01100500c2902410310100005012002c1941e072109400c8510545220054441c248101340c1481c968051203c0c81d008403801c1e580c020901891032828015203c02880b606041d045000305034000600c00171030340b078220341d000c980000810320194001043c8202c1584004e0302200d07404092180302d9608480d00010b0010060044081c000503d40810b040500c2252008a00303003113800c00e030600c008603c030313090b51070781c80442540c009400015058125240542042c00010118036200000903c0f0001c0943c3e091040f50010366045c6840e511001181c03090034a0040d654402030400140300b4081005034101058058960034a060084000d03501c1b1141c004032045002150700003003080004100c0d6a0385c1c01034018208441d041c15 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 655389577 1250 655388327 655388339
    0x30e100203090d0804020a21060606020606060906180301020403030518240a0e09070309051506370b0918010b04142805120102040608070503070e0301140117030301 72
    0x78070b0610b042c01e400e0081d00c4c004141551141c01146018050b030019400c000705281810501c2c4090004094400798a06800899820300c04a03100d401094000c00f46400d1440b440100138045c1c2c800c3d2606100419103c000c01c20b00c1d100ac1c0098001035010f511040d446960a0802020f4001c6840c03860384100f03080f1041c00c504015044240c03880680d108456a220001c880d02501c1d44002c07518010f40c00340f401d40c1004030095254003c1800d40348a0000d80c1d00c001c141007260098003105850710759102d252030350201c441c2c10806550388400c90344480807050170100441e500c0f200148941010210031000950810181804034144251402000c1071885543c503150752404e49000301e009941c070403004441105510b0b48c40c0c0030340200c07078070407011403d000700881d404a402d240d8440c46250b00444800c0324041c8070242c18800c1d64221181c079101c203084c03662111005c4500745e2000308004144032030004241032544091050610500d04140240710035410102c852005540101c011249644104018410 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 655390827 1250 655389577 655389583
    0x30d0e090c090904120c050a0b151e100207030803010b030a060608060d141e060a2304030f05190305010905010f031e0c0b030901050a050f061806010201060f06030e10020309 76
    0x3000f5000345171031182280c0d0703e104442601c091000900548681d105110901c00039403041805588150345c46052200c240c010300040200001d1180c6c03195103511441c030811b0400810030031a80d00c0520681c3c446507120b540c0c1a0260b0400c1e00000280c08000c401c01078043d40b24462a00502640c0c20f010b2003d141020000785100d48205d001420345c408106800c44501e4104820090364555524003421754805054a542e100f908541100c8410700b8040303074901300e031400294490103c62421449081d036456850a903100302e0403d8485003002800c0000d07203c1c0403c0d55005180346640355030041417551412440300c00740c5030181c001000c0821040400c0000480c2801055400c1c510180380c4880b0391130700d0134220f03aa80d144c2e40c8941a0040e00000f000000017045d4001ca00c24102381e00200050f40f40d0050034a503100c021a2500e40160010806446c14003500c040568094014800440c0081d151240801e001da4240c0c07000c00800d44542c4c240204032014080d0710a0f11264039421400c0d07203440200302d07503 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 655392077 1250 655390827 655390831
    0x3070e0c190e0d061b05030609130804030b0703050a050c09130e01060f03050d0f140414120d170a11090909010e06010f061704020303090618030d0e090c0909 69
    0x7414003504120703a8552801020240d11101000703000314801e69581c00d00001600c01c155205400c048096a4401258000c105690080002409101050742c1e00d400c081034080700500b00ba1400c070024000000015040220741f44103882ca55400704103401e00c2800350050310750140c0401502e00c0240002805601e56034412001e01c040140e001ca0242c04082e078460041c66240c00401181c480c260b008170502000007102442918580c0d14044141e6854808484140705610013100d100000c2000704282161316510b420f50f0710b0020040000c22101e515800c3c90588a0503460000c076450985e01700e600c605504140d94002c000c840144400d0004041c014110f20900e540380f441087c64a012034488082544a00b10300030981003100e10b0744d6122010404c02d050a48103800025080700000110341548000060186d54050019410002101e04100d02034100d031a140ba468001d0005401c0555402c200b40504200c0750344440091501c1c0400388966600003d1100d05150420481d1b4403942d2945d1034250303 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 655393327 1250 655392077 655392097
    0x1204140114061507021504031b0f08031209011806061d0609010e041401020301030c0e0705091305060f0a030c1401020d0905010806041127030a1703060d080f030603070e0c 75
    0x1c4e507101107038800030703001c904c204030300303100c1c444021601200b084070b19132145884040c0361800110440c2e0310000100702c2400c0e80128052904240a4291640450100541c00c81c04807000412010799070282042da400d90300c9011f40720142c40d0b207010800502821812001b02448449404d50342c949540840c41001041c03142e954581507400c001010700028000411807546114002e56603035940c0d003499107003c0080c0c01100206000742c0c0c045901c13240075908540b4000302c0174212501e5403d034204004000c21004120a40005414110402507581c1e2104080618411400742540741c3c01c1030919480d501c41c40f40342c0750540d8000e80f0512401070300300266404803a401d00c0c2580d0303156201c1c4007240143c0540405c1c10030010022401c0c1614030009445005c8280103180d41d14010000c3d13408140c2daa56451034040c2c1001c11714040c000c0c00b442c6540085510180141555850022950b1890681d610078041c5001146010052018524003402110020401c28030f0342d005074242401c2d035640324807641d0503403 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 655394577 1250 655393327 655393369
    0x9060308090d1403030406090519150f0b040c020f070509091203070507020a0303020d0e0a270e0604051f051005040b0409050706020d08091917120414011406 69
    0x2803400c00040c0009600700382e180c0ea0a4170384174140ba15280026080000c022200d501480420350b10142601c0003540000ea00300784908101411046e0400c0104960040d9a588a486240e1009242c50318002e0201c0c1c00358980c0148961717600034050b24101281750300824480d8805030705000e40c00e600000c030360a4185a1080942d034035192030b00141c0c0c1a00c188070009400560315040001411740102d00780080e54002d81b1541d4100c0301c43c00400c401c070130480c025101c000203481406001c000c0b801c0c0400d420000d00c6d110018441d15441c00741840c00340c08031402c840c035501824162500200702070001c1c038520000d035010710180c20401801038400e941405154007460766807049400300d994a400c84804c55400900740c0702d90710b488a100039120b180c201014000320380050080b03210b170000016240541160a081e400c041046642c1d048915440503c004030340720414401c0360800c00700703071507240d0003030b445494041000c60158502c6400d460480003019610440e80042100944500e03091000140c4ca001c09 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 655395683 1106 655394577 655394599
    0x13090614090303130305130b0c0d02030c03030c0304150504140c0105070f080a020a0b07020a020f0409020901090b0a0b0403050a0614011526040c0608010906030809 72
    0x110758926481000091608000c8241c9845003921900c0c1652500c0101c0040c41066403054005031080b180010f04140e000408200d5400d040c80c0390b001850038000e1106d982500d07070000804440810300000b00041c200240654041d0303890110010803c40f41c201400c00d8101c45050101e418214403d05507c50342642c002c200340c40311a0343c40844990701c050190707100d100380c0d0403000d90502584281d00d1700c0400284d038a00d050f0710545890b401000c0401c081d004200340030b0322900402c1c1c060352074103401c0409070300c9070302c0400e06490b8807a0010030300a4480c00480c158101a500ca000f1038080405d01000300100800d00140c0503005000c00e00042990000d500c41c02c0d8000e00c0b03140e10185a100840360542e00440204500f0403500c8450920359510180b107100604080350210391881c0005414084503801a0845001d0920200104851410340e501e85182c2d1140e088154407600034220303 = true := by decide +kernel

theorem cover : BRFrame.Cov 655215827 655395683 := by
  have h0 := BRFrame.cov_init 655215827
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655215827 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655215827 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655215827 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655215827 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655215827 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655215827 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655215827 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655215827 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655215827 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655215827 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655215827 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655215827 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655215827 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655215827 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655215827 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655215827 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655215827 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655215827 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655215827 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655215827 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655215827 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655215827 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655215827 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655215827 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655215827 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655215827 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655215827 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655215827 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655215827 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655215827 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655215827 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655215827 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655215827 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655215827 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655215827 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655215827 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655215827 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655215827 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655215827 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655215827 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655215827 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655215827 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655215827 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655215827 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655215827 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655215827 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655215827 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655215827 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655215827 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655215827 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655215827 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655215827 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655215827 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655215827 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655215827 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655215827 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655215827 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655215827 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655215827 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655215827 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655215827 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655215827 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655215827 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655215827 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655215827 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655215827 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655215827 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655215827 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655215827 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655215827 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655215827 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655215827 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655215827 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655215827 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655215827 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655215827 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655215827 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655215827 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655215827 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655215827 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655215827 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655215827 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655215827 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655215827 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655215827 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655215827 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655215827 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655215827 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655215827 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655215827 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655215827 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655215827 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655215827 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655215827 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655215827 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655215827 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655215827 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655215827 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655215827 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655215827 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655215827 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655215827 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655215827 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655215827 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655215827 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655215827 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655215827 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655215827 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655215827 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655215827 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655215827 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655215827 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655215827 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655215827 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655215827 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655215827 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655215827 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655215827 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655215827 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655215827 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655215827 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655215827 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655215827 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655215827 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655215827 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655215827 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655215827 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655215827 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655215827 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655215827 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655215827 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655215827 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655215827 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655215827 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655215827 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655215827 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655215827 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655215827 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655215827 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655215827 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655215827 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655215827 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655215827 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655215827 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 655215827 ≤ n) (h2 : n < 655395683) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
