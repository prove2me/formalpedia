-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4356
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T12:21:36.600327+00:00
-- url     : https://prove2.me/submissions/c7e51e76-772e-4c4d-b10f-1f08fcb92480

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 783273381 ≤ n < 783453237 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 783274631 1250 783273381 783273401
    0xc030a0b0f1f1103090d02010311270108010b1c0b01210209191d181e19110907090b0a031b09140f06040b040306140105030a0f030c0501020d 62
    0x40011800c0c0c00d1440d08690356400c0b01c0340c00400b13503050101e0640084e0039251383c0040a410f15440b6102c0a40202e4804101c130480e1303004210031940d80b80b081842d501c1c005032000c02103010452000010403003401000503501c03078503504914608900400440103019100c40803581c1e062040409203103200d020850904070b0740c400301f130000607190240e203010401710080c0e086601d4840220584148096a01c1c55a840c030403220500d0281240d0f1500c64642d49100407000c4100000c1c00303a280002d01e001801d0310259500107080c821180c42d0505110f22808000c0360540042022002040d13441490410080d8907030311038803900300100c4256913510a008254050416000066620a21b40120300700603e15114004081d01d400c0c44000d003403115070034885038103e4085209a03d46070030f0304800c0c0d07290300448000d07044000015440e0b40c0d8a1401e01c000c0d041421148514071008400450181400602d401c01d294001d03482801814098400791002a200d55081d1865502000400540d1540c0d0090f0f03500c031 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 783275881 1250 783274631 783274669
    0x20130f0506030607210c180303080a050f01142b0f0b0a020a080f04020a03050d09030c090b01020c100c05160305010c0207150f1107032402030c030a0b0f 67
    0x2841c00e8401c25003002c00091843d420f000380b001d81040a8030000102c108119030040f00080c0c4a5801a0183c031804203881e00310a880341c6a40780481090703400b01111b03005502080701800147c4a00b03009050340c20007405402c020b4010400d1010b514a0240e044004c01c3c014842c422900240100a0340184468190291100851443c00c00c08000c0c0d07026271903500c50500c0303904500b00030000000912241004d0004404004c220000c40c040d0359812580320011944402100d1500746880030140920116100c2528603804044000a5403000da0123885030140050b400741208407440c0b020800d40d0491243e40404003d00c45450b000007440070403040707041d00c2441e403140e0000c611f03610301a0b00396003c3e00c90841c110742118030108511948046091403419440c1003101304074880d403204803000c800700c0c2d24a85581c400d413800001800b02c4407a421080a114000c540c001180b8041c900040e4401913601640c80d40b01040092105d49040d80f00c00702480000700351680641d0000001012601e180c0308160349 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 783277131 1250 783275881 783275891
    0x80f091503011d13030206061219060f0e0705060301050103090c0807060e0f1c02010809101406010f1404030b0a090f05100c0908060a020d06080a110906040920130f 72
    0x108150500c000394056440c00c0b130142112103e40e002901d0340400307462a8000d0081c40c0d44254010f00503c070821610321800c1c404184150f680c14001c0143c5601e80f40310013014908801c40c4a00180420340d02c0585602404492840e444c0c04011401070162581c26034a07084480004245d00b030f400d01c4107100404156840c420301842c20810000941c110800407031090707846000d84100248203024885103160242000c905940c0c60342c04103424101c407034040202d107618228503400017844041d03545011311000e0340c4800c03000550110030b03551a017400c48940034041c3c00b03000410000e83c2503008968072410000c80440c04c40c840c1d41c0d03001c140c41c040103000c48079a003182054440072100303407050803501012441d240003907070724003161692034803005405102b4594000500e001c194041da0841d800821420045031301ba03c509d42000c151151961031464450b00e59600030610741e03e1300d8090454500e0300442c58098107a03070010a042c81c00006041c1e203400c00e0088181000240c40c510402082003518480416 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 783278381 1250 783277131 783277169
    0xb150f0d0c051e0d02010c2a0e09010203070207150e060d0c1101110703030f0603020a0f060f0905100c0501090b070e130c020303040209041109071e0804080f09150301 73
    0x80100740d00f07403841e4021060525846410766070107440c0801c40c1e40a00300344a140794541007100700d6101141c8003203480b0300c0e024071000c0e072043c2001c148012140c44c1ca480e4040c5455071414103090b07100584181c001640011800d1001d540c142421400c40074290074045845078006012543d15080028815038541d5a004a802d4942d0001d003c0c00c908480003008021008000145c445c2c0c50040440240c1056aa1040046807100075402100a16001810030072450758404250b60802490f008a40020b8100c141d8902d070a40602e045505540d0000d000118403040c0c0e01c4100c504c1000c051041e90309640380c105046c0411512801140501c2d010b030307101d1508208160034007640f020704001c0d48512502d4181e20380030380760703012098070340140e4120f030b030b9240989803418452804004038a2040d80300710b061090101190300140b00b11140c181140750713104050400d030f05c00d80d031042003240c006d03007004801c20178105107801840007040000c1005040d036030162000c24005415400981020201c1604564400 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 783279631 1250 783278381 783278389
    0x31b17120603010c090605130f0e0613140103030825020705011701030209010605090a0305060f0412020a0209061018151b170f0906071b05030304030b150f0d0c05 71
    0x56001c10141c00034801001e10302801004440340b80310f6001040300c003051112250003542500d400030071140c48604041a03c4a49d1980c906c0000e41d051071080c410703500f220740e5108490081000c111907005a800303550b0f00c0c40c1c6081d5000540104000c00000b4080e0400c0c280c01c10824801c2c41030841a0b000b00030f40350500d03001600a0210740701506e403042003040101300590711800514190340b81803a100b0303100e00503400410150450754200070224003c841c10030801c006084030180c031071802024814609846c00c0c1c41a42c40350450607003e074101d4008000205141001c40c00341e20348000341e16000001c061101c000c030410312620f411040c07010303800d0828954810340c0203582034800184e41803039591401d905e941c0c0046a90424000074070140e0080b814902c2e15440701305640d8044805001c40d6622000352904403641b004049c0e903452050105032021130142000000d480035a07501c018000c02c1e0307864050720000c0034500c80751003c2e03101c0c0d21485038621a40b204c0c11401c403d41d00c1105801e05981c00c0000b00 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 783280881 1250 783279631 783279667
    0xf061e04080a0f110129220b040b030316111c020f0f030f03040305071e0303030b060d02072402040b12060307030f0302060912031009020d09021e0f120703031b17 71
    0x8984103500c8505040d15040031f044180d03a0201c20320304002400242d2802140c06820041c0d116541404041030250031502540c070014204c80c41580903035019101401088400035684021042460b400b204200041c10040100c412240004000904403401000020328141d038084418201d508041000c0080103c1000710700050048201c41a6141c01d4070080c01d60000010720014007055151010040383c1d0f15520304550348841c1c00803007550303502420b0a10944850f5070180e1110590317405c80030407203182003501c251b40581d80c04070103107880d10b8400c91020517140030107440564180641e4400100189a9004402c2c0d094440d401a200e1442c05000c118280801c141114000b441c0400c10806410200d9400b4000e440d034840005031582082d0106130014604030b079000f9000020b0401e89103141601c1b501000080d0001c840c805a50b4190f001400000c801068200310030340d1000d0f4051000034060380740c14038040002a0740020305ca0741529681200342449140303003c5440000b8010b0340442c014102 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 783282131 1250 783280881 783280961
    0x70903031205040b0606031812071a06150702040209030d0f1106220819090906050a35100204171c0f020f0f061e04080a0f1101 56
    0x8100b000b8074142e01c9030074800400a01c040d110b810000006044440d1201401d0300c1001100102d4000e40c0206280558503400311b4001d4488211800c080c03101c03020000c243c540300700800380c44c2074103003002c00381c5041d5150402e02040381c0c007903000c4c40b104060381c9080105e0345549a043c3d40e09440c0329000d28003c1c0511008101e0039546400c01c5c000c00c504843d0b09802100e00440d840c02036014544181030411003405a54000c1282c1840030340384001c0300d9803050341a015240d50200070800300340d9030300030003580d800240728051108840e10002c0200c2416480b13030000d400800c588c1070b0401e440e1032410504001882000551143e40440c2c04d01c1001060282001480184001409070200940d10400720154003501c2000f0000043d1102000354400c3c0031441003503001c0800c45941140c810800c41d21800203ca010380038003051050074041c01d441002d494013998001084610346100d40130300319900c02500c00c7c101d00b8005194514805a03200b4070400082c030340130400b00c001c040100e44480c800c40c81d502c10 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 783283381 1250 783282131 783282167
    0x909040b060a170c0f010c0b130c060315050d050106180203010e010f06050d0b011e02060906070804080715060509010305030c0d080709051c0c03051c0207032d02060307090303 77
    0x54601c3d00c039903000502e0340034030b08103da44a600130910b00c0100c4500782c030311500400141c1c00c0024044d1507290810f1107000c07a031244039551420381d190070b4100d00712408900c0c01d80c90031700e210b1410001420501492140203010300000b040146c0c64118500c582d40c5003150903c412940003004001400e448080d140c094640d0f1400905490301d00840109280500d001c0b140381c0b1546d5403540f48081c0c0c010b03e82012403d64080c0010941074444d00040d444200c115020070080c09220700140586d44158101d51181d42c0c8841c0c590704240c41500c4000c04502003201002005566100c04103540e0360700c541b414000d41c4500011036075070b601c00c400c8504203110a4101414007c540050103a1241c03c06080010740b4016a14076041c643c4c0c1c5c482c403a541c020103140203402036034038041c08000d00c2800301c2e400c207403600c42008001003420002e0080b41c0e5a042440054200d000007504516111003281c01000c4a141c134030305040103406182c0004149900c1a00c0420104210840810030150000c02c0c841c031002a00c2 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 783284631 1250 783283381 783283409
    0xc0d031209051c03060504020a0f05161e020118030c18180c0302013b0d0614090f06011a030a0b13050603010c05040b03010603090203150f07121506050c01020909040b060a 75
    0x12024221949800c1d89406006020680d0021041501043e03130b0056080358001050537031043d080c440c40c1000c410b007640000c00318070602c0881e4107003c408808403030b4000000f10344545400c001140b48170340d072140001d482b5182d01c0c540130f035400f0711b081c40f2407207078014114940101d245200141c40708443c840707400d482891019030800100300b01da4030800c01d164051458008906079000040340301184100082c43d46140c03d41e4130b00150300c81018944640c050008480c11000b0510010f90b61304400d104000c080c05408011040c0d003e80c0070b01840d04050410f402050040700900003e88400c40913030542c1c7c4080c0c0d604100511850700740540703148054039040c00c0e032600e030030030300541c03020f100500620060544030307031400c41151410480c3c0c145104801021030b6030740c00c1c800140c40c0708032411f858400c001070b030b00c0101e444c100880340b00303401884a40c6042d03a61100e140c40400e0f03840d50401c0e60f446403607541c02d01a00c40f2a4442c5048280320340d103c0c1520341801d280800c204807011043d50020030140380c0c16 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 783285881 1250 783284631 783284647
    0x190309081f0e0c0f060a02010905011104050a050d05030d0207020f130c0305060103020708192708100507171009090302011b0912030e042c0105090c0d031209051c0306050402 76
    0x2241c4c07420700e0703444c05660250b07483d00b41c080c040c1c0c05800c2c00c070002401e070343c60021883c002040c0d2402403c283d1b50101ca40001c0d0941e00c1d410004140d16070400034006d030300b007003140700400317190b550040003c00e2010309041000781c1c05c0300000e800c103a0020400210141c4620781520303115814071455a110300309090850034001c10340c644070001e01a41d400c008040400c2603c41c0c4000c0e0192200c00f0b04804000040d910300f00040f00c107a101044c1901c1a00e6151080c5044800b0780031041c05424426015a601d80712003082006840300100000307058103404a94001d40800d60700c0c40b5018185000e806500041011280105e10200400c0401130a03420000520800d01c9502c032032441345d200c2c4940500e884400c0201d048005001085007805038201c1566007042109001146038440020200c09402040141d656404d125110324041007556442400900940b00080c080e40f001c00703812489200028441705696206860310400c00d0281990900c00f1103400411136060080e000a41815a0258103080c22 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 783287131 1250 783285881 783285889
    0x3030703050f091015050607050f07060f08390903070f0506040e1b0d06180e0705130b10110609030a05040e090c0409110111070305190309081f0e0c 65
    0x620509801070503280c50000350320401c40384000c4054040180746648c0c4003102e190032699689580162085030007200b5002440742c1c001c1450444524494071017454655481c4030903410600c0043d40b00c412744140c0c03140d081564102c1c00d0b000100303001e06030400d982c0d941c814041519000940c0d21100076480740c480b00b40316544900080e2800c9032540184810140c03240340400741a20020001e26440600c04540c00d0343e444040c0c0c000008541700e988030721541e11104103144083d80c02132005480300350702540c000c20180c1009182c0300201081c030040054110b003c40002011915401e04820018071010107102c00898184800d940014610000714502105c503200a46036004030712a20300c1c000301c1900000c0c091301c01480200640c840061041003003000d24508031205841032042c0d20b0005071003407903d042581c0000b0b014019290000004d21800c003031110144044d5980707180032410880c90342d00010b0120405c00654a004002c2e1124044e9495140103400c11601c0586021103103a01c000d88441d42c54031 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 783288381 1250 783287131 783287143
    0x4270609020a1e1802030403021203060604090218090906040c050d080405030a0b1602030702011d21030405011404050d02120f030c0303090c1008010905130f0503030703050f09 77
    0x150101011480000c14000110b02000c258451002c1120300000780511800441d49542518000580701c130701c40c82e0b00001d160480c0000c0760024056032100103c0c2c0b4450801c480034540c44000101450303d071540b60b002010990700070411000d40300c3c0e019109400746240002620b64040181c1c80213100038545a1a0840c1800c21407040c5d0f8000c2d40e0707c42600c01844201c0c0308aa015003400380c100c0e01d04c0b10301e03441d119420200454560000040c2120080f0b0304510200460300c4182d0160340741d142c0c200c0038101e030440c40c030b854928071640a43c1035091200c100720f01142c0340e020703008003502964440380741000241142e190307982046007280c0100014002030b92890700020304281c0607200c0151055401c4070b2030345060780c0c2d60043d100d58070000c10249050305000008610400c802c4c5c040d260089402024018040c00d203101d040c0124540d9001801400d20651015501140a06003100d00005c0d80c1c80710400c504440724196030903000001000003c503014000c860304401c1010540d81589844146191592 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 783289631 1250 783288381 783288383
    0x1201120206160c0302040c08070201112d0d14040507091e1805061302150c1f0209100503150904020f010311070b070c120e130f090f110427 61
    0x807205035125400d100103e8002405194042d0040100495500001c0d00c110006c40da008019030801c20341c03d06180c042030694210f440200d0444071070b03081400310034000c1d440900607041c00100a1040c20748203c0c0c28000c4d800c0207101004100054101424001c2c00d00c2499000125018100b1804548407290780750100a004000717003002480a4a0460021187d9410200134001d84605e00c03d010080f82c025652040b854401c86044170900b41841c840031750f5005110041031680c004c641003141c90200702d0031030b5031501d20451005141414101c0055001075a140d614000908044100030745890a040c2c45595800300720381d05001490b00354000380610203041e414a041648a040f00c0c0d20b0044407000347c65403154052110a05890601c0b07004209036500c0500780c0300610700907602c3d03099a000c0d0015500c2017001800b00882c1e5101c1d100c9040c0070786800342000c40e21603500c220450108203148020300c45076106289116082040d6800c21040e0380c5000c401c80140c0d880741c150284010000f12420407e1 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 783290881 1250 783289631 783289657
    0x708070b0d020a020a0209010b031515030105010309210815120a060b040e01050a0b0306060901120b0415051f1403150408120703050702100509030327030c031201120206 74
    0x2503d8089401c9040c10081c0000a40000d440c1d0700126542c1d0844015600c55904001c8404544c3c80141c00c001c04c481c091101d2000d007030010001446194883c2c1c220f51031003401411030610f1603204484244140e0050302c60040042c1030b00c0b00380000410350140028940104880107410b02d02d1001c41c0380d8448072403100c020301159071040145481d8869130006c24584812800804c0b02e881c010040501502d96030491500c81d000741800180249880f01c00281a100e4007070b416040450642d8602c2d03420b28001d0420384600d41d020322500c0420707002c0d00030703e44244505250a0345003079110300f82262a0050b81c00c000805403a2162840103a1000103034201001100078240c01395884a0404003458440c42240d041c0c0440407404100070a0707010b402c1240107000741e50880348880541070780e0804840054600550580007003002c20211040c05039a0180d520809080c41030314505030440314a1035000c2d1824200c690400f103811600c1d0106810114014046014180701c016802e50004a541c0710707039a00380700c3c9 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 783292131 1250 783290881 783290887
    0x9180e01110408030405090f13030c02010507121709011e020f0d0c05030121020f040b0f090114010801080f071a0d0903112119031509020a020708070b0d02 68
    0x548109402a4800c140007001c03865032191590f81c0f41c0c0e1070b03a003d030140601a0801e440826015548411680d103d906001d0042c4021816681c085542c00e4100f0301c10307410064180030305004204804000340158420340c8641c151010000626045800c00620283c0d01d40d24054524100410302c1d00ca10301003000c0c0b00001681d0380711004c044503050089500389901e00349418180c03500c45420200070b60603502c40d0020724920400a0040204003023810304029040160b4a4402900d82050340004c00030b401c000304014a04a0004046640a50f09a003c0c0e6001c996108091200b0b580046090703001d8880d60001d0b00f642d14123075400d0b03555184144560030044003011031f41c64903400c8920030b4415440d004402404072840c20300380101541807404048070140200c0300c0e44941c42104041d032806c4001b1402041d802c100c0702d0405250509031000003682455100c20380007040c0403c1340000006030240c00d60041e210700d2030200003468190550007410701a8000c00c018000a0501400d07918612a5048050380d = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 783293381 1250 783292131 783292151
    0x71409010e030f010609140a020403080906030a09151d01090b060907020a060203010f230d021207030b0f07230306040c09210b1f030209060303071704030c060918 71
    0x11604074420f002103141c1d440d0842c0860080308507000304141300413103501d00401e502c41c445800102e1003248001810401e04014031100f50410401840d8000d4030850001401421f07620b03096030045500d050341c0702c0c869568954900305454840c0e0309900906036402048a01f00c10381d1f80c042c801c10080c00092142542c0310018090720f101304041101d065000314150b442e540d55034903003a04072800b402a0301160031200380b403e0301e404524008034141c000c02021600080b166809010110000f1002d9100d0b80c0541d80001c030108829142c254012424012030401615000300c0040c4183c4092120410b402440940c2c00d4070484031105494110500715800140100083c01c141c51400c603d41c0803c43c0c0746d10503003a0030307191107440000461290065000c540341c1e80d54881404842c4501d2004030150180303160050001d420708060140d03016101400b00c0749020f1081d1103c02d0300061010540c00802c800103000c4c820403480c0200800100344c02d0411a41c01030a251241c2e00c008a19203100401030b40e2035030021 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 783294631 1250 783293381 783293383
    0x91e0504061b020a1703150108060609120a111002071809020d11150901051b033601021b0402090d0206030106120510210303060b04090c0206071409010e03 68
    0x9100e56071404240c2c144140c41c006900c42100b0300c0c040d50841d0b02d182d000e0201c28250f1046038403c4040b14010700440140c81300542d114880540b54580094052001e0305950b200d80c0603a6098503443d4000f40745190f440d2600c55610f0030350341c07011401440c01150600309a40c000502100303460384069011300850400c04100010709040401030b40c0a4512042c0c1d1003071040505040304049826913070807014604540680149200e810300c41400208100180c1503071032084407080c2c00516200c01582d1030111000701440c80c0c0e0700100140b02522110407450b42d005101050180c2d403159083c0040c3c10b1100780070b030241010484d0048054000c40d000034a0030300030b43c1c0b642e400c040215801007207544c0700e58480030010b100003a0b61505040152410000c610320741004c0003818112070107815442e11003111845410708801501030110107044d25000d000c900c2420160103007000d080805000604841245402490a04054080c1040c458202c80504941590308121108486e00b8200340300081c0094000c2 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 783295881 1250 783294631 783294641
    0x9021f030e01020d0b03010506010c021e060f0c03090a0807080307030e03030c15070306060c0f02040c1b06020717160b15090a0903030e0d09150318050c0a091e050406 73
    0x200210b940300042651441030294041e4444000590003003042d41d41c0c0c40c0c019a441844104041d40c003e500584e00084040c0818203e2020b440141416003060700880240106801120007851a5000480e088016003070040c00c50380181003001c01030842e285001c817095143e200302100a010072420301200b0515440400803236400320045401c56000390074100c5515020b81702034a0a00000303040c81c1c0c00007104c52080815000003508940c1e8135481000d00c1d803c0000030030250021000380000742041d00804e01042440311450f40c000c0d0409640e80b10585040a2640003000c2c00540080c0140b101102981c00700850302c01c940d5101d80f40c90303000d4407001c503480044500100850f80c03001c200740800241d41542d8100c0c0c03160a200e51400c0c8040c130400d92015856259640c9d100c00019080d081c20003c240c41c20a000780881998140000ca0450822403500c4020229405840f0b60b8021100d0307500341e0902145042c001d00a00b0700c10071200701083c2c0030801110703215a42c80606500c480c0481d040c420350f5805 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 783297131 1250 783295881 783295901
    0x1205060f101514030703050604150b0316031d10110a051606020d0911030115050117041a0f090c01140702090a14011d070201090b010314070503010e0f1009021f03 71
    0x10b4480c903005000030082d060841e523150090342001e01c075544e80713a0a81200c109964440003010300703654400410030b45800760720802508058650840034a80d0140607a11005418840054a8072030b18040c0f00005490741007003400100d0504115205031075a100c0700352801c24003075103d035801c013007c3c41c00d00601078020300d4501c0c0801807a000c0c90404020380d80450100b9101f0a800034405501c02490003444800c49206045c046040200180c0303102c0166030800e0b070300c00d109505000320407244180100c20503070704030b8007403880400070780502c00401410416070010040034a000c5610008134819000700e8000c1c54002800340e001314010a10008250b0441c10300e12034191a42012581d581e08483c050440c40c2c0d010000785514840802d100034810700600d07036036a80041110360140d00e5a81da0000c407a9024800d00e2003030040c0c40002c12190340a000d001081080c40c401440500d910391070281c24401c241001c055214902704027040140c95400d4030650415000c61298041440c03020182c0281c409540 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 783298381 1250 783297131 783297167
    0x50c180c07151a0301140402060a0c1e2a0311010f021c030207022803020d05031c05060a24030e190c1d040b01050f1201061205060f1015 60
    0x280f80150881c0c04a60703114103400c2200240304084046180f00b41e2010f0503580690442020004070b074003c1d018030403801809214101c20b00503110300611325900319150704000c44c1d502071044804895000c12840030200c04002d24402d00c621851340d134401d0300c0f0016803d4128140075150750007445540c024096443c00403905290b8468840341d44000034025030151408074802d9005440d03468802120f402d41d000d13880ca00c0c0303d03060170a0f4295001c11580c0040400201c03410300c0100540e8904103904950424910060680420b0b641031010030800c0c580e12a400120b0800440c680d054410401007544400d820698200002c00c41d10002805082c940d8160303c002407005404403010420446580007004c45240b01909400484517042440101718140c1d8080c0c000904400140654901103e20b1444060005d280c0010f041c00e600c101c030700303440c5a588950712181140310f0392001e112043c4540795000b4801180100c0c2468841011040c810180c09078070a2a803841c041c450480f4080c01e40750700c0108981ca = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 783299631 1250 783298381 783298391
    0x1020304030b0c131d0106031a031f0c0e03100b0f09090a030f0905010203180303130815060312041208070b0a05180102041a0d0209040207080304050c180c0715 70
    0x90340c0442d040e03001108000e120551301c1e400080070211060703801c046040003c0d002d203043e4a4008114007030704501e045100401c0030246ca40329180e4040003a40b0001114000b910660040c203000c01044465450702d0303005010050b080d422050f5008103d00c0301000400600250b090445d2001c2000301844021240c0c02800202c14411403050009124604500c43e0307a07100f08806418108541c80302c00340c8075203030240c1d07c03c0c4018400001c42c21549445880041c0c102c17800e100a01030180b0020102da803040c003040d00090a00381c4400142c41d115076101109a000b45a807080075618940580303c0e81c425010270f01c0d81c1c0c007803c0303080260000c2102c14064100b0b803038141904060407804c00a100544840b0b010000055000300b07180301c10700940d000c655254202d079040000302c840100311503100904515255038200840040ca50351032010f0f0a180b4019460300d43c586c0391030310b0454030b0a001740314090f101b41504034401101911309610207034801c543c020819191b040707602e02120480c00c1105c002c0c00b428104 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 783300881 1250 783299631 783299641
    0x90c091009020a0c050c0f06030103080a020f0601060513091a060304060902041b02060723091f09050a0905040512181f0906031b050c0a0803010308030114191401020304030b 76
    0x341c0442e030307180c0180160740c00410108200511007c00010032a00300009200400100c0c10307145c080c003903065044c019600c89000c8921018104907098010801084010030030011a51040846034040c1031411000c008880c5507001c0c084202400c2401d107442214000700040402940d44c05c0560b10750350207401030252500c0c1d846407440750800340380f01350b0043c4250780000341c090340f00b101d5101400d580048000b444d41d10030549008190b00805100c3d400000c03801054807031603468900c0a0384004130382e840c200c00600782030410041c4015644041c0c0c1c001c0c101003d0001082002c200724410701c4003000f1080d40d6090720441161000528011140c0c4001c0b0034030694820880707092038110314111641c80d9004c09031101800e80484002c0c52452051035400e001c10300c0058000c10050010311b00c204202e070100303c543d9031550b400703034001d03001252030b128040010881c6004903555251a0b040858070001030a403000501c14862115108101100401c50310181c0b0320b074001d100f00ca000d1500100766010a20700 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 783302131 1250 783300881 783300887
    0x50d26030402040c0e0f13090212030c121903050a0f0e070303031b0215100f062102040e0402190f03080315032a130501090c1106090c091009020a 64
    0x4507400c0e8080d03070500b05040c02d41071060282c201e140314010244004503260909005980c403070409141d203510390352690700740583d540c0d801c420140801500115501d418100360300c0e0614007084001600c0c0384d4203101310034150f506598014405501807400042c07941d2200071036000340110300712604601e441e0004000081030b010071000b080d28000c1d2800e00030402401444004041c500075800016000304216140c6020040d03e030f41d40001a5034410003103191038040c000341c1524070382e104002103400007901140804ca040401c154100c1007100450070316291070712001890800400c000c2c840c0c00701c4180b0b024040b800c80620405010341e0148040441d417079141c112103552090303400307400b0180e5450340250710349800030b030340c5203550740700400079001e0103408214002c009900d4034242ea0110380e0090310800d81c40c07075120b118002c06400340d01141e90b480101028100c8030103c00c2d81c0800d81c000c4010000c62010009411036036500c152901407895036000d0881c00380314140d82000c00694000980040142e40c = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 783303381 1250 783302131 783302137
    0xf07180f08031803030f0f13090509030a090b072003011e060905150f01110f01090f120206070503070c06060308120f01210305210705040f1e050d26 65
    0x21990804081200240003010f82d00e028044041b0151101044407070400c10211000d481d0244007180d91800c1c00b5241d048190640e4030403648204294008101c40c40b026a200c1003e100030305410002620b40a11071f16909044002c410804061004003c2800c0a5450950284c4440195440c040340d84c800c108180c0400740455110b002800c504184c04106245590342855805000041c4010307000010300005540311010b407008070842c2d000300c0e40d4614176460203000301d042861040c10000c50000c0c0c6850f02c2070500403013511000855114100308010f4582090440b60403484505000f42d40242a25203c0068015900010aa044040359002c0f41151080003907006584040d0428120b80c3c0701c041c0d03c5414100581000b00a81680f031a03540828082c40c001d0001182c42c200d043c1c0c00c02c5a60b1010030161106580d10400244c0000c0c0070065520060801c1000e0070107460325024410020303050b9480b1421a00419208800d068692170030081e03060070551a40c280c6204490040c0390080120340207130 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 783304631 1250 783303381 783303397
    0x30a052d03070e030c061204020a03060e01050103020a0b090307140a0906152c0f1c051c020d080627150f090f070311090301020f0c070503060f07180f0803 68
    0x507803c030210b030310309183c081aa41e60307108001c0e00513800e02e1b6110006030b00580000d0300581c0c01503042c180200204020780140701c1484c0c440350000c100d0354035501c1440390307005040d4060000072106102003406503a01091103411103020440c3c09030110080380c001500004681c1c052404286041800070f400d0f1510307403c4844c615030584030f6262110384142d100c9002c1c0c500e00c60f020080fa15084c0c1502d038915188004801d031f0703000600000601d100c010000801603050f01000d84489e485109090100f03101407a112024030b400e48003400750300008039400390180c28082c220318803801d5030180d1050302e0030345c1c2083d00c0151100411000796504000408040040242c22818041c8004030f00d0440c182c14503c50003030150f054404030488640e0b40c403004400030040c034600c0102001c3c1c100110036181d50240040c2c54584190881c0ca90303a16040c1c2d074100d1800e00c80764007090280c0c00140030090740034007081203980d01030b12604040d20000407080c0c1c8d112440c400e80c1c1210041d1201100041000100000504810 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 783305881 1250 783304631 783304637
    0xc02030105060a03080d021c140a0605010e0f0108061507030f26070c0201020703051b090105030613030f0207050a03290f061909020301033002030a052d0307 69
    0x40d2030b05024805440014040075201c1c1404210200801d0f041d0f5005024100e4076031003900a01c8032001085064924200080101600042c00c4c0301e02d2203142d00c1140e000300402d08080e003181c00342c0d0000c01c5500e0b800da03001c41c1c18421007200141c80c5443c1d105460f202c00807410259555034509140107003e4441d400d03611070005029a680303080303d0106419614484a5a46070794009a858a2040b2800030312604220b046000384000040010710422100f1408804400c00f140c61002d03042c180002c2c030300140d01041c0b0942c0a901403100d001c040c04401c040882e0140b60400587c40c0d0414181d03c0c04003d5400749803c00c514140001c10300a446002d42c007051002144954603105618ec4000c0c4a03130305075a85e00344440300c10003080c0d6510b00040304c0745c9440700850705c0540107a901e40700c000498009a200f6200509050005440101c1501c01c80c00d43c4220024001c24240c074001009580340100003c1e18180007001039250080c451030398800c0000c8100b4541c0250340c0c5180003e41d07003650410380b80c0c5804 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 783307131 1250 783305881 783305891
    0x120204030206130617040302280c080c130614040b01230d0c02030307171320240904050411060a0c0c090c120c0513031a060402070b040b04060b030a030c020301 70
    0x10044d01035121386d020301d405500400303800c0280365043c134050274040d00d824400310489052000041c0036282d00c030000c1c1512000b409101004800340000c200ba184403030b60202d49000828418071100e0300c010000c0724015900001d014410600580e034a081c4005104040080d0540111040c11100300403e82024048030502055030080000d0340d07680000c2d21010081550912086c0c0d8240c1002e2005503c140f200a8040c0000d025458031030034103114204001443e401071000c6003c500b0401e034503031400070000c0d804a55400004804403464021406954410740c1c60700046000d014a02c4101442c48800401f4103584054080c40038182c01303810a011079968840320000220800d644c41446580d910549a00c40c1c0c0c3c4040301c0080004254981c04c220034030500340880040d4481d42c91131000954410700419901800d1190702c9034000b500204200e11541c010808140064044a0b0f01500709901040e0042e140e200c40c98594064000c180309590103100303101150061551110030310060754000d40007049 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 783308381 1250 783307131 783307157
    0x7050c030115080a020111100207051b030f071e0f0803120a0c0914031c081806060d11031c0e0a0803030411060a090b07030c03020f0c0a061202040302061306 69
    0x40708800b5114095868000682e64009940a80b02c040220340c640000c1d104102c07101e00030f031004ca070400030080c0c403d43d114001700300f20100900c0d80c48080100480003440c001c03001d480003e17560383c000e002d0325214012030040016084000b43c580c00c09011400404280d06898099030750b030300e820080d10215040d48403c041000c5e550240b0031040e01d03061540d01d02c89201e082c50301c00484451203d0260350503216411108444140580c0901c03a00d540a54480441d41440c003219800360440340e00700300503504a00107000440d529900300d65001d40d888203001d6003041490002908180001e20081407403042e45a40794083d0343e001c2c140ca030710003808603680c06070652682600d0fa07a9000495009001d101c00d81082040d52804402400b1031603180c0c81e1a8070b0081c0c030340b04c05400d1508694001c4010660001c04a01015014070144c030801807000d009205100405002414150042c80b131041880180014115840610b4048501540d0090102a0341d280d4a450a98010480e4410840040c86600c8094 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 783309631 1250 783308381 783308411
    0xa060f030b0d050c012a03050c060c03090a0b060105120114042d05061207030302010b13051302210109050a060b0306150f0a0e0f06031b06220b07050c0301 68
    0x544010f40103001050400415801035813041c1c904050040080700e81006001c03201c40c01a111400c1e54030940d40d1640f1002010b5a00d490620043c1035403007540814020003031500c0300080e41c00111500705484c1d441988441d401642c41e4440c03030102c0380121180d0780010442580501c40009103107416102000360000700300303111916000b0000603008548021100b9190f402c0280c120581000c1300074034080e141152103c005250407100d80c000c8015035100c5080e40390b10301e0000030016040c610020148000c6c0b40c50090085c071070345d140c5c1c0001d01c50a09207a0346c900451402146511211140008000562441c200079950b002003400880e156402c1c940940034034200460494050381c0360554080c5260740d46070402200348056010a500140c0294000400c484c0d81c0010794000d14021080c08041c2c00d025041c18101400c0c0141d2480d170f1b11a03007040c1d2440c1c0e00d8420450310101d1510300d24070340060014034403841c64503556000f5410840003048020500401246410803124124020000c0c00758010b049 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 783310881 1250 783309631 783309649
    0x322b030e0303011701060f030b06090c090105090405040503040f0e0f09010209010503150f0a170c120a150e0303040803010e0609130602030a110c010e012403140c0a060f030b 76
    0x110352500148010414000c039962020403a80103040045001d50729400c10302c642d0100d6a00a0715403a895800340601803c28850050300b00300c2c1008050302c3d040c0d110002800714840da80007280100c1e60b450004041c000180f060b100601121141030380710350764800c1161042c0500f41c400007040101c56000c00c0c540300d0144200c90b010001a1030321400d56032055886042c1701e01c2c2d0320ba620340048150001410381e54840100c02c0c054034180784c2007051030f02d40316140c0380f0706441e98540714091916a501810112400aa90394080d03500001c45100b508295004001a0040c52001c401c144404418413003040350000203141a900f250000c80d40d90f54030700040151000302036132546011041b07091a0780108040d500215480b80f48001d020901122651114129900910310880540d40d922001c892410080c06625510300540d60b4070003010510780002503505005200041001e5841201000c0b4003c09001d03c0e280d15400400000e0f5503660b0b118003822540707500d4010340009251140e11044d518001d00300d = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 783312131 1250 783310881 783310901
    0xb0106050706051501170903041a03071e09090213081c020d0807140c03220f090b090606071406090c011e02070e070309020607050a0c0b030103322b03 66
    0x1c1c41c06d14000340014608940805460804940800c0001240c50441c1018602c0c0c000e04c1c2990b13031030341d0b880c00f840001c0510005580382c0c4c6070084038100e8460020342c400c034091700b512040ea1005944100616072090211030310740c032401c83c41c044d002c03d0001d0300344680c020310400002ca40941d042c1d01003080e8212a403a804507000800f02c0d50090031a80e00c1c0528201408400301990b045900e01080c0852000d00c45540c100509165400d80d481404a04000c201d000d00410f120b00003400306850396400511042001860940501c4022414030180240164072030200d8261109640e09410501502e94503912806881c6000c0346d240c48810b0a824202d541e4089000d840e9405080d41e9410180140040e03400900224209525902e240c0050b80c0c1300380040005c40c1c41100103112030040c5182c948104921a8401101c94400b0300040021418813030220311081545540c401d120020001003000901400c81c10b000103100e10300681011045106c20320340c4034409a68190842444540100c0545854002d = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 783313381 1250 783312131 783312137
    0x702040b09010b0703050901030605030a0c03051209032a0a03060b0f0a05220b0303040b030a06050303030714070240021c0b0a030f21050f04140109030b0106050706051501 75
    0x120001c241b082000c0c29041405140201c0c0c0d003035035080001d1034204a054180c812b00c0580d0400c00421108004040c8048000c0404904040101000a8484070110b81d035602800780442503505501343d0030400b0000c4a401405e80d0041912400d002c0010700c150301e03076140218405401d80c8510301d050b028082c00c9a00041038000d0701c240680d82110100e204981d9402840e44443c45007695035418406040038248039110242c692500080702010f070348440c3d100600980040090100d2507a02c442d04140810440311102d50780c1c001c504c0425032010700c12001160398010ba4112149002e03c5900d1811031400310320040c1816181c80f1030302000c07442342c0e0302800400c203880c0710088518800e075080382d80e00120043c039400c801d650781e071107110b240507080314220b910742c0c40c456412100c0000c0f8543d41380d0000c264503015040a102d0355511000d88907500850308248030010070786075941e12401381107001d103034050300b41c120310b503274510703024140d900258030032a0640c1c1050000758005030f1081a000304100165 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 783314631 1250 783313381 783313387
    0x8160617191103090a1e0203071a1201121a220609060216020a060203070b07140c0706021b0d0c0905190c09050a05041e0e0312040501020702040b09010b 67
    0x106451158007024201900341502d4038819188461a2005184259030b868040c069080c09454400212062000322403140c005412610000d600d0004401042c0c4a01c41d02825140d6203e007250394a90042c4007410306c40801c1900040b442c15400f20340307080918072505c142c1d160702c640403600800160080300c4c241042c601055401c5070f00402c3d0a100307076445009010010b541c040c0e6490321030580e4031905603a481992200709100440c00c00708191801040c45101850074400729580c0d030704643c2401380034501000162004a80b82c0c9803450101c907440d100360303401c40c0e50180d565070f4083d407640f80c00084401c500900580c41c1a1509000070f04504c580e9000c2140b207021030508000700b00429010741400d02c140c034031944840382402d8522515107942500c0d01c84141d03440c906010001d00382d0194020078061424904150100580b0701d510722401e2a02c03000114150180c06c0341180346001d400c03c0081c540d42008280320a00c1019401072005034000d6a081c04440007203010b10403158420720401501104c20 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 783315881 1250 783314631 783314641
    0xd0905011e0c080a050702090109020711060a02122503031e0204030309180225020328060506060903010c17070c0213180204050a020d1505030c0f12060108160617 71
    0x155000703100344c03445030400c03500381105034004c1b03902c401c026007165260303543c0081d80e0f009001c1c001c04c4212240c00100e42442c0340500b035483c000d4551050340103084188001050074030f01307118001001d03000350340514614180e90701e142c2001006071405000380d04c840c954400300180c4400541c022282540c5d096143d0b00d034801d107014064001d080f1010300b900420740d420301469003820b2901c0c25100d455018211040001c00d1180100b40c00c1c03c0203003403e003d011500c41e0450f0300c110664400f029840d80c00010024030796807150003092042c4910000c488c2c3c95440e04a9280da4140c119140964525000701343c045a0760f121241511a08060480070354000180c00f400180700b0281c1d01b00700c842d90305e40d402c02c0b82e03504100d81c00b0a040e203000f0760301d03244040e030007103030502e1845298800d4010214481201d025000c0c58040401d403102d0101c0049401200e1010302c03a81c5903241c91000a0b085c5003c20f0403600b6a607901c1304240d4455207041e0701c3c209901c101d00c00c0014202c1c40394240c3d81c600360b45d68010250315196 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 783317131 1250 783315881 783315893
    0x2120921031504150608070905091603140a061d0405121e0a0e011205010b091002010e030307081f0e01090906090506070909150f0e04080c0d0905011e0c 67
    0x2005001e482d0850611440b003150f6152800b5003281180342100d140036450824501a150203002840702040108001d0304210700c1d5180c48049802500c1c1040800199046150442c060a00040342110b0340c101c02c0180050b18595900010464000b4912240c2800c80d4100e03400c5081000d0314058040e51006a04041101c410001058541c0c0101803001603030202c150311100c0c03a0480c18280006c6658890082c2865030020844d4800f004140da04000c69810300d01440d03917a00035154079030300500c1e0941240103450300035400150312a5602044030b489140c6281c00401c840380c21a0525400e035034a0b101000c184501e01384800075a0301d26200203c05030308005501c0001c003d000010350f141c2c0e448451010100d8030601040c0c2c001c120555824421170b041560b1001900d054110780f501100c1000000c0041040b518001010f6a07a070792000d02458503903040c00d035080e001c0e02d143c1200034000e49804585035500a1481c50441d40c0a88901541c0700d6000d00902d1100c450b801d94602042d03ca00400d070005803 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 783318381 1250 783317131 783317137
    0x90f0a020607021c1e120216091e020f03070e0907050301090c050f03090d08011403060a050604020909010b0304150504031b1b060302040f05060f0a11070905070302120921 75
    0x1161030012400b1512540700c03001d00814090040c00b01709081c8020b002801402c00041c11825040d00040082504151400381006d12a00c0750038146540d8090f041a21a00440c6928031080a41c9042d034407a056010b5400c0c2c1c1c0d0348250344000100344c100c0252881d81c1041e01d401c0e0b20407174160315510705503840c041c22900a810413521840400004119003840c440c1c0e4030001e140600c2501c0c0c020b2049010209000d40801010b0300102c83d04a91904507076601d640018640703130301c030070603802c040303941c0c0c450001190181c01810b81481c2e01140076000400c03030b40c09141c080c0d03100358001d011090103d41002d0007034085402c203880c06030026000c0400340300e511640900801c06907126082c0c07080c2254440506d48812802c1d600300c4400039400050400c91000745442c684003a1000315201854003810780082c10840c8a840c60074011300008454040c07092006014481c0100702540080c0f03d24604148001e00a6100b0b2000400b45040600031460115001440c01c0300400d034515035a014a440420010980e0 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 783319631 1250 783318381 783318409
    0x6120201170907091b02010627020c03041d0901050a020306100302310e0a06141005040e040c0509130c060309060906090809031002120703020c16030803090f0a02060702 74
    0x11003071440c0010381000511a11a0050301d40030035405c910240c84c00242504c031242c1c08001e040302c81e007102c001420f9010690510380c1107200801641d0701c01c00c400c040c6c21800345a0020601b450b1048184000b0204544124031800c4808020030036907a038440c2c000d04a00042d02c1540d0012204900311403040c2c0244e000305405031032542c0c826a00c008484549e000122400390841c10007881490400c500f401d04010f00c0c3e04003800c20000d02105051911101c506030b22190b2070340c8106c45d007031703d2103002c14016411600580070850350074021b8501030a0130600e1036003500c42d8901aa4030703e4005202c1e011111782001c41c5c0c9900201c11402c692615408030060f200e040c10984003240e84a800c1d40015409100b90714100d4810100d1035110001001010700b44040e501e07029000500400c000d0f851340d1042e0260503070211181c00c00603110415040400c2c90000020401407106c04080f0740803007448240c03405144103040c40340844025000900d51b031504c0350007001000390021000e00400c0c0040c03400100f948011 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 783320881 1250 783319631 783319633
    0x1225051608191104090312051f17061f0314070f05011b061a0d050106210b01120f0812090106060f090506031f091b0806030c010809190312061202011709 67
    0x520140c44141f04880301500c580b0f045001050f010b03107900b1050b0103100010009110728420032416645007a40b5404010700c0d1500c2c0c5601d65070014405075410403180702941d007000c01c1c410a101c03410b1600d9030355181030080074407580809500046942c4200c003240d82041d40e00e0010f0401121aa460001424606025034004410411501000d407544003105115602034400480d04e140303805007030040c02050320441522050580003840209032210390b4141160308242080e40b10882a0510282601400034001c002c01000101c00690900e015140d601464a01d0001c000c4030350740b02019143c10b03074003405c5540480d918000800c0103207880c030059540000500d070160100f8190245010380c2000a4010b0b0344100e59486003104034bc8010744e00300c1710905007030400c81a5803d1850000e9550a215240e144c1009880e500048002d5402d100044030b0001c41e1155458101e900c1c500034255200c0f0071202d400046c0b410000007a003421004414103156010307168080202e903543d01121590100600015103 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 783322131 1250 783320881 783320897
    0xc310f020c151b090319031e1d0613120206040f060206011701050415050727090f05011220220e12250516081911040903 53
    0x300711018010140190140c00314500340703141004940b25100008440d9414900090110159070303200060546a42e0940d208840c0d9141030500d802c44000c0d240b81256050007812215043c0c2007504011554925058003a004481b41c0e1481d0900000380078020b20b004a03078142e1501001060001c4c0d5081200381d00241c041450245c541c0320b00300003561254481c0d80107a000000400c04030146000900000c1c402c0c1c002400581840d45904400003041c08403903214540e54008130784441d001d030340f0360811400c141941143c00c0d200318a43d841c80013043c1c40307003150207030600040780d00020480c03003168140c55850140c0021ba074041d0b102e01c50360754009025011020a4a0790f012680c0d5210381411010144145080075a601c441c80220180e8410b012003032040c0d88000702c2005081c0350703502682c1007444514034641491140400202582101c1c40020b40b1500441542c803418039200c2204000340d44603a011602d0b000050040d8400715003010002404212015110f607145144c01c1d00a8800c40b4000e2030f1100d0 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 783323381 1250 783322131 783322147
    0x30e0d0218010f050319020604030602160219091103090a081c05340206010603050a0b041107060501120b06190e07020703020109080d12050402041d0c310f02 69
    0x450749030207820505648812400412a600d42040381140c0c04160804169501d00d5690226165001e5800010701540c4c0202e2940e80350180b91640c43e042d0317600105502c541c1060300d02281e0354421b150003034150132410003031401585071004044038040d08c80200103001c0105541c640c0303090f41d0000049018688451000d800f107800c220f000f0140510b981030213541c500e00901c01e40c2c108420b1003140100d00c043c000c103050340205401150080c115070f018140803403242e880175076800041455403041c50b4045e142c4038080c00051580d101a02d500d91103590b040141e6629450340e060020844600100660200c400183d020b0900c1c0025040c08080c1841289205ea21240c1e08194540211034020050707010017010010346d0381c800307440c0c00140091009411f918a42d80c50041180007100c913411142900c0b05e01003000c5407120350141034003100c44205503180e2188d0140d4103440f401d0341c00c40d06214801e0804121030320b0101c0b4414040c007a1049000c150074640508050000e800082c40440c10241c0c2406a21 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 783324631 1250 783323381 783323419
    0x300f0c04082a030d1d04050c0a030e070b0703050414040603050a030f02010227130c1202130803121006051204060f0e10020c0613050d08101a07031b030e0d02 69
    0x5030000c0300c9846035040440d41030024030409081c0c517210351059090800f4000386913402821226190001d180100d50400d040c0b070201d2620006600034000d0030710004202d803d15a001014005880705034100b8000004080100310603a03049002c05040d0350003c3d042400064003811030000b12422900000d428000d030740c41c03c00e140513543c03042d10304000e10000354018149083d00782a503207003081d001c0401002809a2005003003000c7c12041c040280d031700041d00c03204540c60b90030200041139a0400c8070fa846841c038400d10824003080c2c401e0803014200039030104086024505465107508641c0c080403580c0c0c0c0700d4641c0e50240088241c8808516502e0141c018000010b02c00c03040203221598026036200c28400116190141c028503410481803e0200c1000003407010580a1518283d4039003401c150b100c551110312a900190300882280700459186440203140c0d001070440d040c000d840c1e44130000746020410f00103105610000707001030400901400240b8105500740c082e140081c00006500c3c0c40302c0015 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 783325881 1250 783324631 783324643
    0x1203011509030b0c0d0c0309111002120406021609050919060f0f0b12160b070804170c12010903140a0306120f1b0e0408300f0c04082a03 60
    0x25a4607000580c0102d505090254101c4000031f45010842c42c5110707186c03c1394190122180758480d044035000703004214030802070140405141d106140d5199070b0303900c010307540300c000e50012203403844255000550504248100c0e48241d004001920701402c22028000781c800011404885d40c3e580d80180034450300681c41003400c107100d031440c00200100d800701008200140c203000c0d0780c51580074001500b107410039a40d0b9001180c4203110348548942c030618205d1207a0040d904030502030b10501c01d4bc0c2c10380302800500b00251207010b81e00000d5414004d44602e081c0c0c1d107200c8002e03001c00e0313110016032140c842450041a1040b45441c0026490349c0780d50001c8208508580255501c1641d9448881030180c140320f0142e2103900341c0e1031010803c0c81c01c100c09008040c000c1001e0916003020030030200d5003001700d1a80c10031340c0541c807050300d00c81d8a040e040312030354009480c010b00024140d000250030b4162002150192600c0e40c004001d04440780701035000c0c4240e0016841e002c44600d103140c0026071020414 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 783327131 1250 783325881 783325891
    0x109080a0c05040e030405030c0d230c0103050a0605010e010e0604121a0a14042d081207080613090503120115020c010314070f020a0b0109060e01081203011509030b 72
    0x1e00125841d06041005860740400c0943e8160020070081015680000e83c81d40c0b1004195010b0312242c2040c07e00941c86010348401c1c141d002c2c204442c250a07083c01260f0080080000d0300c040181e506d4061100701201e0503030042034082848189210055801503002c0c2c12440b0008105d24a01902d035522845042c130401001c072080480e2a5a80001d031218002156016a50310750420100001c400346410f410b0b8040c0c0094040100207144045c0b903d1081d940203644030303102e000c1c402c600607140b0b442c40307803540250b81030f004044000c0c010507080c52060b170440307004680003421001d000c1055820034004100d6407208a40a2200b0401403000402e0b40c2d1146008045180c0b0703d8041041c0d440b0082d041c11100344a003410180740032542041c907114403245540081840c40e010f0000061048207a02e01040c2c0eaa014041107604000003c412800f50800400d03170301d440c0d1200c0450b999440d005642c0701801c2d060090782c2c01c810720062020004440041200d030710645030011240f69642c4500d40960701c10fa40c = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 783328381 1250 783327131 783327143
    0x509030a1713091a130603081b0105070201050105010221090d030e0307080304320409061b05120103030f051908040308130f1103010f0f0507090e091b0109080a 70
    0x9965003428014203484008015040c01030214640c2c1c10060914006420304c8140b1901c2010103418000d04550f01c804c3c0030303640c070041c41c3c0d0f914244400030362242000c402d5071039810341c207100c001020345106000b41412a01d06800500f00300885062600d401075907912074a403844008e100419a0f9503558012030b28290282e2543c40f0f03580d88003000e01d414155140c1051403503034810403042005184016145110058a03078403d41d540c607621011804503942c055205510a061046443c2805110350103001541150905140704031105007098070103026a03200020405586801000468051000c046c03010081c0d140440c9050000d02484100040507c2d05074001a180002c1000b0543c00c0019103410540840307030071800355100d58443e10844580c940041058007030301c2000c0384070384003500800e40ca11a000014070808844440d0383c0010081200d9410000c0c020701d5000620f0708440c0b48190081d01c0803030140a21101c001c400d01e82012150500b6030410a02c0d881c0000c02c08400d108199901d0b00c660 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 783329631 1250 783328381 783328387
    0x15150f01050c28050f1f09081215030c01031802090a1508070e0a09050a030e040f0f05150f0a0306050606040909061a01020d0512042a0815160509030a17 67
    0x100b450b41c50100040d84011740742d440100e010391102d00101c4480c00d084181100803034800e0480c0b030042001d000310301d490f07010301c5000304c10310895018488034580148800e400b25224407904074011400d0303406105284140e40e00d00034103900941000d11203540c1c4645110400300341180b414403d15209039a603805818603810101080c0099551012042e4000b000c17035206002e108503503141c05844446401c402018001441840512511503820410100001c00d60401113050158100400390a007204c0c1a050420f160030741c441c0501d440c0008900844c00a09540030040c1144e0b2001d004000180c42e00c0c0d8000130074000000d00402c00e001c3d80d10200c1c82104042080f49000d00745035200d041c540441742c1550401d003c20354113640d000c011340f0088040b003605c0c1c940c1c40d1214242140b0201c1c2c000c121011030000150103103d00a60182580d080340d00b6001114510324280c0f005c442101c00c1074808020f45440d12000c210341d035204802600d11a079008003a15105030441d62401190a00a000396100032004 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 783330881 1250 783329631 783329633
    0x702030c150307020d09030309060807030608250e13170c010903030603110f090a0b0a03080c0d1202030c070609081612230901081e01060215150f01050c28 68
    0x62000810050160070861b501e1825070340c024080e40250301600c01007254120016030b090740b00340c000e10000c00e4001f040c0c0e447d5a000c5200300b41084140c0a1001c1c64900310080051050013142c20300e841882d1080b0558a0303164030703944214162040c000070101201c010300210388912000e00c101c5902c0e0384a40c0b4005031692071490500444c030402490a0322800d44008045007984840340c1c9180d02c4015008001280c80d10360300050400000d50700090100e00000c207850084980020709005105c60985132011200c1459000e03070164442100c0c20301e4008014041030740041d0560304002803081c0304281c0ba80c101030010f21002c68841480b0030a540c1641e41c008642c001540120031851928440060401d0030f0112440039540e80c03140c142c549041250785000155403807800d811410381c40c29285000b030a02c1d6940d040003595604000542c4882080c45404140680641e06ca904940d00b00900300c1c207240e0034440019900c43d007120700e1007007217401a4201c48100c2d83c030b6000489002105d100d086d55044102d = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 783332131 1250 783330881 783330883
    0x30904061a0d0c0203040e130b06010c050c0402090a080a060203150d05190204022107030e0c1f210b0102190f0210091e030b06010e0a1a040b040806160807050403080702030c15030702 80
    0x8ac01403418080700182d890b0114001103440307011a04c0030744015954409100c041003882c0c41d2548028001d0051400007020040d242c0c004600900281a40e017a60101c803404100100001d040c00820b107610484460412035021807004c0c108500082005052000d01512074038500c0032000300003c824070724410060781c0c2e5050322a03480c050114400502c6181c00e010b0100301200d804002e26600300c00e000301c002c60f503244a0301c5480c81c03d10a0740010708196006046410150030700802d187d0140c041d524101d14485041d0881c10506078000300c0440480c440d82c0c0038041e43c030850003080010000310480214031301c90700d400d84010035561080290384003032842c00c01062000000c0d050504110380c0030103603115591b810400130107888840b0b407a5584005120801c500078400c950001003c5a00442d00090031f080200c1d03001e00c2048416030b410100020b42c001204c1c022012500360300450410701060002c640200b0141c0a020700c007508031200d40b0011000609034100034040032446000000401408943c = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 783333381 1250 783332131 783332153
    0x50c040b1b1c050702060c01020744120a0e01020c0a0620090105030703091208010806070801081c020709091b090605060403150f0905030904061a0d0c0203040e13 71
    0x10180c20740803030044010b00144076104a05000c1d00c1510040703090a1710400030760494040d564080c080c484441c01061154248051864880c0c15481e58074110080703400d1992040f4400c087c117000d481e8900b80b40c16a001d8641d0501402c2e010b001a512101d00400300c030248020410847c101000b00440c010a18008041e1101201c070300a0400e0980c1035148108100019184011402d0070000d4aa640340c1804400a00d10000050840b0340b40308583c086c042d80002c03181741038411000544486540e03051055418107020310500d201544000352400c245900c1c44901040800617105131480341d550b52010704159881d4000030340e10282149074030000c9401a41d10180103294001c0c05002c05440c0c00001005400b9a01c009005086e0161140751001800d5000e81d00003a2400e604000511407410a240e50760801f01d65203000d03030300e84400842e9130b4441651010740700174810300140c903011817100b8050143c10000410b10541c401800b0208405c6082d4010358072070400da1f080c1603202000b501740030005003 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 783334631 1250 783333381 783333403
    0x1109041407120818010c0f0b0114030303040c030b1803031008010b03070f05010e0f1c03030510050a050d080c0d020a020406060801080606090414010c11010e0c0303030406050c040b1b 80
    0x8441014050004800d82c0646408420081d004004c00074000010384044580d054001c0c40b445060f6640c00030407111036295810390303401c4502c0880031400141415601d00c01510041c11000e070301002000041c15003100d03268400304120b1300c00c0445444403c038030300c0c58000b55140442c03104412400d00800000b481400c0300041d084004051640c6000183c81a030585809454100700084601c1032541d1507450500758081c5000e0b1000b40c0c00200c502c40301c090980f241e501180002e051a0201d0104140c481c8404190345c00202051485e40c584400c000001801110480760408140801c48201406001116034090560090000300f0903510401c4120344e40e94201c082449080001400b0340d03140020500d81c000c2e4143c0c0c08072640d40312414000242c10102540f030b60550b0030081440030743ca40c40041c0b00c50301c0c50760700000c2c04685449010070b91a400791010f4150181d0041c00000c01041d0755420198104008064240c6801c2d1a5074162500b50b12860411003810f035070b996190a001c40c200051081c003 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 783335881 1250 783334631 783334649
    0xf0c0c0306010e07081b040303050306090a0203090312060d0203010207050601030c0b0a0e040c020c0301061203200c0d2906010f030e060106050d020f16050d030c02060a02071109041407 81
    0xe43c141200e01d401504080c00620400c0700c50700002c0d14041da120045100e200401d002603403521340c2d0b890300804a0b4001c6440c1405034600f64049443c1400b00d009a0b4011510800034604000e6030405c40ba15000d0006c010301d074458441101d010268901b0302c0201a05c80c0108083d16003981182000504035041e58025800410200a4051060f900030000404800111004200c009610f03034100d00d080d0141c00344e2541365286c01da0010725000407007401c035401c43c130985401503441013440c6203008a42c9801d00300c582c0c03604a01d414039060324000064036810351140c014000120281c0528035a10111a507c1e0b10341120a0410301a80e90b8114810448441c81880c00380300f9403c42104003500c401040c030800050140103c0c5015002c82ca0b6015503104202072010035803500b41c03160800e504c4141d601d5080e14240143c00401109038030a00403050039148c00c1c0c00601c8651111041e030310096121001c00ea13401d24000d941024180d0b04c00d01c8090046000e00020450412000081400e202c001d41c403040309 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 783337131 1250 783335881 783335893
    0x2220506100e060909060607021008090c01020c180c070804030b15100f110109080f03061f020a0f020f120d0318170c1905030a020607030603030c020f060c030f0c0c03 73
    0xd681d80104070780d1101380070303211800d0341d0b1645404210340d4041c07640000d40c022030b030040c6504daa0340d10030901845024070130304556000215800582c0c83c0e140e503525080d000340315000050200101200e0854010448540c824581b582c2620f941c3c9558001c0e40044031404840e1050014076100403000b052081802c59443e90a44c0a150f0054200881c582500061024070b031030f4183d1407074007944070558440d0040220340e51822003c1030050749034001c807801445042c0c3c01030076651200046154500841e02d64000300f5145503582c50f40c1c810380d50f0b860b10803030380300c191540310300d28a880e03034107803004030543e80c1c0d004040407103034060040e0546030151542070704030106000c60b4011402c1e0001600c42a0001c001c101d5840f901c0007142428448003e08503a10b441c3d5008850042000000003004d90180076030a481044d240c0c0c2404405540c0700d0302c0003400080c01c0c2c0c02001c02526201c0c40b88403102700020007951814054041c042d0845e000952400c078650804074840680071010b10a110305400c1c03c80181c20 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 783338381 1250 783337131 783337157
    0x9090203060c1c0b030c190f06050c061812040b070204050c0a0c02040e0319022512230d0c02090a0603022b020d0606080f0a1e0222050610 61
    0x10b9905103e80c49407180d40710500706045450038003c00380c0600c0040d0288240305030422040003c56000d06c100700d5030044031000003034898400c1c0301745c1d2084500300d009030525446030706810290f517694006800150080d1040114450280700040c4000c0203c101c1454036119240100412100001c0102c400024100510310090f0f1f4004602100c0e85d03412034000074846403408100d8511300841d044450b40d103142104c240038007030300007d4040b00d140340e41008070700b58460420511318041e550f101d001c10701c00d08050300380c00040e020045425064108444001d82d846104401c81c0b03480c2e51300c1c04800128111003680c0056080801030f040e807000b650313001801b0040c03469010481452003500c0030960080c0c04881005a0601000110000f64004019070610b425a041c2500201994400c0009a2041c407500501d0381c603010400031200b075003210b840d42d281c132002203044a8103000010100c0c1c0c032080005d1909540c0c1060a007580780c1295000c000101c602c0e0140910950016070040c07013082c803040d905902 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 783339631 1250 783338381 783338407
    0x3111006051c08041a2206020c010c0303140c0910020a0b040201030203060604090501090b09251412090703060501050307030c0909030e090a0e010b010c150506030c030709090203060c 80
    0x2804160391056a030040c50031506000b007050080d03400c02c00000c0f40c5d40000d000070002d4040a0400394818040c1682c2c02071986010072002c1000b0b110300030150700110503140b425805100226a00c4c1c0c02400c1c04240142505040e4161a00407902002528004031710b4080f1f0b810702044141d0b0b442e580780001c002c0100a0386603600e50180041c00241059000400179481c0e8403004217980041480300d078213000550b10740300000086c0c112070010310300440d0300e40e001401c005c0906111401101e50390a031000b54610014084941c0c0343c810f000d540a841c2c040200084080400e82074a03c10310400f005858500c0c29440c0902c1610320681c00a4401e0740701c284148003240c8141958022501e14240c000ba602400f85803c1e00e18850411541e648100340000300110f000186e006048030140d02c4000b0043e1b0f5054100542d24650a12405419445c0c1a168036682c0302603a40183e40000c2c0081c22200d04140400c00a843c0c404550040c3c3c0b413a586980e0107500b1820104920b9401c040f40032081400c1c100d04503040 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 783340881 1250 783339631 783339649
    0x50711040203090c030d02010501030308131a0603011b0203030103021005042301120f091b060e061b0618010b01141602010c060e0c011103030915070e03030301030311100605 76
    0x420300c959030010100c1c51a00c0200090301038600064140c40d00307402121006402010248020b130041111003000411b0300c403003030607484a242c0d400420900c950f0003030390242d002c45200418481d05590790b0301925450091107104100c1c4c8001a5009598960451060025a80703000900d21f09024007400103011000d0b51200c0e50020203040b50001140ea8901c500407118a0000c04400d6025850001001f0883c140c9402c075080d00c5004007801d0b02d07488141d800040507041c071841001d00003404100c240350345180900040400a8000107001e09600707250307640505205080d071315214600a980440b8560803002c4c0940003400a007400c111985820b00c08106030140710b6225501d170b8200c00c0e0301843c0d04582c02992061b00080c0c002c0300c100201100e4014403981c54815101e01400728088008040145400200b100e104513400f00242c400664112210090b030600500280700b442100c24400400d514100b0185008601035980c91201d96014a501d60400f4071032500b18201508001c400d00c682d460740688 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 783342131 1250 783340881 783340913
    0x40f0b09011e0501051f1215090b031c050c150109140a09080409051e242202070203190b010f0602030c07030b06010509190f0506070c0522020705010c0f0507 69
    0x19459441036105012119010350043c03581c2c055140c00400110452594512070581327400c1d41c41081074480800c1055903801c8007040d8904801203c80e410ba103140c2c414805081080352070800c890042c0044808021030f00d509030400011581d0b00e4102400000d103428529400c840c200d03404003d000e11a44600c0c21911841c0640d0711070648460120f40d00401c0164a8100c0a000c1410000e15040c021410041c0d110a04200c4030b00540c40e200080040c40e2502000c3c4e50003044e03001c045181901208040084e4115078001e036418020100340400c0c1d4014945c4416900e8464052440c881d818a00421010303445c1c3d812074802c41d4014041c0c240e0f512000111102a607811454034011a40c2c0c000040b159403040414203604107101058040e042c601d0313010307003509070f84000040102e070760b88a005002c140d0145420140140d92450340410050401c080b00004903140006031a40c4c041050300c0c65404e82c3c2c00490200c500da0340d03952120381116400040900c441c0301e1468207030301d081c01d0f64a0300b1813806100302c1 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 783343381 1250 783342131 783342169
    0x180807030f0201170702060402090c0f04090b0609090c03060307062a1b08030310051219050a0b0f06010305150a140a05151804060617040f0b09011e050105 68
    0x44000b035a00440e810070300c01ea03401e0b401d003040c1e2410f084001d4446100b81c50890190752501d0208160340c01c948151503042ca038a40d1803500702454401000040c0c03040f84030041e08800d04029202d4192107110000744100903840150b0f55909142007410301d0301da800e5000000b00f001001601400c280f9285041c1711108540340c0403100c0c148942061440b050200e00f92001c03010003410001f44081004c00503510401580811440b01c44d40c8105000718a03089c85182c0c50711740c110b0131035600c0140c400185909120700500841d5070300b001a68440149401c10b44072281031501500c104529903a2502400307501452005c540c40d0395a6103030003c00c400c655075001d000c06081d0301601403c0c5c2611403d150304002d15004003000b42c000c0207141d91005030b502504501040c500c9079440300a8038205030190000f10780c0d0b00c3e9a09103c4c482da02c481003800e130001510031600c00d6072584e9400b01203108440c078903024020040000941507182a10000260180c6030440c103006d003800300422480d40c0f14983d50503046c50f810 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 783344631 1250 783343381 783343403
    0x605070207060e0f010e010810050406080d0216060206040b072106080d030917091507030905011103040f0902030619060810050a0e04060b0613030b012105120c0307060207110118080703 81
    0x6044c07104440980d40ac5079810920302000051560400109101007841d03076001d0311064601e841140313555032801c0c0105000b5a00a80100c0d00140074814142d80c401268503240425072061042603100c80000d50304200196107030b034018019150144060000310f240b0b81420448080303195103510840c142d001440500141c00304640080741ca42000360504525110089540c03a0b1652401038035a40050240740e00203008030100500300744001080314140c0d10250314444681c2d14002290010f5417009110541103c0086075125014200a00368000742100d030312001280e1409014a40d25501705900040c4a404520b0703007000715003040070740150015008580030500e100e008001c107a041c482d408011a00480641c40082445001c4078001d0503103001c4000e00078543c26041604c1005124800050f2242c0c0022092800c2640703840c0003031078500c0225007030b00d05043c21612071501303d0700080c205403982c460302003058400750307440303006070103400d240c0d94442d42d035142401580c595807a480e000061003081d0074 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 783345881 1250 783344631 783344641
    0x118140d020c0118031e05240a0b0a032405060f150708070209090a0606090504031d030c0a17010c0c08040303140d1803030515180c070605070207060e0f010e0108 71
    0x1522444c40174640090921140d00f00086410540003c00041030341c0314001c846600185072120101001181c5009445d00c2140e21000040001404250036095100d00d514100000003440c18031003031840074100b546a00f165015004103070a8880040003148070b0360030380d07203c0340140e503624000131020b8600181c02034075000c09203007601d040d1141c900d001e54444d900340d0030440781d4040004c26201c401c0c801c08007440500c0d55007251000b610420348004000c0f907800390030300107099006aa00003400400500719000b88461001244034400e140c0c114100865805070040d01e002d100340a1041e44c18203601c0c01c1101e400054a910019024a000040820240a03d00004d800d20182a00c01c4542c000388200150500c2422005010035049000c4010904000004605954907010540e40141c0030b000c0c00710340c00c0c00c03070709a0b030820301c00030284600c00209000f10408101e8030303c01c00d8031900980d002000e01a0074000050082d032000b40e0407612901c89001c0b00c5183e40d900038555881c10f4070030f00f031850311600c40d = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 783347131 1250 783345881 783345917
    0x13050127270b1602150c1b0319030605010804021306030b090a0c0807060215100819062405100302070c0608010303120203041e05030c06090102180402040819030507050118140d020c01 80
    0x507c10030100c484854001606c003544040018908890342c1e222035402d54400c40020750507580180b14190215220100007009800d140b141a402d40c01d8405000506607220740d10001240015581c010003544059840d83c104401038071110081d001d254000c1400914182009688502c0700c82c50414151410022405510010b9040340140030000c0684480c0c0d444440e40700302c05441c2c10420381e41e80d400e00040e101c001c00c1c0070031090032680300e03070301030100d024101000d00c081000380c50703506810140d003042180c000c61000c102c0d070030141c622507a4107840303035145042c0180940c00d10400c4440b464810014032000400303126110130861016042c41c082c240d41414a6400e40c01040700c140707005d00591041060b80344043d401840f207591f4030012909000741502c2031100701d014070b000d02c1c04503038000c61105101d140013030b280081540c424506a4944030719540d4031030a44180d01c0c40000115049011441008641841502005100340080090300001c0b03000a544941035009141400121881164030001e = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 783348381 1250 783347131 783347137
    0x306130f050a0f030e0402160303050907211703090a17040801140a0510062102040f0e010e1e0f0601090914040213050127270b1602150c 60
    0x14100040e188034000ba402c1500c1d0b4601000070480000c1e000c0801000300f85014402c0d1140560003c003250742c0808207540940041401411400c2e1034131600f41e0004000b0003c020011031140d4100c1120303151030480c60404600000e01241d00340c03031a824410440f810100045023911a03402440c08031038500c0c4004d1003000d61140c0c1e0004020703035092211a902c44c9944502c000e02916200710300704155a6440d451501d114000d024450010f0030b1404843d0010340402d203240703036002904600514103a83c03602565280030143d84440d650a00d0900100409259a44060703888182c40030303000c0c2c802840034104e001c402001441100e00c3e940c48400314081740d200c1c0082d100a081140d03001c101c3c140c90b07088191021003040320200e1185100e0116001d02070242d0003075a048a18501e49107080e2009948141348031076070011034400147e0341c0c3d1600d035454502038000c2c10020100300c19031a80607003e070a01c01003c20f001030613413401420380201c40d00165030016444800444256101e000c980b982140ea2036544 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 783349631 1250 783348381 783348383
    0x40f08090607081204050d08060d06200a090e06010311040303110a050609010b12014101030b181507050d090209010617070905010c080f0d11090f0901050306130f 71
    0x900482c06041e00c0c65201301090040340940110b448586120b082100c06840850340180c01110600c1c1c1080060401e0b0000e070890420542903c07004080c1504400b01c41e003040988000103101034004000310010609016000301081c45c0c28440450b02007640c80c000c1c1702c0d6220040410110404000d000807052000d841e00301d07800010303200c0c035041583d01c440c00717001c4424015120300d9144086145c440700503c529000024140c1c42c01540ca1070342d0344030441640c1c002c082110301c10354034014a942c00d5400742205010f0b5215800803c00c40c24040006044002d841840d081c03250701c051803039044c0b0303103c2501603988440706d450100d50303481003010708a0140070318000007504406a500049001c2e6004124034008850f0b020301320b1920b03030361800e01f160b240c2450310686010901000c40e071008107240c28000c00165070308422403131400070728a218a048809401c1918404030001c20820090b2600310600d1803100d20031242041c2e5541454000303629030380b000d0500f84881c0c000709802810048c101880c4400d52b = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 783350881 1250 783349631 783349643
    0xb0a11010b180a230f04051507120f020703090b031003080f0a0e180114062203060605010e0f280602161a1605190f0b0609040f08090607 60
    0xb08086118203050203094030071801c040d0801c04456100c00704842a43c040001000f40325415071589140540260300180c03090b203141c069503c101082804615180380501d60319035419005840403080b0f90101d80c148600400450700401c442804a0f40c005050810b41d038503106206e035030380c580101c8040071655951005001d18000b10b40643d2100240d4040e180b42207280d00d98140c5404503804001e0030044004001d80046400d030018098100282c4000007000009000c441c542544550100c440f00b030032980a42c40100310050a2040207401d0251000418080c2031952461110380c00048146140c0076020f40206030309001c81c098050180382c9802c103004502c040138001c2d030b145c940094596501400360340203c82445030000c0c54800781c6440038014011011403500702501031a01036402900001300340c07803c0c440c0c2000650049030004104a41c2e9200d0010944041d80500d000590001d000b03140902c20f4200d40d08010101d1000c0c0110f85904d079001078130a50345c0700c180c8002003580c09825005801 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 783352131 1250 783350881 783350899
    0x11803030c0b060d1707080702061b070e161107090c2007031509050f1606020f06070e0d0c120b0a05090c0102030f0904061805040b070305010b0a11010b 67
    0x241a0807080c003100a50050150b00b6895807054103010304840d031020001d140075801d00d44850301028031310103000018441c40d6014030b4070407a030300020602c0c1c1244141c900161007910510740b500c00100700302801445100d5a41d4000d2621102280c0000f841000d9807050000041c4800a0100b0034011030000e000c1801c0304009400003488014842861180c2c00700c000321031061000c1050307800042440071283e0040d000e425905442c480785026003480039040301e0a200720314008138400300c20301100360b0b40540780c015441d9280c505540286030001310900c00d03005401000602512a500844c51400f2050a031681c0346100f001d4533200a926200d82d00122910003502a8242000340b03001350302c0c0c002d912080050069440740c960043d04d5204003c10140942d1080002c1810022518080e0007c0b013002400001c995039036160611100c01c02c20b49820405940e0b03010401003000041c80241c000304285020801c560400741d00303620600c9140c40c02420b0020303010b0a1409032100350008031040700040d000c00300d = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 783353381 1250 783352131 783352133
    0x40b0109091109010f02010e0303070e011107090509013909031b0302040b060c070509061206090f011409060406020f0913060303030b0f0901050409030c0b04080703020d0516060b011803 81
    0xb45640103020740d10700040000f0403401015105010b8000c0c0c100080c00a50300c0e603258bc21017a642d002c0c010140c141070103190404005012010f105200040500e52800b0a1a10703227520320508540c3c0d1400c591700d4907035038440d011038502c05800504640e95444803182c40d070700030380c00010740e02070745198001043e005900e091400c034101c1644411044034825a41808014480c500f04072590050002c0b03401240d022917170400c29440d0125199800050103004105509100c610a6081c00812640c1d001240e0050082465002e824481e908074200300f8500e400c450f09000c08015140d050180c00502502e4000c10030b0041050702c181158a40800140f5082a452b01d01203000c01400c0039100550219140501d20201410800c80020303a40c140108580e90581c2040c0404c001002703258019030410409603403034400141c102960314000c0340901c8a054a030005480c0091400c00380c20313500c82c100082400280b1b21506842985103444c1e0740014081003140414004a5070b42e42041d070384141c0b08002d010004 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 783354631 1250 783353381 783353411
    0x1003180302240705090d14030c060f01050a0e0f0a02480c1309170d050106050702010c1e23070b0906120705040f0b0901021b0f040b010909 61
    0x540c640014480710107680c01002694042482c0031a10080890400c00c0640c08a1074400c04203606584104211000e0f0210403c0f400d20f141c00410418096078000310602c1001a140b0f03030303d28014081240d8181009040c1056640040740240654541040031004a50001095015141544414516540400c808800004c5001000c1450b0048038005c3c180240704042c240230304000c2c110840c4000e122030900141071150030282d40140000c00c076940c4c800d43c000035050640c28030040f0341440805031540345840030b4100703d51040c0e02160500500b000005d0042c3d80100d6403012040d0000e8950594241003203131600c00e00306525008010038004800d201c0c0484030101038200c2d4140740022240070316203039050681e0318800c2d130040d07560000d0140b00c1c41c501000c4504c010341d800200d03482c000b0700700780ea1144001810400e0b900881031803880482d080d54556410451303801001304501580e40542d40c420003054021036000d032203d000326203910402400fa4015082c0300700412054108018039116110b0348 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 783355881 1250 783354631 783354643
    0x90a3012030b0a08191a0a0203011d100e06031c051c0614150d060f031208040b0606090609150309010507050708030a0f0f020d06030302100e0c1003180302 68
    0x1103004a03242002401c56801c00e41c444405070f51803e002012042c080c0010f8414102407240100c444591048004c03280c0011101c074140500540d0001603200c0d41402003000f07580955482d4415030700c2d5203508011400ca00030302e0b0710f0300300e0301001c181c0020340c3c50310f03000f01c0c1c24042c945d6012041c2c021000c48400c0c1c02c603403100050007060541c000a0385041400d4600500b1349440d44160700309941c02e6100c0010b0351900900c948c88260107400034a141030340c180e00000903128980e000b131602520f04001041031000c0300941c03d0040c010361420840c14501652206c500080c0903191501802011440c4035158070345104a40040e240144100300e407406128050380103600458940c0340e0b41d400c08000c281101d009009440f84d10b944106528210741e038140c0948002c007403c0403500718041d240e4500400c0341d035142c4010184485400c04c00704040b401c5080c080c3ca840c64207204045039514101143c0e240e0040441c42080e001c4085401e0400d4604008044014010749060115000516259081019000550 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 783357131 1250 783355881 783355913
    0x50307030920120a0812131b0612050609160207050604090e0c0a030201080403110c060706020a03110c0a110a03021f02150609010909030c0c06020d1202090a30 70
    0x200702c00e50383e68842950b102d40d00d580000340348810a2128038809091501030580c0040c2015442c3d10152a07034903100d148001650005016451000702031043c1c43d0311010b014a0718090000511070b904100c00031552015006103019500c125217100c0032421842800000000c100091111b6142c42d00c444080303000b401c1d102081d410900c1055088c0e180b031b05028100008498051311440611303035803902e0990b038010300451801c2e441c2c081e8241188641d5904005000564020100142c0300c541450001e02254070701144400390910601040c4c000c9100060780240b65a4040402c0042e98000301c04038048410b01e0b04029404190010400b80949090a008502c1226a400c54940a04821980200280598003150806280b00c014004640640c1000b442e180c40303454001c600280a440300c07865070009801c80e40c01a0000340c1c00384010b07641709400ba103032003944160452520010740d0000d0340c03901c00d900c250b000d201d03c0c81514204ad62610090420980e110141d2074540c0340301407074422001c00a0f054 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 783358381 1250 783357131 783357139
    0xe04021206220c0531051314042405011401031d0304090b24040e0c09030a0b0a0e070f060819020a03020712110a080d0b0604090b0a24050307030920 65
    0x500b17045908000d1850598a052900044c80e06010501028081c0308141108050301c41400081e90f0303d04507107440c4240c1c015864054440d2440004421020b0f984207568042c50030a40188041401d60040d070610308824240000d400200e12100380400300085d80509250001080020f45045250030160721000212984500e00200130b0303103028001d00780c0b0401510110180700500918020300110746d000310b08008081d0404084900091801600100c100d464902c0d00f000d01c0201d0405004052409111a010f46003190419560b458041403520402c020401c2c00c101080150400c0700e0481219808400305540e100703003280700a006075100120494041040a00c6600c0c01e52080d0920a00d00040d0400b0700020f10b61520340140540040f00d0b45070f81d04d5540d02c0081600d0740c032a0024001840c1500740411600030341c100b003000e12007607a8044400540000b0300485102030b1079607800d40b100c00500303000740c49481c2d03c201140241110040145100c111140110061041e0071f0400f40c2c100c0100c0b = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 783359631 1250 783358381 783358417
    0x30b011e08060c0711060c0a1a0603010b030a0230010c0906080402010f0309110a181b05070332030603070501231c05160e04021206220c05 61
    0x1c500075075114411030b01c106152405000c41000500742e6500410108002022141084194240603040c085a0307041201c1046a9500f6101d000e0405210168441000ca0080104003903410220391102e0010b0002446035800700d41c00c1600080300b40011074800707206685400450701c210f05080c020499800078201142c0040c01c00104513104800d10751046030b042e9184104896150419006403181c1d07001211140c2000c0b40d0030b002a110704045400800c00301410755094040a00b411003100d031841d80220240060210034151303150404200c8520513414035088102e44500050710104005110104c0281c240c00c0e152040391800722000385004240490560b0300300382d511801581c0400b0229000f003400c803489103070207081e201c00f1806850031040702d2841f041410b1008614808545044540c441e000c500000310034241c80d0701480e1142c1c1e0100c266011460824031615a101c04031000b041c56120f8100c1c1c50041d0801c0500000c410003402c3c0440090089029000c40030b0300b80e40000001e4200c0f90002 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 783360881 1250 783359631 783359639
    0x80601030f200a0605031005060c160b0301050d0f030302040801090602041d0603070603020c011d160f0e04060c020a0b0403110f162d030303020405010809010b011710030b011e 77
    0x2e0610000564002000c484050b0b280000554080d00b00408039060340a84480020f040d480d0280106203a0304400d02802c071260b810824142265620f40102c3c641e02024001405591586804005099001559814108564034003180a84a0354229190a500b8603039481c0400410f0340103030060381c4085012030b4040a06151440710541e08444081d07040e0f02448041107000e0295000b400c6c0c5078288400403524400300c14100341d111030486e03a4003625510005d00c1da00c00740005042040545a281500c05141d881c01040036601a0060809000c49542d8115061014001c00021680c268030450b0290145401c0c1806030010600304004c040d0340c001c54070888050f03800403420124264107030b04d651014505200b840321a40114040c0e000b032254000045031090482002081c006612030b680160741e690030400018001107002d0000030890303040c11540010f1307a800055000c0a0091040825026a038a03802a03964042e180d0010700307869091703c00032444404a480140c807140c04515031303003000c5660b = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 783362131 1250 783360881 783360923
    0x81f0b0609010c2910031b0303050d23040b100501141b0304050a180b0a05030316060605121c05030708010b0901090b12091b010c1704080601030f 64
    0x2541201e070380010101c071200303000600c05140705500c0c10700d1614510541481011620240c05058071183d000e0702d0145410402c110501009502d00410f0399000d42d441c91442d68058001d01034100001001e80d2119030b10603644074845003003181c489805000350020b0405050804081038181c5072842c444403410408281940202445014540d01074070031f901d001c1c0e80004194800c01021050f100324001004001525070307400144c05c0c00741511082441d0941a4402e1070400c035160105224014280c0b02c03001c02280d600801034800c81540004002052170661410f0f00c001c05890304400d5201a081c584011440c3e000640820100c82c02c4d001c0010121620a054030f15000845081001421001c01440000c503407101a11780d80320f040c10140d6540342c891002942e40e800c0178800000e0340e150003007004006001004407050b0440c4c0881c043c80c00e0a05240001c0c000710105201815643e00030780d034490300c20050002c50f401044000207076940355860340317444100e032070340e0324002d840e50000c5400201003415 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 783363381 1250 783362131 783362137
    0xf030a0b0103060e100b0c01110c0d09060215160c06020d0905070b130b0f091309030216030308061c0c08010b01080109050f06010305070c0210080709060201060e13020604081f0b06 79
    0x800308111703000184c5415240d008a5100c40603e0f1829501c0b9485054500c8a11002d003408500e03150161031005c42d42c0e080140008030701d40c4804119440811030f04044c180c9138603030365000200c983d2807050340320080d80309551061408400030f02c820300c001141039181c042d03640000364891181c02911185503136107000c1c130058059071002c11004410101c0402400b075004000f0b00e10789484004180c1058944030005082800016000041035110300b40c0c5400c059051064008000041200d114400c1c1161001403007081c00405c45809025000c006003610f404200d40040c1e2194010407001029495440060180c0007280005001c5114203000dc0f410b03911600901d8801c0710500b01d4008159034000044000e018041c0c101018080034102c507402684031210f82d04c5540c401d030348490307103582032550008050b00c10b2980101c0840e49071001c00d00c0403880382509560410301c2c0348900100000b140c000200c00d4800e5510031402c1d403240c982d00c048400030020b00004a107144d8441002910304078000c1c4003040c8 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 783364631 1250 783363381 783363391
    0x10c021603020f0907141306110d0f030c020a020d05070503010506011d0910030501091a1008120705030c030d0c030f050906040b0a020d180501060815070507080f030a0b0103060e 78
    0x31101d00040790030b414040e4013158445050700d01a50010003190001400d948030003554904075003158000c0c0000c0d82c00c884a10364004000005005040941a008220321b210100c00820103451f581a440c0e0240f0070091422000e40080c40480c8403562485d26603602c41e1144690b40c002c0d42410000f45035980107100181c9060b92110010580300060710030410095030040080307104006103400070021540c24802d81400d6842040e07a0f0442d00001900800030900c0208440031000c01080e050029081c0442c000600201038a1a180c41d0109880d0880c00d5001d10010855544404900303c10b0a40f4143c0041141341000d44041000c040241c1860b020759604030303082100c5602990103c2c1c00110100c0c4120350028022100504003d04000c10a003541d810f090500d521100454500d41400000c0c4180700040c01c4210040c4200d0029100740d4000400c0140040d06210b00880e104080c082c004044034a19900c40c0180c0360b60380791040c6040000c200006007140060710301000400e2104011030118021 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 783365881 1250 783364631 783364639
    0xd170f16080705040f0b0c060c04080d0804050111160b06030715080901110c0102091f0801060f02010e0111030f1501140c03161118010e130203010e0d02010c02160302 73
    0x39541020058030441400b402440410008010014502c0f2484011030090036499480d281e80d40c103070085030781c6070400181c0340e00a0f602041004010f00c501c005021010400d83c0d007040b003034580d502d0608900410303803510288200000012031001402c6c0c20710920038658820882001d4503103d400905549580714092520b4030200244e4009406000c0c2610301c0e80f1507200c0300003003940c00e2450300380d03080e44d01f1a1115541c541c1d0041040075061411403150140746050414690441d01c0380c0301e004140754018821007062118880c1426000c0d8400e4100ba1149510b0300d000744520881d1050595840d80104d0311f0403046000580030803481d0750864418898401d050b034030f00310380d40c1c0c2802403441c01e5404a02041e1252004100e01070021005083d00095140a07210720080840c90340240b00c010003122111007445100300c0010f20034807285800403500b040740740c4801c6144d508184082401410f800d20108258812007c00c2c2c2c0d89540e05400c10070407440305909035000c410388190750305030380e075a103010007944 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 783367131 1250 783365881 783365911
    0x90303060d030c08071713090e07060305040212060910050a2903150a05041b06091412150402190503100f021b070302090c0406051902010e0d170f 64
    0x82445140f028810710300403d42d003442c0c000203680701e20080d40401148210440c000c100340d5000104a907440004082c100e006001c2500d40c00003203915820700b0f000300030078076542d070000c9010740d11200b05030700c07480e6031141c1100e81a00300f0401156443c000600003004041c10200010b5503065507024414120b22500004c14500d034400a1039400440220001074040c4940050100d80d0340144841c240518210340703000625082c141440564080340c034042e42c0610b080c0d07210401c046948070014804950b00400011210012900007440c5c400f081c2d000c01200e0b12517040540240108228418003a6108403050800d07000300340c100e00301f10446841500c2d41a00318024a5605d10b0245c1c00618441a1150b00140f61251200c83c9550b01c0034003e41450740ca0344021030600860811006170340d041904808168100b038a088002020740c07003a11052401c051010482c902c400e0f000b50046001c200c481ca0964a01490b5690000c00150074000e044080740e4084000c01e0354088102c0a0030300403540804e050103 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 783368381 1250 783367131 783367133
    0x60b040606050f09130e0d0e13020c03040b0d090639020309090c04030c0305070905090c1507020102070b0d09110d030503130c030503040902070b0a0501140112020d020c070608090303060d 82
    0xb03000701200102c17580300b03480d02c0450040007014804482a04100e0700c914901c41100006d0040744a0200700b441d0b2518410000040700310000030a480441e15107480055a8007001006071000d044444e0006104605000c58150810408030038128241c84429500f10303040b0500d203000480e0750384d107426100560420003d21080341041946203034041800c4044914055880e0382c1c0101c2107150b82d005862540082e0001e015a522500076542c0220780040180010001034000a8030b00488039400ea184045c001000c10459000348407140041c4101c40410780c644085200700c0000e070855182c1201c401c41c81c401c082030a071810701c101c19441509652081c0c1141d0711719000410503c0001404e50788507404000010025100700014009450100009070f11a5642d244c14141e20303801809998901c1d040400511080002007000d0a45040034600840e5252024030b00c00002d2040400c1680d199000040d0303003800c04400036605c41141c41c240e8804076140e0305d43e40c10948034001903030816800411404600c1c = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 783369631 1250 783368381 783368389
    0xf04020f0918060910061d0120030a0e030307050c09090703140a12030b100f0314091c020a15150e0403080a06050105070206030c25060b040606050f09 66
    0x80440d44151028030340016040002e01d25588440b45203007146400c41001020b040461040e0b40100000c04a0b800403410301d4030103800c20301030385000d01c1000410301110016030710a1031a0f28229a006515802c0380000c03000241e02d0303034400034402c400300d42048031801c41ca08000088a207116005400b420821554408210341510b02505203c1c0c0b174403a40c4008804030f4002c0b109075031002d002100a148101c5c5600e810a4202504000e0b101031500d0614010702544038408461050206803522044c101d1107140c0640c0180900b4034481d0040626000f0005052800954500280425095130603040d00c2a6000c03a600c3c8443d000c01001d001c102c00f481520400030b90802c1801526007c1c5584d0307080d07180c130200105154100c40582c0000d440c0c8051000d01070507445070398060a000e20300742d4500181500030034020300c80a8610f0111980019002e005200144500c3c1c1000900b1000c180015405060040191100b4070525206500d03000c030020b8118025411214540040e030195401d00b01351001b04 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 783370881 1250 783369631 783369637
    0xb090a091e110d0201051b1605040902220f0c1205090102030112030e01090e0a051608060105070b360105060a2103140d02120115080615090d060218040603020f0402 72
    0x80741805807e009840c84034441038060b01012080d180100940c43c96402c0d5015564000d6118a014610b032020200240e1202c08688221704440185622100201a5240c0050041c460301303158551074901901e10391940080300c1c5245104a010500c69600c0e0942004e00300d100a1058046125040303034140c0c00240103680d401c3c2c4103907050605100f00b85d0745203449000b20004481c4609031035652820444040489200c4074404042840d02c40010301d0108006020340c81108000340c08070306580005901508410f45c400c5e8080c40c000c206102c9600c1c087c100030b14403406000240d4141d404c1c8400225a03040c240030780800c64081c05548180c00700b07807a01092418007c0d0038260708000c10741c81c00c0e900c01000d14000301203881012a005030340d000201600c0d1074070310303040e0824840e41511010a00901d5800380740190490000c0392071041d01d0b82c611440d84058887c21041e9600014441c9040c0103208540e8003511041707002c3e1140d000611840d03000c01c41185c1907400020740c851840000015141030580c0a = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 783372131 1250 783370881 783370883
    0x1d0709061103070b010e061206010b031302030c1f17100b0d0e06010f05010f0903170310080d020d1d031e071a0a141315030b090a091e110d 61
    0x68901c2c0000c3c0391070305580483d0980010010401e114140403140c108801e20706510f40c05503001d0401c80d410140f5042803440702424540c000f0341c851a030741e4151740c2d09018941728540c0040204001e00040c100204201d4110221200800c982c0090051203108024100e48039501007500f100340c4509141500000f9042104d0180d141603854046c008003c0c400c10000c0d0103099030303107403100415107042c00040038035406407409820454943c004100040410280825050039801c0690303c039601c400202c1085441035000c90820710410340d41c4800640c020811245080e00341d0707942ccc2d40e002198080e603908052480d515603010360000610264890000da00009100340500550320455998500b1420b00480082c1198041200082e90100d480c0c0002c0e41c60140509040b400c1d042c0b04034003047c1c00d03007050315108a401184002c1c0800341100d2195000090081e0000c000c40e82c03031f00300038003014001d22480004880f500441c040d0000d603210040180b1143c1075102d20694900031381c1f0b40901c01c000c1400301c0 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 783373381 1250 783372131 783372133
    0x4031205041109150301061509032d030509030106320f19090f0c0525020402161101051306180803070803070f2a020f030105101d07090611 61
    0x3052010b29a54241c40b58019080402c101141030040360426086a8040d4030070401e8506035043d402c09a500001e00c2803c0b01d23040075082c82464100244100d644c0e4003403900c07400c040300d602c40c01c01c00c140d01305025180f03015098000b00600c0381c03124240101d0030000404136010410710007003200000b00d00c0344e040c5d140d0380c406800c00c4144400075012a4443c44284101c5824914015040c4208000e070701c00c00b8400b4180641c240246248800007070034910807421100030802c07610000d5601c1d00f10074015a040c2941c042e10841d9104208140c1d581400b039460012500d0607030085400000f58403607c291000302102918240201d0318102042d602000078484da6104182c1100002499010601c013404995002d808a160349150010009001803074120000041c001c1e1400b1303200c1050500c100345802c60403840d81c06076000c0124000640f400001c12070099056081230b040205154401103c5400c4440810385640090442e00120010810407920540041d42c20032041100c00e10951060229030500c00c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 783374631 1250 783373381 783373403
    0x308010506131809030e030a0206031911030c0c100b15160609120216120b0a0e0709060504060504051303081b031e070c05210f1812060403120504 64
    0x3c0c0f0600d0080643c82624003040e62564418145900001044441c2c141100a4124030f5559400100340d40000341c822061217442d445819140240b503072002820414081220781c5a15140340207106603408080300400c03074000c14403601c48100d250b000700406140000c007031604032030500307481d4007864000b1803110314803204800789003000c0b130214400c0047c0e40f40030300008405410541c4019180040d084105240700c0b032100010400b443c000c213010f2b03030400d0303111820400305c0e120407070b002c409000308407280c001a004d801c50016144120398030017001c903642a541442015610020801210740407500702014030311600d100030001e80701d0300f1002d900403042916034030a0800c000041519400c1101c070002c40042c49000c15440c121703024140369005c207081c0b8040607d80040da96560715500391044591000442c042055250034107442a074030080003401490b030719540c1d8000c6100d132030b030060851980030360900c0501801c0107802060701445039405803107407458101078240300802054020010b4a0701c50050b = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 783375881 1250 783374631 783374639
    0x6010b0906071505010807051f0c030306051008070807020309060f0304020d0c090209010314041509230319050705030406050706020d0603030809060a02042304020f280c030801050613 80
    0x9031506203c40403500000910b0360400075203a1400076983c06c05845242824090300010a80a46c0701d8240007031480c02113040c52480c60158081c0c121174101c150f000c04a91011880b542e070220390399209918075996501180c881c1c00c03082c0d07140e1007076080098001e07400300000b00c040e609540056400074809400b10b2071164a5480e101115175213034000b154030035000a145461907900d80615907c10280d81d1070b040ca40c0c1400ea0b0f82c10800142a05c62000d50354944003681c09100c00700314070084400c1940c0300070b080740c0503001180740c80c0d03071000c00729030f001d141181046005c1d28402e00544400c107502800031445d082c2416429140382d009400229102502048051611581c1d8012440254800e8540c85100d080045216090a0300104004201441403100708000d5076112030061104180040c18040e000d56040854081e20800306804804140003a120345c0308130a8400d0800c102a0451711350811400c810002c54480e0b001a134080d0009030940014040c1d460000c2c0104490446009079500e65561 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 783377131 1250 783375881 783375893
    0x90303080408090307080f0105010f061d040e060a0603170301050a1a0706110a170f240406240311040612091202030d1d15060604170715080906010b090607 68
    0x105401c46c10b016000220107080191090140d14098440480322185550070b0001c010321005552103d00d848070b8082220b4900e41d103503544807000c1075102c081500c03001c0c40c000d0501c078041e0100384000c5a0700e41c0c08042d0603140203e018142c0b030503203400404070341d1514501180f04203006003801401c404603004224950025081c0d00c1050103440c44003101a1b110300c0300b040702a05100c02c1c0e111915102c3c02103410007280a0348454505c0d0301c02c07210107a0220300f030001c440d1102c0c140601b1000640161505401103494442c00c1211040643c1d0b600003000b0b03110b4103240c00c800780c1e0013035a0358403080e031414441403025502484954407031591000000800d01c1c0a42c449002d00c0801c008503801603040010300c8642d1100f10301036800000c60100383e09548070001c64142d60f54200700c0d4200040c005941d0042001c6503644005c482c0240002d035289000da603540c003441d84c1c0300c800b184a03881d0311201600750100c21600591100c1d209500820203480240e213000a9400590b05c409081d42d071000d010484440040e070 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 783378381 1250 783377131 783377143
    0xf060a0e04050105040b152206030209010b0705190305070201030b011b060510120b160e06040303020f150121080c0304060306080d0e03030a050c0a1e0317070903030804080903 77
    0x4090b900204003401c060400e5405e07000701a054492100c810003451340c0701d848545481c0d04100e0311803100030203162900110340082074a500025800201600000342c0001c000c0040d210440c0907800761101c1d101c044a81030000c913903006005021940500c0503001641c0030344d002e0610070350181042c0f210150303001101e48080718007580c00c854075660307001030100d00c0c9890000781c0003a0950b940118154422a16440d0340400010100341c40780081d00d16003074aa501c111505410350402400c10354030f03652a46006510b403211103090417210701c140c887e00c6040c0074009407211304079010b541d8159100044180512805c0c00185415036681b4820440b950754140100010802060f0075500000d41500f0404101d0500a01e00841801c001c6800c0f0390070b03441d5401000721000840f0a041c50ba44c0c8681841003542400d1b0000f10151a4889043c40c40b000c404c0c05191084030544a960382c1c1024110030940000c520b0001d0b280d000002d82d503c241400081d0103081c4c1d4039081800340301040c0c14100c40f100001c0c0742c42 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 783379631 1250 783378381 783378383
    0xf090a1502070c080c18130602210c0906030c0a20070602060a0e0706230a270b16060204050904080a0f02010b090a020d0e010623010306030b0f060a0e04 67
    0x2607002511a041c850b1151000000e022524094844030018400258001d000503680300c4040c0b40d0480440c210114410180c07441a5201100395168114808058480c03c0701c0e18001003442d81490001c2d0502c2140021680c01120040c07440341181c50301e0f0301e0128a5001030400d40c09114030040420f044001000c080101d1120900040075114103048000b070910300040c2200140b6400c141c50786c1240e050105002d41528220325290702c11070403208a1048100520860701d5445000251a811030f5078080036200f5480301d109030901c545604003441c41030a107094416200d902c001403042d0a588104942510601401008003504140e2100d00107010990140c400700c509440006003414115080580c1a0f0101400d000030801d4044401c04a011200f008001e02000e990014020780361490a0744503480d030740300182c002c00250b51100c6c040d03555508480d80d42003004c80d84920079501e540c424001d25040e00ea1014203900541c4640703101c3c044066020307240990003414040c2c0032880f02d101c410401c0c465 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 783380881 1250 783379631 783379673
    0xa06020a0b0702160603020a17150f15090d08040b0f0a0806100c0b19020c01060504230718091d0c0d08040909080705150601080f090a1401021c061a04030b0f090a 71
    0x40ad01c910400840b401429503150151104005151848490605903080f910b01030715040c000a60900e4144200e100f10341109000300c0b00403034070080050b548000391a101c2150b4440e001e0390786071030302040324020401c0e007000002200020f081001460b040c0001d90450200321282c0c1440d404185614160f80041d400500c050390b651804000502e000d0050851410080c40d50100d00e0b590326009400c0c8041c002c2540090010410071103910442c540c54980042440a00800050021500880c120b01c801d030b413250207a00c0b441640104c41d10700100c00f0700190703a0020060b8a000e03e0101070310050300c1141800d66415105101400225806116036807044001208403080c5150440000d407628034040c011001c0220402c0410012820000328405119004910010184007905659000e40304403a030801402d103e0500b507010900c6582c1040098600c1030004240d09070020034142040d008070700c006004203c40c01d0110305084c070701c1004d03e40c001034054280c03901100c180d00c4020084100110f07901403 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 783382131 1250 783380881 783380911
    0x160302060307124101080a0f0f1a0628090f060e0907030303050a1a09100911040305010609050f2419090b01080115120b0a06020a0b0702160603020a17 66
    0xd2911310038110440818003841070320003541004050360340d030b01156030000c0048880420b0541400450301d800812640d11162001c04280489410b8085840a4a0050280003000000e8404028020280003510a000c0032090003070314000004000e001c107000c0d5600103a64658020800952070070855104050b0b44005010300307851031030002e048500041502803082c0c68022042c004041e824404242c1d1396007161014210388840c1021501207080d130703002c0680300c0d01d0700c6000810b0000d0603001d0000c8034002c000802500e9a140c03c41c5068a0041b92030104241d00140050160070404074110100c011681345100c02485420202e8041101034880085c40e0301000401c20010b0000d0103110803c50007031a1400443d407401011140d402d40400803030050114810301c640340480c4960084082d07400080000300402e998010103500d42c2c1d6076a03815181e0040351400640800d00009906c0b2019290341444600303d40303419008c40c000e400100b940d0040004c141c4054056441c076a102d5030107100038a0b440e01d1 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 783383381 1250 783382131 783382211
    0xc020d02060315011103040e012607030308011401080f0c070f060c02010b0a060c020307030803060409060615022a2718010b0307061403070c080c0c0316030206030712 73
    0x5800c0c2020040e41c400c6d070080005015842401d540103045443e03145022201840c2c080c440e007496000810ba030862881075090000a15038040710031412540e0948840d880c0107200740044600010407076600c9400c5c0c040101003203500104200400e01280520744c0c401d071100c0c05036654400d6540704c3c840c0030f006039150090240c0d240f8081f20790b403004103442d0604243c104001d40c0441d85882d01c5100162500e14088005580c5440310340285901c5940190200404c0c0e4541c034001c40c0c01404003d00704018820000302a80140300030844d0000744500000300c2c02c002c4612020025003400c01e640701d07143c00c2035031703c42621001c41c400c0c1c8050050341400d12440001c0301601d101421034400004131803181d400344404002e02e5070494407107450400c00429003603596641c04810786640d200300d84010140007000030300001d80e600215611150b150101c0a5400907030180b803410300524010700000c2c0d840354003000032508803070140700c0c5119a82c01e40d00000c20740000d0304810124550a1310414a0307200d0140c05030b21 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 783384631 1250 783383381 783383387
    0x180c09060310030c23040b0301022118030918100905040305070b070e10050c0109050a0f2108060622080f060105040207050a1b120f060e01050c03070c020d0206031501 73
    0x14050b109100c07103103a0700031070b5440d240480040f90141c175001d9036688001207581e40b4290121840c41c03407600f000d00d10f800484210b0358003100080f41c40e0000c441500b00d1549022002004407581d81000900d00080305e1600c1d070312000d1005010748440c40002e0541c00000301911a40111441a80281c0307480f5141c0c0d5036424103070b0365604010003441c104004600b9002681e038404078100c0e2440c0071454a40d0322601040d07812030042880ca80d010306240700754400c0c00b003040f52405000d94028819004410040c680203024070814000140b250013241d03a240019455041100c00781603203100026000c01d10b503c0c4100210280760464000400c25000045841c400b03c0d401c010306c6004100c190341c00c40c5000e6807610303041d4036405082c80c0103202401070841d160100c0c0603002e00300702400c501d030741d0144120414900b4801e070148458040354464184103017030b0358031302042c800c032407081078020505460b555a0820844c0c002262201c00c0741c5c001c5010f1000000741c3c0310103016510400c6100401c000384192a4005 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 783385881 1250 783384631 783384653
    0x7090903030e060f1b04030b09060610020a1709030a02040f05063d141c0501051c140102070501051503011508070b0a0905060703020a03080a0b180c0906031003 70
    0x640160f40c40b80c02482200462802001d60119400d6840c08060340c80f2602c9481c1072140d503002901100350201407264074003010031014007604085503800010301d1381d440d0030b98540401203030250244100740c0384207082e084000010198200b000301921184202a8002400c641d054201d4952071640c1700204910383c10094402460f0380b43e9003a84000312211800320654050b1a040b44c002d80840041000c8401c038015030b12a4408042e04ca8025192010b01680242d0741c0c001c190221142c070b08080c0000740c47d0404490341d00100d0710080000d08660015111999001e130b06540701081d45d0745c2040400c002c00c0c03003807080c2c40c0601a400046c00071070368014101400d42c2e0568029024280100100b0001c1010008000301242c10340e0840648401c450401501c800700964041038115170001110800c0550201c0d820030210b1003070315208210346404095200311801000441c3c0c000540452409100d000d0400c11680306010210b02ca00d8049120085861508260f0388070300b1200c40c03800c090080041441034 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 783387131 1250 783385881 783385901
    0x6051302030307080906120403080f01090209060307030b0a0819050d090803030a0c0201061205010f0507050a0e151303050d0210090807140a02120312241e030709090303 74
    0x144144100003500000e0300c2c1e00c5403220040c20310100181c103076020f03220380054800781d12014076000c42d1841c0034100a00402e0341101c0040e4568500310001c150702e405d602c04e50b14002d030007900071419aa20b81d03009070001d0440035081540101c4010380090001801c0154404406911644200718900c07072034118917200002c280c410a1080303082c000c2c000440000181c1354031198041d004035200752100d40c241e00401135134021640d2010f09000d42401d02c0030542140e100000061401c000560300c0700303c202c4503030140445035800240d01c54002200740c134044041e41192000707103480c94a4005200341c03204403d80b82c1c0e801201c25030000d24500c1c0d107250301032100511820748440140004800d80d55084064820b075500103010030403014400569103802c00c101c541c1e403637010b04008104642d18081030360f80d40080c2c0300c090400a4500001d00345110a83d0307500e480d41c200200e20810821414104503002c0400c1c0c0400c00e03551001414000d15580820868008004110000072280f049080003025104c8444c5 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 783388381 1250 783387131 783387151
    0xe0c09030c0418081b031207080a0b030d03020703092301020709090f230a0c0519050a210c03080d27170702030106030606050109050306150d02010504150c0605 70
    0x4a200c0040f030000c10341c0c0035459202d4141652044000e0254110101d0610040010311011550a080b13034840c014072401415961941181661801c00e40026a01e02024040d0560400444c07845000c2c0240c0143c1440c9100303080640c80c241d201e920320305030910181c14141c980e100f400755619041d42c050002c0780240144003800e0019208a0300c0303400f4800c04040c4000c0c060000f909819a6030440700c941e0301220740700c410940d01e0041e01070411028912030780c003800b8800c54800002e0030400c1d40c4034428100315040540701110880c03910118012000b084c544c0145c020031445c82c0b440000b4001004140a14481d0424584494555901004a5442e40e0780c58036081031080400381444682c04409006940c03000b10760005024081c0c20303c0f0700d4010100000c0d01503080c05c0c0040100146908480161402a62009405030303039041003641d508410b88840c1498113040841c0e50031400d00c1c0042c52001030040c142180b0b41136450040c10500d02c1907603001000210b00340c140f402009014019140c201c52814 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 783389631 1250 783388381 783388391
    0xa0809190e06061308010c090305070609030302060c0a140c0303040615080a141e070e0f060607030e030c060a02011a040b011704060b1f020f03161b0e0c09030c04 71
    0x1070103500c01c0058820b0348103000100e10410085081e074000707009041503000a01c640c02400030058183d80c51760204440d540224640032545038480c50440003241c1e010b90082169850b18403141c10a640f250403020f040003031400b40d2403080c104d0312000340380024051004580d2890030341000703821149141c0c03206045182100042001c003400141d4000340c00c1d00301031811f0140041c0350b00a480c00382000301e8080750307500e6000141d0109c00c0104110080300c207110300300d280307580c0d91205070b412000b4100d8255600040a010030380109105e40ca4a03426420040c088070f1400464400140c01034004804100051b03440e0b0050030184050601d4176a1031400a55061002d4601c00002a029250034404080c3c3c0551110004060004036001020038800150044161982c03401781141d41c03000f100541c4c0054410300c0842c1d240d035200001190021484c5030b445500082d01c540c1d88000c0c003004c1c40700c4000788019503a404928240f0310084640151136200d10682e86060350000c1c9420701000c003c131244628541 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 783390881 1250 783389631 783389639
    0x609060f0601030e07050a0902071509170319090b2e090f18050705010f140d0209120f010e07061e1103120702100f05060d031209050a080919 62
    0x500c103440d4000c10309007000308890402c1c54844d840c0c0302e8290310003580840d140400054000d00c40d4000d29400d8015640351050708030781d2145005445202034010408661100001c002800c103001031174003c88209940382418070b048901c58203031240400280d82c0e1114480904c00c1d220f01c0d06a88121074055501e50082c200200703084014190755620404c0f02c02610784092248481071036014040c4103003000d0410b4020215424900c1e80e410850040a0100c1c040c4540964a1406006102c3c51102c100c40ea292800003400844000b941000c58031039085070a1410b480900041441140208042da030000900882503203191441d0025a40c0a40c090001014a0302c0e203415688840400127001c2d03041c019088001d0b4005a072841c410601601c044545040502030003039404100d02ca600c41e80c005040c000300204c00018000c0f40e1058075a1640300c406180c91000180c094031486541443c0c1d04000910f080316a115181021003640c0e0898074100c000494444610380001c60b07075124809526800d003450b0038 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 783392131 1250 783390881 783390901
    0x504050d030203060a081c030b15071509080c0c030d0518100212030406060e07140d11090a090e1903090623040602030c07051509060708070206070f0302060906 70
    0x2204600c40406800200143c096201c00036800c00a1050800310355003240c0ba40d24041342e140442e004400028184200880d075850307c0503031a0540c20314800204e15103840c5030b603140a0350880014586403192900c0ca10b10108844d20060100c826401d03000e800302c11422000c040c1400b800c11255030070301400703000182c140340c0c402200041d02c08060b2056011905e48401c00c0c0d1038102c42081454a20400108000c00c018158200000f214010102e506860701c0e003c2c4141e031a00342c2c00c3d41c0301c2d01e65030b41403050b40c4454000d0380004d880300840c070762028a00b901c50b0010449680e829000706001a4071030350711031012241009058100009502402c015031050b0781c009202a620b88984002c101c50000c01c0c1c00407140c1c2c44801c402c00e4101020041da13445d5140c00103522034000d40403031a8640252400002ca0742080300094101030347d01640b4519250144081004c1d5402000707065511040610803540161a0400284041401501001480f91071440c0081c1b4144d070007098030141d44c0058003880011a0 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 783393381 1250 783392131 783392143
    0x70e18060f07171302090711010506030a240906020a020708070b0f1b030c010203010311090703060b19211409030a020705040b03030d06180c0504050d030c030207120309090c03050405 80
    0x3d81c241104644442192240200604101135480700d40706090000c7d90f45c01c41c5d41903a90400e418001d01c82c6580c2c0008041c3c071b41025401c05018540c02c9564050003a440500e2520342c2c0b0241c810005001c0030350344902c000c03078100524600c05644041001d100d404402c02c1090014480f66036514604050000c10410900452a4120710300d14403240800d8190014415544141d0304d00300219180e603582e040c10b85441c10f24000060040d05000d01040115129008100954040c0707015980b074034020a8050110740c02081a08040110240c003000c0b51000c4450313049412880301070089600302d00b40846104550f000b600c80c1a007640200283e8010a401142550444000301d130009410442030020908501c2041c00651a940c50702c9000b003200d000085d14148103d076401d40c01c00440e178061000ba074541c4203c0c0502d50313200f10200c1d030120000e07100e6030100008a10038415260761940d50144400c00012069044020a5003241c0c10300c120811341c41035005d100c44500c2d082c03000d410f094907121f445074 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 783394631 1250 783393381 783393407
    0x4060515033301080f3d0b1e2b020d0903020109110105070b040b0a1d0a03121107030c0512040602100c0e031e070e18060f07 55
    0xc101000099680c60300c40d60419003101c200c80e000da00102a40d032016003580311400041d0100c1c0018020405119a0b54556441050031068200466503000019000c0b0015a00e580808111290010910f010f0075040d5400805440442a448a11950340581c1506060b50b14a81418041c410700c01c00a9048081c0c2039517003924044050003a4a092080e80a80319144070240058140b00074542090f0341540b045c00203c1c01010240300034451800110f42511a00001501d400e80440105000c01c01d808100383d00500b1000c030000790400c0306e00c0382d40700c1240d905005800c1d0780c0080480350103042e00440b4504140c02d0b499020010304031003103210407660040c55030250810110100640402c0000c009411071030f441c0140d16500d560ba80c3c08000d654202c10920341071890b04003010260828046e0b402e80c402204001d01a18242c1000d00d02c0407120b0040c0c2e048a07065220390f036000140002c00481d064010714102c6c58151540c00e10b00d01440c5021000b50040c0b0804c03003940204140d6030fa11650384a460 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 783395881 1250 783394631 783394669
    0xc03080411030a0212060603070e09101806061203080c1e0702010e0910090b0405070503040212031e0918060307050f120115030b090f0c0609041e050106030605040605 73
    0x452180c00c04a0718100803e8802500208050100f10104600240300c40c45034200310b0458480d9600c550307210140481c1501d150740503510280b0401071020054000c1c1c041c01c806403015450f580316684500c42503817200c0d8403200e9030b9040240f2503414503900c018201d600421600880f49003003c040e1000c6405c00d43d2400f462079603100440c620b801c580c400e110390105514001c1c00f43c541c0e81400028242c3c054014414510305500c0c2074010f0305181080d0240c42c7c4500c82039150b45041d41c0e82d54003484240040994040d100d800108112040048a070109110044003000300741d031165101c0060000c1c0030206504585c6460740c4004000503550005002c109443d000d4820f110811020408121540041e8420498950a203041824440c0000c240681240d006941e1014613407034a0341031540714441e21a1100c155004282d1015180c1498001840800405440001c6122400d003411000c201d440010504068840004214141e4180580c1000c0d05045504003c85840c202c0090340080c081d10800352a = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 783397131 1250 783395881 783395903
    0x120503160e060c0d0503010f080c0a052e030c0f051204080f04030822050d030e04050408120f180c0616050f120406030f060608063007080106060c030804 67
    0x40382c0b50344042c2c3c0c1052210504807107444000c008003030510380090042100420b410032002404401c00224021400c6003c2c5c0480035a60801013444804204d0360070200090100c01c1c1c6c0080e07000010b45a2058107042c5650024950400f911b00501a140510f070441c2005828044040c1001c00500f030b0f5504075600c490a9565018040d20203445402103a0002e4911540440e640343c2145d0380456040a034207020040220301d903201c40400502140504d03002d0000703450141c04403281d080c01d0340700b84c3d0810700980078242018850303114a41d1002e402ca40c034400a0303c0d51024400044140c6c0f8551040c80c40c0d050103001448040c001003403843c001d0920b5000402c0d5050105001d000084c40510b1a107411603040d03035808540302c4401101c40c0d0091180c03000003407516020b510403c1c0703d48501c1040c5ca17000d50350082d40d81c5560082012070400d81602c20000000d188a00001f82e84190b0800e00e201281d030301404440e480d0a0003182100d220381c1c0050700740600c0008490000c1c0e803242c60507620550001c0e480304 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 783398381 1250 783397131 783397157
    0xd060b1804150b1314091006030b010b0706061a0a0305010e0c0909040f020a080d0809010507080105010507050c091306060909051c0201090c09020301031101030e0c01050d021608030412050316 84
    0x1a0401c0070702c0e40c078412514100c10211099480c006480c446c10260044800940e00080d50600700c41c141e101c00f17402c100c00c4200500c28201008000c1003428014803003c03e865494660b07040c0034041d021a02120020f000400100003a01030082900406030055410f0b19864074400070b510501c00c2d82c5145104400c2c03940098104410301c00140f40780c07600540100d287c191544407250703560706a020500041800d00000030020001401154402e603003650340c0c074516904e4800192001d820110301102e403070099200005030b07034448100d8184504c54085111107030b80704d2401d00c0c2040310907580250841c83c7c249110b41d0041140010408005000740715058181c04c54500b08a00400c03c241d40103200c03101980c2d0014449025030003460590713000b84200700c5004140c100550454040030104d882681200c252202c096000320080c101d04001d504015207010380c406c503124040b030b92000d01198082804400d200501480680030303204001182826881c40c01d14110440b200508407094400704003009002c00 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 783399631 1250 783398381 783398389
    0x180c2a030c0c0e01080609030712111507031a1207140a09090302030a030f050912030c040b03130b0903120c030c040e0f01090e210d0b0d060b1804150b 66
    0x1100c1e05401001442846403500c00455400c402885036481a12a081c045910304401004442e403c0360f105a581c04a10341e000810341d502840107408000703078050b40c0000003090741c0c040307070583c0301c0d907a59035001030300900100d0f003401c140702c050300c85e14000c200c413002c0400f0300640040c2141c26600402400070300800075400040c0c40004940160401d81c0c1041c6000c800c060300040a003404446544092000c0c000945c4210216a800c48003442d859004090000c0c100b81c810004607003100c80240c03003031b02c0d050b02c43d4200d0205605c161444996051407012580900000c203d55517048605000650b00d850040002840030500c05405002000740c000003155980300e28104880080c4001401c2070503e1411a04052015009100d14484e00d8188407111009140124035028000513210014280704c5a40c40b000d00785821007a900c00c1c1065880004030b41c69610548000e20a510a00000c19508026000d102c100381540340303028001400103082c44002203981e204e64102d6070f100d5400054021140c0b0000d = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 783400881 1250 783399631 783399647
    0x90b03011803080417210604020427051b07140703020d0312111611040617160506030402060a0305091501180b060f161b180c2a03 57
    0x903001c0c0c1d0454104040401d6000074034548142e004111480e0b0300140d4207200007140c401c14110341d94081ca40c0080d010510701048081350007032000780005080c142c9500c020b80c00e08185121112040c501c0c3e07141d11820354070350b014041c0d0080c00003480c10241e840b9502c500042c0d0203a020000e00d400086505800001c40410545000316002052541c20700042c2c14060a91203046005100441c1005242c91442c45084101d032541c0c02c10141101208100f03441ea084400600740c40181d009844090000b40740c0c56201807640e80c00c0c0314401500c900761f050164014040e2590388030a0080314184200f20240e40d61000b41c0b00301d1006414045059520030050604045486164600307400c83e41001040d03c10418029034440300a54030108480a02e1800f0000240680a18016003040070402e4513001c407400d0380040e008038420a42d100d03c0322203181c0e410002582580002850198041c0d11800b08c00c20707802609000006414031031070358406004804002c4960b00c0244a0310381b10641e441c403c041c170842da0 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 783402131 1250 783400881 783400901
    0x9010e010c0302041e06120b0301020f07050c19050603010924030c060f08040f060b010c06141e1614091c020103150b0304121e090f120804090b0301 65
    0x82000740d8585030054003d4009010380c100708114004000014080d49407840151b41c450f4403240c0340003650382c000e000a40561142c01b07401d95024000a1300c0c103c0c081c0b001d40b544512400203400c4070340007001440400c00d91401540214684400e04001917103649040300d055a250140100b20700344c2405543c0903607840a02031401140751f05c10000103001c05110b0802c06ea41c081d980720704115208034821038038070409480140c001c4206142500005000b61b202c00d180c04410b06140e0583c1c0701986030031b01101c1030a9410001c000840081215171504010750341d5110641d45454450780c1007050249000b6100300c0301010500c4408050000ca43d0f0342c000a954039500c0007842e00d45103516000f6550300f40d100c544000ca001c40d081030554049200c1101511054841078060702e07046682c2c58480310781428034079003620248540040303c0000c40510807190f000910362501c4003803c03d03142210300b03586900180e0041c840f04100c0c200050000c0c043c01b08940449142020103c0c0364410100002d00403c40c0d50b103 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 783403381 1250 783402131 783402133
    0x8070c080c06040b1906080c10030b3604030509010818030d091a0103120e01090306020c0102120105031c1103090916110d0906050a1106011403300309010e 68
    0x204002c1040b000110007403084c44420317205026541c2944402082d00c40034042e02415030420024014131f42001d842d1840c1e2008a4580400d009510f00d020030200400d2407091034004920b100b00c0001c010950304038440e03011000084003110704d020b490050542c02842d102a04005044c00410f0409031040c076a04000f444a00641e82c0c2c0b800030301c074080024080c3d1682129405100d08420000580d00d0f0710300e6040701e070018170340c0820920001080b12545028146c80b03050040060011021407070b24800b822031143c140c0001030382ca0b48000492a40c130354050303012038800e034041d00c0c4c5200e404120080c0c03655400c5003400d01c040f07900107801c0c020b425402246201a00300e00f03034000300706031403000000c0c44203200c460fa00e415140a040c0240c10362039200341000507020079034860040091520800c014005117000d413600743c1a000b14900c250782132003401e07440381d07139010400c0120741c40a16080c40f008903c603003042e40c0c01e069645404d0368056030840401074142c2c2031030040002401c502d820b40000702c040340c0c108 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 783404631 1250 783403381 783403393
    0x1090f1d01020c16122303030406091a010614090a0503030307030615050702030a03120905120309010b0402090f061b010c2f0601051c1a061503040308070c080c 70
    0x44000303030007900440007002d902c0c812001c200d204402c2064080080d03410190414a0350b29241d103496913525140f0301c805020301d01131180000c608001f03201442c000c070700c207c10120754885c4905102109000c98036103804039580220040002c0342d0002150900f1a503c00521a1034031024000104104480e03440690980400400c01c54a2a45036000c0801d49500c070107286081401c3c1c41089801d8080d03a14001d4059100020460104e4014010301d4a1a5800304011403080d105a070395905007400c00c3c81c0403070122401700c2806410407081c010000c0f403540c180c2e070071410007030004009811040c00f400568080d0100003444640c4c0104401c080300d9801207200240101103202e00700030b10749010508202d1120700b0a48504040f13000700300000c03d804d00508000e01d03450f428207040010320120981ca012a0b42c401c00300e50000a25030b0300c0e05d20a000006620043c0e1407401009214040090b5151500080010030800c40000e0700711020b1038010b0f0307103407a01300c20156039454840850700c550104411144140 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 783405881 1250 783404631 783404681
    0xa021e16030b010e010605040b0906030a110d1506181205010b0a0e060406270e0c0a060206090705040c09030f081606090210030501120b1b03090607031b0801090f 71
    0x1421419049030800300031000e443e03a0746c0c4411102d5004500503080c2c03440c801c2101c80340c44d2034204007131034110546660004410400c41003113282ca621842d100501640c0307074500000708106140194004081c5c03400c100040101c4030182c1c1e0f50a0800340210045503404102000900809601c0181c0c0e5800240c0b1000e1410789803508460110402c030385262046003440404500d000c0310301000c04c1c4d02c0380e1b01c604182c0700c4080c0c0303181e82010b003849110780703002d0b84100c04c16050103903640d4036850000d0a194003e419a82010002d213400c0000320342020b0f0281c0d081c83d809048950340503446a089030703000408511032500d1494014018402c104085c0070264490b408601407001d15405460081c1c402c035003480c0c25000c0d00c0c0e400e9090718000d1080035010801c111000011448034410aa80085508400250545041c44481c020b0f002030b0741e01c02540d44802c080103d1300360940b099200f84c0820382d01404036030b00c80450003000d0301c00500481e2040d545506090300445480d4218940e0b001044520420100d80 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 783407131 1250 783405881 783405893
    0xc061a031231030b01060203070206030411010c061802040615080c0d02091504261b13050703050f070305042006120408130506190e0a030b070207060906050a021e1603 73
    0x80c003042c0d03070004140e0700001b0050f00010803509100e07805801d15040d03036103940300d408080ca0710310311903410b0004e8030518200083c11751180c07081628120708511040b0207507005000c01c4668507004003180300e061944d800d8210f500031202e1355000003050103203075540580f080c5000190095030702c501e0f00215a034801000c10004000a001030b245406101341a00c902034de41440d003102c04210001c42074200aa240c150884044136440c00b40b4405800c81c516010b258604004503001110701600182d0303140180011035004506054108089160500603411f054940182e01c0e030040b01c3d114240040810800d029840e0b8105540e0700540340c1034001c007a8600343c100307980c281c1d0044a40c0062501051008513891400d07005840081e81c030f40056815a140002c01035a404034619003c560003882c00300000300094100514031b00c103d005502034504140b4000c0c024003084100d41095041c002e042c010f80d10710b00d50003c0c009400e003205072408442e01c2a009440c600b0b28600112400030000d00190100500003 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 783408381 1250 783407131 783407227
    0x91b07050717070303030f200903010617010e0c0d050601120f0614091002040b07060207021c0503040603050709080a230102041205070501141206060405100c061a0312 73
    0x20182d18280042103e0a894404944030024410300f23005007a604441c0d5040c00101030080120302a000203405500d94000c4189921426080710030750b910341d1100c83e074503441400005500c2d4425a0801c3d5041e095585240d103070700d814016054040c070459074810521150100c02000b0380d412400c10800340030042058141c000c03007143d00e0000e03881000c81d0356105000d2882142c04443c10219a2424403409943c0c0700302030342c401d0300300707991007000600082030448905d403d01c544540315500455455181c0803001e0181c800040c080c400b40095490308224204000c074521a1240d803021441d90135040040411009000d040d51010f4158070106011900c0800203c0c0380c07407214040c02c102c0700c055a5541c01166000724240152120300c2040c809809094070300c0303030b13080e80100c0002c0645082076211004118601030240307010000a81000710041030289522800480425081c408802c50f521140402d0799140c1905107120b880c0c000044d4002241044c113240402c400d6421403600401e1072007600034460348 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 783409631 1250 783408381 783408383
    0x6030f060c21111b16080c031e070b0f0c160b070303020a17011d010806010311010f230d0b10051e13060e01170f0411190e0114091b070507170703 64
    0x5d218a48089800c0000240084800400400501d031210425100c120007082d003118904175440340c0000032403804200e10240c03446064600e2610745401c2000b508a2400500c10200300c0a60303080c0c042070180480d1403040301d03540303600341c180035030380d042c0034007003110300381c8006110f80c0c00f007807800e000820540610103138a042604c1c03241c00100350740d03240c2e102151034100a1000030601410300c038100c80294003c0782c0869103c0b00c1ca007032454841194607040800700800104020b940000051149842103030b81c81403a51250003514455a007400c2c00c880581140b02d41043c0040c510800f4162400d4401e001c01182d0f0314140340c02020034180c0c0d480902801c119454559603010421000003111100c60004a0034414401d1005005032500c498592071201441d00c1c0c141a0130030150400c01000000707420100c0014a00e9074854640f5602d40399410b4162150360310424480d0035130a0510115288001d07541c4120581501d82507070314406407030031030300d8941c0d10780c041106c000ba54803034142e0030040030a80784112 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 783410881 1250 783409631 783409663
    0x801021905090f0d03020a0501060308030f0a0b030d27090b040c021501050d0804031a0114030c0a05090603031204030c02102a110406030f060c21111b 66
    0x144000d2038251424003501190303940000001c0902c50386841c00c03848142105009006441c9600705c1611114292010342d0000e43eaa400c000040c000f42400028615074031407568001080301118500020b6115010680e6020402000030300b1070750710301c41d44c124015201000104581030761b0760b40c00e4480007074049140d50f14421480c202e084501c550010880c813002d20701c0600158100d07803c040030010005045142980c41c9a81804007000082c004a41d03107156040000d6021031640c903060030b0a03046000c5580440c000e4001100907034035a01c1c0c407003040c815641c0444622110340c1e14030740820f1030760140040003843e19071400c1c140b109164001400b1002180203940b05603003003241c1a03042d10a9800280301c1c050b14446c8482c81640d091180b03540c110003502c15070b001d880c40b068150019003035078042d400944000705004030403000c20260b842114544649400e01d04e20719101b100c8011203034455106502005500c0300c01150301036040c4001c864900c0414204564481c80941c00c255451101c0c130b080d0045 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 783412131 1250 783410881 783410917
    0x110715110d181205010f02031e24061e070c0608010815061905043e0703050c150109020405191a21250c15050c070c080102 54
    0x4951181070140b003000711840e620300d01c00b440c016088820445480059400d5541c404144064040fa4002140900038050806103d40d00c025180e80e4a4603000e03003004161000e003100c5605250001102c81c4040004491840d15108a0b001805c2c440c1c40700d0862450500f40020001c0400c41141c2000054030155510503001e40c1c1c0701c0412590300c01030a210748100c4003090000a0480c5080782d2124130b000f005c0800d02c81c41c20795500100302039540491480010500c080d060220b00c01440301040010f0b815040030b200790842d80c1c03034201a07902c1200c10150400030000360006500400304001c0c0c2c410400800b00800030745c0c0d5a5007880003500180a100d00ca00000608490744203040da20a4041d0360007031a01071070308d4102128a103425404002849a1242c1c0c0001102901200c0100341c3d100e0700e403821225144041034601c240000c00c01e0041901406031664030440131440c4051702d0001d804a0b040009a2920b8141d801000d41c01401d80003092041e00d14000300d484c840c1034003d06440c1300c14200d5250 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 783413381 1250 783412131 783412153
    0xe010f06020601140303030f04061e20160b131b050a050301020a020705010e0f1807020606090103051914030a031a0a05010e04020304111003020304020f01170711071511 74
    0x48043c10300f04c0e06501d98018404a516070210308050ba82041c8950301c005211301d10340d000e0810b43d00c101c03990f064559a076803900c00104151a400d51040340b070201a404e1400c0308940480d81c02500104000d0300f56042c0780e0014101500b611003440b81680c01c1118202d00850410484142c80864064a400341070020000510f90405000ba5120319005e600640050760130840115044004024107551044180c649018540c40c4c8034804000701094807515050b6280641c0040e2030120090070441c00340e015240100040303100031407008152854a0420b158a8040d03042140310a181402c40c0390140c040007031900034454142e40101081c5010a0404a01d00340700c504004840d89544905804110050b04658140c64250300070b5030302910804005d0702461605000c1010b40381c120428001082d40001400154946030004806180c002d18011005541d0b014901003903204c0074089005000e109a054288101c0038049071000d003162030708801c0c00380c0d00404c2c010168003500c03a012045018108003a1 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 783414631 1250 783413381 783413399
    0x210050703050d0c090f03080904140403050d11040914060112050c090103020903010e1204210f06090f02060f0d060b03041212020412061406030604050715090e010f06020601 76
    0x2034845901038841e00c0c10300c10080c460001a00c0044102c0041200c00440410441c00c620382c0c440155025078256522161914284000c1310301201034060000840b03000c000019038001c0c02c4881c1c091004a011541700512890118240119001801001d0628400018449000c0c8115100310030980e41c00c7d035801c051006000c1110310076a12580000020403560308a035000380c00520003028060000075544501d0102c0a051000020841c0c0d41e4040c005001c1001030404040c214510b80c0012023032842c00c0c60350380d0380b084101340c2c250002d1029890302e013600184040441d9031290030313402038a03483c1c3e05c4c41200401d40459100c4000e02004a1400303001254151000042d01c0c455540003c0202014190400940307891400d943d01402041c0c08010200b00700d02d40c1c003104403890744552408600000810280110329000410490007940440c0801010410000f9008120b50074a074081034a070719030701c104680d00103c035000300181c1d10041c000012000009000142215203036800c2c0c4020346d072500800 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 783415881 1250 783414631 783414637
    0x70506070f081b040305160614040e06010806060904061403071a07080f040b0c16080d080a0f020c060c0306040b15030c030c07050d02010f2003011202030109020d0609021005 76
    0x15074005080e080000c1c04280e8407610103010300c4500c1182c42d0400f540d03030380c80c80c0ca4590340c49810344041d0701140d010000244c124621450b50baa070320741040e00f041d0604201c0c1d0554a001001141004400c501281407601c4841c01c030f880d0250003900c10f0100c01d40b501c5c414510841c3c5480d01600911505600042ca2142421945036040e020342c455803401159442d00c03801604000c804140200b41003100046a004420003004608448400351400e4161036804894016107039020203d146c000024551100d5031110400c0da020b0482a40016054140c0310300c000240140c100c1c25404c0d1080b0414030140d0392114002d0b5206120459007808280062400d1003941440700c03079000520b2509002080c09888902c01465010709021145401c102058030f5042c54501403401c0750b00580d54480c0c0042c5031007554050700c40900c1058181824000c20170500301903d02c0144100355070401150072400443d6020342107100d24a800801800046200c4e0418000a20480c0004c078860046c01c040c0c450654094019 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 783417131 1250 783415881 783415907
    0x13060806041704230316150311161a0702010908120915010303080711070b0706020906090a031b1413051302060c0d0801090b100c060608010c0507050607 67
    0x3514081e1030700e41d1500350281c4070010010072184240404100c05a13200080c104902045014100d00c240d071a090504150143c540a242c448801400b0710003928a50341c0c0d050765000c2231130002031407041c40c1c401946900032517002c4607180094501403c10310102224000d080311840e41c0d481061b0f00e840c0c40690803a108402c1c014092a81482324807500049450310551090000b400d4502e40f5180074001c00c00c14009030001c4020031125014030140683c02807c40032184110401050418100b24440c00c41c0c2c040c60500500d225000140f0032103540341e0300c0541e01e510001810705550b0701e4030b81c40c02010113aa0380340c0703405180c0c1c2c0310030001401d01410001f0071780414018120700780e00006d0403c0a409458014000107940c08a02c4201c001a09d60b000140400240d80307010f050441160702004124141c181c2c82484501e007050b902044c035507600312402c0920f09150401c00d116031801c4c5012406081c07540d11442465107058210701506400100810681d031141c0140c46003a03071000360540d001200400 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 783418381 1250 783417131 783417133
    0x11e050412051e0a0c050f01060602030f0708040f06021c140435060604060b040321090305070e0601030506041e20030a1a030d020606101b0b010302130608 68
    0x8040e40c601c6002d10010700040c50403a1082c20024a00c9000c090709600a028040005102d00c00e00350074040309020751800d4440143c000c0c040e032031070200d000755207005a500c141d560480011b20482044000812100100480c080c01c041080d03548802079103400a0450f8558412900103003ca03415112341420b40f910b07464101e06605080c200005802d1110801010012544503a096403882160380c0680c0e80281010310020415860444207000a5a1041c1e0003036000c4102031000340002000701080503249840d52012071025014034004469a629a0740050014040e0740300226448041040a512540c1e00f031300c041c046a10b40c101440102c0c0d41b20450300515400b807485405554030700c1c1d00080e001201c080c040506001c0c0040280a607a40240c440403400741d506c0e03201c8840c00040312030100300d4040032000741410810117000a52200d400505451261090741403454003140120817001200741d02c0701004130b00b940b803807400421104013804245c0c4a9030344040804c01c048102d00958040e500014 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 783419631 1250 783418381 783418403
    0x10e0709030f02010c200a062d1b05030414150711031f050a05010501020d0c03080606120f101a070b130f150c030204051e21011e0504 59
    0x20710389000c2c82c030400c0d10403410440c100c1015008140c0f0001c61010780013600c2481080c00c4030708020080c031191540d0055090004043ca04440989886001c0540410152840d080d8111500342101c1c2e48920407566005000f0054144081c030a00201402c16511b60403200c1c0748002c6814104040d092800260304014401084400b00180251440d030020721406000c41e0000b07480918030341001821002801011a603031410031010101e00c0c020940102800c3c0050082441d00c108000e10b6108801000380a0140c003c010079002d4071404115040340f440304090301e040341030104641b0010f480603900b040e55609040800b048040e09810140c3d0400e1146500340d15060142d5030b0007900d110001c101c0c4105940a00c80b000c0460340840110000c1840740d00f07840c0201800040200884a0400d1038034209807041c44180300744e44400c021001700c0b00700b140001500c1416040012080c005008080d82d000100c0442c1d542c0043c8150028900c4107450425696103528030007541c0c040314400c880190074001e40c4 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 783420881 1250 783419631 783419633
    0x309020d120212161511070f110607080a3b0604051c230606010c150c091503050c090103092a0603051302030709020d021b0c030105010e070903 63
    0xd003052006038a80d005480c0d40503882100b003581e5030880c4d02d851580d04c950f03200d0142045020241400d11400c0814200809203220f07100c40710500680340000c040300d580c1294002803106143d5042002400107292580d034401601e00b111040d0040c015150100c1e1a5110080320803252880e501100001e402e610a84082e02e4441c0c2040d401114110580040c410040446c840c0c50b0259028140900c800106401d00a41d1070701e00542058020041c000305104000c658841002180385078002d4405d10300031100054078107081c00e00d80c40030914421811701d400c070410910b07a08940340300101d8070f40c0c035004103103241651016425a5002c4507102d80d18142040790080e150300991260401a000e40e094142030071910f8404e071103068402418058204e03a0403420003d40b645806456440058421380a160078619400700344da44245015010006401080d046c1d01c560080d810b44196012411141d906d0503030000a06440f44005c200940c000e50800002042d0341c050301b1901030081c00c45540c1c031b868181c55 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 783422131 1250 783420881 783420893
    0x702150a080a1d030f0406170705040303120b0405090a030906020102070506060d2102033609070e0a0b0c0609010c0f050306010c0c0806060a06091406070c0302040203130b070309020d 80
    0x14410a10810314101d210700c5039101c020009400c170b100e005280140c0c1d481c02d041008d082107000d600344080603114001007040d15580842540c0c1126414204108005003c00417400134004e503204040e0410304d030100300b140d5a4000070b00c2e01001c038005d89030000c2542c1c40b000d00724240c1c402c80301d014140740d02120110302e003414942901040c1a0095080203002c000e05c20640040000043e090f1005034030109074000f81103e82e061702840005c801e280305001c0c0d483d82041d051a048040001840741070010300041c100c90140302803040010000348a0703041c15441e0b0051402ca9002599000d41d076129010004508120520504501d22070a40300c105008007240760403100c0740e1005008a040080c4140f0782e0300098ad4001c20320000d00240d4002d44a940f40400906c0010440ea40c00b4400700010241e0030026480801a0060085001c1c0c40242d80d4103030a04050755030300015840290840d01c0041003000e149010385009121030b00c90311102c0d03c02d44441e80220240c45100c407000e540025551740080009070 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 783423381 1250 783422131 783422141
    0xb01030c050a17090a06021b0105010b0702090c0a120f0f20040302090c0d0501060e090a1e0b060f0309010504020a080d0e04020d09120f180b030a0e0f01050703020702150a080a 77
    0x214000031170308040881d0303031494244e8114030003a00000384c1da42c0e181c6500b007900380509070240c9003000c41903051031015000105d000601910300b2810b2000014000c41007440303010941000030031284280170102d8124042002003808014442d00300c3d1604060618403094510161154080d004c4040e0805041d6020081100c1000c1d12480b04110100301d040b550000750701a1500030802900e0350f0000002a109000d400032004202e12030b010726200b00c2942100454100401b5004503160016140b20803001003003240c03103030090606800c4004020042c072441c0542125120f20300c00e48031a401c480c0d6585940c0c0e610308020300c108021450044608031282825030107270142441c01c100101d00d4103010340306c1c001c4291002c440c0b20006043c01040044198001001e6500c1105036400109014a0718001a101780006405071420070f071500e000b0071501d90b007080303020042100c40000b00014141f030b11001d4029404000d08a0003010300d820640a41e295500550304905003035200c6454035075610000302c0c0208 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 783424631 1250 783423381 783423391
    0x9061303060e07150203070302150903160c0501090503031201030f06090b04151a2407080a0f021014040b180d080906060a08070e07050f0307030b01030c050a17 70
    0xa850140000100384540141d082180d205006001e0311800c00d24022203040b80380c08108150b5000700a5500081d900068120740c41a0300d1815a0154880500a90546c40f40c000003050160305c0c1d0300702d031050002011b20030381114001d8854030399a9685006041e00e038098401484807035518403004101080fa00d0402980451050070002604c12950b90740001510041c1c4080c2e400c0b000c6850000100c200a120740c400d8000b10030500c6c060742a5007400102d2224060751851140c0d40610501c01c08051003070169112260b00c5000c040e1107401c030500041600c18248001c10040c0f0460602d02010001c0e071003240c04991075181d03c030300e0b036a0b03803034039203c1c8140406868030074038a490643d840010a020700240ca000c600c03550300c005450401412083c0b40072005806144150307001082004540c0c0001401012281902d50045450b56500d6055526001e86d03111541c540034008208105a0b505500001c2d521074240c1b001c0180307050100c01280c1b02e00965615001145a406448040b0704480c0b8000d503102d = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 783425881 1250 783424631 783424657
    0x203030a051306090b0402040b060c100f0213060f090e01031a090c0301240806010803071b030204060e07020f070806011206060b0406091a03070f050901110a120e010c080906 76
    0xb1107407580d400003140c000c2c0703c080c0e481101c0030003404118900350148468209080f54940c3c00e00811035030440d11031003d0350340d80703a106d42d4a0340540301140d559015141c4018520056200b99980c580015200c069420a503500041000c140865540041c42c1c1b000e045c0d81e004445105100b000020101460310094440d40c0c1500c6007031b40e00c5009030b8090003a001c0d8203055805009501244a00c0c403c1035100070b8219198541010b0b006006ca0312000055a10740f581050702600100d81d54002043c00c0411740e00083c0d089400c0c05808110301c5480d800e1580142010b6003113555118000c8000ca0725054640281c40481d04038100401c406c10704001302803452400f81400142c00c65031241082420b40c03181d8403040c0498041d881c100600e40c0b6880700b03605040450003440389545070001000b400140d4036040701c410301001241c4100f0076445490a00d5000915504071041c84180b82001009a940c00c8403c100050944400c002c5651081402441440d805108181890480b0003044029005403031600c000c = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 783427131 1250 783425881 783425911
    0x1020322050309090403020c0a060219030c0f060501090203071407020d0209100b1201080f0d080705180d11030f0a11040f0b0607080a080109020f030622020a2a030203030a05 76
    0x100d07a900700130103000750f2280d00200b040580385000d00036403031001d50281c001e542191301314200705102c07103500d40921030341840c080318004024039048000381d10088016140a02d84000800c80340d0265004502551b0583c6520030a041c0002200d000ea20500313500941200000c000d000050803e0b007110741c0c010401d808040c20312522034480440c02d4001469060000e04003c00402084a040c807036007030300c5121007005e0013100c07801c3e40025041e07182c0600040d0401a0000302103420f1014a44102d8800400810010914000c1d05103201c000d0500555030f4070078050010804406d00c4001410810564040380303401540c08100c04100080080ca82404401d64980d4000e40103569400005c0c20710b01c1c4209012034552481400080c80000c05820581c1d0182c0b04100e51100c0b481c4030015294001000c485503041016038043e02c440041c0c1009020742e805000ac580c031b0641c2500310814500c5040402c64520301c10b03082c00b0342c861031080204000340258204001080d2841c91a4000580c810425941150 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 783428381 1250 783427131 783427147
    0xd11090606090d050618010c050a110c04050708150f01021905070801150807080606090103110409021009050f0402163003050106020607030c021b0d02150c0f010203220503 75
    0x4040003d15004549a0b0403400821100044c120b2911501c1b1035040d00070030034034000d01e601418920400307100d0002e1010b1460007000e510300400011034000c07000380041c0706070b060528004d0101403040d0b134a48000728940704d64650310300701080381d803600c443d05a00820010104a001e4031003012941801c0d1650b0003000f0001c1441d038000d000305202c3c10b111808030400140b402c8a26800c000b1641c000b06881d811860a2242c02e40c1d40c5d41e00103040d2504051080e216184040008006100f400030003500207040744503150150360403540d01021100d040d074251130800b500c0420070080340f00314401d44016820000c2110042044c1c009403070746809400d064501c681c0900e2000104440b103110396a400252114014486150b05203c5a0b42240540c10180082c0840c5e40f00a501c5209404501401c01c03603242c1c11400c280e403402e00003244150050000400321200080c4040203902480c0300c0d001522840404140315141482280e10420403420302401a17056002d81405204418100351801e01c41449011 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 783429631 1250 783428381 783428389
    0xd1a190b130b1801020d09080705100c0b0a0501140a0503120f0403060603320d2615040c180b0d090203060a050603011505060f0c160b04140d1109060609 67
    0x12030320040c01ca03a60f07808401c141c4002481c2151480c0480100584200e0401403481c0001d00300061322030440d904480314443c8002207801c1c0454040c0034190860340014000500420b074080f03416605103206880708a40d0f2001806102500b9104a903010391007480000003009503203000c2c00700c114112803042d00d040d9a0f92150b100346d840c1500b050390000c1f03a89110802d602e000e51241070441c038000da2010451448145040d4a80704600c081e801405007003240c0e482e0401c281000c45001807c403481503812800e00180100300120000e08040c040c40c500350358540011b024881800701c806408424040c0541001080c0c044c5401c07001640e1482070310b0304150801a40c040c400c5da88641241d0b4400601c078507000c0c0405094880010400d2208003501c241400240c445004480c003140d901e5200302e94440d0908401d44c41c0844683c0d01d0b05040c00803201c08203050103e60000c008980c403a100846014040c07004000486100b541c0003860101046c800582134105411125800b0b8030051519080500d120041 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 783430881 1250 783429631 783429637
    0x41a070302030f220201081008150412020708071202010519080907150c02092a070c050102120a0315050a0f06030e0604020f0108090307080d1a190b130b 67
    0x201203500441000640303451a4096580541340c4000540c11240b00707100c9000350480c64502030f04011424001611155400a0030790013401c015048030500030510f61800f42074072080e6011903540228400c0c0003000c81c030020700082540d440710080e1440a20f002000e01d4000740311a070480c1401000d002e1400741c048002010a511441d5880b040d4a80c1340100169041121903045034164182c42c050011079168415004c3c038113950306840c2e809407502c2c0c00d4100103003245407880321511031b003400d0010904602e2217000b07400030a00c0f40c15645106a1200016601c5032604010201400003c0c003100020610a0704419004c15044232403a40c52134496006c242419035540184420070405a0700300701d83ea40c1845000c55200418002d030070181000d900049034110780c03800c0b5032704104090700861151072040c42240c0303029a2201c000b940d43c0b24200d801ca009010558640e200c81200740269403200d0400103d080101384911560b00041402d008100d0002c1e00408070009201c05034400c08580f0850030001 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 783432131 1250 783430881 783430891
    0x30a08040201030b222007050312163e0d02120319110c060403120e03090a0e090a0221061e0103060207020402250b0901020a1403041a 59
    0x15180945418000076041d98040d00700079000340c1c1c0b024800b1081c103c80c059290610b0b00b0240340480c449151015220121080100e9400d40f65000a01002001000001418144404581000c2603030720307070809903c0d00600b4284040400c1c1c140d15800c0440c426404882034541d04d000c092824040a000b591811002946142910340c0c042d0995819482d01002424603c0d4803900c2024074500d4040345034151402c80041740550541c0343ca0080300501d404806446400403100b04617030142c138040c2401002805020702002c40d00e4501881c0c2c0c0c13200400807003160303440030700504164010b03454a40e408000d4007004048460030700074660f0800050392003420100703202c0307400c40040340c0000ca00452241025005400c02c50030184100e900c0d009410500180c504480d08428010f8803904a0b00101d4043e100c0c015903100f02540c102c4040507d0031201c900d0700141409800c0305401555402c5841d402c0340f05602107480031030307011101000703140d500f20001c6500a21818104411176102c0d0148042e4110943c2c0d = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 783433381 1250 783432131 783432137
    0x5130b07020625022104030f0b0618011212092d0b0703090e07020c0a15020114071b151e05060d03080105090604090c0b0405030c03060f0621030a 64
    0x2003072106a01c610883e81d04030b01c0c845184040c14007000030000e9950804a003250070400d070b00310100c0c2c5045201a00361001141c001040d40000300c4c843c50066415901260854850449407444808a00c1e0302e10080e0f040c1e840d0074801b1070008030306031600c40e8040c4d0341c03050050404c011100086070f00d50029807101c550002c03003403000181d540a0149400700c2d00c0d00c4c0d0000c80209005100d91801b003a030114030103080307174a05281d00e9070645914038120b042041000c010b5800140c84440060459420606c0004d1420180c0c020441d05511600c0200c03d403100303840150006510503600701034a400c8100e005505881803054a039a0110b60488500b528035009012640420960717580c03c0440890090a5010404a4143c10070400079600984690010302589010b074000708001800c0303850b0351703004075001c0b50010040783c80955640101d80055000b401413a0190040421034410f500300014030f1405103490103a62207038ad54a1606200000e0182c1c206034031b00c5405000c034510b80c0e660510060488401c81d503 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 783434631 1250 783433381 783433393
    0xf031803050304112d0f0109050d0812042301061a0c07150504030218070903080d0f06030602090a0b1215010234120507060302130f090c03050603070e06010305130b0702 74
    0x83c2840c1e8500901c040c0c5d0901076202800355048a0b0f03400b20003407060310408c6803c284c0f082c01504200905001e000e040f480c0801c2c00310240024005041c2c11034031007070540f54586243d00122040d0320300361086440f5903040c00d01341080e4103481c82034807030242408508a5044426513581c0707480d0740307444c41c80b9802e07180081100090203000b5403e00054980d68100c0c5100c0008250910000040c6046190b109c003401180c07011450042e17401054200340361440c0e150800380405502c0f824080020f5001a046921441c980724000500d103101c4019542000d800e002e40200b03ea8810340250003a00107030000b1070460246400038002100c5da0513440032800030041c000c14400e41031400709528100c154006022000b4a458940d000a5000a40c01c0c180c82e072501d0096100c0c2011505606524400e4125401c1c108803000c0c0410a12540d520107000944d0390340d010721030780d11408141f58480a083c018030580c1d40341240024050b5006e5044982c101d8200c0041162513010358840042c034a106460040040e0009 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 783435881 1250 783434631 783434689
    0x1f0e01110306040e070819030e181005030721110a120201030c14032a0a0302030a15150c03140c150603160501140c01110a0f03180305030411 62
    0x910134a1031481401e4010b04816040c503810310344c2c1d01c04c4084000701d4071125100e18410544285841220280044c02000405403103520040360b5038000c5406034045a043c131000100f91800040300800c8a03c108040b40791015620758a403d002c0d040c04090b100d88d00d44040d4840191500a2a0b10042c41e040d684c1d91111403d501c001030544941c5100d40f401c228451300c0a0381d26a011804980d0002909101041c80300440c01412a021034013200003090b0320f00c08202e841c0c103a505030700107602c1200d54200420082d0020800ea410010301d5001d02d21a41441c2c44090500d03500a80c54281550302a00305140c101103e0382c80104d455200800840c010b400200c0c22082036440e2076002e03904020101d000e0030301a040c0c518043d14480a03841418100412903103031003114809101110080b058a800034441c042490700103403900d9001e60b501e0400190044d060089281c402e1003200e4000308161644030100149480807942604003070015680e50346c0c1942d108000c0e0351412010b280000d09000f110944480c0d03 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 783437131 1250 783435881 783435889
    0x1e2601120605060306010b0f07020a03120e1f140a02030d0207030905010f030e12090d050d0c0b0c0403050705060306040f0903020105190204050a060804140a0b04020a06111f0e01110306 81
    0xc050503c6000343c1c0504010b2010403c03030811354550b52078042c602e50f222902070002604019041c1d001421a11024070408805648450002c2003103a040d9583c0440c0410380480f4040840c6185410001584200201c91603440000003482400350510481c0e060681c0f0084003070803030344180d80880c007083d802c0004010658112074802600b500c07600b03040041d040510318081e12410725040c0340c04880c5c00080e0740c440300d42e07403584140d180941200440341d600b111f0340c401501ca050005403d803a4000a20002460900031504031000d0b03e82c0000904003040c42c00007808203581014002550007500c0e0194980102c04074403502140321700a50001c00c050909042909040500250008881e030041000b0710607502c4010001086500a1810040d20740c0e0314186515011008081030384640074524030103081c0101814410700a9008503242001c05546a8042d622070882c1c0d0a26040b5820003040d41c15102008136290704104500d80021400d41545000e050844505102208140c0c10200c180140c0d070074 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 783438381 1250 783437131 783437141
    0x3160b070611090a29220b03073510050f0103020708040302130209030f010b0f0a1d18030d020c010b0d0c12020a0906080d020d1e26011206 61
    0x1600350016282c4035105000c24a4405a80074424103090f21810f88540d20314019112601c00e0108000e0030389500c0300b48010f18590702c0b0401d907001500000340000c6841d0040804070b0b4015030b27094070f03460303100070300e10381e4550000d806107142d00c810881c02254a031413810303842162440b5030303001800c2c000140d0404081041c19030f400501c02d0b041601c10300c2a54002000b41084600780ca0b0100c41c0605c10400115076000a031240841c0140c2600801c1c1c00d0044242054102c603155190440300400c44503000810702c0000c41c0c1a1041c0300019400b00ca410080c1035803030000030703084848111020400440c220b04145940d0001700131403c091fa000035014800c0d403080c0700e1441041401c807584816985c168407600c0d507809070703801044038140d40044200c0031543c502c2c2c42c0ca00208010801400080d594a400d19101c0e6403030008080940202c810414406224055a00c60190780c17001201902d120f90745c003224201070400901d44441d00e129201102400c03010344c814020034034080fa10034516044c1c50200c050754 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 783439631 1250 783438381 783438401
    0x5120108032106040204090213080d0302031905070e040204060e13050702030a12020c070905192906040f0e070f0e0901060f0e091f05011103090d0203160b0706 70
    0x81c00078015a4102070303010740841c10360360b00c01c021604261036520006000380b04651210300c10038800124860403a00b011010703811201d0650a680188000d1001a07040e0700c000c581c01c044490300340c4028140010075902440d0030070807503e044150b04212501180072a40190000c50100d58a4080308502e0325100c200034a100c0c00d0b200040c02941000c84000e0340d00e000391024042841014100c40403196201c1d070503114886820705c100c50405541d40c000390000d180c15580000a80c22510031145040300c9405466252040901c040380c10074074203056440341c41c60422855622203400c0000013074040d5102402400360150b4040d00c1c0c0c0608140c2800b9040000d121403c0c1d05101020340003079120344e00c0c1051203045136510300380300000c01d904007000c80d0030b555184000c5600002035010300c0703072100070b014800440031522445072003c1502d980054a0020700c03125890b141c3c0d4410001288142070145484038014070140403034544014104e41c240000804d90081d4006000c003183c0041409054080e041180b = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 783440881 1250 783439631 783439633
    0xd111617010f0e1b120d1103070b01090501051203072d06060305100e070e0c0d29130b03060402190e0405010218100e040e030c16090f02040605030f09010f0c05120108 73
    0x361441040e041e190081b150f5000d0502c442010301040c0340f40d040c800c44041507400081d40c0e4040d82c44180c1c0600905081c090380c0e010703030001d19000b64240e600004498106400c004c1c0282080c401456000012840380201500c401406942500140030b5020345c902a500c0f941c040e102504440c1c400c88100c0e070b419400d0078101e0780510410003800203105509900488114150b079640c3c480c01e003c420180c00d008905600000b14541d003c0c1503000110722000c6040d20440351600c2c26803c00340001d09035260191025410380101c4040703001032070041d01c072405140301740c5200c035105580d5082c12585000110380640300d036500090480001d003040c4131000c180718030445805044400b0319030001c10580d82c0c4044d280c02540c0d5042c5030f0f11048070030019a0081039071803003101c001c20241040840030711014418642c10b00d060000102d080c107000d0081c0c800b40c8046941e01425a950790b403441341400b402a048400a541e980c03e4a200c001c00b5010710003040b10b813600e0702940d855003e8401c03401510305078028196 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 783442131 1250 783440881 783440899
    0xd110c0409020a03031419020c0906040c120e0c0a03030801141906030507020a05070f0302010801090501140d06020c1605121b01050a0318050d111617010f0e1b 70
    0x59403003103e1082565090b161170102d0380d11007407040f0807900c1140303440440ca280c4401d00440c850760009865034054000d4031001d080c0d4039280e0501055420710544200400d408411542d400e8259501581d000080f01048411610099002c6802170700b00760015000a131a41005000100700e03542d21040c0e41605940486105c08010b019200c1c840807070051104054442002ca04128800c01c040e00c82a5081401d60354015a503001200c02401688000c0f4049080c41d0000900c81099101da54100d6850300920188120b03020208150580d00c1641214a80d81c2849001c1000000f08428603c007101c04809040c072500b8441008600c580c9102c10700d20315848000310300740220503c0001b14841100303080940e200e00c00b800e002d80140650031080e0101035100d41800c0188031000850503031111194581050360322080c07500640740c5a01c4004640c50403241e82041000305040d503d003112010100e400003851100d1400b444003510a1002000c00310790100c21280345001c2003280e04203a0400495001407 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 783443381 1250 783442131 783442133
    0x5010216080d0f0c0b01080c030f03040503071401050f0309010f0605090405070b1305360c0304021509060d0b12032502041409010e06060604051815030d110c0409 71
    0x603031402c2d185201010840302c1c0100706411801410303100c1d000c0c0e51010051142c3d40c1c444007400c4e642c91601c000f0030f21078232807101200c900c98004001c5800340c801c058007900c601410204080203204003001c009040044c00c02401408100c80b60203035024034030324000455443c005138206001e1383c04603000184684030352030600000400000740442202e80b1080740c0c03502c8030090782c5000140d91040c3c0c0440e800c44103200c94072010082254105000314611000c80402d01100c490f9245085402c6070038201000b01000840c1c003618103100211901c542d201c00092034608010040b4070180c00100708898001e031500106045807800e40340b50082001c0902c015814034004005880c210900159010010643e1040700015034540e03030804403a000da103509008503070405406003802010500c1c80702c0d42c94001c0750701090043c50000304070341c21200004c140c4480d0003120009030800f20805820701192511072300300103099403003c4c01500b00d22031160b2a00b091044c40d40203400e0500680d5080144500e281a00e40c0c0 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 783444631 1250 783443381 783443383
    0x9021311030a0902012102030109061502030a0e0d020a080f1509070b0d0f0c0801031e0b060f280807080a0320010213030804080c181305031c060501021608 68
    0x30303a00c1445228003240c1c4400e2800146e81c2841c001c84410f00482101d11010482a240e400441c100c80103482e040003030a42e602e1003d4000d0030781903000030040e0401c1044c0e0b207841c0c0c8904006008800000d003d11a100c101d40d00140900085a000003240d8005e00301c0080e0614081c01002d00180c020241c1007002e140400c0030300c0e02d601d00ca005413158a10b011801480601950303112441c000c0e2007020403c1a10380380d0340050300502c000d10080fa2450540d403400f1014400800141c002140d001440100230f440e41e200b0001d80000781056103400682c200c1088407000c0b1141c00e1031241803100e000e400c507110709001e00c07a410004150000851544600100000298043c8403e5005c8800b02940d042406a034900b150181c414040666a500b1401c1c00100510854030024411910500100d40c40d030b0007080c06101c4046200c1e10243e000c0110140019180303072803c8108840907100b05c0c103982c5010358800e445070308000d80440c00131800c0c1d41c0c1d8030f060000b942c04103c0c5100d800708003050318042e07514203d0b0075 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 783445881 1250 783444631 783444637
    0x70302061e13060215060a1511060702030301031202010209030c06030c1903021909050607080310080601060e040c030b010c020f0301090204050a06060212070f030e12010f0509011107050c0f01051201060309021311 93
    0x1040e11008c222004909040c8150710351301c1c4c040c41300e0302911050f0030642c43c002e59076042808203840b00c002d07812065480b140140f00300c40510b0b4000d400f6010100300c8c8000c201035500002c0002c680b0b90000c000c109400c1c008403c16003010a0191001621038501c001ca681d00d82000303c00200c24454010b0040c000e55690a082c0c0e40c0c02940003298650ba40c0c0c48811002d8103030805e40c80002d4512561b000481d005420640b81000d0180c25202000034031688a000c5054130043d546650109204085010160a08001c0b1211107107010740003046203201980850111001103c448151a50740c0101740400d0341d0501c041c1507511305842545082201c2c5489004101b407103000010700707010010940c90401c0c3c64000304d110006003000e008204007410b45d02c001019280071201aa02946001c0c410b07036081c01040203640320349811900501c40d040c103807410b111004540a8007103041c044244282040c92600c28202d84c043c2c5010354010620840e5031052094054505c425010500d0a0102d900c544d00100416 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 783447131 1250 783445881 783445889
    0x90d1a0a0921020f06010b03250509010c1106160606080106030201140d11031312050f040b220803070302010b0105030408031609080102180909030408070302061e13060215060a 77
    0x32002d149160100305a240c1411500189494000e110002840701e01ca41c024501c29141203100f0544111005140464210300c144000c0c0400c00c00d0043d44e00c0380d4856a20030403040d10401030750721030481800000322103410107c03580484080854a0760200001c074000c50b001070841e00024030420382035078000780c02c3c100d00410b4043c82728404580ca805400e1981c10525441c10340785012541d0342400c21002d040501c1c01c07402902c0e100e080c0f0000d09400740c8114100e404104145e4660303418182010700c550388950020300c0400d145a002c2005021142020701d100c00141003546c0190755641c035a26000c0e00791403540e154541403100a00422000c107844c0c404599100046410034864444603400c01e503180034481d08001001c3d072001c91683d9170700300350700124003906104881110140c2d840a0440e0743e41d2041d409000c9540d00326000400c01402d148025000016661050301122110940c9040e020307000204484182c1c000040308100c002e40520400942000410070203034a031800300046401503003e07103d = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 783448381 1250 783447131 783447173
    0x1406090c031e04080a17010b0901210e0309100c03080402041116050c010e030c130e120f0a0801060e0a140301020c01061706090d1202090105090d1a0a09 67
    0x80001d03452144004071400318503990039414903d040c182060052a0000841040459080c00701a01c0c000c074030034a043c2c101c2c0c400104892a101e051030046a03031007001e4030801407910070076840c511001b4941c024910b41444c180e00541e15601c1080411090070702201e8a8400c0c060541040c4010030741c05649654800e806507000b017a1404000d9a0303482a208609c0c035040c0036034054441504100340070a0080004a090343d0703900548082d4010141c031080c01079a002d85c0010356281c12a03520109800c01c1424000303100a44031582e40311076501c4041d9108032440c444410000919a14030703900103106a026012900c0c260600c1180f5030045841071006001e0780c202a5101919444903540940496000080010081c03149517515510840e17604154041c44600b030080800040c1d080303034002460a00c011860391140308825000d0740c01e4000354006000241046410801d84d00c83c0d40781c9a01980c0c01780d1060422001403541961140d040d0140940980403107828012502d02140b09080d20460360083c43c5 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 783449631 1250 783448381 783448387
    0x30f170112080c0d0c0b100503150402010c02090a0c0219051509070902070c08070b0a1d0607240b060f0a0513030f210201020304020d031214010b07061406090c 70
    0x10400c0c4203a0f015503c941e40e140c1c4200c61000004581c00000700b0000c6124507407005035a15042d1264880241902805030503500c03221081d4909043c046203203800a0040c18414510b83c025000b00790b4412045528039407544d114408100d980360f04121b068240000d04c1b5013001510241e84c0c40c6901e54045000401c407802c0c034140401d0400c0c105110410050441940c215919229071400c1c5041080c6446104030134051820002030f984d45038000c480003801e882d620803100d12082a116040550000d149030303003084080c020320f03001628107c080807114450541130928010700c161003005075200d01c1a081c6c040ea400f03100c14103001c1205030658403103000900f481030b218016445d4000b42c02d0802c1d40041c005d040340403a404140320b042801551401c0d414800c82d0f40c1407035000d10613400e030b10043e1030094124912103407000c080707803160584019071ba10316840450b000c0034024080211398401c0c4c00c10304050348002207881c10004244241e001e0f048400350744400c01c1c606880060801c41c1d0040c1a5074082d2000 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 783450881 1250 783449631 783449633
    0x100f0908030a1701120b1f030f110909120f0a0c050d03140f01030c05130e06151009151103040807060f1409031b030a0f0807030f170112 60
    0x604200000e8603160044a803603100904008029044480c0800350221540001090700d0302041080c81d06541c210308001c0c0390303031039100f00418118204072030041c5400c140c00001c80045c6d05003201018450103240c9030f2202c3d00d030500812400b6440902070180c1c95024046641800b041c000980c1c2da00c244644071142c452201d0001a62841c2d01c84d50010701c607000c1c038462514555096409521518800018001c080e0b4400d00001004030081c000034200302c3c9076034408c002d1f44ca440301611981007140ea1010401d0000c05c06850319117a01500c100d080811440f4804006050907044076001002030b241100300315242441454080840c0c40740700c0304201e052114030410b920104100c078000c144030400c60302c0c0c0c03035030301c40340101121846096540007641a0160410502114064488010f0003c0183c140401c1c3c20801c03001c440304401d481a018002c048211010481034640c42961318098403006940d45401d00d0014502c1c02d84082071401d20a0b55880040241b1498001c40c2c15a039641d0012040d075201 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 783452131 1250 783450881 783450887
    0x13061b020a080a091a1e03040c050402160b16110a0f061a06040305010b090c0703120504020111011104090c0f020d0e0303040b0d090311070501140d14040b10060c02100f 74
    0x100b5080138850b00a07504403207100c60304050051a03030340c440c02d4411b00310502003000c00500d0700c0b090b54098031903081032106002c4c600d401d80c0200080078164107040e035070a005564004402c40200c800240e203405640300380d9441500080d01c1201111000007401d840003081ea18840c9510741200040c00c0b15950f01040c00740d51101c0c202880407806c1c0103182d262103070b80c0c0c1d1503c18064900041d0840c0514950400318401a103001c0a0b10107459051700c0c0c404c581054901c20030010180240180c0c10405507118103e1641400e01c645900b204400c003800f5a00d50821030200e0980d00c0c0d100d119800c01c078401c0d9458803000e50115081c2c0514445141003072500a14400103440c50086070015014120000358400880d2002e611640d500740c4680c40c0c2d84020100c8000442d202c1d44648981808940c0c0761580c800c1060809004040d050f13420180028522040005249401e00444041700d4001d009000c0c80040301c0d2a034040c20091005261410240c282076010421a405039101350051044462201c0c00c2c880c0 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 783453237 1106 783452131 783452147
    0x60c190e01051b0c0a0902070501180c030b0a020c101b032c01090615031b0501020d0804030c020330130b07080705030313061b020a080a 60
    0x283e501e00b1080a08281c0d0010900740c094800e41c0d446079a142c441c003401401c55103a00689413051860032030b00311498110260001c506213480b00000850500440f0240c03a404912684241c80e02101c8102034001c034941d8940f00d0154151002070910a0352241c5031315203881920395605c000c0d82c0740c10f400300e507507618801c0c041b00915407002445004601c413890350002c0103800040e220445888810031182d01c402030700303010010032004209100b810809440c02c6c4898103a00304541d407503c0e0001c0e55541701d240a683c01d00c02c4100024013454000c40641301c0c01c503006402d03500c0403c003501100107501d0b00040b400040000c66503079210a100d40301d09454010f580c01d840318012600308084101c01e50041c80c030443e0120030810645000800c1071000d540182402e2040e088803e00502c0d09406955100e10011090a00c0c0c00000b60b40d00c0d8005511079420b5001041a0348ea05400c500444640b1 = true := by decide +kernel

theorem cover : BRFrame.Cov 783273381 783453237 := by
  have h0 := BRFrame.cov_init 783273381
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783273381 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783273381 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783273381 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783273381 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783273381 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783273381 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783273381 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783273381 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783273381 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783273381 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783273381 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783273381 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783273381 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783273381 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783273381 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783273381 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783273381 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783273381 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783273381 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783273381 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783273381 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783273381 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783273381 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783273381 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783273381 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783273381 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783273381 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783273381 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783273381 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783273381 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783273381 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783273381 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783273381 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783273381 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783273381 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783273381 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783273381 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783273381 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783273381 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783273381 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783273381 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783273381 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783273381 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783273381 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783273381 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783273381 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783273381 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783273381 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783273381 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783273381 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783273381 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783273381 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783273381 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783273381 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783273381 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783273381 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783273381 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783273381 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783273381 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783273381 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783273381 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783273381 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783273381 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783273381 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783273381 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783273381 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783273381 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783273381 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783273381 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783273381 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783273381 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783273381 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783273381 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783273381 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783273381 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783273381 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783273381 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783273381 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783273381 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783273381 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783273381 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783273381 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783273381 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783273381 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783273381 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783273381 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783273381 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783273381 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783273381 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783273381 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783273381 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783273381 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783273381 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783273381 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783273381 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783273381 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783273381 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783273381 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783273381 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783273381 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783273381 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783273381 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783273381 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783273381 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783273381 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783273381 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783273381 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783273381 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783273381 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783273381 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783273381 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783273381 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783273381 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783273381 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783273381 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783273381 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783273381 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783273381 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783273381 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783273381 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783273381 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783273381 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783273381 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783273381 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783273381 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783273381 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783273381 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783273381 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783273381 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783273381 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783273381 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783273381 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783273381 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783273381 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783273381 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783273381 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783273381 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783273381 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783273381 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783273381 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783273381 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783273381 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783273381 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783273381 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 783273381 ≤ n) (h2 : n < 783453237) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
