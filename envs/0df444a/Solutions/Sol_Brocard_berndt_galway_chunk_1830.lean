-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1830
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T04:49:34.287266+00:00
-- url     : https://prove2.me/submissions/6a641b69-e4bb-4889-87a3-1129b802765a

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 328956834 ≤ n < 329136690 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 328958084 1250 328956834 328956853
    0xd051507080402010e040c020c01180e010801020a170103020d020607030318050c03160311040b12010c0f110a030807050d0f02041706070c0b0420040207030e030706020106060519030914 81
    0xc00c07410280c2e1720340003030b5020010241c000600a4480c9031080071030f0304100c44688001000c4d620010340c00090b100703171000d1a04e2540d490398424000e5014441d500c0200d51055043d05d01000d0b24a01b2604032500907000030390400d070030b40c20080c15a108990403000d01d90b541c00446550280e050115540900c910300a0840c00e16a80401d483d0024941c1c4c104040f015181047c00001c14851541c11031150581d40440d8000e65800010000010480b81014947c6000c100c21645070340023004681c1c02c0c0042d11040c0d201d41c0124041d94545000b1003020700421012070201d8540c2e84100000d1158190050f000180d40007d0080d01341640d100c3e42c0600038265810390701010340001031152540211060615094094140c1d581d08984800107102a0490000d141c8840b83c4188240e4130441e40e000050045540313440500c1c0c0a1300002201c07050380e01a22840c10003144e014014403440c0c0540740c960710b0b80c500384200f45142450f117840d107601d00c804040d203c08c0140b00044a05010880b0b0b0060745019205060 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 328959334 1250 328958084 328958087
    0x5040e0c070b070c0c08161502012706140705180a080d080a05090a1a06040b0a03080c0f061e0414010c120c05041503050709031b0314010504050c0d05150708040201 72
    0x10705d650001c01c15608480d906001001c078903e40d003030456602d800d40d41d6401140c10426401020502c0c140fa40071700041c840c0c0c60603003403080c00140c2d030184140c0b001c2013190300891440130101c2e0122010000b00740f0804c514811822018800c59491381e006010084182c2c4820702c550030211804d400d1004962000b0a0008a40d4035000740c95220044074001c1c80411700e241c03141c0d203c0c0c400b03a24040c0d60f2030300323903801040140d1541d170083c0c070010300040c1a510f14241e80b0301d00000c903a031017041908068042d0340740100c45d40c0c0c4041480b501604000c46180600050f01407604200c0740090002c444413044105e018160308001c0c0681007640c401c0d0707140c0580c07000a40d10140260350030321000d00d003040030410051200c0001d00e154400742030b0940c90b00003034640d918101504c40204c40c1d0000f60014000c0e904226006503070203c6401500e1083c105008444030401c8000d0030b0303403c180c500419503006601e0210b010b052110540c076495009408036401c41c8402545911703c003100781d9421000501000401044d035 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 328960584 1250 328959334 328959353
    0x40b0705100b0a06080403020102040b040b040302010f031a060c0c09090a0b01060804051c0c020411030129070201030e1c08070e01110c01030c0207050603011805010e010605040e0c070b070c 83
    0x15000810601280b03002070000b035507a84850180d581406001404541418401d6040d10302400d01040c08558aa8540032a141c40d50032911049002030200c2a55a0350b00d4806e0152100e85820720081245d440c101c5002c000b0580c0110041c1c0c5030314810741e45401000d82d180244a40a103000502801598240c1d0c00c14840e0241c0581000c0103000180080c000020f20000d2043c000101400c07c0040882840e81d0032070b0078042200c40650702906109900c40d851080c1e81c0114102c4082c2072115941024610700c04007001b1300400ca490b4804818840100554000e0700b00c040c03850041d03000e503400710304864241080300a116031848006022001003080003500007011030a041c03002d003000003034224000c90f900d80d40c19000311014101074440909d050102e000b00001d001034000107000c03d44079a1202c03c2d01e50001107440b02d6100b40e90400000182050741c200840d4184d41091707a80910340f03810b24064142006015002805054041007910081703041c1031800ba000b400155500c02c070602282c245000703d07 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 328961834 1250 328960584 328960603
    0x1090509030304030e040f06030206030405010606030507032a091205060739050c0a06020105160e03071a0708031e07030219230a02030304061107030c060f0b06040b0705 74
    0x2030740d1003007040c8000701c0c0d089259503040440440300425081510b221003006414580d200070b4010801005210400070117400103001c1e10350540d4200240e0fa80c00c20110b0640e00d155a040094075014840c15585201c18800f10a010040c0c0c1003030302c0303250398078035072600d09000307004040c0e441d5001030060001d0154444c1003001d03405100d41d880d541c1e403040080940c01c045401041144401043e00c09407003044428002001522802069500a203940c2c00c400790180408a8a071110840404080458075000c2c00b10481c20300d07000750040c0100c0381444c0940009040e0b94910040743d0a0034001000000c450340d0081d8400c52044107140d500031078404541d00c0c090b4001e4240740a040c01448440104c80c0c1e240704005804080346421b50070300451808100b03101c8040364254280e41000a40f8030340c415000002140903901c500401c00003481001d84420f5a802101c40c0180080c0e4101d0000011a006030061441600982c100003088840580000c40603805544075103075611010600806106007440138038003 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 328963084 1250 328961834 328961851
    0x50a05010501080c030603070305061e010e0906010b220b0408160302031f0b0a0e0603060112030906030b0315010f05011107030c06050f0c0a1b060302132706030803010905 75
    0xa5504200000c0d05640d002407488103a2140800040c403142da04001040086420030141d440504044062030080e04000c034184000c107628000016081000c003400714460804100a41416402e0906a0f0451b80c020b0601100c41d200c907103281c14042955020100080c4000311000707035100d24000a29040010325500d585085044403001c0015880200f440002c403000340e000c22129841d0410440002c1c02c45a041c550014420301e0b0100d84603002c2e0225034007500c4220101c4851340e9032901c10000400b4800c00c0200040c0c00581c0c100140d9000313411050700d40f06e0050941c1e000000c804026107040c03800364031450303050180b9201003240c1e507084900c040c0b0003111301c2c015220721821611400c510117000c0c4a000200304d80041c0720741070001000c040d180445a50001d60b0380d48049820212000800750040901c0c1c2000d4070030002d4000d00038800c0b214200c600f07070829004a407601006ca11010151409030f20b40d528600e4071490007d03c03601c500006144106581903c9504020590007100c4d4020319085 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 328964334 1250 328963084 328963091
    0x1109060310020d110d060303230412080904360f02090a11030f07030b010305010321050c010e0307051903080a09020d021c12210504140a1203050a 64
    0x40a9280480d101021803406003001d03030342e10740e80c454081c010300302064071988404020505d028902502e400200c2101d01a5403040142015640c4101c10349080100646080e80104410002a03401c44040b851440c021242c0c08d052041d20f00129050b243c44041c8940440f00c3c5000030340360380e00501e80000c1c0c0000107202c2e502d05681240d4452411141c80c51019220b11500c10006542e60318a82014020394030140b071070780d00c0b41411140c006185000340c46d0400801d08065040105520a119042c1200d4018401d8600c0450141071450503010001d40c032000c104c001c01001141420901490203030a02c05802180d41c2c0140e41880e42c02e0580e5041c004076614039109040c030201e6406801950080c0054500040c0d0044c1407001a40c22103020340000e40149156100307101034210550002c40d42c43c01540f412505100460b0f0071079000a10b03c0004604e48107100c81c8404900403948030340d510030310401114100f0000703141401c1c40c000c180039007140d500c84800c0d045d00401e9070601a10b5041460b1079000e1 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 328965584 1250 328964334 328964341
    0x206040b0706050a060602370210020a1a13080d09060213060e0312030612010e010603030509091503280209010e012c0103030f05120a02190203030408090d0314030903071109 76
    0xc1c80d548d8810912486861800341240b07580880043d0058501d0b64000c0c0580010240f29101a4031603031010b0b426144080950003d403400071030800c025102e01c40c0f015900b80d00600c0d5035580c910b00d070056603c082066544601a03c002039080c0300412000d20080b10f0001304924200000f003c04808808072030287c0c1245102960414154003a40d8011408490850140a01c001d000d401420b103022300c1480e941c01e21318000140740c0c01000400c481071003655504015034818102e051103410307582c2a10b800d684503e0b0644003824121900c10f4004601c284094010302ca15000500b80324000e0300701c001001608401005100c210076083d81c80e0354960306202c0a0001012107040c0c0c1e01c0300500c0054140b11507001c441c0c0d45e66125600310782d08610a051188968101042c0b04d000940040b0071818800c03084c2403441c0f1255000000303584c4181c3d445240075241c42200310500a0409190b9401c60600c0b1450610616040480b40518070039005540210748481d01410041004075080d40054002e4280c01d050 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 328966834 1250 328965584 328965613
    0xc030b060412080c03070c06090504230c04050d0c0602010c1b081b0d08010501020f03090d02130605060c0a020901060f0210051f09020409060e070c0b040206040b0706050a060602 78
    0x80d1011140684481d040c010302d2810400040e216441014445000002d0740348200900080000160740c0300340d50303820055403140c09000c1180d5540342c40c8072800745c4019100304070285415800e940071205005050030a5515404181c45101d0000100e5540030f4140061010a03824030aa0018038014030348007188444010060450094940e4003400340c550000c0c8101c01d005e030000d8141c0031284440c003140c020512200005001c50408e014060050180c41400004550000b0548940c038000600741102888590308124000c0d0790240d000c44201d4031000c000415680744d0001d06031240001c0c000d007040140c41d104104240304160460800d0020640b030502d00168001102c03035001c4161040090551940c047c0a0505140ca144042050f1075200010541c280745401510455004040600990352107440d145c0c1d10702401c036022400141e00030382800c00b01e561111410b40140c0050300c030038902500c920101e00ca0b90f0200c070043d692184c4a8003801381d1100319105042c01802540301414000000314070 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 328968084 1250 328966834 328966837
    0x2030c03010e040201030b060c010b03120a0e0f0a080a05250f180603020909030a170108030f0a03090b010b1803070e060618091e0703020901050901030507021e0606040c030b06 77
    0x1542c010910070340c002011a4007039030101009102c0100fa9944544400301d401f4060901d01c80c0c0d0038002d0042083c00b428941e11042034031040369440d203c0c010090b5a08040c00b003603c06820681d43d0103041030500240219040c0004410203002d900078281c03106a2100d11010503009402581c02c0a140031410410b0107488107a140a0390b000c104201881d00da0400c801c4003901c0603130000f0758000e413100240503010000100600c40031900d601c5e0396100800100c0c003800e40d40c00901c5003001d281c2042001011105100008004031101800d00054400c41d644603014050401d8011141d0060006580c070729a0740600320ba8401c08800318002c1c001c03c1e0406001211030300000d00b10744d0007203a01190440c0909514002e640101d40041d082d141a4500020041082d81003600708410344030b004070101d003c8600c28000c0740c01541060311180d24095880c00114018a402010303141180507506030b0300c5852900f40c104c24140400b600c004d0819003001d4080004407051094440d060502c0d00b8408880c640307906d0f0 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 328969334 1250 328968084 328968089
    0x90b0708070501060e1b04030506040b0612010c020109031409030d03050a1d060414070332031308060a180f03140307080103060605090105010215090715090801050a02030c0301 77
    0x501619010645003111039400740140080c40c81d400c0580208602c01d043c19039500c103041a0b109017201c100c038100e041085104500000d4900d4000344001404215880c43d602e0b000312019120b442482400312019013100c0b020342030800140d45520141d014035034000c141c4507018807400d907039601e828070080000e5034809043c100c26051689800010f406c0c011541d003e40008000381c48074041d08403505800c9903c4540440341220107603000000010384002c005400340540354007200b110060700b100b0640902a80d080001340d900240002009402e5510901c041c0889001c0c0d554001c0e18142030034641390400c0341c020a101c04c80c0780703040b5038100c6c1000e015407a80c20040e00040a41d43c0c80c4a1801c2c129103010581124884580000061048903580400c0050491f401041c00301f041540350f2003005810301c800c1c4030baa40164041c0c04250300301900c8a42c0b49800c0f4894400f02c8400c0c2da42e07a42440412030b04d50030b041c004a1101343d401c01041e102809055408001c0440445c51807805801c501d0301c500060 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 328970584 1250 328969334 328969349
    0x50915090c0c030a0c23060a18020a03121e09120203190c030b0109090b06130905120a0908010b0a06050a02030f04090b010201230a0b01051c0212010f03020109 70
    0x300c01180d6024090811202100c402da0190307a500e0b0348080000d45001003001c011281900300841c0351070f000143d100c001c00d0b92401741001d85015101e580540010305004004000c41c09205010040180e0b55a40503100451103181080030100003210060508240182d40c00c07400c2075242500086142d0102180081e5190782c0750102001c03035540042498000365401e01204192882c6114003440040c581d00012241300d00b0140c00a1703030700c410b1540c2c20b13121320700340003030141a40b04042091480c0c031071400d24143c4550800043c0059150b1200c0e8640074003501d10354048200003420000c000c1c0d2041a0783c01a00c0c80b10000e003c0c00400f04046000400c5034444c003c20804081070f0310b98824420710407500149000041c1d280c072140c441544100a08006602c40d026600c0e015000b0180094248180444c81c03190b840e80c130195403002c1c00000504410302e06036042010030041003030745400c11910403c1c0f44045010058440000003010981554107800404407030112040402c0142e074010b00c158181c8096 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 328971834 1250 328970584 328970599
    0xb1201031e020a270614030f1c050306040f06150e09100902031b0a020129011403090c0904080c0d09081209043201050411040b07020d140105010e01050915 68
    0x40680c1d81c6513002c2c01a100d440306040100c00686105100b40f41000140c08605407122100d9007207405554110000e5408100c107645e5104207082030081003d103500c050081d0000c21441c40940501c1e00f1034509401c040c009141c1c917802181943c0c1d001a031640d82420a40d680045410204084810a40b99210748034074940c0000c002205546001d03100380c400c0b45030490303464940040d007001a000e40407201c0b80c4c1c640103215105c240340398644441e80741001181070f143c1070424401d07441200c07461b5000074092803851040b511780445544458000510850090402c0c1c5c0c0c40d034015034909818590154010300400ca860380b01404190004106e82640317030300628990303a0310b102e94000301d00501681c07240c541c000302ca007001e600440075408081210140b2589030301181682c813001004101d600010003128241403e0009100c680401002001382600040c4100c440e0482d56079440e50906001c455920942d455400412000000440c0035015000445402c20646072058000110655560440340b00b584c0 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 328973084 1250 328971834 328971869
    0x40209040204090b070509180106080a0b0102031c050402090105040908030a1a120a030f03050c0a140f0c0a0302010507020109030c0605071e0e01110a1703040c0b1201031e020a 77
    0xb550790014403416130043c0e000071a40350600c409000e03501b0a5450740d02480c00c0b90700d101c41800c00c8074005416240316498028054880401c000c0c007e00a00b010707541507100400c4400c1b004914401008520415101c001c00d081c54140b052000741c0c101a0700450045007031035030341000200001c0036a079000c011000d00240030300301142c520b043d4030403040c2407942024400601468801c0086100072485010341c68545044004410032000c40e081207804080410707050143d007507880d01c1a910b503014030251050182c140005a1041152503100102c004810f0713100318130315010580c081c096181e000107140001c20800c16142c4014105210404000b0522556900004e0350140140010081108140000315013502c51001c06490010b807030100d1030100e0003a14146441080c005001a1386944c4203001d01030440e82b00070b402c2c1d00e5070000b410460310384080b800042203003242c1c41c000d003107603900241e8100b10651645c140008070034400075100103040c0c5115001e5001d6112030250703000b1600a0812054600d0 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 328974334 1250 328973084 328973089
    0x30510024305030405150a02011404050607030e011e061502011107020f01032904110408070905060a0815010513020712050a03090209040f11010206010f0e1e0a060e10030b0402090402 80
    0x711342d80260b0b80c00600d181e4600c0b41c640140c40540100166600204144590102d1540e11444221030080996202070009441325200e908040e10003101c17030300007180100320944003c07030b250f005c2d81621208aa07905810000c1c030031100700464102c81c41d40000c03c407400d0720940f03145c907920580002a018101c11b480d14400c6034800d134400d0f1034504070800440e01a68611051034000d088403031540348201e0608004c07c0c800b0900f0001c5604a61103807009082d242e15043d542130150400034100c5a004403940350000d000300080c0000f40402907a4001140303103604110401482080c507803082d91600b8414041c2900081410001d4008100103040007911542e519200f2405400c00010003500821100140070400041601609041c0e2146030154040b08112004988c0d881091046100307050303640900b00301c070b00c881c1d0f11240d40000449201100001100542d402c2c452810354661019960307036035080007075a520380b0a10f604100da0451003d070492031070302c400b543c0345009080a449135000902207011035 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 328975584 1250 328974334 328974337
    0x2010318050102070c1a3c03040c06090603051e0a0f020c3d050705040e0411010e060901090b16021206010611010507171003051002430503 61
    0x1079124000390f50301d94561520144075801c0c0c0c421034094429a070b01c800e0000e0740c480709031a45008644480c074494089862688202440d02405101c1650f100000402005210000354411405540d84c00c111a02c2c024000b860b00306240d119004041c40c00c4184404d4000301e40d01c0580341240d0f40c0d0785001c1601c8403240c1400910841c9032001c6580d200040c0c09402071808148600800707140744c0d100000c81c855030140031001b02c03d0311a030840d05814015040c00d1400560245030811180c1c5016800d0035101c110140400e0f10964043c1c0b02e840440d07124a42542e440903a000d4880f905882d0740d0b08144018001030440c4080d0302030b07003518050210341c141c261122700380030740712440e0028070300c51680c1e400501164581c2403c0c02030701e00007403030b40b003660107010814000c040c00b03a46241d49900a20b0818150945800806001c1c800c0da094111030000104404000034a1a49480701c001a070307600020035510f089650031020140088280c155482050100c10035000c00c40b0900b500540f8002c40a1130840c1c2107 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 328976834 1250 328975584 328975631
    0x41103030309160b040609030818030613050c18150105090a090903080109051b07110409050d020c0a0806010e0907270b031b0609060705011d061008060103020103 71
    0x520020003004400b000006070030101d80a034002c0c1040f403a8594800105510035070041c100407982c00002000000c541000400c104040981c2c00300e480c031140d50002e400c00809681c0362042810710390845090010038495400d500c00700b165400c4c0d00d030f0810b040716068020300900d14514603500c0e000c12031659008400301c40c0b50710b1004100c922000d0300c1c0c04c400c07002020305070030941c0001c48160001c510900303988500790040d0040c041000030f41640c0d440c4119103a10814044500c2d4683c2000030183ba11a0701580780701607c524086d21080341c0c280343c000c0c900b00c159078500d40300c0e0400030402c02000e503000c203903181034811690741e004c0a07503244400035181914070b920100403413484404500c28940042d060301015203150100f032291a107207908065403132040010400308001d40c411602002e14101d401000a000043c00d5141019202d803a0142107c816005030054003035140b100707078804002442029030108000104800382c6040485503030f610103050200905040e40c0d40e0002c000d0041a2031254031 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 328978084 1250 328976834 328976839
    0x209040b03100207060b01080c1c0603062c011103041103120d0203012c0f071b05030c010c301e0e070b0a0c02010804080c030f070302060f130b0411 65
    0x81c11001c50040096000901c16a001482c06001c60290361013071b034009005002d2007e0b46821310000151351620541d81d000c0341c0c82b9869880e00300000040207070152502191010f20000b001803484039045158101600000391a0791400d0381e4580c0344c0340400147c980064114548080614424011900d00000c4640342050090041254540b6511640003141070b6580319a1643c0e401038034048452401c81c0c040d40701103480c1c0c17207640050003a072581d400701d650091840c0f9141c0a0f5504102ca00c00c00345c0d03e40c50003504c25410003d21040b2918090203403024240c16440e0000405c3d60b4034802c89031180c0c0c0041c1c0c3c0b00c1180442202944a000c49030080c00076450454070302c00d80486c81c40c6001c0014a103185802c1d2047c0140700000401d484540280c0350448000e44a03102948000e6004443d0844000c6c0112014031081c0900b880c119030800c040c040300141004c1c496500e52607030402074500a0010481c0818141003030421001c21300c50f07401000c42c00c0e884100714090b6241c0703142859100b0800c0d4842074 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 328979334 1250 328978084 328978093
    0x10180506010f0f0902031e1f080607051c06090c1205130b010e07110106060809060907030308150102100f02120108030405012312040b0703241a1e07020a080607020a03030209040b03 79
    0x404400f6140d03448c1d0221100001c0442c060f5964007085407200350031604480452401e111400509a04a00c0c443d40c001c0d80382c1c1c00054454580812004498102040c071002403002c00a07034034040b015120305504090100499890108203585282e07038001c05008041c03040e161007011036180c0c1e0103044515100e12400c3c0082c059680c550000a000c020300f1200c001e01c1b4031403c4003159180c00d010030440196078255449000381d999050081801c0c1031008001e0341184618618903071036415504c1503180e10456840302507a140d0070310120605c11001078004d10b103660010031080103141c1e0054100101112030348a0b504e544035070030a20825074002d1004c011308502050040108120381c180480e4420182c51300c0030043c00303c5840c1107006500180c0700b101da12070049402400307440e00000c0c0400c54800070100321450720b9802c40200e1045004e50261075060200030504004500d40a50f804016002d410002c000c18900402d00950360122403d003d82496400034001d2030035211034201d014030100103030440303 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 328980584 1250 328979334 328979341
    0xc0b0a09031202090a03061a0909010204050f1f081905040605011701020a200102130f030606050121050619030b04060c03060803120910180506010f0f0902031e 70
    0x4060100d1500460000c0e0482c504a00190043d10030340e25010b1000e401c8007039203429a030b2801c1c001d02540b00c6004d14042c80d041018159541c5042c900d114030600ca0026845034a40070030310001d900c403280305a21440504440b0511050803100088100741a86441307140c81e06ca100f031000740100c44019900486090100308030610809400c80fa0403170b50500070152000c185c40d02d500c0d08034018a1121302c001a540d00702184140d000485410000d550319000602c0c100d9904105054403819500c0301200a90b42c490801c14080350f03205840c020b00b02820031103400600a80c2c452802e0342030588004c2920303603c1c030225034140c1f9820803980c8005642c03503820700040d40703d05003040c400404840c2180c10f28103009601071054843e009c1c440403038405000840c20070105020714296498004c2c80302106e807180380d032610b0a6446c10f025030981040003c00c03840c1101020306020b805d00405801c131400e840c034002c0c0100507080a148591080fa400c0520051f02c81e207880740075030540c5403000b0300c130390100c0512030a0 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 328981834 1250 328980584 328980601
    0xa0302030714070b0603100e0307060e0c04050405070315021227071d01080109080912010f1b0f080f06040b1914120708030a030b0f121605030111040b0a0c0b 69
    0xd4045d04085003242c194a034040006010740e502103001c03074102d40080c06041e0024445401a4402460680540b0a2044210089070071204112003e80d40360788562010010f20402078404400805084001c4d490300340071000709040340318003900404d405802d0039052050a2060207003815040c1400c2d06079800540d0302e45071a081013401282101c80502140000902e0038014031442c000079500007021820320340c0130400c12076420517810140301c580d522410f403481d01c102284941c100d50b00184440c1002850040300050441da030f680900002c0c401c120381070040722000c040559601050840c1c1c04241c007248030002c07c14880c07441154440d060101c03000401e10b0007005002400000f416100d400710b4803810b41d40300f0703541c000600c25400250801c10249108c00d00c80e4100b1504454060490b0203410b2001021501140005209441a0b001202e4403103403503800c040b41d9001001d08500034040300c061a003102245e4070840c800c017070140800181080b066405009515010703a0400ca15114038900f8840 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 328983084 1250 328981834 328981853
    0x10206070c0f0b1618080703081b01060b12060d0b0610140c030301080c0108070918060b0a030b03060702070b03160e060a05090a0522110c010f090c1202060a030203071407 75
    0x3901d0b40455040000710460380d031042c0090003200e40310001020300f1f902e07640b5401d4035030380b00041280c0300d110000b5102004840c01d0050b403009060042065945030324010350341c0a4030340c02400183c4101c901e81098070209580c1201c0e95001101110060103002010340c0030398807081f4540940c001c03803102290004032900c001c0080d60480c0d02074002d60b1580b42c0d00310011104418100c60302000300e6103180c42031150701c4400440c114041481207000030b042c0c3e1a400b0082103900902e00c45400241ca40405101c0d600302400315076044056400207003001403c01c1c1540f030003800001c11018154803080724500c00b140c401c1d4452400548042e2180e6568080d140b030003420759120000e1940604d500900008540c1004400b60801c481c41e0703c5810b00151004004030007034512454405565241031201c200c03180020b1198024200144200003002025894800109041c42d400010042402801c4001685405003100c8011046241c0142d40383c0d00c0c50800d681803440b0011f0144080c00c046083d00404ca21540f = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 328984334 1250 328983084 328983121
    0x806030115080a020f040504030206070305060d02090a0203180303011a0d0b0d0804090e061302010518030d090503010e0703080901121808040801050906070906030926030123010206070c0f0b 83
    0x4901156043c0941c01b441b064820071342e03000b80160302c03040016440501c40d82c071160300850000c1c41c1c4940b43c00c0d02d0300000c18204096900280042d4000705001060390750540d620355031040c2201860640d07140241411061161000c58440501d00045114503000e0035840b0f1103e04100419404080c062814140300b980c005004024103c0c1c138210318445e00020002c1c41905c40c03c1e044d02c0d2605009580d0340112020b80020950710b00100b1070f1070f1152040d503010303c5001000461a0750317400c1441d00c0c000c03c142c2518200540c1500e280c100800920101e45040105d55040c0420700781840004003449545009043c1846140200400340c075150080240d0f14009008640400d4000d0259846079a4901c0d11500195101000300341c88010401c42240690403542c0924020001852951a0400c030b09209088210017002811800401404004000c0201002c0c12108611207425080484000703513440d000034140905010b074155a240401c100f44140054250340b126a074019410404c100c200b8000310030 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 328985584 1250 328984334 328984339
    0x50f25061b09030b0601110114010602061e040b0c0304020a08030403060903080a0b0a1a0c01051006080106020d08011404230a2f0c03130b070203160b07030806030115080a02 76
    0x5030034854003034850b1000c0029280c1100d100041525000300665403c1407485036000595203900303898000c240b0b184d03070030380c02009070790042d00c114030781140d050144002aa0050341d801a44409100206000081c9968040b004480e801d541c1e03155400044c0d000032541c1e0110030a840002004010800070b600302909491080d201c2182c981c640d49800000c0d200c000da000c907045484920208a00b82d2818820001e442049043c11701c0d00c22124440d80c01d540d0112602d102c041820002002848e50128541d80182814400340000c607001040c000c00480b03044c8203030110b078142c6540b2288966241e5004010032484c0e00114850904100d40d41c0e10350000c01c40d81c40303190364604010000e14058080848040000e81c0f858650300340200d280e015510740120081c041140701c180100030700602e03180c00a5014028880255480306001d2040601e000d03820a002034881d0b000510802c2039840c803200355016980e141c00e124280c1c0e620741000ca4010012180740c02081c000c0c607080000d8109002c1100291280203 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 328986834 1250 328985584 328985621
    0x90f14011e121a10021c030605090403050d02040f060c02030c0312250209040f150b0a090f0b040203010b04091113051e040507120f0c050f2506 63
    0xaa1140542000c056010002c90380d454409000c048050b4018020080f458001a5050600001150303140c0080040318000d0380c4010f00500d4900880c0c0384165100c00189420f001d034031300b044081060450060b02c010107101010800380b409822540642d8041d01003440d103065400e985081c011700d100802c2d00300741c0c02801030080300d40d03084c113020400b205c105242003005442e0040c544c8003440c2040252140017050110303030000e00c005039240c120760350040380240c00f01040c402d464107200e4600803142c4503114500349071845141d4191503003903801d400c031900e000c40001d204c10100c0d00d445c00384c05450046940309100100101e0b90a076000c0c090401d85e191b200081014405580c540d06c0311707200d0303928500400180100108014070b4410310403c5500010740710600300b011004081801d89800351901d1012402010203401300940c5441030240400c1c0c030b42c02c148005540044003070700d0781c450115200c00c1110300080000d082e101d0000c000008441d80c00309414041401d090003401032a003040d81e641410302 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 328988084 1250 328986834 328986857
    0x1d0c01081e1017120f07080c06011202120f1c030f0f0e0c01032c0708010908120c121512030c030309151603021b03190824060a090f1401 60
    0x8000400e0305404e02c030143c2c0740385441000c1c0017101045d08080c00c2180c100d2000c0100e036540e00070038801c590082885910105448002d4810460b10501c0f012000c40c06a1200d00302e04a60b0000003000b1440307610080030f58600300ca200714202c000e055004d429408660400c4043c280000d030b240c6c8002d40b40088001a90380450100004400b0394542400781a40224100310000c9003100c2e0301c01c003c2e0010704040880d00e0f0550344610160a403840c10000352428913010881030303601d8202028860784004c0290783c503480c00182100228812801030100790551184031248110760322240301c00d01c0071400450403641c170f90850b041407070755030341c4203c0e01c45400d030043c071080b0f440c450040510b030b6015642400d05200c040415040407002908059882d4036000d1a81c0140080101c051000f040e1ba1401d0b440c07100182c4070011000f9081c47d50284c41d003c0f503460031520301d044000e44440e8421000500300c981e59605d85800000320399405068010701040c40c074030000001c800f40686200f2001f0b0b6400e132100389080c813 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 328989334 1250 328988084 328988129
    0x100c02030609030a140f0408060a1a09010302031005040c12150605060313121704050a060c020607090306110405030d090801050601020a0c030308130b0703020403020102011d0c01081e10 81
    0x24130100c0c00701103141d4110108900c200b0b00c0207014059664100c050610341d8400001d072804005a450900199486280042c0402a031000041e90141a5003010741c83d490755000c2503980501c0e41d000c00c0d429540300041003c22880000080041031082001d08900c8814140350340c8111080380c1101040303140a10001d4507061920503284a000d01700f20401d01030134952038408400300303455041030800202d0085074162094141080d1b010303a0050f801040401304034035000341240d880044402c2036610980812009940c003401d007205480e072148000c00c011403000103403861070150740c100c1d50381405100140f12107141e0106204003101d5016000303001035140d8000590311a030b8040c001900da0004070a0a00129025168064002240010000c114070342500c90807c42c0070142e406800090300000c0410070b40da42401034640e10792141918041080c2180405503807a030040c00000e041c88100800142c24038000f810080030716640916002803498585a028000b101c6800f40340041882c0d46e405c880e819 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 328990584 1250 328989334 328989337
    0x90f0f11040218010944011a010206060405101707050603040302010c0216030302120901050d090b06030c0405160305190c0801150f230c03040f0603050c0c1911100c0203060903 77
    0x585102008140030f515291303000c150b04500c4801c061442860b154180e8080400d204000c0d123100009507280445c0e049134002801c00303e01814640c440c604040a02c84112880c907400c1c0200c6148130241c0704d10000f030540c040d0400d4801e60001ba4001404010002896010340040201250540c02c0e100940184002003865104500001d0f00581c490705480044680020080981c0c03003050501c5030070594141e08000580d8900d40040305c06407200002e000700f0742001c22036911090340481b400d01c6245408000d0118040c1d401c0c0d101c1c0304158407030300880e000c0501c03043e0300d00c02480c28400034421458407480c051300c00302080c401d000c081c44440400001d024810446407114071095a603440c0c1845844c80c0e030b80c070441408401003038403030b9041000007981e1768200006d0004240c20461030041502d0001d003e0211032000300040001d203010803111104a0001c5151030840030100d8000e0600512030500204040c0e840310b0396a040a010201a28150b0b00041001c40c0e851084080b648581e40e800c0380191030303 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 328991834 1250 328990584 328990619
    0x1119051603080612030307030c02060901020406120b0105070b0109060e150105070605060303160b091e0a0f060609110c06060604050d020108040611030f1009090f0f110402180109 78
    0x400c6911014580040e120780002604400003d1810f145264100c880505541c42500c81c4008296902d200c20341c101c0d0103014041c1d0101c002d078003c50030240382c40c07130282990b103d520380080ba03e955804a2441a030240c0f0030341d01c1b0907800c003483c0812b075a1654800001022075004a00380310b0310304800200307140c41c1e900030100c0b03010b010703510941415600e60f00d15001d0f0ac406441d20364180400d02051805400303180030313079030240d001d039010f001a402c102400c1401d15105140b18204460300f101c00040200c000103040d031003981d0181d01c02407404114200038000748419004159201d00b8503860f4200034039090080d1001480300019039801c1d4440008020843c4914440d07660010317142218200958051040c3c81c3c0e1107405081d0100d401d03c1c0c500204801c603401164010801e46581042c083c00154075241d842c06409503210402c002901911400300c231404403003005207845000d1014a080000200c1854000c8002402c00d5495003071071313640003562400d45080e46d4000b0760214800a0031121041c2c42288 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 328993084 1250 328991834 328991857
    0x80a0207030c15060302030f10050609070215130c0605030403030c0e151803150108060112052d01050f33060906190513090212070e0301060801111905 66
    0x120036141d961000d000e80c3c0024003890b56299034100000150710207005c62403580c0d994001600110107000c0c0c02c030301142c00282c0035601400d446003c0069158000519292282d07205174982c60664500c0d54099140202000040001072040000102150000091030003148262418012803005000407600010350819491b40f084540044120010305800205021000302454110000075403020034a4604070003010b424080c808001004440020300c0300501405004021840940468898a6480c4415a503242c604230300c1d0451004403c03080c0e6104224007004000038062464000100b480022003260b290f80d58403c01140c030032400d00e00360130b840c4039018138800780c80c0c0302030b07101051110a4100000d8243c2000040051614100d8428403001d07021540303688665645400c3c410010341c0c00511391080c54218010310050400405040c009507220f610751404181c030038100c1c80001e0141145a01ca101654685242882d80d01d440c040101640c0781c41021a40b46807030100d004407180d1051881e17401 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 328994334 1250 328993084 328993097
    0x608190207020a35100b030a0b040615240806040b0d06090206090604140411120f1f090605120a02031902031501090b1e0a06050c10050115080a020703 66
    0xc18808403004c0303812040181c20025034400300a4800d00011450000c11016551100e40c042c0d0403012940a26030403510706070040c0001003990354400c101d00354080c0c03004165944441015156881c1d00c003041c3e00078080fa0304024504040e1406007075001011000080000b000b001c00a06d40341464040c81d116920f0280600c4170118681c0c403010000c0016110803a440700701001059071031369500300900054203c41407003481d4031515208100c104d861f0742403018507981e0306000d0076900f001e5500003940d0150030710250715020350701d480180d402710010302602c0702412100480815001340a5100406581c0140c800540030351090078069a1200a004000d40c568440300701c8149220408034005000c40c405030480c0c950089080304c0c010b040710243c000e5003945648580c034000c185046040b003d000070002074442401c0e400500400d056482600582082c0a0300141420080004121808000b203100c1d00820855842e031341e0900d0100e9007031740800f0000c0c0d03d0002148020a207442203031940c55141d00d41a = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 328995584 1250 328994334 328994339
    0x903030806030f0d0504090c0e06030c0d090503190e0315070f0e130507080a0e0304060f1106040b07020d0e03030910030e0a03030b030f0a0209061212040608190207020a 74
    0x100e031500030040c00290540200c00b074200d50010200030040401c201034585540340e40c148010042104c00800140003000703104e000d401c10546501c4100c0e60445550520295201ea10900e22800341c141c1034030080c010301c0005004500d8410813014050031402594800c0f400f40c42800c101b6940e400c40b0319244800304481404201140e02a441e40c403417090300340c02c000782e44450110010f0f006165017260000140d40310010800b5a6620426040d4414650b40040003140d1008905564030301170350080009104040904680c0c043c018a035800030404031008480462a0a03d0409100d00b02500c100e00580f040390660b622180c001d05034550a030b40058025801d01004404100750a03003141c88101c145541c03410307103031406801807180100c075070300a44011a004052390241740c0b4180c04030101400350780244050b40700584d16125031640100b070803556a0340f54681101100c0c101100262075200c006000280001e94903001034409109000f070304040d601c0404000d443c1c100ba0b11500900960060b081c1c0d009 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 328996834 1250 328995584 328995587
    0x60e040209181009050709060902070b01050927010c1701080604080304020a150e1c02150309190317010603050405030a110f121e070f06020903010b061b120a090303 72
    0x203a03100d8202c03001151a6000308480c2501201c4400a0030368454119440600c801c1c0d02d240a254000c2110200861405005845242c40641c060203001c1c0b05020031808074010000708008140c078031f00d504a0480c003c41155040364028207641d462000072a24820b1003a194905528455040715900000380403c0e039980e50701d00c0c01a6100510480c0c0c03000704d00e2000b08140132aa005c0440c040e203503840388a01c480c500c404008646001c00c11100401a10780c000100503282d00c04081c0c4421201c2c0e4215490b9111072040504008081c1d501510003496006400c0a044d0f001203050401e0615010800c280c4c0d884410440c10f4030021600a05070360700c20070260034103d20498000030740c8107002c025078003200f44036620306c2e0419240c2c80300348825440200300a141c81c2c5010711844288a0103071600d80c5016031079560000c103002140c00240007107901107a8070407107032400c0d000795646240003411595518a161800c41402c0040b40c20203006104800341c8516000d0803c04443c0995503a44900034000e1a40e5030 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 328998084 1250 328996834 328996861
    0x70503101a061303240e0c0f04050714070f020301090f1a010605030c13080105090c090901022a1501090f0e2b17070c031e0935010b04060e040209 64
    0x20096000043c05d03002e00d210f00d0551003010104500c41c8041c001d00c600a1082001800d42486c03030b82d1042c2d02d840207100c1c0150708480c00c0c040c018207003074407984c07640c0040c1003400081e5141100a5055400e00d0542c0d000c00c1102d42103140a0f41c03041d603050100f500d11000008120509004d0074001c100e0800104103c000a803015183e140303038144800304000d803921041c509483c0140e07615141944103680901e030914000840c907500c441c0d02c5c0021820642c100d1048002010718819084110202c5c5c480f040303688106010a41441c40c14044413239041d6958102e00004000240121031003510b800e40d1080450004241c04882110a0135000808000343c0710501050034007500f00c50501010450841c114600c1c411028451500c07074503200e20600c1c40c0c0c10054058009401c400700012680c0841d01d0f0410b42051076a025240d82c246040b0010000180207000308403183c0e013804d806060b8481000c50704505402050702d0003402e403070500003a0f03660b521901403004107507002540403002d4000202150403140 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 328999334 1250 328998084 328998113
    0x5010507021906021c0509100804141b1e0a05040f0204031e02090601020601080303010b030a0b030307060b01030b061305040e010b1503091923070503101a061303 71
    0x14104052410718070618007007201c843d0b0080000d1307044401c0494100e0010f401c107401400c10380c1801440e20b242c01c00020404000b5410450520801c90041020300c81400b0500c078901e18000c0c21508144c5410446480e1300d40822143d44c819000c004107106000d07103c03031440c0120040605000030392401c00b0104409008181406000c1035802c1c40b0000109084000011003121415080b01d04940c65006004d08403000503c1c050565010390010032001000208803411944411600768a90f04c510126101801c0c444c9a0305a1520001c10003009210055201c04913003013090301c00b002036244080500c10940914a44d00d110041c0703508003001141440e80041011825a40001079800140d8000903254040305540c244404404020070401040070843d40d01c00c4404e850056018624aa843d0300750310030520318080703d044c400a04c02d00140382c20403802019103402030a07100c5002c020701d1006c0c010842c68041541000c0d00c140729164038100141110900b0401c6042e0003001070464850b62443c23003002 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 329000584 1250 328999334 328999339
    0x130501020f0403030c0b0a0204081e0109120203030603070f05060708070609020612041506031707020d0209240a1a03070c082107030c08130203120d02030f01080312010501050702 78
    0x8120448241d20350400500140d0b20035101c207103208940d814a241d0281000b40a05005441088248803144000500c0c2c06400c0b00c0002541180d0201030429004d80001c00e801400000411034107035070ba0b6004000395224640c00e40485007447c1e6208200034007032905104850b0407442c10091503003c506000c004009081c09403001044400d210380c003040242c0e0105030708400005100091104100201590064041c4681818011141952123079811403200030034107a640d150018080e802c5440c0d4101c00901d071900203281c03510310b1078400002420300d104a0070380024603074144090f055a1501040607010b03102d84841448025006003802c60f81544058007200a102070a0540742c00285240e004155410340000b400d81210b508016a01c1001809025070080c1820300001c801e1039580200c1d4503034040c008500003424818240046410b045800f4024080700b40000b40c00b5150350526001503000d20706d000c60304c1095a0381d4411081d164000d10819000400b025001000b242d03100f01c0141511a000 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 329001834 1250 329000584 329000587
    0x306041e060e0607090305070b030403020c0108060f0a0e090c0a0f05211f060801022d040509090f0d020a05060420040207030207060f0318060c11071e0909030813050102 74
    0x2400700c81890104204d81072070004408a000b4001c000040c0b040c10000c146442c1002e0440c02d207598040c2d242c10604001ea810030035240d0000d11107039a000302020800303201500d0801c0b2191030740003844040341e044074400c25600c42c1411200d154108a1030311411101c4141c05504064206800c021450703800008003201498140c1d0703680400311040c482e0320b800b903200d401e208007014001002c6000351001035200104c0b44e40705001202841201c010306080107411071001e88105410200c40001c24081c54001c035420156540801442c0400012030412202a020455980c140042d804036a540a4103000811a40190010070005102e102c520020070802203500000c032660300303021904a07007140707200368010f034081e00c1c007005000c1d0020072030003089000d482d062005040070300303e410071100e0ba504002e014595618400da0303c40e100700080e02c48040c40c2401d0782d440690b241e40170010000d002181a6000410032000030300e130420f900c12104100d916889903025651031701500740c81c0346d242c1941550315540 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 329003084 1250 329001834 329001851
    0xa0206060f102001270308010b030106200708150f0105040b0d15200a03050f0907030803060a09051305011103061f090503070f080105090a2a0801020a09080c0306041e06 74
    0xc184c000100308048604884417030070390341c0c00c000301440d1041c0c1c030507014020204014000c1c00d80c0190741c00101907240701d4038044454441011031600c3d00d50350000300c1500a0b02c1c8664800403046982c14041d0021004504c504d0740c0300e00c100000ca81c0403410f442d44c40012603a8030400030310200340704000e5039822180018600074401c840720140e036166a1015000000207550141c003901441100c0d0450841041e4002511b40b0f181070a540c1e00541c00040c06866010001400031313540c0c0c1e2040006006c1c0d01c0f00a01941c1003424998900c80004141180d065003010011820408404280c0f4425000206003249002e200c3e000c0403980c480031092042008414140880d032600d0400640c4001e02e0700404100e90549405500c81c210360010b0b004e207015420031600c0001040310314894445404000000c3e0102c1c802100180b6007150b400c0c1c0c010843d075400420a00a51a0030507584400c42d1811810744800c55410010540c45071401c860003403400942c0404284001240c5c4c102c40019486500d0000e214070 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 329004334 1250 329003084 329003111
    0x70302120a12030b0117010612150b0f28050415030b030609160803070c0b0310030606030b060108130f0b0711100507020d0503070906031509020a0206060f102001 71
    0x30b0a088600030a846203d61111964494006085200380c005c14680c1c2d5410403038010000381c00e14070802041503c0b203a0064040d48607540d00001006d002c85d41c071356595903003400c03425241c0245c914a04104120204080c0e90885e00841042c18000369990910b82070800383c8501c618020076a181c020556210b405003015102000f0003030081d003c4100a110314007071103508008001550300b01e0f010942090202c1d400207003000c0c90000640d032a40719225100c0c0e81b050304141d43d500303440c1c1c000f40c81642046400014040d8580300386000b90020703030300c806c5d0a42d5682c4650070044c04203003004180182c50071090001c03581c1d83d4a0250882d115190112003180442201880c11010a03100c2c14074907584d00c207102c003d640400c100d000405150030030600f18500200c4c05403400d4400d1203aa028181c0b141e000c81809055196210082c1c000070b0003c645400310f0752002540e50303600300d907168010342400034103a03042d140442031200e00310425510030501e4004024030b1507041e041c0c011003054540d01c3c1c26030000c401 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 329005584 1250 329004334 329004353
    0x1120623130f05030d1a061c09060b030d08040516030f110418060b0a05180112020a050a0b130501020f10230106020a030e090f072304060203090406050f03070302120a 73
    0xa0381e10000c00c2071014805240c0d0383c02e05182e042886021f081150704074105a030031085009415170800058001e4150501c903001e022040c954030f926010b00c000180f405500014030600441c09081118408449900d1766080703598940405080002d21408c3c410000b483e15555501c268000382021075080c1580c0340c44008580465021100c203074880303000303415030304001c40b1140091604640e900c856071040c0d81007849070f85042c003d810f00d003003030710026100b903464070f407070010040030098251000c49a4500c021541d5030840c01485200404a44000445600c0041c001c4110072800c00580340b0a0320a404080042045407146c4800e5024161032644061103907002c54002c3c095034019101502142c40c00500f045021610107102d0901c107420b000703041d035410102e035034032415500b002d0314124800880e0f001200c003003544501841a000030702185144d800720141403401d10964013031180e251103a0400c0312009868404c80d4046d44034910400c051701e1304190000c034040003001628041b550f079840e00400e0 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 329006834 1250 329005584 329005597
    0x1050d090611032e0509040816080d0b190302152d120c12070806120604110111071802210703090b06030d0f05130e01120623130f0503 59
    0x807201c40d44889155000c0d440f00380441c110050000d080d04c241460002609208050800f078403d040110b002800c00041e03445034040290020a001e880e036040c000d110029103d402d194a005100306c541100101d100f00303c41800356503004100e01140c6040e82d201c00e07250303000b60710441c07404816400d461001d000002c860744404010403034034564a5030003910640d98194082d0108920f40701c10000059030300300081e061074104d002031800d4000e684a9000040310000840e8404c804e174003c1d031090200700551003000c10701d1804282c8a58160388104003503e078443c201d9100358800c582c585656400c10b01c200354000c1000002003803082c8100c401c1d024a090500104503090710109595080c030780c00384031143d404241c1c0301c2d60403001404890011203005110520040a04040c000e001c1040c0b819140750100d540c028100da002400420343c0c2d14890f480340ca109104054034610b284c50601c030b02c8400c0c2d4107910500c0031003001028010382c0300d10150301c03000f90f1000425644081100c1c0304100044050009000c03 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 329008084 1250 329006834 329006851
    0xa09020a090204030c0b040b0702060f072009150a0905101512050a18060b0f060c01061d010305060f090715030e0f06060d0818060703050c0115030201050d09061103 72
    0x3c440e4114070302a02c030b841042d0031100c90325000b8841001311905c1e01080359403183d4180c60300c1d500c5a0f010000d14501e03005803d001040075035070041045807407480c0b0b02c2400600d2005c0341c03c40d81c1501c0c0d4a140d5105a00710070007aa81203007401c28184140c010a40200b07400001040c5d265509a55828400d05141d9110081c0b40002d0001120200b012055000300340d0450800941000203d1a4004845054090701ca00400440d1034003c8460140c1d1468010030f04500050540d40c0c0d94180f500c1590f008103058003d4103000100b490b5103411003d046080e2034162a070102c000c1207107890310352900f82990f000401403145441a04404034072568843c0e484d000d40030040e180451248041840740f8141f480c240380300003190303000340c0401400e035030749c0d562100790980c112118503a160740c194691040c0c0c001d4000080e401103000a004020154050020030100030500020050100451200300710442284006030025030b040c051100e0600c0c16900440380345100d100002103601105032820740702c0d0021200c030706 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 329009334 1250 329008084 329008087
    0x90905041a0f04111017070201091e150905120c01180c052d040c050904060b03010611010204050a06121d0601050307080304081b060706110403060c020f0d080a09020a0902 75
    0x2c1000144c4a8165560f201120102c00e02c2c0f10036031000f00302c0d03050b0301441c13050703c03000001181c5581e00070b6020302c0e101c2d44c05c001e02c6003191111300c913590003945c070742d040448124100501120b80d0300c00340c4c40398955940d4401c1c06041d80100610b80c0c94403a0308800e4203110155a24070040030a11002d4020084942c49a5030040b00d05140c00208000c0321560704003a9003180d00000314620780000c2041940007100c04a50004110100c0801121a409065a0990001c0c600700020420301e000c50003950494850340e8411040841660b003003402c1c0c3c001c501c9a0303034111800640c24807015000d40e0101010600c06080020107104c41380090321100d90401103607842da08035600510190070b00744182c01c06408007400551609203800d010a40e14011010010120459001c100f14a5030b2410111200c254000c0c07024030920b5265943c1c22041e906c1880b04a489070b251007a184507060001c01d0000f002856017002c1e10700c004010f541034400d088003c0218810386d584000803801a0f50700c040c200058240602c005 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 329010584 1250 329009334 329009341
    0xc040c091806090e010e0616090509190506060a230904050f04110f1c02031203090102030a06090504050c040b04061d06180c0a050f09040e010c090510090905041a0f 72
    0x4030201c6804d02002c021503410134500121941c1c0018040d80c1041c079058080c1008100003100312a500140d811642d840811a0300340000c40062403242540d050003181f04115944800c4104a00c074490000300c01c0c040b80d20f001035545910211400c1c014601c241c40d42d02c61802c01403100090403030340121a002030510102040c0800e003d0650003103231603800c0960704081c40f194400b00080206131280c600e0f8181c41c1c1403503140c504540b01031200d40c5c4000406113201d5180d00340310546c60b010750004c8a0f030304091460f01070700103030311082400740750701a90300400a0048907604c0c009000107082c060348040e80060b101c1d400025090194816004520040d582861885c10000204407446146030003160038162034405102e882c4c2d9810048035803404075410003aa550302c3c014840030007802418042c550051400801130106031040d0002d80c00c1c0c04113030303075900c00180d16a400c004449650104d00070000d02c4102d01440302a9040c2c0c80541c0140c0984100c000c0081401c0d921501040111251466800b008050 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 329011834 1250 329010584 329010599
    0x180d0212030c360405100513020f04120312020a0504050103200a0309140610060c110405010f1509060519020c06070822051503040f050d08190b030c040c091806 70
    0xa003007096501300c0b014400c50034802c3c2001e1412940b8040e20f0b2152450305000f05d8541400e504079080e400d0440450354581b544c40001c140c915007080d1054002c00d941d41c42034410380016100716a4020401e4907898205400c180044008014a041d12040d0106001200880b444560f014004401c0e06a130042284c41340c501d070900214034010302c0c1c09501d500050500c0036000b0b0510304e002c1500c03124a400703112001c0c10b0904107400765174042e150b60850700d841c001040d031400061020040c3c405000030504502d52134081160100001d03c91031001500500810010f10002000c41c2d18808040c41104c1c8222800000140140c2c001c0000b00ca04000010b00e0300e81100140c1519500010742042c09100b0910307080120342200301c1102c480790f0a000000029081000030a08070580743c0c1c20004403030400740034141c003420b442070585a9076070416000b00c0400121a0a000e0342e051083d0103009848041480d05c240000b400342d0344a00c01c184070b0002d1000c203402d05c4500007140103841011000c29000d1610b2034 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 329013084 1250 329011834 329011927
    0x20901020f010219080606070b07030b041a0a0e0601170c0304060e0a0804030f1703040b181b0d05010e030a031e0b090f060105040504020a08180d0212030c 68
    0x2a0041c035a40188900d011903c011020f00c1c803150624240460240da56130300141c4148220b00000780308181c920b05004010b54168414403048a0555007000159140502c144051003032602d607903408144200b090081201c10f07041c0e65001401810b0021644070b004140c030154000446036a22240408420002801118010b4005046514015060340003103921000c110f0b204501000d4071030011403980f141080200304104a183d20300003280364880c10945018400705c80140c980e1950403a0504489011160200c0c030600c20381a0259020101c2801609004030702008007000e640325580c584103017500f51410710003041400015030300011035071402050011b4124144010100051074011a600e180c0c94403080aa040901c80354544056540c9a00484041c8241c0e04001d400c40c0c000320b840c8110070340282c2080e004071210728440305d902045074580b650f83c01922560800580c80458041041e003a81d60086800240c001d52407807503d220790030541d140c0700d00003c0d00300c4c401a102203400d0141d0076080 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 329014334 1250 329013084 329013103
    0x3011116050c010507030801090527030304060f0b0333012403050708060d020f130b0a080606060f16020a0e010303030b0301090804171f0b03150c0a0c030e04090602090102 75
    0x7801405c0c02400e07107004021340c00500400b44203a83c0c900200d0409480035075280c46030a003000326a845203902c517001c59202e030001c0d282290782c00e0900700903200c8400c0724025640b911070041c00804001d5401480220007111403441a1040d020300100c0980d0000080000e0f03010308104200e04421109542c0d5004280c1a403004010405142c403050100385075121070002d4110f8021039103261851510b00029040d0460800e146031b0000c034145120034810000e401c0300c4004901220028545660303507000ca511107600301c80243e403203001001100c100710240c901810980e030030210038000f941c440354046081c103499070300010000d0802000400030964580115074002c5810383c004d01081820382d0b40e4082d45d003d24014010b2200080e0092030350071508200664958048201642c10000042006c5000303090440e0200c2c0680103525445035040d800d040030600400382101103514001d000e400803145500d80f600228104050501d50708003c2e512801002000ca0180d0710050b9100d80740800a840c00340042c = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 329015584 1250 329014334 329014337
    0x30d02010204080a11030f060a06150203030c03180717160611060403121e020711010c0803010e06040905030a1e0e130c1b0303020405040606051602010e03011116050c01 74
    0x412082c40f039541c0100e03011103d1640200303084810070f041000a410701b2010440c00d40d0610a050402103440040d030000001c5420742411940b600c41300c5041261203100c1101c41e0300c0c2c100340400110300c40000001c2190619801c11068035046078403050122840345000b24640d01c01e03888102013076441e07224007c4250003400141044416810301040480c0c644400030800780c240b0000c10410020500284c101565080d1103061156001c010b10400350025000f171a4140c411045100c030407642c40d4003512401500030381002506045070720703000c060a05500010160360b041030300d500324000000c45c1017003e060300111640340c0903412946c80e07903004020003000a1440801c01081c00040e03890b101c0c3d45882007011000040441c2c03c900080064039400322007820b4001b0b0301103501142080c03540c1640607200f0ba440807a4103100b15950f07a2000c903014020f40c00ea100c012662041a2401580628041181c10784060000f141c031311000345000300c841d0450300703a90034022041f4621004101060080300180f0009 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 329016834 1250 329015584 329015587
    0x1a0c04180b090f0426040e070206060a090213120f060e1b010c062406030501060c0809060a1419020c0d050d08090a020a03060f3c0204050618030d020102 67
    0x80000042c1003480207421000c86044074800b180900250036884505600c04030740c3c10140860016030010558054824424070a42a00215010300e101007034003801000c00800401c050390810b0384510080d40003c0c480520711044500c00541d54050802d00349529004694410314010383c0e042c580e0070b81303180110803105a0840c072500c1b5130720b6818102800e0b45070380030b181c00410160289000001060340e6054558144622042081c244026003031641c00c0c0c50150790309010a9a8941c000e94960020540080410301f040c050281c403410f0410150642d809503180c603040c2514505680a140e5025141c1d9a650601600031841016010004520b402c2800e850246603002035884107610781401225030b004100005000c607510b50010001c0188481d0010200140142d90786000c00c01000d607070164003071650030b2580342c21015965104101c80c070316a03a00d01c03d00644000d80f9440803030b121248110742041e0300384400b08050300c542e03004e01a520a001009846501104201807604000404040440e0300 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 329018084 1250 329016834 329016851
    0xd1503080a0e0a0f090902031005060105070609032708010606080c0313080714030405040c020a0213020903010e120d06120f020d21030c08100806010e041a0c0418 71
    0x200c035411030301168101d00c2c0581c14044140c00081c5403000992100405000801012445040035845201554403c5041b54a01c11051440c030040d54001c982d01408903000303000d26400700f4455040004068071920300002030141a20180d441c2c45180c045d80d542800c000312051007410400d00c10140685000c3c00c1c181c605213400c5047d145d40348401004107003207241135914a020408128141c8825941c002544090030108a44480d1380380c0081c03180510a81c00d10801c11030403800400d003611340b960041c108022032881980311001a51140e48010382540d40d504200b040322105100c00881c404c0b00b221015030315205082c030b24040d0341d2541c00c110440750b8503644000004a48200b4007102c02d9058821102114507800d1900000b0901001120b8081c6000c19500c0c00b140d06501190149481c2e03101c0d104142c0700c0561229502c9c4403801192010b0748a40c3c01844021142c03204698058400d251101c0341208a07440901c003000241c64030718645402107030511845038050628103404002420401030f600 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 329019334 1250 329018084 329018093
    0x902161b0608090c13090c1d0907050a121101020f0d090801050a060b0406081b030c0310060302090607061508241303080402010c150c0c060f06050102060705030711060c0d1503 77
    0x1651000d20751400365508090f01c104482c40828a00a02c8074151300054102343c1070311000740000841e04941540030301040400c062608040241c00c0e9080a0365044100c501a41d59464106208141906501c540d0602800d00f440030003440c00d0034141e076960408040d21f401602400d44401408071a012814094140003403002002034034215001032800404a031605e20208045a01500d1040c241c84400410482c642d11a41e0045018094030060000150f031307241c504030120b010fa0b01c110381e40071108015090100e81c0a8100104482181c0c0411414690b9224070781d140500b008420000001001c00313030f40b04d40c17210500385607100340c0425a544e18840345a03001492480010802814005108180d00030700c0b0701c030560501e04200e0340c01300300150309003c10003505204400c403080724020305060100079109860b024440484a041e0000c008030748601ea01500d00c0d41004201c582004200900411011405c106e058021000b1441e550398034041100d01c0070035200078008103c03490010010800008 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 329020584 1250 329019334 329019349
    0xb0f0705030412050c0625020115050f0102151518070f030c05070f05011a04020c032a060703050118090309061409030102040e0618100902161b0608090c 67
    0x80d40543c044041803d0303040152018003404c0800101172052404000210184140002d200d80c1010785550041100c004204d00341c440e02003504901c9000c01c3c004011380d060030583ca803c6a14140182c42108080e042500844101161407001030315000e000d510f03803810500401120310144444103244c6141c00740c0094880044000103008056031f850040d41c44a101f032081c1d40b241c81e8000381003456001542003842c00380481040e408240c46000e0481025464184229140314075542c0c0514108003079001c2c04020a031215007c082065050002c60703d503084140700700307881307900a51400109e65040250700c0440c8001d0000c4050344900d404010b0001c170b508442481c08881240c030f03100e01c1c1c00d69220041c1c03450b8040e0b9402c15815600100d004200380d44002d07801e0348a800b05481021180034150480c071803402c000d40d40c4004420b043c842c184000c00c0c0940003000d6244003140c2c40c1c1800d45169417005411020a40b043d55110b002c05010300c0940d41c014000c0d60840040c0f002070002060f0500000d920 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 329021834 1250 329020584 329020591
    0x1107030806010e0f030a2105090d02190f03050a0c060c113319090501081b0f0f0304020108090106060e13091718010f080403030b0d020306090a0b0f070503 68
    0x51100c0c00f0b400004540c0c80e0a205004c01c040034064035000c44440c07400300b81c0b0600c604440280c60510307008000d41716100381c050710300030704005001d807000c0440c0740c00384420924a1a810020020100000708003006030012280056126400400c6034900d10300305000c0400c8544c2141d400c100180c0b40034030200d9070390102e211a012084030207004600c03111406000c00700c0785a0700390004419a15003809038080384070281c00382808408103c01e503580021b404032005041d80c0550b80c003050050001c90304070006004886010fa01c801d80304c0340307440300901c80403259030070010000c02880c3c0b00200700011564030407886a0051480380090020314200320019007400c2c030920445004400211031544002126040b5440e11908840d01001400c0c2c0a20700c06415070050304407a500b01c440c009940e01e075506c181c1d10f07079040000955170b807042d0342c455540c1200504800b14449510107102d41051025a80c03c1c06458043d410b081c0c000c11031f401300b900c1c1881c0d2030f5070f004000641510480342000b01160b04103089036032 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 329023084 1250 329021834 329021837
    0x816030809030a060507020705010216030201140a0201020c0307080403120809030306040c02032a0f03070308190f1104090b040902090103110d0c0806010e010806190c0e06030a0f110703080601 84
    0x80360300722880420301d4810b0390031019241904040c180400c00d9000f065810507140d0030303800d44001d42c035200c04010403111030f444000d0015610600c1b03803100092030806402402c00a1002600c0c08801000440c0380d5007020714117403201c3c9000181042002030044001c42080342508101ca440d15060691355100d000c01003030140115112480d110707000380300f8800c80d4840d40e002c4500d07001d1080b5841443c01c0580e8804440c04041c414480e110b06103007000801d44480c2c07541996000c85c0b9544400200c0c1c80c2c14085040345590b241c0f1298903020750026801244008000c410649031035134901500c2070244c0e0890441799009524010035407001d81c0311114087e05403504082c04010303080c1b1210109040701c8034000040d107007400c44d0b14080b035008004541c0350704861034542d42c0c1c0c0d19a40c840407100d8072084140c03011451480c0917006001c01c00c0a0f0742001c01e1100140c03c06008180440d004100107520466003000d84640d200620b100c01c1415200c0d072081c00f40c0d10102c627401c0144684d00a401c40b03201405090 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 329024334 1250 329023084 329023087
    0x1d07240e10141b0706090501080408030604090201090308030406050709050a030b060607080403080a02030913020306030a0b060102070b0a020601080d0e0a0608060406180507030b030c0609060322120908160308 91
    0x90000044003c0342c0c0182c07a0100350390510252003040c280c841e8414018000010f109100000b803035841200c00d81d000313a40114440e4599102d0700100401014000000c905002d20030100201244001015501c140c2c01810017159915091000910101650f000707284180e0700c40200740003045601c03c0f0680e00c080140c480d6565200c4600f0404da07a40115400200b01170070010340094944e40c00300c044c00003d001510010340c5002d20720328040990004440050b01580049041c101140c80c440555030403150600603901e85503210b2400c0d07a0319500c84a59007025900104c0100701d1007108000d03020050350a0710300b002e0210341c4080042c0c0a410075215540c01c0007009001324034a640d07594440002030526100ca86081403014000c000509000c40d40300700840d00c4c140c4e6581e041d04010440ea00e6620303000300f90501c0c00408804110f040c0e080078104e10401c0381010a032810746000d0202c10048213020f0100d18200b05080c0500030505000e94006801940018010002445042d840441540c0c1d1041c0100d = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 329025584 1250 329024334 329024357
    0x1e03080c010e070803120a1b03090f06050901150801020f0f0a02010621140a0302060c0708040f06090f0602030c0c0d060b2d06030402060d1d07240e10 66
    0x12805001407000c9803140c3c0c0903400000500d200b0002c010050744075050030002c00b070b9aa034400e1a00b01c8410042001041025840329400329100e1352249074018402c403550804080d86840705001c0759400c940c95062603540348103000d0545020344600001f400310307070000e40c5404042080c51000d8020581c1c09961140040303150880c0c1c0d8001c3d004a0044c00011200c48406c0b020107410483c014480e410a80e40f16400c9005000c43c00c001141c140141901030300200b00c19203a4081d01c03e406c4d441580f0a84184009101c007050b0440e1611548005000c01c2c2d0342d803001c2508280884054060640c00181594003c21243c03455a4000c11000a803030021a24017643c03807414148103014114400b1010780c04124500e8400010403c016410803090b038004031601d043d0740f80c80500c00d940c4019180a980b040c0b05200805003000c0c25000035501880868895000c15480100f59260400c06c0e000241c4501c0c582c0c0b84205141c81c0801c29210140141ca40414074412240c00328640745070000c2c0071020041d40c0d0004 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 329026834 1250 329025584 329025607
    0x1404110904020102120a09150e0a26010f0f1b0903082b050901060504020a08013609031205060d022b030c0c050609090c0a0c0605070201020c06011e0308 67
    0x400c1d0140440011750307aa00c0e880e14200800408041c01140e41881c0b1910701114814451041180d004c100580031000c40c40c2080b821044c1844094883e00714040b1546101321003290038046c1d00c680c000e00510124005414818080c280d5035000c1d41c1c0107441d214240546400755102c1405401c50b500800800d40c2e0700c0f09182c0700b8000485100c4801d08003481d02516661900c500e6105510881800d0020000c954440c82040168842c401801c00000c01c05401403018104800081c0d03107150054580031068101c0c05640c003107500c4040d0340070600907907505141e41850303009480054140001203007000a03107481c0c0c000900c144051440a401480c0c04c1940301c40f000c100c00354004259084407110341c495403152400400400120a084800c658410303400074040c02c0075019079011f401d00921001c101d5844c4c448101c5550407a0008408100040120b50081525485004e004a0a0b980056a00c000a0184d28680041a440382c3d006410080245003c0309210407103d083e40d40c01507440b03030b81e40d003103224 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 329028084 1250 329026834 329026843
    0xa05220b0601050f070506100801050705090f0a0905130c0f12201c140c0604060f03020d020318011b02060c090301060f06020a030f0809150402012c041404110904020102 74
    0x351314801c8000f90140030310000054952240c5c1c40501283e520540341c2e881113090724001e82c8c1d9a000316105206109507454802c0c0341c900803400140c68040c86a1b5a5411102600c2e4241e900c030041c1000004217005108591040002504039500307480c0c001440d1012244002e01c01c5400600490040220680c0600507441c01d0244544010401c2000100c00740c80208100c9078000b04642d401341e460207400a207140404c80000d0840d00a15030f41c107261800c003082d00d000258244440c2015400c10014070b00d001c0754030166006d205003181014400c2c00851601e402c607020703101d03820303c15420408400400d603400507503582d100075810300301c40d2a62442004a409040f180d00491024011410003041d495400602096058080c1c2d4030f256440990440584080c903041e5200703001600030340119000c01c9001c5c0611034003d4410f00d0200e10103401040103040140340010b4404800d900b041c80507940340b03054090041001c08021080c2c01034180360b500d007042050100c0856008500700c400060640e0b00a01 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 329029334 1250 329028084 329028097
    0x7180207050604081b010513170d020d021809090c040209040e10020a0818030403020d03170702100606020c01090909140d020d0201061a12100f0e0a05220b060105 71
    0x40b40c40c02d05080c684100e07079401918403000000d0100e0b16400d15008140640c134022403018418116413401501c40c5550940c440c1014000d07800c0030428112849010320051103d2010244016200c0781900d00c05c190241c481c160031032060a01c0b00912401d50004112003031100012500148d5621005001c94081c043d2a5441c0480c0d02442a0303d40740401180c000f404c0341d24140c0d070b4040c20380c1e40d10600200006142e225040c400d50080c4414401814042031080d030807402801c0002c90700c1e03202c20751585101001c841c00e00060f08044001120445240525070107004c007030016040c140081000203110b1401c80c41a84401900c07241c2d51800c0c0849001c151041050703104c291105800104c00c013a54030822150707004010361030410700169404e486601d2882104030100c6240c60a00c0c0454044158140600807000300071860790001b880095202280300286111015980c840c40d01d15640411075000421030103070b120050700ca142000e00d4507680920705550004084940751901c40c0100c50600942 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 329030584 1250 329029334 329029343
    0x91512050405070b0403030512160f0c030302041203050c1b01021207020d020409081803031e0a09080313080114070c0803040f020a030602030402031009030e121203040624060207180207 81
    0x5c010062580c048000c09842107544c050148a4440d1181070b6443c03a851100100010000b01c2480b605910880d82540c170b89000340341c09800d103612840e8440103400007040460215500041001940406100650782005000403590b625092040045c3d190f02e5003103c00c0a0484002800c0d10840d51201c910317942554000e0302c00c0200020f98981200e9541c81a4000d007100c82c800003189074a132500000321a14250740040401c1d004004101482c2c1a800650f400401e0000000c008145032a0420280c0300b2441da51100001c0309140a10345402c4400e0000c0c8018042222401c1001442e0807000b03100d00c140d44000201e640380d50b02d041840c600a50b03908001d601031131000000041c01301c0f0b5005940558002c03001d0b0b9006140f50b00d850f40854011082c01070110703214420b5a45203203012651350340038034a054161001044020501c44496204132412a001e5546610a03808401c05c41b0318440003542d4030030b45002c1c050608501940d614900e01c00d58092054030380c0e07420500c402a80640303101a500 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 329031834 1250 329030584 329030587
    0x1c0302070606171b13052211010f0206060307060f0203040e0a0603200906090a0207020303190906110a1506051002010b01030507050412080304051509070303091512050405070b 77
    0x203e500d1001c105804112412840c0300f10745408041c070743c0a50410382020402024040d96482d225400c1001e0b0030000c218038028075090301d06035000207008444000c5a880b804c00307040e180588000250240c903083c0c0503802154805400c204040e180050000280c9540d410400c0f40c02c101024104d00d5481541c104482702403601003848039210301600300d4000e80e44151722044071212800d0061482d9014201d40590040c070900100e42030741005041c80c0c3c6c0091001d080503152501c140c01081c13459001c1441d1031040b40c40104508044e950185100c40900b207503241480300c00c000b0001d240c4d95842001d01c040c1800c05241144140055281e02c500010a005800d655035014807d03c081c0c0200440c1c0040d60200f800c120020304054801da003150152201051894680101a20356401d40e81004100f181d640c40b4882c80c58400324203041c1d26500c10508030300108a250300f1490000e051728600e03400f083c0c0e9414036030124a0072680280031711036130368400600000d0300e6403641013a5151000561009840110 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 329033084 1250 329031834 329031839
    0x1302040312080105150c100e0f01150807050111100e0a02180a0c08070c031107031a31030c050a170c0f0c090f040c03020a09020711040903021c0302070606 68
    0x1004003941e41218130031503521180e08021450b0510307034420702050040c01e401030800e4100700c200b00e600c012050325481e07040320b05420411104c01e0031602218400c2c83c5110301d0002c1009009810411900984020b19240003a42803900b0314035904c1810021080110b500e80c0b2601d034441104100d4541c0c13030b035001001c41901c812030f0504c10f500d2050943e13940a140e800c01c54a1501f42d03000da0340c414001c801c40c0c0c0c2e807004a0354458500304c8445507841d0082d900380c0620039000010032100f81c11140014042c11407003043e41060f0b11500c108114035510000c0503980020001e07900c00e5017181d42d075141501800c21103100d002c1c0e0710748582050f0549200900020511400b440c192090708050034075040e25100325407030742c812000307400e03a18009281c0c01d42c1d1082c69080015850704401c0d85079034000e0b2154000c4da040b103450398000b8044400c0e85e000148800e0340414060103201030300b10100360302842a03c0070014144180c600035102c54400c40e00b0400c6580b80101030740003a00c20381c11613029940000003000200d8 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 329034334 1250 329033084 329033087
    0x90c03120809011401150207260f01111905121005100203070203061b070501060806040201080c130905070e030106080c010906020f030405010c080d0e06180109111302040312 76
    0x580c0e10030000080e0024005880501c0511514901800145420a440c2e00e417a22251304115842d00351400c50181100c00144c604065001540180f07041e0b541c0901c40d5041c00c102c516241c81c420f980c00b016030608020040c1110041e08440154071340c0010480c0d503051295080c0d40c5c5110b890300720010312220b0070800c034860701003078200c200355502165a28440d070700d5250100e0f40e1380603080000e903040c0c0000e40031802c2140e80491070300400320174a1302a410301035141c03941421146242c0c000c2001d40c220b60100402c40da400640c060f400081d104040c1c0c200188a135401031507640c5030180c0c200042d80c9d10b0100354250f000c3c841200c02d0b504018022300881e0303180d0160b59101c01c0c803001c00038089140b040001c50f015001040401c0601a402c0007541054a01b100440d10203503218804e45900100f00300c08640f441483c0914039414420300020300343c03030504442c24141342c080c0101c4101580d24041a280014136192500484180115a41c0703841811407840752000b440317182d00c0140750700c811460200445 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 329035584 1250 329034334 329034353
    0x14100305011b2007030804060203030a1523031009060204140414071809110a020601150210111210030b0601091a070f050d09050f1903030c06090c03 65
    0x168480d50080c00b10304141d507011006000e06050107404640e034088805691442c282c6000c1c1c07020304010468440b243e42e500c9205640d40240c0040b80107810000412550f9a4140180c00680103206028082c651038203180d111030781016400c0804003801d11801c40f04541c1c080211002d0704503000700400c8100d1203480d16a00951091150f1400d00f00d4000b403e016030310705441942c0501c4c01005d50300e01242d550840071070307180542d042070a110340001c060101e40d81c4e002d4416020018138030f0b40c0055544000d058041c2c94100160f200d420391410701840c1c840038075800301e00c1c1c4201c40302c200e00219010041c1d03443d045090180e5611403421f189000c0400c03100e408007040042c1203130b000c2c40b00c4003000d8950a004582d03685613030080300c0546030f000e028a1044210030740100a0180038080c0e4100451050b500c0904062300c0c034412000040040c44280842e240440a03008078210840709410320071030110008008941910029050000324010401401801d410214919a00201e008250307902c0b8900a0f400 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 329036834 1250 329035584 329035589
    0x150e0a020a020f07050d14010f0c0c061b02070614040b0d020307081005100503040305120a05090c04290d14030a12050f0c1305120606090f0c0d0b01031410 68
    0x510540c1981283d801c03004c00c100041d640f01400c141000d00c816222620401420b211200903503580d9003003003042080034402d0f15500c1000780d80c0c5134600e0102c5d041c90400d503001c402c000ba00030401000683c02007600003e5950407203003035082054a981d05500c03854114041c550160b60201310000310500110500d90007540300340026102c2c1d464a88415000d6242142c3c2070040c1900180b00c42d000100ba180250301540c0d119102c1c0c688a840e06281d1880d00d4000c41064800024181d04c440c24003001030024040741d400307000c0c280c5082141c210610381c83d54961003500c86600e40700000d5401d090706503ca50640c20410754100c40544003818403401c54958036440f50143d100000c46006007560f15000c3d038020306000b81d00c58904010541c403005007941040d40210110114000b49c03800000d003e848985140c0440c042d0000600700301d14012007030280164008042d2124035100d64204a190191002954282005004005005948000103034000c1000c0c015010b00340001c2d0041102c000c85540c2100103 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 329038084 1250 329036834 329036837
    0x8130b10080a150e190609061e09150b060304110f1e13060302031c200a1103030c0601060e01020a150c090f051503060a21050c010804080304020103150e0a020a 70
    0x2c4e20f0030f0a800d10761100d42c2d650700d00031101c940700c1e01c2401084a0780c00000c00c050040c900056032442001c40079016a5440ca10a141a616079400740c0520480b1196240000c0c0ea881050000b02c600000003403040c4801000100314001d203100c50031036629660030914024401400d00383c0c0030300000300403002035409540800e02c58001c00307800145841e03441c001d07042100d034050014518070200a45020204801c1c0c0314081c100070100c507103541c01115441c4041140c54121019040810050800360085405820828020343c010052101170450005600b411901c8030301d4010000000c55004034100002004064003e2415107810f40c0000010380c40701d03503081c41c02c2d1600b101150790b494003000146c0c60380c40748552109141102004ea07504050045520a40040018840300e46030410410b03020400702c0414038003c4c82c13803081402c020b810411004600c0007400d0440b5207182c16503881c4603900c0001d100a04241d1584020900c8404001d514000f0700940f40c0d450805140c504140300007500200c0c007440 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 329039334 1250 329038084 329038091
    0x7061d0f0118020105042304020f09030709020405090f090a0f0c140d030807050708040806040f021504030510090501090203154017031003060c08130b10080a15 70
    0xb18121581240e09590980c1a101c19040c94a083c010011450030300302e56011050310702a003e0031595540c8010482410b405090980391914281030524080d084e1300301d203c80e58810402809196a5558050750010440760303076071916a0341411483c144104030000810701284010b40108100e003000e003550076655555900340d004071a46042080c403818415000c2d020821920211f012103100d071005002403806440045d00d000d0303840804a1800100310b5061300c0008170306070f005e011850a01c0c913001c080c20380e150410b8141410364440d6a125040c1d0020185419620690007080001c203401103907405400405645100310b0100101a608408598000016100d100c4102550180782c208a1400351030801c0f50541c01d181c904070311080ca1081d60151521b04040b900030000d0f1162800940c803d205e641401c1160f0f0307145141040c256071038200c0d548140102e00003000743e011b45882c450b0554035007141ca142819107840e03021a140c00b643d5040f80509000f16001da0060103510031081e00103554211041 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 329040584 1250 329039334 329039351
    0x706060e0615070f0605070203130b120c0708090f0a05060313030305092109010201090c08011a1206070e04060503010c02060f01050a120803070201021303120314071407061d0f01 78
    0x904510420500030b010f1484407091101080c05503000940c00687c0340100c078a07204242504841448807940030301044d4600044400402041801281d0090701040c00c3c981410415564034219001e00c1d051180101104440c105195230ba40e0f030701230020075003c1e0006d552814040700e5100100711126064001c0f030f0131320b00416000000000d840030500c0811032545042d185040049030b681e4819400c0504542d200c00c5510003003140041500c0090071404000549d240d0f184205100811095a03214440c008403941c40b0813490703001c120300b58482543e1030907124500300000010024003407500225010f41c0b90400c0c0103c0c03140c0000f03050740100711842030105280e130f9034030800412404170300480815a465810180c00200100d000d140c10407041d000241c1005514000010b18003001d40c02620510014103c11400031b400d407013140001010300ea9400c9191034100005000200341e0040c66915207c0010b0003801c0c48041da014404c41d0320708111000c50b15110401840d074502004185c801d265107850040c = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 329041834 1250 329040584 329040619
    0x30c060c050c03070b18030309151b0409020d0e07080c010912050309271303180501050906090301060e0103030306080d050c06070324080304061202091804080706060e06 74
    0x156081000d44100851400404e66500c400d60000a00246001c0ca6000741103181100248065071003056100001e102c484420107622074014400340050000f0000c540c3c0b590350b000d100e84c2c00c0f81c055400405001d03070b450801d220120000c0410b040324499a01910b200419643c0012811442d581707404d82c0c4403100d0603141c2e80803040800c01c540d0002e00960041040100a09081e84100c1071030000404031124202c0c43e40e2450f0452408803036012883c07529040b25820107070490302040c1c05003200c107e04c42d170882c2000c0000c0c2041c4101040c842c03041710f0110f1101e141c0e03030782504004003405030a110074415580d6460054082c0c0400e006130f100d140122048008003a210b8415901601580c4000f8405ca88444405400170041c1030105047d0004404000b210007498100040c000d26007800155910f84c40c0540c010300c4100b92416005480d030040002c401d1a680b005803c501060100c40080040c1c0c985140c0342d1013510a020008002d41d080c010700007184030003c43e000d4450f24040d60300d064805048100c = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 329043084 1250 329041834 329041837
    0x9060319150e0114040f031e0c021305090c060d06030606150e15040b031b0a11010c09060c060c02032502090609011809053903070806240409030c060c05 67
    0x456809044c654400900481c951410050116000781015404c6c110503644c17004c0035028404815011a10301104c55046080c404940740c07070f0300c0200c00200002c0c10803c3c2017903181c01c882014203100d05404240c1d1041189950310100041d94000c2e4100f111641d40d41404000f0340c003803400b280100c0c1500403552400e0a1003001140d0300580d0368120707407a00742400102c50050700b001d8030400d000d02c8010a034046044c0000d00400da180c18640f15448140030040c559829982207802080800800352410040c054100c0c01c240d116960249000c17803680d04a00c070403440c40c003441006071704e1615076028a00040350403070700c64007443d4004d072070074009907440e00e00f4880161800c4c4200300450070185c0040f03102244581c06018183c0c8540c044c0c030440d02800e1011856024200e484e140000c000c04d4000c0449071440d01b01e0b0700200410340c05004014a00319100d0344070600100700e140b0300380044040c0c41c20300c2400c01032034811a600420400281c0540d04005203000054001210410302c0c107080559032a02580 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 329044334 1250 329043084 329043101
    0x3020f1f0f050415052a03070b040807120f180f0605071a070504170a020f011107080d0305041103070b09010309051203042f03060609060319150e01 65
    0x4034220315020805011503034007401454920400c0400c1c0004954a8594007410201d09650342c4c555449904e2031030004108508038070b01c40c02100e00501c00e0722225a011041e5040c1c41d4101b44500c440e0398030750525181901c6081c0c1b00414903266591640362140e04540c80181c101e825544036034a910240c11400c20801180c0074021050020700c00c10000c80344550024843c0c13074810200001d280d00e201e841d03280c80d0141629941c004c01c2002c6014800540c1d1035000e00b0b290320f03880c0000c10740e00c1400d40118499164480420b4100103007101c00d507407000f004002003002048100c084550881c1d41c4207000f4000c120a403021034088907a410003401510700050f01e001a2100303400c80303074508000100190010140f03240c0807036980c0113802c20fa081004822000d944518011030805040801d0104e00c2c2051152100155034424074103021000180c0300010304a50103a002e9450040c1c40e1581c1000074644208100d86030010040034a1090801000c1c90080b81e654a5000c020310119009010b50350030f0324540b0 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 329045584 1250 329044334 329044369
    0x30209010c1103012318010b0a090203041407030305090405060102010c080c0d0b03060405010b0909121210050301050406140c07051f02130605070b06120a030f210603020f 75
    0x181d000a020840d03010454042900040000520411340906441410049221160340030340303110410511400e0501103030014803803c0d0003044a90360380e400280741442180540c1503017503800300c00030741000311154409008900c85400c6584c07443d92490020a15440307a8827042c0131328201008103103154014022614012015181d0782000c4d914414401419045860084410b41d181c01041c642c07520300b030200e180103502880010034128822420300030313240d4014120284d05c6d0302c8182013a50031518103040c3d034411290314001e043c0c2c5441e1854404d5900c40d80390041603055207040d0901c420400030368030441031210340302c4a11509035501000314000380a00c1001030910340240207421916000d100d20300c0f012700300c4075000508061074650f110702d0b0300016070002000b081001551000340070044002c03e52041e021110b030f6031111490403070345442d02071101e0010140f24910306912080c074001c02c0300c42c0325001c0b510a0644001c44142074000070300081c0c401a4009e52142c6203480c01814104030012101000 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 329046834 1250 329045584 329045597
    0x4140a02070213090b040201030c031d0723030712050a02060a03020d1103090a0b0a110301031202010e010903140310090e030a080603010218010f0207050604230301140a0903030605030613050d03020901 88
    0x25031f001940500302e48811030302015910407070b0b03001d018000120008240758002c020500141843c8624242c4902c110a00107440107a1411004079035000491401b91a02d029200c4113003010703464503c0ca841900200254490000301324600601d03855405000020320303c007024010b0340d0000d100391a141c84140c990082903008081a100414000d0b5401608902c201400155010010b01e1a90094200303030811140c49280c0d441c1c0d010550346c2409500c80c4c0300c0703004008100800c420340d4050301302c807101c6100200924000c40050040d0403011000c0c0014051028144135400b40280c0d0b032512540048442d8002c59411000302d110340c24140700361017500b00201401501025248019262445400d905008500c41e100707000c152070b02c0f51006040182100306403a5074240300000c024903469002200340c2e0082c0c0c90001140b684900c2242c080d0b410a0005000060403034803424105c02800315a00704076054480e00c0c0030b00c4015600c0083d0140c1240c022000d07248000020f501c101e007a48101880c00d0b000915 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 329048084 1250 329046834 329046841
    0x150a1a01021b03030d180311010c0c0f051f0209030d021b060903032b0e1c140d060b0409060f080c0906061b0717010c021b04140a02070213090b 63
    0x18104004504018000c08690a00c00460740100540d1a80010002c4006c83c8088540c10140c020080102e00c104200003030250070446900140000c96891020300b00da90380c02c0200d028008180159001c03812543c036481c0b0901e101c40300560203544042e040714086c2c030442039280750291004c42e02d60900600c0c4200d00e200d040f19042041442e07000710110b580d1502040102421300c1d5180f0607090304911000e180640e038040c41d0b070b1800c0d0846611585481498012501da00c841440d90344480f0b803000c4c1241040c5640d43e0814071080018010700f180c8a24003460700e080400d01108020190084603001a0140811a2586e4480c510035101d44103c12096000086400c01443c01481d00c41c0e102c0f0f4040c06040c00c0c050700356929014260b100c40410a643c100ea0303000d000420100e20100203074400c00009001d08011924021340e1041c030b29101203803490012101010541d150b800014903866105e95003080b5051a01c20800203500500c812840b440641c0ca901004204034003a221041741c12680c107048654 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 329049334 1250 329048084 329048113
    0x30908011512320c0409020607031d1309170c030708091c150c050906041208160c0e0601020109030504060318120903020306060a030c0b070303020c150a1a0102 70
    0xb00148045030f00020100c00c841410302e00701441d80124404261003112004100800c50074071801e40303040e5000c1c508150300c1001503103440e411100382503410f1400c4c600712039404122404100740312120581c040c9004210795034841003a0001d1840b00d0140c0d02011400c0520140380c2110303c10f1a0552016410902c14540400c03110000b0b0000c007800a0b0070701035a010401910400700710b00d020216111202e440c04030002c0029881080358034030381801c0c01d03450a0b41410005009002e42e1054503504142c0503071800030000c00f201070301c148044003202d402003007500380b84c180c18203149400741c0101103131100001031266105009410300c190305034a038a8540781c20a83c0c120003404007801240807080ba01c102c070b0000103c0d07903441021018180c4d42ca109500c1c2c21881054100f550141c2007502c1004800014404240f424500d80200d5140c44110780d901e00e91850250701034003c61001000d030303000f041c1c1c0c4008a80e000c25046403151540300d008024102489074090040481608640d0051f485408941c0100 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 329050584 1250 329049334 329049359
    0x2010215040302120325110606010801031e02010912030f021501120308061909020a0207090603150b01170a0605010f17070f0306050607050717030c03070b0a140f040309080115 77
    0x259048084286109420910074001b001c546401e030001403501101c0d0603008014005d454000400b4078088641e549961201c404d000d400d0711034030124048491403142103a004402001c0200801d20f0394079486144c609019001e0400224010003500480000d0f01c03150030880c000078142c448503445941c0c458850744044645600040a0581003204410f0500081e0820f00494008115819001d80e48a01c807241c02410b03d00f165111165084c01c04806200060320018075a04156902c0000901d00c00500012101c8092582d81d008104a481c414407040c01d425400c801d085d2035003030322030110317500c004101103403045904801010b0041c00c00000c80d511030710413001c00740002d200d454081010741e00c0c0d00019910354440384085a480e800f40c40100011a40304030b2880e1030700741a20180d8100442d22000d140c0300d12400900900d03024600c03000075041d10803580310881110032410000f4251030001c1c0d00f001000c8040d50141d0108088005c0002d0b0710205002e540d2105880518801a80b4170f0840c0c40d031040c = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 329051834 1250 329050584 329050591
    0x60804031e0e0310050103050d09051302030a1107060e01050c03040209060f0a15080a0605030312070507020117010608041a06010c0b1003060e072c040201110703080f07020102150403021203 83
    0x70080020b0a1100c0340d642080064061802d42600080d2545903140c01841c0556070303031500b018010220010051996005407400c0700c0d0301e1500300582d80c1d13600e511181004010000003120100b1011400350203004c01a4013100c4403d00040c000c00c200d450f4031040d240030f40011107000354459110320000d8202d00f0a03600741500a44c001d0105c1031126103800000c607200081411400005030320400300403208901e03001d80801030005501452030241e030020b1030521107000429040600400003030960859200b503c460030700d0515900e40c400d00d035840f941c0060990001381c0342959246030107031500700020a480550380c001c20058603040010700c01995940003c540052680c052000c00e00030000c040303115402030340b0404e080b01c8007800d011810f10014040300074800e0b054200382981d820544030030b04040d0740034039001a02401d1032000300041c00340d52460700c040c58000034660030021402c80c8484000c074028009140c800d03000d85203604607a20000c00b42c01c40c1280d0150040e40074125040210b444000103540 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 329053084 1250 329051834 329051837
    0x207020f061602150a17090a034a0f030705040b0409080c1c080405030f0c0307020a03150f0b1003020a020a05150402090f061e0316030f020a060804031e 67
    0x380c42e01541c0000c0c2030f0900b40c0306a800346507800070395003000c0c5600c03255040d0403811058a1026505040d2021540c40761b640b28014184011440740399407102d12451440320b10b8040500000200001c02e28020368042040c1002001c20401c060310180d5140410320f654543c0c1c0050000c040031071500080201425181920030b41007a0b54018074030114001400410120740d03490014180c040340c1c0ca90a030407240c4800c00d5402008101d00501000403000300c100c0303207110060400542c0b2450305500c8a4258891880000d60190560700300004000181c1e0402c0410322102200f000140c00c1c00345240e007500c0b90070b0202035000c6404070250401a005e0342c050051000c4600c111518256a41c0d034861601c240300c24481300314083c1008010440c504040929404031b071200c001582070a2000c04a20550350f110020040300d010704851203000c0e1820021400070704044054400410343d01d0625500d803401d040402c4e030107200c640794003003803c0d03006035043c0c1e0280d070303040e542d0034450324000540348d050301d0f0410b84400 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 329054334 1250 329053084 329053117
    0x904020409020304080301030c0509070c030305040311061509060a14060a090f171009020108072d0c020a090605030a0f0609020402120a060501110c060c150117010c030207020f06 78
    0xd041410792000d10b2085100f0303800550340b94114103007040310049a500140c8107440c0300d810020300d66805403041c8402d0707030f0504000c240c84d261482c090f101a00d6014000205100700410800e8000d43c104200f10058001da44001564a400c2c0510026200c240588034020080d64a0704005080c00e8004000303400c02840d0a200c004e40790b01d14500001340c1036001c0e04001040110030030503610148940b5a4540d905d400c02c01869160b6800617102082c020302490500030041c0d5018003401040080142c1400000303015180d0b4440510b002d41000e02c2039206900420204c600480c61403194894a0250f8030014014401c0e458a966008640b04010108481c0d082d00e4598160040e155030000c0d0401e80a440521500392800084100c100d60940d84051b0412440c0201d82c04510004038140c1e44c0c1d1030703054610607034072a01d581e0380300e240559101582e0180100d000c00060540f10a0a4440c00c10032000028030ae288040f0004070107901a4103c00b940c05010310070a440c89103401d5000301a42030030030310281e = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 329055584 1250 329054334 329054339
    0xf03072c060403140a050304030c0e0601081611010b04051006170405070510031401030807110a0609090b0a05100c030906030c05040510020a0b0c031603020f0304060b0a031704090608012009040204 86
    0x4505523040341d4401c03a41003880300c03800d0003920301403514180c3c004403e1a0002e414a4102c44208801c8080b044641c18040c450984e4030102c4420b41140c5200702c0c000d4001d10003802c0c080070b11a5034614610030100001c9007059114140d40c908000b040c0543c0e0010014001142130004226001501c10144002e2503a6030f10342d10a08101d81000074000c500810f042078881d0420b0a0880c08819585241d038811030f0340310420722541c0d4001c08503d0540320110000980c6200c0c11001c5200880740f5041a40d02081c00b081644001d40d1114035840c841d03100380c4e41d4200701c50765020264280c410b080380707400100d50103110901007070900609170284032000b40304954180315251603520f808802554807040070b020000070442c402e013400c80c00403018802441d0861174a000c000c405a02400040c000411040d1250182503443c1d80d070141c45000795070011014048440e1041c030288055105104410246081640c0024071410622443c40b0000f40458480c400701320800e080d074125806034038059441a400d0001 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 329056834 1250 329055584 329055593
    0x3041a07050601150e012105060105070b040f11030f0607051318050703150302030309090a090512070204050a270501021c0b090615070b0406020f03072c060403140a 72
    0x1058003d001c0c45016000c49050303443c0081c0301c03807107210001b4107104050603034007a100b0111410059010680100240684907500120740500c245100981202180814042803244030b031454081e0381c2c45529680c11000e400c009141e290300385092500c54503000007000400e070600034401020104207200038280c00d1500c5d0342c010700c40744402480c0c819210743c1e00c00400c0443c1e50140711341c403c00c41040312046021840c6500003640ca00c1044010b60040909001060f105a6160043c0000e07561103015107a5403191203084c699507400810041e0b124038200808910380a4051003000c4c04040510410b41742c40018800c2c3c0340e44c030728200c2022100c0d507500300540c103003826080c0d80404200f01c0000d4081140d503105000c12202c0500504000d110310052400780c01c1200c0d0f10b00c2203034140e6611101301e1880796250f04110009008080390609961000003c0060341548003050340c2541e141c034941442e07008444903c4002c0c1445074134010390000c904001c01c0c8041542141c4540000c1d4016003142c10f5140280c0c2c9 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 329058084 1250 329056834 329056843
    0x60403030c0b09011109012001090528020609040510050316030512030f16020703061d160506091c0507080f190314090441040503041a0705 61
    0x41640051076098488042001103020036400408100003403240003104002204c82e4416013040c281071004d2042120201c1c0304206050401d040702c04002c0000014900300f040e292032900d01104410400340455259603507070f400c003208640350003610007403d04940c4000d10004040c0030709a0030712004510000130b419075040010a4440850317402d1041c4040ca545000c9103810b00c2d103c4103002c101b200f401001761010912002c1903108016600c01d80703030100c0f0080c0aa081003425003000e40164105001c0542c0b241045519012002c805012140810110750503054031031004d0184076884001040000c04c94901020004d0125060100030681300b402991031614010305a442800704da0044240a030b50401e0910400001803a4005030758201c190b95a002820f004000c481c09021000c0410300043d00d840f02e030f20400403841021081b0205d0315424900c15881c0d04062110002c0140303001c5d22030400141b5212035401917030b11100842c00c090030a903181b030300c1c8640c4204101c0780e840180105000b0036030401 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 329059334 1250 329058084 329058089
    0x20d0207050f0d02010b1c0206090a03060c031a0f18061c12020106060810030206030406020c03070c080f0d0c02040b01020102220608101d09030405041401080c0406030507091107020604 81
    0x2c0080c1412070060030040d003903a403a01c1c1c1240c80742c0f8401214034030210080405c030405680c1225400d5480b0000400030b000792400c1d810190401d890300e0101030f4580c0c0c00d0f90000a07184c00866005411414010810080b00c070803842c80d079005000344480c07044c55034001c02c01e5600580001c207041100c14042216804149805000350340c400030284940d15426020321036000a410b56260401e61460102c00c035140340141d03480001d00449000001500340905a815116884142810707070303540e4903039410000016009401844440e028038075034104102d1001030300d024010680e0300e511044440c2e5400300001012070040c0c0c10305554003084550740c1e49107a00c40d6901120100340e09048218184000241440c070300400d02103d81c60401d506001141c2114510f4008a02c542003141c0160b0322607107014290f00440d0701c1581c0140c204100707411425180d036280c1e8141e030000c00032644081c6281c41000700755480c920002d00315400070042031003c1d654580110525800e231900d0039250040c15401305009900c550b = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 329060584 1250 329059334 329059363
    0x30c16022202130f050303030f0a140c0a0f03020405030c010c1a0c07060f18021003091506090e120418060b0f040348030f030215070203120a020d020705 67
    0x4486a01c0a41405440080c003804c02c000070f00b42d4100b4000c039607640300203040e42030000d00d0781001840c00802034103c4d108042c0180e200c0c0300c980c2040a110f00807504858a13450109d410001c0004a29201c1d10035101212001030042104030500401520030a500c84030070342c0d5244086004c0b01c429113a410350180600c0440d85615512103180c1803080480c1c0d110000f1081460038001090303440c500c188118484c01d40c044030601c92864032550103800509880e140104401c05090500c0024082c0d44e000c04100c0e09100020b02102c500404a40d481e614a41043c05603824140002d025901b0707003a00c040c4c4041101c440014216450b40743ca0f1160341c0058518403902040041c040c0200101c1040341409114140ea2010400c1503031000701845800004810300c440e04055040551418404540001103030803500c3c40404d200c5c1404c0c02500d0f140c0d52000e55411880030340204640310320000403146e00200c10405858551103005040000c0c0d40b00e62181d24800381c00780101404641d042c02682c1d11303610075 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 329061834 1250 329060584 329060587
    0x31709060103021002010b0a05042301062a08030723030a06053d0c15050907051f030209060903100b09130b010e0417160b0a02030c16022202 62
    0x42d4030400921802d413808401c216414903035000d9943c1c0303030b800041e81500c0044a010801c0c010200782c002c0d80c55010300b00001c41c0e819510001400f2604104081e22461840e03046004142c1515140d1416a045190084c1900010400a4000c1e4031582e1405014403101d0190000d207051190454001e03007040e0350107e440342ea125020400c03840d0605204120302d8050492030403903000e61031104204451298988190300107013048001c554424003032200401e510403250b009004c50900442c0080100700d070390190600c1803410100e081d03d02132910481c0f040388040030f030a600c01280c00c120080e400182429400c401d0910a05e01199424412006062468800050070f58071803401c211500c800905004c011348586410440401c40500004d41901d0a0702e4103402c2a454511300311704000c066a080100704c500c0446e03c400141c00c41c0c180544180e014a003e400151201050b250483c4001c0d2030701d0303501761410000c09044c000703c1034001d0381643c00202440c1107021041c28020f400b02142c0e0f05803401550 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 329063084 1250 329061834 329061839
    0x1030804090617060a0903020c06131d06031e0114073b0603060f0a0e010602011b0914010c020402030106030213090902300109061a03150606070317090601 68
    0x20184102d074000d249101001070804900da030340300e4640300d000d03142000d000e03118401c0c0c5044c140204008140164050542c40c1c0e680c61740c8440301800141d0b4010180324450001d500d0510b841240da102e405080c0050180022240c500c1c2a4a404841140f0362000c035520b4862060a10524650131440b034070302601c0701c100c44240103422000282c45c56403040c2038030106101d12403034402c1d10075090901c480c054078401d589407100400141c40c01d180450b610f511180340e070030124130019504c1045040316240d400a2088112165180443d604443c40e0b003c0000c4200c882001004141003108030001c5040c10700c1c19003440141c01140603070307000360447c401182e000601c5645040a80c80200024110000108500c06d8aa80019203100b0650041043c01005c0620a401051241b810759000d41c0300714000c1160070302074941100038060540c032800b8003d5105404046905012072801110404a6107200361a542c150030000c5030340080174180c040040c60201000d5407040500c0d090301616030303000103007415071 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 329064334 1250 329063084 329063099
    0xf03030302030a140c2d0406050403020a060c03140307050909090304061107080616090b07050c0f01080603071502030d0204090e120f0409050402010c0210181a070615050901030804 79
    0x414403c15503600c248040108880c92180c0020364885d0100106c1001c0d04144c80c106440218450a424450310b00f00000c000440ba9044401030040702c0c42500c0b00889242e880100707550007283c0050103808a041d0f99403070900c2c400d01c00e000319808445400c03e0781c01c140c4084089001104119030405035030f480000c052003202c0c0c0002642007142004001030124030304003405542c80f040e01500c0b50390748940505265884e54050104040906000ba41d00b0780c44064504019966500450b903050003801c030109442025482128a14414200a002020260300d40707600c043c11002a03a035640c0c1140402d203c42c1c07040f09100c1c0001d000074090004003140c020f600f00011814400058035540306040204144a000c1100d070050301c04903824290000380503074850005032001200002c0003544490302c203406046040d00f0280c0d007200103400825034491152681a01c00320103a007405500d040350428040d1100088054000400c400c1c4011010b0111030380d240c003c943e6410081e001100c1160b0f01003018000752 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 329065584 1250 329064334 329064341
    0x2070204230f0c04080c040203070e0d05030406080c31090608010e07060c0c0e0601200f07051009090b040905030a021005060607030806131407030b0103110a05120901060f03030302030a 81
    0x143c00400841c581031612000329074980c140d00d8050700881e001b1001480c0280102f1081d090b110024084880c00e48281c1391042d229440390003401e000c0381e000b1022a5100c003c03007083d240030000d161110690f09280c145881269191111000504103c00d000401e001119000ba14000c0c896a4000309080250200a13400c1c442c10303402001c200a994152200800c0340707604560101c2c1c01c407420341030180d2030341c0c00101c42c105c5240d580c24860f070301c01d58a401034900c00064140085016042071302d010589400c20040703da40303400b0140000036403102083c05960900d40c4912510b800c0107000081261440e9211030950300410b00e0103004d1b8010020400300300003540035071540024104c400d07500c3c214059801916038600641054001e03088680c6601d8900c126600c904d02c845118450800e06143c0440000d0180200f401d42c1400203040484070240d02861200f03403548540741e512920b00704148941c40c0e861014009240091542d210000040c407100010841c40c05076000e55005607481c0f501003444001e4 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 329066834 1250 329065584 329065591
    0x271f080606070206030f180105070504060f0908100b0111070303020106060206010653160c20010504090203040c061b0f020105090609030714090f0f040602070204230f 73
    0x1071071040020100681c0c5420803607501c400152114022500c40c46142a6040e500031022181507207000280000c2540140250007160000d07524651458130140d421285411588918441584007281c1030982c2c15164000b0702d0680d006250001c512a0070b0100c1518018040d8800d0740540d55661040c0718071a0f0502200c0d01500080c2043d0511300010244540c2501e03141058080b482c00c01c442c900da0150340811200d000071f03400d80c41094000004a402d00e160039040e10604072496400c0b8821003240e000d071084002064100c440c8490001070081c101040158000003507040210400000c25545094409540100e005403401e941180c10580c000c0e0070640e4078000d82c0307c01800d00c80f140380090150b070300350400c559080c60481c2d2125217402c00b041c620300a07503580729407501403088086803080c0d501c148115074000c1101c269510b078031504070074007084c2026503040b88141014000180031039110340013460701610203000000c00d00700c2c0b88001454250f15421040b1903d034402c3c00c2c0941c1101803002281c2 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 329068084 1250 329066834 329066839
    0x6041502061003033515130c0e091003020a0f08010f020702061903020409020715050c1e0c100203090a06060509161412092a06271f0806 60
    0x50541143c138094100e68009042c40c11161044031402c03004c4494001c43c02c400b0f91040b112240e1800c0458440f852070501403070142c007a40440701c40c1402030f642c500411003421243d80323603a83d120020034240010102d00611910700000070780d50000c0140c9442440d68001c0581a020300c444900304821103094481880c4091a060b0043c801c5d840982c0c2c460701211180710100610350000d0302000c04c1507019003d2039002c01046880800d180302401550320940e02115024002000071340c1d1070341c080800f180580c6a00c0003c40c1d00c80001c80310203400b4032000380115003420044030002c1500c0002c1109a9004413001718040e00300d01d0307408040040500902c03001d0309044030346080d1440d183d00201d0001658000213420001c5017101c00003010ba03070400300c03030111855480c010f15138640400d8143e60340e08588503100418080b03988411500070241401415510001c0c2500c0c40e1440300030010107090000c0c0040c00404e0030b68a98068107607603109440c42030f06c944801804800900308809001d01900514490 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 329069334 1250 329068084 329068111
    0xf0114041d0313030c1202091501020f0708150609010e010b0f1210050108060a06051c02090a0b0901260402270f010f061701290a0801050a17100507020c0604150206 72
    0x300588e00c01001c039a1000070301901c85243c6005200407488c000340c034264032030176009082010400a80208240a6210724842040d40b07075160902032140c032031000d1007403011196226005209010800c030041c403031520440100e034281640300f1528003100d107060300c0b4400034003140c3c0020032003560410308440c0e200900b1903007101c0380c615160707024019120345d14007403441d200307c07180d030002c110074540c141c803d9040007520390301e0703101e46680410480354000780280303010481140368040c0c1c903002007156540e8600c6009400031207071204c1c2c0c24000304940700250700b450500545001c21000119201240c862034140860301c4055241801000c04c540e0f081d0043c80c1009001141c21012211344240c00d030444c1c1d07080791240c038020080d01d450848030101c1154820800f5001030351004040c3d110314114160351b01220742c0300c0c905550b03500161003688448840c41d4180c10000610000e508164002e42d4010000d0040c3d46840314000b0010704036903c1b0f80c01000300111101c1511195660412110741d00c0b184604850 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 329070584 1250 329069334 329069369
    0xe0a2907020307210c050109080a110a0f0b0606070f1110052706120907180c0804140102040b04030614010905070c0f1b0902070201080f0114041d0313030c 68
    0x24540241c0d54000d9040403800d01881d8888540300e005c8659941d904007000300001d060301e151106142e4428100d0600180c0b03110407500025501103400c5a01c6a807080800900050325511b550030b08500500c40c03070340324605020240c0840c05024100303c44611417003440c880c02450340100000c440b010303284071080100c20b00a651b40c5414130310f8881003a42d5115001c0d0561050040010f0071403042d0020f00901051200074450408030000d1001300340c03403142109840d0300c0e0030030410b41304890751005242e0016890301d0100b0046420b0224854000e90f400b000546815100c0003881400d0748035500446d640350f5900000c80512030841036950150081e004140410304141d18002c085289800c00904606442282c0004220345031f070169042d07085901500741030310395481c2d9160007900128401e034046040c0c0720004544000041100c1d05071240c45582c802e560091400380302c028102e115104000410860300f000040d042000640088121100c50127a0f0ba800d520340700400880c42d81c4042e8004c0c1880098 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 329071834 1250 329070584 329070593
    0x60603021603050c161d01060302070c0b130806130209060906030c1504030f030c1416060c030c061802031005010b160302011d0102041e0f0302040e0a2907020307 71
    0x2030703980321909454001d445001c201001c0d82000940301c404581040084070024102e1404442e48041654010321074045a03030395071040d01130348620200102200480102800a621404081d100c03254607241c11254250315000c0c040c2c508401550b034000c49902131550001103240c00b04605a02450a950701051805c0c980e000c01e0386d815480e20520312410b1104100403c42170141c003624001e58004c039a00702510301e182009000380c13040002c19114400307514402e011280001540850601a0344002c010b076a25156044500c1448600100e04010001141001081090048030090013103d04001090300c140e2041601d0f011021001500183c1090010800044402c0988a604843c010b6030f010000e20f506c0e08030b004110052070f500303a808a10251111100d0158054400e8507001c1311605078180c6048a5440500000c0c4110034500142075005d00c010f04141c1c200503210842c0104541c0e10500b0340da80e10452012100b03085078042880794607943c6240e8001790060300410b1030700140d803034030301a03448 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 329073084 1250 329071834 329071867
    0x516180e04080c030a0305061201050f0103020111030d1506090f030b010e060607060507080a0f06080304030f06110703030c030c090506070b070504150203090f0a0506070605060a0f03060f06060302 86
    0x60010308219880001e01440340040890320680d501e00192952042c440402a00801041d24071038010517605042d10034030320701441094080e10401051107856880c40e401114191007860b811701c1c0381c1c003003400990005203050181c0701031000486c08080050303003050002842c034095030b0721450100c41c200004001040000a600d415070f0521503400042e80d69440200f0100d20414034006c244030300d480b040258856020051034021130305041c0600c511405014040e0a9139414025140150402c1204100240b044140040071078410440801c0a9001040140c03464000c01c805501003510745c0086802198140b01d0401e901500c1c1c1004580c150520010079014090ac14000303260804042c0403c250a00440a0300e004151403262404900f0200c07000a4898001181c2203014045d1110700d2166460f1461244040d650060300060401d04291100790140170003405880d00b00d02c0c0c44c40c02007014601c0b254803401950003511b000c81c43c00040c42c4004110740380e981c020303010103205210b0b07100c0c5050b01e1407 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 329074334 1250 329073084 329073089
    0x1302040e01051c2004110f0307080c0a05040927350708090406050a091406090708160c1203060806131203020f09180601120b030d0804150906051618 65
    0x13400c030745810f5030410110300181611808405c0c403071070204000e4110001c520046210703941c60768400e45030342c50f4131030481101e0051070524404280148000e002c0d483c06580454003032010107502c104100381c18940c1c01c0088403004030641d284500107403000c01c10441024500030751800764112000083c8501598140f0313010300e00c401030a440d0300190010143c4e07a503401240c09040700800ea4a506580c0390074000c010200b41004040307102c6140e00050305480d20111007031240c030894071868416594001e100b82455010b408000601c40911242000300703c81420f09680c2903c25100000c409041000b0300e45071250003401140c6445101c0841e80006564604800174820503090142e210360b590b860707480b02ca0140322180e903004100301e404020314806880c01180502402e80f50318000c00032900e040300c01d41e03800c0c00ca11030305648141071034021284a0044151f1042c062a030800c50049c1020444040e2002c0d00c00507119035031581c050260940b107507030361543c081800b030412200550840c03019000c00d030b4952 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 329075584 1250 329074334 329074373
    0x22101140603090f0f06011e03080d020708070b0f100e072106080303090a120203121611010c0921020102120a050c0a03020703060c14070b04021302040e01051c 70
    0xb102040788210b082140b000c0c02c584010940f40880e0050040303c1d62241c0920410110000c441c40300300404e00124070010a580c0c00c100840d140000480d00c8101a50080c0e10854070035400300044408500d40e00e055600680900700a00014101111807020707102050704520807010016082c081c145411407004c547c4000710120b400e603200e500c0c0078a900100516440303c40c49000010801c502c80700c0c041501d1032103034070500d0010340d82c038401d0340f04036583c2c0650940d01540607150342c04070b840342c400101c42c0000c0402c45d191054000070386e6402c03982036841c0c40d107010307010413441300e400c1c000c40046e0701c0c2c1c001c0b200d5214000ca07084004140c000035600c50000001e00030aa0000030300120041c840c400300c032140d520180032a0300041103850002e60b540d50038030007640c28a00e010400602207100303500115100b0041500c0500b03000598a8031416101b010f00b089902c00007211103400c0c528540e0000d000103150407100c03c6025890131041c008880d0b400031240200e40d9140440d900011003504070b440c03820702c54 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 329076834 1250 329075584 329075587
    0xe0a0b100e0402190203190203030f040303090501091e0209250c05010b0604060809060601080c09040b010207241b02010507031d0409060203060f010f0807050a050409020408010221011406 82
    0x166020030028404c80500c1003c11007031003c14919150004018920040c0540c4001076004022000320388902040e04c00100e030002c144049008030303101e034000210142c09407000042e01c55a5075500d454000c0c01400c60f030304901d00c03121501c1c15864160b10381030b40038540f010030605204410302c521001c046521040814000c8000c511814420250300c2005c15110107004550780329118040035003460030459003a0302500c600c0c000240307194400c80750310380288141204941450205c0d0100006040030364003050461044410004502c3c0c0840791441080390182490001c04014107401403003d034000c90303155048000c5556610060741d0200449181680601e4044150f0300302148511700c07100101c00c01e5038001e0521031080c1c28000b441d80154045d090071240407121124440040d10f030400340142440104d51800300013900a401100241040c11130351518900d8180c440001508a03005508004440e070b42c0403603182c17030307080c40c5034031006411013030180081e26589001c0ca440f031120490092240103c00 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 329078084 1250 329076834 329076857
    0x11070b0f0705030403050f0a0c0f0f27150f0501260c070f030e0120061503121b0106060504080715030b0913030806060a050d0213051305010e0a0b10 65
    0x30f03c1030714099580701c81a41e003009030484005981c0c0032006419608200b141c400042e4406d011310310070049858428110000901e03180800c200c40e020070890f003039050206401002c110b0400e114a046000e50074400d080d0042c20320324900342c03046039900030905100038607030154000c0c400c021103130085256a032881030060303907828584211070156550040840043c0000c210401d40c001200441a40003a130314070701c10b8180b4401d4030b007130034244e0f0003d421543c00070004076220f9806c080015a64400c06001c0f01c080b034500980c3ea0190380c6c044041d4420851b410002001d407480d080c018017008181e40d281207401c4c2810485002e4981040d48500d00800c3e0f80154038041032030103030f0880526441c009003400307428030340b60b031143ca881110024110300182d10040002c40511b00001590b00e18002c035034400e810984d01010084c029400b84444201d8486c0002002038203a80e043c440c5101d00100c4080402c85500d0668080f81c0a403020700000c8609043c2024070002ea12a03003a890441404c62a14a42058 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 329079334 1250 329078084 329078093
    0xe01062306040b04030b040519030e090601030608030a030501031a06010203040918060207150c050c0a110d050a050d020c15030a0903121514120d080a0e060f0711070b0f07 75
    0x106030341c003c58816102043c0001800010000284528020010354404c0aa110381c03205c040c5910910090205503101c0341241581406202c0e81d5107c041030400082c0075485004030b61440d0410301d9200002529940140100140e42c1c0c905000c2070b108242d102d002d070030b010340040c0d280c0c020341c080c0e800100c1e0744115100801c40b00c48040e101c244d8100c0c1045569803480c1c10a148403040c402c813902590780c1449c0d0b10704030641c4500304452802e5000d9000d007070004441c5d603d800d00c1c4091681100d0303200e181e40910802081040c00b903211b043c1c0c400c3c0c00a04900c001001c0280c1030481e040715281c42849802c04a094020103202200e42c045540e40340000d1b824201e14084e070382406aa002c110b115490604c203e0740f0441400c6080c01515030309828000380608070b03800c000709250200040943d940289480e41d003401c0c0286107035a0400030b10340740454030140415400345018000c9851002104034282841122600f2080498144c000035005d0080c4a0a15000c20400d10500d9900150590005104020710 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 329080584 1250 329079334 329079337
    0xf0e150c0f030115080609070519110d0f02061e16030f24090504020609041e020724020307020d0e0315040602031509010f03150b180a0e01062306 64
    0x5070698034041e0303120750b15810f00c41810303501141000049003040021450601e0203101e01c0f48202c04940c1c0d8289490721402c6c50040d02d00304101c1450a110b0b004100c2007000c2003e020032814034180f41c0d032b41c4044004404000b45000000f1341402100f08440c05510451001040155032044041805030440b06040310101c00405a480300c0d86403041c81e22514481030316406028148000c0044000301c002c1d6100d000c008116142920000e500a1003000b5907052404c3c10303001031412519001f65194406076014455080c1e80c04108112000e01d4001d0841c415104089201c002422070581300b10f0540c80e18141c0655140c240c0313146d00c418800c1da09100c041e155010840784030031296250041d607013401c10703144c854007940064424140058a880c5072036028100141e03818109c40440c46041c1c0a0b070703e1511b41d5a0b43c1448003090703040302c580314180d00400e51102c2c03890212002c0c100302c1040c020300d05011103000f2504e810881c0300b426410040200200c00281c0e0601c041b51544100c81180d0000314400200305 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 329081834 1250 329080584 329080597
    0xf0204150b0f131e030506010602010e03070b071404080606011d010806010c0227100504090b19020d110a0305090105010f050906061b03071502030105060412110306090c03010f0e150c 80
    0xc41c02c03442c04c84803601104201049a105004840050362500b0050f0300340c50071400014100d40c42400381c403000c40c03444a645600302c815800c1118071410507280b554103c0e070142d004a0015402807040c00320b03d5030b1080307400a048000b86101103040d030300c800000384160700282455040200710401704040d56034105902030f840800312007954040010303500519112000301ca60380c10301000e1050006a40c1842e0103000030044d4031155032842c1c0c0c0c0c2d42d00810f54100d6612a05207035850350074001d10480840c80c1c0326014104d043c003603405444810b4003000800341c4900030654a900e90500340104034452000782100155041280c80641944c1c4000103d01e480c040c2c012061983c000e0240c5107812101c2c088020700c40c940c011140070307811450764652a0f007644800c3c400c0a0f0081010002000118103d0414000d000d01c01d64500e486017501c0e40010b40703025400c0c1c1d0031813020f41007007840800a150902c1002c80d00540307030009102503400b00d100281c0300d1265003092045103206100040c041c07629803040b11035 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 329083084 1250 329081834 329081849
    0x10f05090d0e03030a0212030a09200310110a0507020d0c030c03020a1e05040b01050904060602060132010c0c121101120e071e0803070f0204150b0f13 66
    0x810314054003840d40d2414850041d001060080e119a4041d04021085a1610a864005020011002140242e65400201410882035858a0340c00016042100c1f81c60116040046c540e256801b280415061a405400412405180c0320a41c600c0108840548050905508166449130054008681e00c1c0115410042c0940000d0102000308010403112000303a034000e4030308103078650711425140562401024100c01c48019220204001d140c540c10121030707480180350560518400c207020a081c1c03446034001c2c401507000a030040c0034103800e098008140810b501120040c0851203090041d03580d0000b100141001003840b07a00c002d1056821407040244201ea00100d0b1a0005051140000c00d10008180c0018022615181641e0361070242002c001e80e640c0181090900d032115080310101d080d401c1c070200c051900c0c000644424240050b155042c06100500c021009510400c811101c0b400b00d200d09440c00580d040c0a88400441501e2070030070605402c80e90b81480000c1e0034040a004e502012 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 329084334 1250 329083084 329083091
    0x3120b06130314120d050103030806012105151f0809070612020304210206090105070c11090726010302030705060f070305090d0c03050114090601120204020f0d09030f14090109120203010f 82
    0xc98031780c0194003040c100d81c040da036500c41c1c60321840011658040100400203100711100b59050006501c5d034401900203001c2d148140340e0101c0740c004510752106410342e1440c041e100e9003c41075002d030001501d5500c1a61640640310745424910041c1107085400c00b0080308d9070340400020100000c0c440e2410803c440304200300d146000c1d002c00255100000c640d44485542007a005c60b800d18001c016081100c0c0d03015900340301c00521881030164a407802407100701008075000700654505e1040030440058034085002d02205e44c150b0061524050440d4441e80c040c000400c080301e8040204400c0d54101039062a1440d03843c141100013a081c401c41c000050058440900c0000030808150700940c0b401c8040e240e114426070300c5070000c2c3d80b211024800d20002e003050300c094070300515060380106114a00520030609100d04004928101d8070074540850124440f04144100d50350003a00c808042c02070805040c1c9000d60020009107020300c0c0344a854100c0000d41c043d03600315a002e420aa900815504042 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 329085584 1250 329084334 329084347
    0xa020702031203011503090206040501050304050a080301080a050f0a0302030a0c060209040f09020415030201140a1211030702060114061c02071b0f060203040e0601082203120b0613031412 82
    0x702e1680c0d02c288103110a24000148404001d0b009004402c64103800030040c90602c0e00e004e00556141d84002e1007291107003d1404503200140c0110007450107003c0c494024440c0c080300e0b00d021072034485821800031650b0301119000e80003990000440340c3d6200c0f42e03c5d14145c41c802d5491b2000c082d02130030701c2d400c1e486424080d0901c2d4200450340111001030088906200740186074160210501c0d10307001c0079001071619600c40d60b00c0244c1c407004001d4031080d4500600d01154400407003084500301900c8004e514400000d010302030b44e041100501425500c0405a102452600060341034460061072403091200303501c40c030000d0411507040d42e01054201c0550001040d0600b1110034000003800b4513181d01d980c840b00403a2091001041c0c0d0281c1d8007828200c0c0751034907008019034028000400c81d101070001200d046644002c4088031121041c8640c65000c800301c4140502c070261002d080c03026008107000c0c41070301100148040c0480403250070080302100780401410490a106e00703244000080c52000801 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 329086834 1250 329085584 329085613
    0x120c0f0d050616031107050a290c0403050c0303040f0315020c031b240117120a0305061807021c1b030e0a09110f0901021005090a0501060b13030b0a02070203 69
    0x8100341075070100305c048081c0c80e10f07204a001e40c440141490380001b1038500000d0641c07400340b408040c0e114a4011180c41c861580c2082d9000700c820036106800800c04100b0440c04000d40001c8400440103181024108166000a5401880060010700360300040701d0b9038083c55030446020521501c00c3e642da9048a40000e11841207004005c40a403094420b5481100d5895008003400c9290000e80413082e480d10380b000705000800c40a10100e4050304042c0514180203500510b01c002c0319484c0415030b4030b03001c4100004000d600d02603040390058070041003002503010405490300300c4a40060b81011000003c21520301d641500314407040c00d24407500c00e0905801582e040e0041c14220740c240c0c3c1441d21140305806070364041884030601001841554480c0607480d000c1c00d030700c07001803040340c0f00030100c10010400d81c1c8050359600c406420040700a400e0240030b020b068058034098600f245001042e0001510200840c40301401c05440c4401240c46111240c048485c00c980050440702a078400c0ac0c1c5 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 329088084 1250 329086834 329086861
    0x71502160b1b0d090602040506070b07170c040314101a09010f060917100501032009040b190912020609060916030210031805030405040b120c0f0d0506 66
    0x4181c494000c410300285a4203007480c407000c0c071004501d0030300e82000318481a1102900e00c00200300c1e00c1c56024400071541c5d8aa80d00540f592a004040b424440d003085100030304140441c131a0306012181110800c1103849800c401c07103048940c0b0001c80a60304040078401400e015084003540c82650600b520032465603090425030442401c2200d401286903a1001c244408800912856002c21402002001b90307030b03d004400c10b074641210301910200d00c0c40142d084115035098000f02d4101d24444007001c0c001418140000394800c00ba1544074060500e82c440c1035141c50014140344206500c03c0541c0b9500301d040e0400f180c030035030103940224103001100010b9103480084820599a1003524001601b000000a005521f486101e9000e40c0b818119003d100f2074030f0301b01e44801c090580b50000c074903404000c003500100544c0100007035030316036040000304400d6a1110a046110310039014503461201804254000c1c0b42c1e0045408908050482c00403903264068000007034210700540c1c00f084948818101c = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 329089334 1250 329088084 329088127
    0x601031e0203060117100902090f0720030322020906060f09031504110901030f17090d05070501080c090901090c03090b071d0a321903050d050301030b0705071502 71
    0x13010fa81d401400c06001101f290321403c0c01030f502403014400b0650101c485c11139039400c00c1c098a071a402d44d0244800e0300e200c1c06200c508500ca1640000200519204400000e140100d18140d1042045d46113030001149410b000d0303c0d40d8440c00d00002c519104500100407240c40c6140a010395124070140b03010b40c02202c800302ea054070007100181361110140390600b02103042e41d80c403540d680012400c9881c2c0035800814950b04145110040062604a69070007040d500b80c0e5108400500d281818070000529030640500b44060b41081403001c05d0966941c1c5e2905415107550810015041152090840c084d004600700901526443c0c0140700159071300c07204840c91b07100394018404507951004140718400d0818400c54500980c000d40c9409114000031a489103007068541020703082c011500003c610b4980c0405d20080c036400003108004000302404822944501803d10604561441c3c60340c410803040100442d0401c04001140790400490040500c07658030201800c40d203890910544905111441 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 329090584 1250 329089334 329089379
    0x1206030c1e221418120412050c210d08090d1101020415090e0907050117100e0c0406020f0726070e0c2104080415111209010f0207080601031e02030601 66
    0x416440c0b0002000074204540315807000c81c3c86c2c90145000e400019101641a0482d03240c0200c405500e075565804481c0d90307004107810b082184203005041054940009002994103200064040040c2d001d00454410718008060900d4000241d406075014020300c1180c2010102c001500c62078003416910090180c1542c0c3c2600045019440700d501041e9542c1c442e224003800296018200400104240650354210001d0056802c40c07580b105c80341c3c2c4100c46c088541d003071036000c04282000515810010380c114100b004000d4050907082031908804c05140c038020341c0d81058802042100201c003004884010302c18820011881d06152a01c0941580709802100e4a20100308071080700c0b4100c035502c03d0045601081662809261031405144603101609a134240050000060303d034200c148003d080c0b6600c034004280e0340c0c88403003002418041101030030100b10340c401ca40501090340e000645034150382c1c0001ca80443c0300140280d008210120410080d098000c09000083c03551030380701000b80c54021b0 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 329091834 1250 329090584 329090611
    0x60712110c01092a03140a021e100311070602030c0c030a0f1e0c021207031502030f0903070c060302031005030307060501080c06090906040f0905031206030c1e2214 72
    0xc2c0b038404e5241c0031400c009510b03400c0f5041c1c020800544c080400c0401c0150041c103072000a109500000d2040d1000c0080c0c100281200104401c54505940c0c80c07080301c0142c2c14104050100824800003d00680c1c0700100081d6001000c2b07a2a0111316040e5031321403800c0411250f4414401400070640c01600300031101042903d0155002c070900b2028044588145a660012080c410340800c2180302a01407e02d40602802c44040007240c1841e900100360606d845015a0743d0034a04002c01e54140c2c001d1543ca0280c2051015200269010030000202d902034903025880343c54160712821002481d81c002e80d4148030014003102003040c0340d04594120b030545c505a600790300d03511061010740e00c21095117640c4045010002940b526003540001c1421100c4c010000f80c41c0c2d110b940719480c3d031340440c0c1e200c0c071342e90000380800400d46030401c540d20310804143d90300d004000400d031100c030401c000013121910484d000211890111702108180703464a40401c0c1c24059450000e8030324403200825a03403151034660 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 329093084 1250 329091834 329091863
    0xa050c10050a080402010c021201090b041b030506040b1b0a0309050c03060108030a030e0c0904080d0c021203042003032b200d0605030715120b03060712110c0109 71
    0x46040e5034900c00b86850b20743e41c90b0740d03070342c01151009400b030002c03030744003c0090324607812410920400049520401800e152406d160500c0ca00504080390f06051018070050b040c4000342000c6000c680165102c5145040c9407600c0d000881c3d10502c2541d45c115101e404101070240b0307a80354010480741030180040d5080020b92078203140c3c44103001d00504241c0d60040209603c50391184c1e10a200441c0076609850000100c0400104400741c02d07a025102d42c0c07004a00381e80542c2051081b0051894a80020140201490040500ba0100a0000d80300301c48c03001c8121002c4070039002c03910505100a040d2681c441448a14034034030304007400c0b42c030f5401d1541550000d00001a114100070400c40c040c4580f1140c1d0714001450b0340e640511f038a254516150540000c140d201000301c40c002d000c10060391074941c04800ca00a01e62821a030b01c6112660501c81062503685002c01c0d07043d041b1003140703130120280000c1000c08024004000401031400e01c0001c22019608042d440505506e10401e080c40c103119 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 329094334 1250 329093084 329093087
    0xa090314210d051f06120204090903110f0604030c060b030a060e03030109140108122505060403080723160b01090e07061106010b090a03150f05010b04080c06030c0c0a050c10 76
    0x80c2c0b41122060b03184c1480305000b114090544015010308162000d440c10361140a24016a001100100c0201c3c55120700118854002d101c1c0441c0d5402c007600400803464180c074028240148180301410507039444010386002c0d01c0501000c004145c028006004265004800d6645c0354400d10a21030038900d007807441c040803852100854100c400e01c42c000c14160428400321080b650141c1940c800c208540051882482009950002c841d40910301400306807415080292081200408020401040c4415002d1075000c0340e84060b842009041c2480d11a02401900c2342050a6400c000c1d01c0008010000600755042d500000c100d807c40310195140240c1d01c540588038080030a050406a80095005210380e40054000c2c1002c0c4d603008000304420740d03580d1169000400c00074002c0d40c07210384540100480d2015402a140100f4025080b10700d003616001405444000c000c0c4060300c2000000049210070304071109603040e088446040e03803140f0040b440c01943e951002c1004074010740c07144000c4003015 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 329095584 1250 329094334 329094361
    0xd05011d07270c0306031a040528030819020c0115050f0108040b0c12010603050601021c020a02040b0f0910060e010905010f08061206010f06090b0a090314210d05 71
    0x8180c00c0c0c00307448504601c003100c2d02c00703440210212010541d07180700000c04126840c15611080300541c400c007134142000d00b803060421b1510407102001c0d1a0840e04240103450000c0050710942c0c2600c3d2402d500c1d1203540610204119145010b030030540046424911141c066000407030324001089882c1401c0d554130244030001045c603004502240101c000200840c4404042035802101c650b1003038a044054420b031b15070400c00707070800b4001a9842c0d00f00b00e0b00e5601084842c1c0681c100c0000340072080740d07011009584e0550403600902841c0c031040314418548a00918110400b4010a46c40702c500c0c0105180c4402c40b0907202d483e00041c4c01c06010809540a484a1070581d10180e58600b02644115010b0390040d1000d001e05800c216000c2d4981e880038806e111060107404030b90047d04504c5d10b0150014002c2880360410fa00301b5500b040b900c9013260f00100020200d036488210f103400704400c138413442d013080c82c40d0101c0d90401180355024500c07400006c1c000e0040d0360340030b41c0400403601c0307902c00c00015 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 329096834 1250 329095584 329095619
    0x2031804050105090622020f0a03140907060e041506020c13110301030f03050c060702010b0a061e110307060606020a0c0e04020306070e040609230f0c03040f020d05011d07 75
    0x15100004503200d8244000c032011200b021884081c0d06d041100c841788203c0e803128481d5640340b400425007803030440d494082e80c4c414a0041240304030500300301195a4170381001303215101c1440344c00555005651500c0d0800708021081d4004443c0c00b80e41c0d101c020751560983c285051090f03100c110311014000e00c9110700340182d07041d41c508900710303070943d03891000b0303d00341d29403d4052100c1440350400c01c2000b04051441410f0544c00403508582c004103100c641e2110b50001018007900305081e08851a00c441c1c00c3e1011416881d1818405521030b003243e003580706601c0d000d0201c50403c8000700707660742c00044800c15940f1034640d140400b503441002008010041d24000d42c5a0441c00110b42018860fa040c480842d10051001440c40d41da02c10001c111441082c42d20360344050620303100043d0361110f032559440203103200b24240c180f400c1e49420041d880001c00c000c0c100811242c0480964898102600c90785503c0002041012000048035500e03040180754002075118040021401501440701080c0 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 329098084 1250 329096834 329096839
    0x9110109080d0503040f0b0405010606030b0f09041b0b0c0303010609120b06150910030509010c090501080f0c04091a211506060d0c0c03090602010501030b0f0910050702031804050105 80
    0xc491030049411a419030010f4000d8441c40075041146d00800d0148414500503031080b40001401032030000c0107000e680300c82e40b03003611406210009041503102c064600354450b41c07000b180038880d0464024040481407681061102c60350101d40200c414500100450503a2115124000031564a01e8418011880032800400d2200005c0c0495203d003046446100055440900f580c288000e900110700309104c03980118000075158000d00106000c00c5c400d1100310007181c5005880281403c0000c2d220040140800c0c9035180c400d07001035900007004050310082c0207403180602c480c41041a188000040540c103c510940d800b03074001d0704410220840d902001d40c1600034111106401c24511404100200801d0f0822004c02040c01c030f12440384201018401345032180308500e402410000c00c440c01c6500310400b9a0f241c100140b000c645865a2603034440c1b03c0800310901c6544101e00300f4141480382500200381400c0101780941207070040054007461080d40619281c2c0b00f402403c010544000380308454 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 329099334 1250 329098084 329098093
    0x12070809060403120b030c03241003020319050a2001020c01020105240a0314010618050709151707021e011512170a0e0f030303091e01060f03060911010908 68
    0x8542406035004000049002800d5500d03281d01c034000b02e414000c034070008050500f600c0001e00203c030127066085270000220a003454043c7e0035517002c00e5070b0781d25400c600e42c1303a4014031a191081120400c460840c00394401c0744103946020400303411605040702c0c54054007601a01007030890a51051040c2481a141c1a0202010b1170001c08450030400c202c084040e040100c0c0300740800450400a1411074107000103000041040c541001055107a03803841c0341011403800d2905010803264016941800e642482c56040c0310700081600a94110090140d2190780f40c201d0b40400c00d10a402145501c40502040720583c13414484c02446400ca030310540c181003159107408818030000039901180041c252040b28218845508415044000e401461078200080e420300f07031007125414101014000c0c0802a0011811402d0490510f900ea802041c480400081c5010b000800c0d032409410400082161110307101c10b59441e030400364040d01807070b01c0940303121071100013465065210b40f80d5907081750612400341 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 329100584 1250 329099334 329099357
    0xc180f01050103110c070b0d0c09030809060d0204121202060705071e2f0307050405040503031504060b040b0d0c140301062102040602030904050604020a0509040506120312070809060403 81
    0x540080c0000c3d40551340641e4144030110800204100c40c0010f030074210001c0340c64020094012096800d010b01c0c2c1002c10200300c1c1e08100082088003580c140b10401c8450549540c40d103200c8070002d0207194000c03800c80760742d04402030900085901c1c0e031000c00d1146d82542c00540d5208000d0718240708070a0020701c446010071095200c407609880c1e00701800e120711094403048101d10801944e0301c510032483c0300c00b808080000c01461404005200041000f41c405001c10725094848944130b0000400e0681c0c500001200d1011a603229400240a001c0822038552156100c200d06801034100540c1d82412500e070090f15824603000c0c00c5500c004c041a2544c0d00d103540c2c2080ea044828000c41c050300f0740718046e240e101641900403030014202903c0300d6801180c0b5440010b08000c140c0d20041d040c1d50140d4410000850300c54ad110003103c242c80300c16540402d00d500d030000030542c030050844995030035001c086014803084030b182000b0350050245036100714140d2118140c0d9038480c001039600070b01182030113042 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 329101834 1250 329100584 329100587
    0x3060f0b060f07080912010608160e2202040f0513060f05060f011b0c033207090b030703020306011202090901060e2d0414070602030f07021216080c180f010501 70
    0x380070580024000811b03010b030b008201400e54815402c18605600001c01d040000b13070130411824014900501c140303849040009544848400f40041c41e4042c0c21080407180a546881d00500d61290f00e0a204110510b846803912240200040341240c0382400c15624010712850f500a04e402160020581022401401c1c0107507a24030800149181c8400c44164480100e03516161b403c00450003513054603c403c0c10946590707400b030010b8442c0840d00703940b00356501e85541d00007800800d640c0c01180000305010507400003450a0019813000b545071046000218040380780c100a42d00107842941c800c0c1c0203860340c1920a00743c0b05a8014464240189800104964043c00c030901c031612100701406944100c0400101641034100d5041e9040c81c006001012541000c112200c024449031010390f05000c601440c4031804d108500c000b900c0794684201004901c1c038184440695194070754141d610180c0d844094684414910140310701c071f2402000b0700f80c4524240008180310320038014010b40d06a023810300 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 329103084 1250 329101834 329101837
    0x1603120b0303090f300307062703050c0a05010e01020c0111040602190206040902160b06030703080d09030315031a0601030506011b050c0618040b032b021603060f0b060f0708 76
    0x20401c1c001d0f0390340b00304c1001820011280b40c08002c103d40071b5175896403142001c0302981c0c001c80c0000c44040100140c0b00d5102e2008041c0d8414541c1490400d50758006107442c42d2a1114182c00039100d94a40031450449070070541c0244450605900203010fa00c400c0941c600580c05175104002c0503802c050702e00d28480d58100c07004004036200402c45814540c480082204980001c0c622038a980c459400800a005450320345540c002c90880c01048030b0390459136a01d650380205a48200619280c0c400c51041600941045100701c16a103207a00115949041c044007005201c0880603025a401000c00c0c8103503c43c3c06100c1c454201a15484910340440040381a003a03861441503980c0e000c0c000400d01d49070750b072600034036950480c0d0081001d0b0203610703010401110010809507200394802c500d00b07144800c81380c20300d0050f11186210070201d180304c3c0030284d05001c0400d846101b041c10f840c002004110840d480405800f800620030800c1c0307000c0078240801e92042410000c40302c0001e20401000650200 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 329104334 1250 329103084 329103109
    0x10170703090b1e012907020301230109060f0e060d050c060f0d0f020c0a0b0702190b1501020106050a05040b010507061409150c030105010804081603120b0303090f 71
    0x900001e04500030385a91031030440503103c0c02c000c3c01c000c035150760000a00f024107a0151042c444460704030f10100644841c07440c00100c030384490301008240c11055590030361044400e22078108413a0712201e03842088611901d000d0082d410420b03d843c40c0458203055501e50b040541d00d80c0c0004100031b4660800300000084440c4ec03ca40394460000740a1050b1030b1000600b0b035003c103030200c4540f1901c0c0d48054400741c40084031000d282d00c0c030601000000d0140001d205140310b420032056241603ca56200302c0c00c0ca02c0b45030f0009510510000c426003040003102c1e0300d0344104040d21b804207403031311508012800e036042c0b80300c0ca0341c4c007a80c00302d42030065107026800b080038400d05041c602c1ca0300070640d47d01d00a41d50f40c1110090180c400a00700030050206201450301c070030f5200301c4801a071070041c41c0a0300c64001801000c0c10060301c1d01c005802c10048800b01e503c0000c00b103000e03000c2d42c072407464021b007460b1281c03003031000b0700341003031144845405d002080c4c80c0501c0b00105044059040e0b28180a049180326 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 329105584 1250 329104334 329104337
    0xa140f091513050706050a030f0b06040323060405030714160e071205010b09090105030d0503040b0709080a06060f05190b130f06051905030c0702120c040c02061005101707 75
    0x507140b41d002070307810040c900090107039846494441340c01c03803809001c039a001d1400801150500c10314503105d40e6048211426a5400402080701c8013106183e000c14800881c101d240314403541003400140000000170704415031140f40f21404004140300d0b00e035100e50f10486482680c3c0b400300018060101607051f485e500c031611b45003450450b40401c02001c282e80d0300303034800f0361900b43c009018000c07800c010700300ea03000d40401e030001c0100035407400c80201144030090011b40165580008108960710429486000300340c0e0178100d402c183d4043c140030004002a100307004156004040000e40b5040610110340c507040d201000f07107085498500c0c507420581c441c40c1c100c41564803c900206460080000789006420169111510340c106e101039451588940205a414000d0500400201002140c100e60a56038190f81c0f80140711180381c0c0152401c80c06000542c1c1c06810180c0420603e580090082d01c200700c1c0c0704200950595039001d0200c1424203c0b10a0001443c030030034007484415015180d41c200116 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 329106834 1250 329105584 329105611
    0x406020606090a0b0d1a1e070f090b0414120c01020a060207020f060c070801050601020604020f010f0212210a05090613030c050102070c06080619060320030a140f0915 73
    0xb4000041c1d00a400c9a80c06c403407443c140540580785003140503078181d111241100b800010850151600004040208500c040080c24841200840d204007181002002c1c810030150301d5075103c41c04070454030600c0c008140500d0402c001450520800030326200f614506030050030a00481f030f25850301030b40c04500181d23000740482e1010344403900d80713100601d07041d41503402174000c450030408050b003910b0000d00b16604550201c42440096541ca04038800c8c408000d09081100c40e0203038005a0400090340c1d4290f8403840007041000030040d42415000b424031160309041810790b10700320100e00302c40c802e4807103040943c0640000f6158040d0396848615060207800e0000e0110583d5440ca42a648490421584186800020007020380c2011f000c1ea04a2400c403a4940101c038129160244a5400d204007400c05440302c92058016100920002d103041009640341c0ea0303894903200035400f600d012510030058460707400c0014440810000014040c3d03c01001919a82c650034441124411010304040c0a0684 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 329108084 1250 329106834 329106851
    0x60f04092108040203071a0d0e1c090f08070e010b1c0203040507030c0605070302210403021306060212070c05010f030b060a03150503120306150c060424020406020606090a 75
    0xc0c101ea840d419003015034900c45180b8061040c142050301e664041c07000340b49070b0b5695013814140c030307019111703221411000004ca52040b10307490361401c542201906868114006c00f0104164400b90420580d440e4403014642d8039911658503580f9030040c4510700100701100010700858428500420345100720091400d039258889901c10202d0f8010f0324200c4550740105030800400c104400d00000400b018240503041c08019203020f515292000d00910300c11005003000d40080c0c544000380c401458000c2d004104948a8400883c01429640202809071080d09409589400008122010203510800e50b554091800740150b03946d5a4130032940c000d054460400b08525260303500603049080e443d0394081201e01c501a04000c5541e40d07508a0bc0c002e030000401d10154a4202e0300b201e41080e029642542c540e0003501d011000b6000304c0b1003814044c01f0703000c2070005024181c8036500740c20381e800c2444030540790741c0b140380e03001c034481c070b106280140c0c00160000f00c0c7d52034042141036102c107a03100c02269080 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 329109334 1250 329108084 329108123
    0xa060e151b300703050912011b0314010f06141804050c0306010e030c1e030c0a030c08010b0a0f12060b1203180301052a12010b040302040b0108060f0409 67
    0x34090781040e14403100920081242c998560340044200c0c1c01500510b00d04603160320700401c0703031189440081c002c0b004408900d508400950050040303041010f600502c0a0348041c0050142c4000c031401c9400b01e10450001c98004039800480c0211107540d100d08903541c081060360700f829040b0700340074001c1d0545004500800e40f11400307104c1c403a0304000e001980e68500800090142000594150300075400b81c048800c0c2e41d1281118050820400841c01000c1a080e42c00640b800205513861a0003c040b5540041004480358200c403c0d568180024010351580200340701c1000200d04c5400741c140700410703081140ba100c00103003a22860142001184200322480801c0c200150420400400e91000800c00480e0500c0d0b1103034a0142c5044000340042c5c10f050115501113109240c10660149a031300c49050b03070150000449a0b014502109142d156a5444000d1455041031205078040c1d4108051004150b02c00c40c6458400c4400800a8040070000400d20002304110a8129501c2c14220340b00c80a50 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 329110584 1250 329109334 329109343
    0x904082206020d08101802090301091103120705121606111c050c0301061b2f040504050d0e040e0105040602070c0b0705060606030604060509040f020a060e151b 70
    0x92000403001880a1610500a1070004004800d6040003e8a070500400b00000e62280f811101e80c440511151922041600000d02c10564a5941986001060010070030700708501e41e0316400403000d41e0000001203003004414420750341c00500c6908032031032004106c280100a029070401c1410070106171413179a6103840c22120b4903100610400c402181401c4400c07000840040c5c0440300b5482030125027803100d51070000d80018000d5109010030a804003022003051040080d180303410140e0f4500d03202c1404140d041c0101c41145403840c140f00150590f82c0c90034140510760184e5484802820500039240013101c506103038001542d40a900c0d000c0e4000c41100c240540760049024941c010703510041841c20800b0689158098002900140078040116401054590b80614251070f444d98940c1d42038006001404290822984204400e06000600480314642c42d05548240c07505030621351941c109846403403005140075481030303900c21000c103031000d03660290030803d210144c240050703800d600029050 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 329111834 1250 329110584 329110627
    0x50a0b03040605251709010603200d0b010e040b010506180405060111010c1d030c0307060e041806020c060601050405030d180801020a11010f1401030b090709020d150e0105030705090408 81
    0xc0940070700314444096260002d1b000941c11001b080070f14515901c082c3d0768078036203c041d03082c00702ca403040d180d40d62607a22402c0c48140d03020300003044a684804554400007002e907000c4c0c81c00c90741c0100200e40c41c00d0240450314460954402e00e44101007010801016140082203241002034900305024000c009008074101d80c031441d2a40c0340c05915990f45a0400c004840000341700303074802000004107450124904042d142580343c01c101147d100b00200780603203141c40d0344401401c0819503c0c02446500c3e405020070784101002d441d0151034200c01190680203a000f9194190006c90b040d144180c0106032882418055030710803201e595448410908903048840e0810201e100d039460707038060396028030a000a444640400300041c41030580d0b559548281400002e0411103d113000c2211184100401e0005008240f000c0d581c0d070b29524100c2007d862001c0a020080c4c42d07941011821031103182482d41130314400b400804440b03103003038200714415002070000d03182c90f030041010720b55461592442c26107 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 329113084 1250 329111834 329111837
    0x50705070201081b032a1206010e010311180d0f11090a06060509040914010903020706030e0601120f030c0c06050901090902090a03060f0b030115030606050a0b0304060525 75
    0x880341100e00002d0118074008007214001e0b11040070307030710141d8001c02c1507035041848203407161383d1003e0107180342080c03022600e02c05c01c6000d004a41010b00800156038544a013400b030b41c52614000b9564015810381e440c00c41c0c1c182c0d1100e800d02440c0407445604e281464032107001010001e045111381c4408828480c5202c00ba58960b900c041c2d170704564203050f040150004040c0000300521850414002c1c11030141400b164412900c410a05091050041911f003044a000000b0070803e11945000382d03681c2110320501d0042070500704c2c013000e002c2000c181241200c00e24150001070808030f81d101018901080c100310144081c103255440841c0d000b00414020300103036240c05035a80104800074141d00c110b64031450000340104200211071300c0b100c1c14101100e6103c00081000302d0211884c4c806000848901034240d8039080c852180003071459010000c80780a04001c000aa0700d0710107011070044e95002e407980101d0b041003c01d000452990200d98840410a400192400d140b070300c5c66108a4441007080 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 329114334 1250 329113084 329113087
    0xa09171206060310050415090510090e0a02130213030803070e030c0405220602310b1e0d110f07060f050106020c0909100203090a1502040b030a0507020a0501050705 72
    0x6600c480140e9504031804a851904511300290304440c40601805518011521089035014480002d4400c4019080c407002c20700080c6040c1c501d0f1100c00006101d4649a1400c001e103c0144d0321011550604464002d00548030740c80908041401952204448880e000360602c0c1c008041417401703003d54040c15080c0e842e0001115160101860f02c42c0b4600740e58406ca1804007800103120460351001078101506020541000050a207180240200e0f540080c0c488104480310010600d40c076110100500d1100b2800d04603503d8140048441c01030108100200c3e82c0302010030800cc0488020345050400054042105201c250f0700005070707009200c01d4002003102241c41000c001c151b01610005a28400d0200015031512400035554030b0071b060031342c2c012001078001c26080602409480e60200000310155a2400c0c1051324942d41c00000c5800d4a2800b10100303603100b0a1821f0003110200d4280342d1500e8115164a8200002000080e048034190320070a010840094020b0040c14400d1629490b030740d = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 329115584 1250 329114334 329114347
    0x110412081b0f07140a0b0406201603150203010e01050d050703080708030403270504020c01060305010603080918010501021216020d06060f051c0308091905030426150a0917 75
    0x12001d603100300410034800c10580c8010711503145000140c80446040b40303025400e03c140e441c40721249d24507000c2421414001d032040c41002955040001080324403424120144030709008076001280002e00030000e0b00e07944c0400410013440c0201481c80c0950250056881499603650740741030540c44074104403140100802080309050700f00c211401001341d124001a801c3c02d2030100320300d6141c0c51340910381c882c0358007142c0704000340070035072250024540c000d000304141d60b01da003000340050704000400c9204000317045051515503c2c80c49018100c43d0b041c0c0090030240d4040c9441d00c6250400c1c00f000a40da040b512601d405607550b21240342445000f860009181802c041e1089032a40203900010300902c0140e0f03080030300c441c40540290044d17030145800750194982d400d000d4108186481c1c40d84500612904540c24004013100070412611a02114a200c107000c4d60b50304001d034014858003025030030441c14061070004842c80c40da40007014000005410041b56205003051103401a14000c044012421 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 329116834 1250 329115584 329115599
    0x10909050a05070e0d02030705040f0e16032108070c06020c1903141204080c0102070f060c0201050105010806030c1003020c0709060510080103200103020708030f0901110412081b0f07 80
    0x58002c1040a4820460101e481d1b0082a40c0720283e1080a00031903842640d0701c00701e400c540c0034280c1e0103094400d440c0d800d25180a04e011003030f81da0100f0f5a81d201c820a12030301c80a00b01402089141003501d9900442e83e9550b403d035a081e60030481079402035020408441c00b203006008844070340f0710050040000e4442c6060081c100c654510600010b00b508004000a4030201d41c8510b5125500001d4655644008502c080c0613001b40c1c1d10060400c94941048020402141c014225100306a40200111380e0b0700c0300112030040f0203403035840c0c151300107092003406401d00c12200c400c45504d13414054901400c104009103003046036071002c1c081981d03c0d071090000b4078004030700c1e084410703480c58000c22031b504680304c603250400c8e02c2d40340300030342c0c84010308075505a4040d4041e00d06072600721510a07124545184a400c1141044503481419440c02500619071b0300c855003070b1002e4414500103400c211141d5600c4001503802407698028500090301d900051010420600c00c240301c5407030240c40036504e403410 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 329118084 1250 329116834 329116847
    0x140103061b02060106022d330708060609040b100504030501110c030405100311030103140f0105040302030313030207050306090d090609060e010c030509120f1209090114010909050a0507 81
    0x40c401e0464020800401c50b407036001511441004000307078000b14a181111610b80300e003803a80d4110100c2d01407003450040b02140c0c2c4480390001803482d0314500540d6410a1000094101111040c0108244030f0200c0d01a052401c090581a500900001950300c0400e0004141040002c01c980005000281c2401084800e01600003d4880e80710b000d41050f24140c08035481e0f00541c080c0a00814484031018246840f0f50000072100b07044114056a030358403070402400380100c0d01c1840110703105a4554171960081403181620035505a4040c504548581e540b104800402d028107408502c0381345004110307035606019080c0034140c150000d040e804841c1a0160000800e64031000030300480d0003040021980081c00c2d00b03450f00007440d24054096091905452070b024041149411000000b045408031500196070008800301341c08403180020446015440303403158204c010340165260004010705031041d403040b0f04941c0c05060a2a01c0c0707131510007035022910115912041942c441051121083e001103 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 329119334 1250 329118084 329118131
    0xa0b060105120109060501021504021e01020a0602220b0316140d181101170105190e090106092004030b0919030203120708060904150e01060e06090a0e0703060f14010306 74
    0x2780402528507007600000d03400c4400d50400e280440700940181c10341e038424030802e0a001c0c2e00000440d2148224107001d40b8010a401440600b0b0075940400700b41c60801c101503911071003490000210400201034220707820304e00c4a01d08202010280301d400d403484410f008800b1003048111100c003400340541018000e40e004146298184400c401c1029001082102e4041c15540107581b0b21038200314015940422040b2036024450319510902884031140301034012004403a4140c03030500c03521185003401c42d41000014440401c1c840100300030000600960440d0b42d1140351013095403600812500300004240502038114010380000900c82d088640400701d06070458090f24000500789001c101048101c08050000b030300200205d118400303421900d800c174040b505501002404482d9586603c0c03200c1300390a076441403280c40340500081d451b0069208440420714110020407005195464100040000d500000003d640794440d00c0b00105c40d10600034021031040d8800124503922030440007890070400e = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 329120584 1250 329119334 329119363
    0x60b1c060b0a0510030b03030904091208250c0c0b1605060703020f0a050d0b10030e1b21030904050f0108011404030519020f010f1409030901020a0b06010512010906050102 75
    0x8440600858880c1d441d044c403000c40320b040001e0300010700c00001e4910b01455410b9584503003020000343c100207a03c2c034640412003a030b888805041e03c54004404100d0360050302c4148000810a28441c43c5101d50b142c2c5518501894000b900307552104280c1c03440b9440343d4a8403040400850041e4200401002500c0e4041c050385000c505000c041c9040020600c52026404100000450840c41085030365000718a0400010000d404090f1815006405000500300840c9140038030030b01e2000644080e040303001071110041040c8400c3d8458945a00d040c24030141c1c01d419840240080403694403103109040c0100060421a0000c0d80750030072140c01d440c0364072070b030108000c446420700c0700194024003038807400324011400c00351010707002c1c1080703142c0000c41d0501e1a443d800c106d120010741200d0307488401580c41900898044d80d0b03036058190742ea8420b2486d4140180c1c0b2908000d404516141078080d0440414905145040c5651400220900c1f00b0b82003250090f55607201000250380400c0500300d480402c = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 329121834 1250 329120584 329120599
    0x313090204030b0604020f0909040510140c0403081c020304030e04270816051902040605030319030f02270f0a0308120429010f0905040816060b1c060b 66
    0x356030f22001e1032000902202d016035008a03d596100303101c002a1801d100e00500040e900d85054100b5070394805400410500711403800180b140482c0d84480b2940c0300350111059186014695a111185a4491000c1c28603801c3c400b2640550080305000039030280b802942c07081c6164000400300001c440c80b22100702842c501c9204960600a1146050303014903800681c07070740c0c0f50381944000d0700d001d000c201c83c020098010126005603030b00d401e0618125071030003502c00b007090300d484000381603907407003805000049100d401c040c19918610030b800650115105403000341c18000004c0001c0e0a2400564010300500c0ca90000f00415080a40d0780d241e0320401150740400003842c6448000b100d01c5407500314111014810001024010143c4400c2030101c0c2d418845601e240403042028410342003070260040c1080c44100008a450050107868044d13031f0003240c200e18001010440c007040042c8904205c3c1c000e500c41c100441699951703880c000c1080d10050030712224511618104003100c2c041e6211500c1000d4 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 329123084 1250 329121834 329121839
    0x50105150916020316081c02040e04060504020a031203020c010b4e0d0806030c0603010e1005060f0c0c0d05070605030c0708040b091206061c0804080607020313090204 73
    0x940210791a0808090000d000c2e8031141c0000480c25441101900d15030840c0c1c0c1c1e4141400c0010440c0140f00b1403210b010105106440749010314103078440d620070401c8584408020a000c6850f40d404a600203100030310607245c0507900e42d2040c005108104154000c25400704046241070340a0003403108041e4201d806030304040c4c2800381d80a84c880103941c800001705c4029142000020b2181100301c1c40310742480101080d403495840503540d000c69100c1c0c41d0010348031101051050400007810840510b00404440c05c603801c1440100580c88000c1c40015114154203001a01d511650300809103036480810866371242280101850104ca081d2020700620041d4441c9001c00c0000c210a0f0a0300d000745040d0b5942c0d100d00c000508140160400500a00c000080001c0c030384603200d0003002d100b5001e90360229441d100e00c0400307848440c11284160882074031603002d05030280f14141881e006100d42c1512341000e48500e0028903242e002c4420f00d0140c0d000048030442c010f40c5000c040c0007485203400c15481c090 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 329124334 1250 329123084 329123089
    0xb090a080a030207050c150406180311090a0902040c0e0a05090912030c1e0415030e0601140409080705150609090706030b0121051504020a0203400305010515 69
    0xc5101003081c1090380c0410028200034060002d1250f41400a200176045910400fa15000d030340680b24002c08900702ca000741c113204c0400f00c100e038101d030b4120b01c0c12202c400c080414052802c80040081c0011550b403840030006036034a20849951304032503aa8003503450744a505000a18045400c41c0d486188040104218001c0004082d40d00201070800b5a0b200d84170003031203031000d0044030b038000050108070f400d030808182c410000c0d0003100c401601c00e651300b2000e618207504440c03070341d004004650051030044c8041880358041000d0a03101520003d01c10b40c664803400c1ca20f400101040750310390082c140441d462010409215003140040350400c0c40740c10181c04c660ba0310340151103911705160300d5940700b1219a0040090701e00c10301110410521040c1d49100c940c0c02460b0403900c0001c0c03a90203a011081ca81414401d40300100e205400441c0b40090240c41140025120b0f031f41c40300300480000c40c80108070704113120f01000046420254103598294640303d800e441000304051000110b071002000d555 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 329125584 1250 329124334 329124337
    0x14040e0a061a032a0a03300302030903090405100f09050a060b091011101a0109060e0a09110903030705031c050708060603180708101103040f020108090a1a040b090a08 73
    0x1d01e100d504110384d1031840400c06525107944080d101525405003030408a09821601141040098801d100e800e40d40400303404030b0100303030385c3c20b52107034418880e041583c00d00b9401140c010007041c031900c00c4903030303036000550f80e084068205554840c1c4980906c403103044c05004800260a0030b659440c02e00c4440300101d500e01d603800009500f00030511440d10701e52a0107000e0a100000405030600c80c0501340d541680744c40810817180c5000942070f1400155442c4508542401d602c0000d0002d82c81c40d150104c4903018001e44404170302c078cc80d800c11410f0000d076810002400c0d01791040000e541c4a80d89002c441d55245000028030705810308090800c48415441140198414402c0301c509450341c854908594100380c2c41050040503110340354000c1050800040e04040340f1030040c1c01844200301041c08424030740811ba600504400d64043c5220056000d402c2c84c40e40404028102d90070010543c940301e105100282c01036505032540e00034801401240ba6619a1041010004120065042c1d0750700c0c440c1e = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 329126834 1250 329125584 329125633
    0x6010c08071a07030203150d051e010213120b010b040e0f07030f060609141206070e1c0818040e0a0602090607061104091b0914040e0a061a03 62
    0x140c6000603004007000156007041040c01c02602034080035182041c0d000e402980b040d200d44600008248505180345489541204002d0f4010064003141d81c21b0000003484c44401c060f012031554090040780c1c40a11448003003c020100b83d0a0282d020f286e034200751031000d0060b0000803032080200b005100080c0403060721030b0040c0c5240c0740f02025a464042c00c070001c01214a4840486d410950700107442948140c9200030781e00c10141d40c82c101084d000c03c0140001c07511180c00800c1d0807100c002805140a20403041c40458040c06941165842030003c6117092509502200c0b44140030501d400b400340c1130111007201c0d8001391010003184858260440c0d4490703220400400341900011001129180c85040d100c0720f0350310103010b21804442c0c861108080d0013a0080101c80c61808101c11201c2c2d249005070003201c00c0d9519200000c03030401c03180058485031000030540054840b80081c80245040054900e29070203160002801c8254a8503078001c0985858070512a5001d41007032031850102c0d50f0900721 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 329128084 1250 329126834 329126843
    0x70f0605240d020d1a150d030c0204090201021c0f08240904020105160305040305010e0123070302040f080c1002121204110603180c090c07030518190807090506010c 72
    0xb010640d44001450b082d410540100620220b1010051402c035207903400e4001c1c1405903e180e405030b10203081c4400a50071038030181c001220107010101504160f800400564010b105640103403002d5081410707402d1100885500044c1c1c0c1400a03500c40d0343c8003020701e401100381c440c0c4c00e507100c00c1051504180009441c4c91446240f81c0000310f000c5a000e042100e840d50072007001401000240d0801410725002840165095424460030103145e58041c030840300100100c02c002c01c0c031484210100194003400402d41d030240341e402c20012481007080c1c0006001014504000c06d80445100140074190520008907015035010006111920307070302c0802d030f4580002d448806405581c840c00d209504071a00420150400800018070600b10350385219544048880d00c11502c800c52a01e040c0a108082195041ea0480d0240900c00000713200750010201c0380d500c0c0191060080f010000212405c0c54541030300394041840c1c1007008444810300401000700040c8008210078503120b000030700081074400c030060 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 329129334 1250 329128084 329128099
    0x70806090c1003050703060305011823030406050a0507051b0f010c1e061b0e0a080c0109050d050c09011811090916050f030a0207062a0503070212070f060524 69
    0x51780c045c4294407510055401100a00c0007540501030003083c003400e032006584803e0f040d542c0d000d030300ca003288000401d500038000842c42c042c80d02e0000c403001d8000514503401c1100030000000814010030010905101350190581c15018480400000c000c42590341d6062151941c4c1401c0414800b04450f562600e100e10003030103034800381c40c0540c01403402003207008001c15203d901d0462641c2c8404030b0700c01500c0070349428044584401c466543d944140c246180028101c0000340124141403104c0314005100788126050b078201540000c01c1040260001210398811402058801c2258001c0c00400681d0800f803d02e40101c1c8801710700c0ca003c00806201e10b04042e05002034140f0b20610481c0c00f0300842090f419200d0400e0140d0001940c0200c0c01a980c42c1d04003c0300f200b04507100c0f031407184c0f1119000300500d05084501415a05500001c03c1c29080d809094003a0300030540680086c010345104544140540c8000d1802c1c000b00c44000e020980c0f44800407203a05e509418074000320322640c104941d82c4 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 329130584 1250 329129334 329129341
    0xc0b120f15100806011202180f030304030f0602130b0d0b030d0c02030a020f010519050918070f200706020109140d0206280606030903031b12020304060f0e070806090c100305 76
    0x50780c6c0da401c1c904454a0300c5100003001524030301c010784c501440d0b480440c0c0021042c4040750400d6030b02d009902000e003030f1514046000c400039a01e82c2c0280701e02c902000c50009078a90b11010801c1541001103e9601151030b0352031000720b49030900c86c1c1611000c0608041158089980110303035a44074000b0024010090005800c0030f580c00b55050394030b00119404909101e100181004200c0d411980301d85025011106034900c0724000001001d02c60f4280d0b50318483c400c4c6841504070740daa400101d2070703400800f6680c0d0b0030300c202e00c0c28010ba4000c3c1142d07400100349118185044210850045034960f02c641140020f092481c1c2d01162140d00444a0345444000c1840303480d4420601d5205064015081c0c0751280c0001c0894064204401d4030b4001e0300c003004010550030465030300341800c0034081c0c0040c850440b650f0342c400769940616002030181c030303000400f652908044412a01012a0755020341d102440410102d2010030141d540304400700d015140042d4030501149001c1c00c4076a0050509d0780700d1002 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 329131834 1250 329130584 329130587
    0x20a05210a080a1416020c01050703140306010e0405240603011535010e070e0a090c0210050703020310210807050a0f060c0f03050108070308070c0b120f1510080601 72
    0x11381d00c0e6031020074101440b030410410140c48505541070750400350040d540d032420b4640c01340741500c00190b0151101c40d41c0a620140c60310b0960b000400050500000d2650381c030303054030740703101c1e59210f0340d003c2c01503105000d41c500c0c40d13401072032012003080e119681c1000140314400040c4020015050075061a07843d8201c0e94002e08401681c1d503010009590300c0d1483c01c6854155141094100c440b01e2820020755141d950003100c03000050700500c0d402075880181040011541c5d032220b4080252807050750740100800c118a0181c13074094488000094010040c4200100030112613002010320403540d00b01000030740320b900c0c45d02e15201405000c1000200d0404280401071292a21459220000c8406043c0c50b02d0100d0007811040060381c001022040c2d00109640079100c0c25040c0c40358140242602860740c1e544001c254800700040300c8000c0499000210400f250b40944403080ba142042c540780d1a0512800c00034107001030107a01e00307800e40170017010540c980c44082007660720145403014031941c55000 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 329133084 1250 329131834 329131841
    0xc04050415050f0f060414010303080703020c100203161701060c080702040c11060601030e031b010e07060e041a0d020d0501110c01090204050106020c0a0902090a09020a020a05210a080a 81
    0x100d20814100300412a640f0f0318101018480d402c000c0d0b041100c2c0e150201444101c9102c100103085140d1010300603c0800d000341da4559210015180140c41c0000c040000ba05000b83c0c807160415141e00801400364501d00c22550b41c08010240c50005402015801c034440c00c0c00040c441c410034000c1d101c6044080c0000300007100c0c038068005e081031240b101a803c0007805000b4624126400f4020040401c2072503200b80a10960110840e000314103201308120280c00c45150110b51203441d641e1060400101c0d0003d0194000030301ca140c582d80b05008544003800140d0b8010401d446d4841107450300040e15584c0c81803071008164040d1082101c895130ba03c2c00500600c03064039a282041c0011918610740300e815007010940e24801e80d000e21541e641c410302a40d0b45e01b203200c00581d010312aa04d0030b11426400d5070141020100040c501c103641c955811039042264044580940142c100c10002003d02c041080000b512000c0582c0c288000d82900c2d140d2681d40c0156001f040800441c4e2010a00c01c80850f013 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 329134334 1250 329133084 329133113
    0x150c0a0201060f0e0f0a0506030c040b0a08070b07050601090b1c030918020714150601050703020c060406050a030b09060105091302041d180d020303180f100b040e030c0c040504 77
    0x2d92100f03440ea111a212403e8580072606a66860516000941120315500695001e42c070003800a0500c03440040410001d40100703100e640e004020303640c0c000380002e800c001000041411501e0207503520000d0500e43e0510780c058103c0c044503410500c40405544a01690030781420014130300c0030501340305150403110781c0d009510004000050f103c160034400540cad80146071301c52045048034030602d01c2c07c81c42521603200b000c01d0003c0c4162040068100e502440040151512038070540c0c5080030304000003086500150001e80004a0204040550703a03018070070340f49034030022a110726181c0740c1800000c00c0da21582c03c230140581d40710b85070150001e43c1074040e20302400c0c42556010318240201c060201c2980122020400d40c8820315031803900d40e1300030501a40c81003169003d1071a55690f20811045e80c2d0001301403030721070f101c1d819a42548034002d208060140d03680143c081141400481000305503140c2e4200c0c15003a401c100103000f10b42c98005446d0540070f800340c0340810710399180e0030514030701995070 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 329135584 1250 329134334 329134349
    0x70f0f1b080105010503070602060103050c012105010303080403080901051303050a180b0a170f0103110d02040e1b030705090f1302190312031802010c02130207030c1103150c0a020106 80
    0x14000441c0340041074010a068420550840d07100e20b81c2c0d00000c0380c0c1d5800030b20000e0041e800030841d4401075403048148030103c60107000000300c0d00c9030410f0000203d0300d09a01c00d400245920f0184004c141e485000c07103400c294084020311540c01c001c500004c0354419404000c017804000900100c45a0107100c1d8849070990503c0800380195440c500040103501640752a00003500d1880c00c1c2803840c90110900740620082c2c008014603030700715501c2041985810340712a48c040c0d8020222001650785020304484905002e000d030101c400020b008054906106031810b1007500070400500c51900c0342890345038070100301d209107d0389031168a0380118a24003110007039042042d85452802e40d901040707181c3e04a910980e03403000750f02d428a03002c8044034540d407035030100e203020844620055842003117411a200d000a0a000844aa080429049900002d400c901281070940c13240706001d91207001c04001c3d0700660217032201804124188040c1c0000a1130751604450114400300c03201c1c400d60040000e007004 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 329136690 1106 329135584 329135633
    0x301061d07050a022a06072f031506041b1812150203040327180e030316050c061009050711190213230c070f0f 49
    0xc540d56039080301c030404114855071107031b001b080c40c207100314040d90030759a22416010f0107100132144000f0560510555541a80340404d041810030400c1c180260556154800940200040341904a400c010405105800c541009401c64030400700d8000d5982c05030f46104918100e032080000a05003005500f0301400740140e030b00a141c00a100341400c80804501086ca070f0312669503001150202c145040041000e103181b1010032031002c0d0241c0040c40140107503404956030388000703020021601c0f92074070b450b440d540c404c1043e1206482c1020654a00d03081c01402105d09007001c1c0507815010745028045802c09000d48001c000c06010400644424040b00c0c1c4503480715410b85001340c0c0c12401c000030901c48000244510b039424510040c2c085604659401441c503000030090200b07000c00410400a800306501c0080700342000e40c04643d513021111203242492414540ca2400518440d0 = true := by decide +kernel

theorem cover : BRFrame.Cov 328956834 329136690 := by
  have h0 := BRFrame.cov_init 328956834
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328956834 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328956834 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328956834 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328956834 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328956834 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328956834 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328956834 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328956834 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328956834 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328956834 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328956834 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328956834 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328956834 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328956834 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328956834 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328956834 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328956834 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328956834 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328956834 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328956834 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328956834 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328956834 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328956834 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328956834 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328956834 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328956834 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328956834 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328956834 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328956834 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328956834 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328956834 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328956834 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328956834 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328956834 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328956834 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328956834 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328956834 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328956834 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328956834 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328956834 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328956834 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328956834 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328956834 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328956834 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328956834 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328956834 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328956834 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328956834 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328956834 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328956834 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328956834 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328956834 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328956834 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328956834 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328956834 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328956834 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328956834 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328956834 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328956834 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328956834 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328956834 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328956834 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328956834 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328956834 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328956834 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328956834 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328956834 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328956834 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328956834 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328956834 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328956834 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328956834 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328956834 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328956834 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328956834 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328956834 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328956834 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328956834 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328956834 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328956834 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328956834 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328956834 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328956834 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328956834 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328956834 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328956834 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328956834 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328956834 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328956834 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328956834 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328956834 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328956834 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328956834 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328956834 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328956834 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328956834 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328956834 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328956834 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328956834 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328956834 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328956834 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328956834 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328956834 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328956834 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328956834 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328956834 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328956834 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328956834 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328956834 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328956834 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328956834 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328956834 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328956834 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328956834 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328956834 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328956834 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328956834 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328956834 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328956834 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328956834 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328956834 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328956834 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328956834 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328956834 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328956834 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328956834 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328956834 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328956834 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328956834 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328956834 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328956834 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328956834 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328956834 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328956834 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328956834 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328956834 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328956834 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328956834 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328956834 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328956834 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328956834 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328956834 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328956834 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328956834 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 328956834 ≤ n) (h2 : n < 329136690) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
