-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1992
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T05:24:13.076983+00:00
-- url     : https://prove2.me/submissions/119eb500-d88e-45eb-a66d-22686e0e1303

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 358093525 ≤ n < 358273381 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 358094775 1250 358093525 358093529
    0x270405090105041208070c110f06310323100e010c1107060230030703050a1805070902070203070918020a0f05010903020d060e120d0b09040b04111801 66
    0x300000410b401c0c1030a10207071208001c44040d00b409000800e020f06680d10550024002c0c0d001703403040122402200020304011244007500303034000e41c0860400c464280c0c46090804541d003100f03036030078050307510908072003120060300c0043c4c0107210354254512004c1c960031050b22066024420b4600116401d524542241c1d0034082c04040c030380d0342e248403041240d0005480020301003004010721140f4038003c0020f603500d06035405034115180c0e804420845000350070f142d01100d1000030105440e454403100003001010308079007071001c142c00d12a51016036003103030300c01d44035854210000d401300314100703c0c0d840c01948c8014000c03a01440f6241000460200a04c510f500c6224000c29500341c6481c94010450300c3c0006821650307010407207000411440ea0440540402c480e07068030020f807102501e0a00310024165202c5003210340c020134545181c107000c40401041400080c142c208903026024082c00350b103030011140140306000100108010524801a8108030384c0300422660440010142044c00b00400f0307 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 358096025 1250 358094775 358094791
    0x90d0b0405100b2d012001050a060603090f0b100e0a020702040507050c0c0d03050d020c07050111010903051b01090f080705061308121b0403050a0b0109060b270405 72
    0x10307802ca0a421250242c621054400c0701c9020f0041402c003035000190281d15260380c41c0183d02c50740651aa40161842d209100701e01180401010384821382c00d000c0d09044501440851902d940807034001e000f44180744641f60000071a0103154055584c1241c0841d02800d01007a0503401d0400003040c1c0001c02c65544a58507000016844094510510050398000f901c020705100040c030810803108400112803e0300709080303070040710120b1141411381b40fa202d12448910fa540c00014442c2d9441c0c800103106049070300a9a41080007004150078a08842c0071440050000302d08010440c01030320b5036200301c0c117000a018000204600d030b81e96080454402900e0848003250302191a8041c07260a01800d80d1011a0004001a207042c564400c203c0c1d204d02d40040340202d41a40106880480710748106401c032084590f415030740d0342c0740c0c14010758640b2500c8080b00c1c0900500000f241c800c00034094202290064124181003402c4080240d80a651000051b003040c5040c0659079a03d41c2d031401524040e040c1 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 358097275 1250 358096025 358096033
    0x30a0305070501050c041505210108010c020c04050c12060f060403050a1505070801031e020415080f01151802091512090d0e060d110d1b020d02070302010302090d0b0405 74
    0x50b07280150a5038001090000c4110090004200b0036a0b04030411048044500c1d1290341c41c0752200804000650100060050000c4400041151141540004140d1100380c0840f154044100d041009403001110001e1485030b0902810615607030042c0c9407500301000405480d17511801201203101a086544142c0300d0741c2c0901a40000e21100e90b62254a101072070b4418422803500301c0001d0580b0006110080008038280c0c42030241d403c9550820000550017002840042c02e00c810308514030519010320f502c1d90086c402d00301503a80052007440c003001920794610f0305040c40c1c03a8001d28000003c445800e1415020000d95800e540c1d0344405144071002c1c0d05c142a111006003481d90205c0d00002c0600300b4a0f0700203421140c000340c0200e5081075007401102c14039034444880306031401400300c030482400d1030300e0003041a0032016541d4100040780c0e240942d55894050720070400300d950307500c440d0400c070150300056002d1000d03500c0780e001094002d50140c110309240842d46e8540b440b012080b90250b9840e00 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 358098525 1250 358097275 358097287
    0x1050a0e18042a0b1603030207060609020315010207051c140d020102070c171b0301110f070209070f1b080405060d0e07090b0915030106180204060e01051620030a0305 73
    0x440c94254100108005512080c00e403c054407020648285c12146940207805211039081600ca9012200c0740c2d03500c1081480581d45e40c81f5508069007056030f0301d0442c00041c065420555200103100422100c2c020800307009055682105a591070030300b0301c1940c07441410202c1c60401c907010040104042040d500059903001c050820003c4514250042e0f50145040d4101c0b07500341500140101d90703400c05a1036400714a07c01c1001034014007070400595034a03000806c000304103aa54401801c0340074000d8844594030b0741d03030314800c890000d6445c3e91a40892121240a411088c076101c62031a07031842071002514041c1c0f5600081d24640000d280c541c001912080130400d100814840c9000070103060314240207114060f00000c040b8030000b0b02c1200c036000075440d0962a50340c250081e01c0100024085115800340301c0400304044c1d4845d000300710226507114000c450303030b5100d003048800c1d0145585134082400c1e0340f5500c8499000c95a05c5816000003003418174001c645d400c0c01240101d03446519501c0c0d40c0c503 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 358099775 1250 358098525 358098563
    0x7031805071404110a080703060513090c0e09070923090303180705010203161509031101060f030b0606030a0b060a020a06060504050411060a0201060308120106081501050a0e1804 78
    0x100b03042508501550405001c03514140e845400d0781c8804502c1d0801410030f43d502982140240906d40c4415881030750040c40303040c1c080c4540e00107850a400b400782080c045072510050895440280d50100d102d9001243c100141c8503960711184450003094004241509041001203403075106a0f8110b000350000001c3c011075404080303151020b04058005012003514190003c4d4507405070941601850528594510810444944502c0c6081000c041003101c0c1c04c10b42401480c00ca0842c83d0000d0940c60214085a13401100854004481d0712502403c055940c040c10f1220f59040a000c00c5206a00c03100b10044076a01c0034003030301c1c58164135401403800308100e061180c29142258800c5004618020511010400514100d41c4610003503403007960b02c10400d1001c9004000c02e52014140e800c0c00701c0e24141011081c00510b0481c0e62656404080c1e85503e0f0150301030101444c0d40c1404100d0801001c1452405540140d1652400a00241c135000304151a040c1d00c0f0301c116000c68030141e03c04400180c0c8 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 358101025 1250 358099775 358099799
    0x1104060f18150f020604240e15060a0b0c1905010207060e16050a05180712090f03080c030f06040e1009060203011a030903030106030b06040b130e0a0e0709050703180507 74
    0x10200ca04c000c00f001c0c1400e4461680700840d00e01c1074040040e8012425000c011290000d80007400007030115450f4101c201c1660403500c40940b0700b0351080c2c007158000030341d081101081c0c0d1100c80c66000030f0074121300e6080c0581f414010b1b1407800c4420355003d00c00107020941074400d40d48050360400c007400002044180c201d10b20000c64001501c520f01e2041c0501040d1102c01031003e00c2500e08080b10307420b4490803020364154130418842c2ca100c03410181c440c02042072030410400800d00c00c0d12840c00903203914000c01c160380000c650b072404190140d0f0018515140c5500320700c005194a00544094880d100c0c060015110140c01c1505c2d280c1e00080100588024505040c11048031100c41c00d05509218076032607181d1006105103001c054841010001c542e0301c0d0400c650040c0b181c044207907503c038841c80b07824000550510400300f031200310350002003c809140c0a80300d00315444e8406400f000d410030059800418010345510308042d0b40d07048041034041c0f58103003810a81c1c0644018011985004015400 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 358102275 1250 358101025 358101047
    0x70521130c15080f06030f0a050a120809190c080d050417030c0303150319200402040810090809062b0b061206030a0507170c03011104060f1815 63
    0x102c654050b85803a40964407400050f0007a21804455609444110000f441c1268003e01d051890282c5c40d00302d0100035001034140a110711814401c617540e188040b05941650080711031130f8154000711621001c45041044900b2601d10410f01d0404040d02d400f000c614100e00200c402b40806c1c40003030180402200b15000c43c00c0c1048220095103809034100e80b042d200d01000d07002c01c0035442005001c803000c3e81d003404a0b503001c001c01e0b44629480203190410f19990724843e4154904044100b070411407905040c000c64003650313215170042c03c80c0c140e00365805005181a01090780c40300303c1848101d010384d4440005116041446030300750a80b8040385030943c080081e40080280c1c00e40b4103a010401500e44009691a000004480311101d5a0307882c0424280601c3d07100003009406820f0b40410b00007503103000f8043c10b42c0400c044402c050b0b01703030f010704d401c03200280342944008009100c108181c51040040d070300f00c10340d503142000c152890320444860700c4290383c1049030364441c0080d044041680c04000010 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 358103525 1250 358102275 358102289
    0x30303060f0b070b0910050a0209011106160f03060e01060c29041403071b090e06040807260d0f050708041104050a02091801030c1d070521130c 63
    0x14030a19081d0302c0b064610910200a20b21013001d00001e660340c40034000d6080c080c1ea0071105010901d070a02141000354404080d0301d02045002c244420907003000103000340726121010340d0119003035002d00300740c48860075844490300305034490b00c01007080118420214002d2540751508001c0d00d02c070b4640400c0e8400041d403038511251009400c01426800c134010130f600316400c2042c208502c88032880e0681944a081d03009407041020b400d40760003582c13a82c0302134022659500400c21400100e03c510a4407000c058401070403205081c04414007142d4035042610284c080d1800c0d180c101d9080504016807600700203119000d160360380b00500d510f011716014044d070003803041c60140c00750702c0c095654904485000400744d004503524070004041400e0740c1e04440701180002c0280502d44100c00c60350f8203104c801d000864030159207000006c0c1c80350072421200c0c4a4811792050500c0750746d441c0310484d01a0481c50400c58005c80d81d8802c243c424a901058900410151654001e078041c00c5c1044c814420450384a41 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 358104775 1250 358103525 358103549
    0x91903050606031e0613030c2a090204270b0d080a0201050f041e080d18050c04090b070305040f0c03060b120712030c020d020306070801030611030105090f0406090c090603030306 78
    0x540200d00100385c495104050000152440900e42421102101c6651004020398001d0340d2240c001400c1f08400c51b45405030a00040d095030300c0d00005000ea000300e12406840d04541041d20109078403040152401c845200c0300020404158800680c1c000c441c40c00589001d0000559040920380c203009140e4861400f401400c1c0c1030415540f81906500800c00001c03a6007030a40f10081017040c520201c3d4088003284100380181000314808407905144d50804545910a80b00824980e0030a402807042d4140c21601c40c1c055a5120901039028203401003040310300000912410000840105140b030107180036460009120f05603405000e180c0035140c0300020aa0b110080800c9214010744005803001e50510b0500700c00c0880384040703048015158030003541400755000b001b11481d886400e8a040740d01503541071048040355402c1c80220b100a01680703800c0700e0785200080c1038091108600340c2061056100052000f280d4840125440c00d40d000070550b01d17141d00040003030550501481003d445926410 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 358106025 1250 358104775 358104823
    0xa230709050108040b0a0e210d0f0b1f0903051615090f180b04020f0c1920010e03061f0b030c0301060c03020f06070e0a0b0a1409190305060603 63
    0x1706240b401c0180910755940d01d54003070a442410034818250303006001c03614403c40300030414000c18103410444403031090a180a004d114901d415004500001c140903010700079840700b2003604060300c0341c0701a8010034000309500010001d0410030400184600c900c5c964880e107414001200412203c000c034040401c058810144059460010681e00711038241d0040c1090319540092180035012845c0d0480c2c1c064404902020750159100080c08006900d03c02d41e80c0c040d1403407400008990070b2504c0a0700e6401104061062090300081c04a4030306014145142d04c5400d460002e403a0070012100c644082480300085e0516000c80350a50020306409628141107140c000d030360310081e000511412081000e4611040c2c00c5c0750081c424030454040010540b0014034028801a24044c41c0001c4c0070300818003d4170010709105880181c68101c58195070f0802c3c030f80300f010a4106117406c1002d4859000004d04806400d1007805401d4600640c4210041c022a01c0c4c900101403c04210031091036040d00c141d0b080b = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 358107275 1250 358106025 358106033
    0x40e0a0204030b2a130b16030311040305120901051605070302030601050d020f0906011103070c0e06010c020315150307080f0d0507171309060b0702040c03021c050a23070905010804 79
    0x140c1c00c1124040900c02ea21075110419101d0b40c070030179901c4281071000000da800524042d100354a40054087d0f02c2c14810301400500c1e00707503a849144006040c40d01b20545441c081c03044540240848141450720608000d540e5000c0d04a500030b80354201c03104e90060303a00b00111b09060110500605003101d02200c00651a00400c0007100103960191007000c081d0009005680215410b03407480200408482d161011490140803505483c05114408840d12000175107541c800c43e640b600d8140d010b00a08180c55440d00081e80049000e416242003650208105403142c030100203c0303004110714001407102400d0704402070304165140700d904040180c100001400300c0c403c03d070888a448240014655a21100080100440c800360040d40020b824007a0005000e11207002a00101c1d00803a41001a80703160704d000c0c1c04134450100c00700c2c004103103020440c0300004160300140d40604400c0020848402c509100070154031510781d1080944290828840507507400038003c000f41c4400c0c207052500c1d003400d0b11 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 358108525 1250 358107275 358107331
    0x10020c03090a0524070c0806040506040507080303070c030f09031205041406090a1802090306070c1109150f0f0a060305010303092702030a1b122405040b0303040e0a0204030b 76
    0xc505844c4e40041e0080c100701c8541a0240240a0807040d10035a0810f80380c05034403408103030760645003442549004185014040202d80c0030301ea0719205c02c2210122070f68151180c20b4416480024000580c90000216900e10a5074150a08540d60356681e141064608800c5035100b1256a02444060100c40031a450342044882645d07602c1504484141003071090720081e02ca006600c5826000d1070045c4039920341c0040b15440c0c40c903c580e00002d0000840300510000031011108a09440104604020b090614401440d4514006001000203448040200b000780846510010000f55a1030040062580c000c90307541c0a41401540c8001403001c06a440b40e5a9508500b2520301c01ea0000c08a130980c141540010b07103850b86e4020011120f01205030150200c1082001e00d0a500d044c0388030002a40b041a103113001503c074101c0c91740003241c10401800010100328440c1030700762104103c0406c5107940d078018544682103100003d40ea4038110714201c00720540280c50780102c0b046800400c02c44ea070900c6 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 358109775 1250 358108525 358108579
    0x240305040c120f0f06050601030b090907091a1906020d0908101a090901050708160c080705160e0a061208090904060b1305040c080c090c0c10020c03090a05 68
    0x3100344045940702d410b0400464075044001000c049206416104100007904014414042620104114044041884912001240c04410741e8200c80c9007401015010380c4080181d6142c04030400c41c407500c41e80411040701d20103442a0204512103801c0080982c104440600e1200030b1034080d030000e00d06030f12556a00003041c51101815107640141c400c1000080c0c840751030843c01411951282800e4040e54000d15055450b40e0028402000140280c05400081e11107215540d548410041141e01c45007007581100c4400c8400b8000c00c1a062030008900035a100a0300e400010501242009490802120300661004100c642c14042980100e0301102c140c881600f03007130780c6084007076642d0b01d40140280440b6900541c00341c007811400052400580c0004e05c1144124204501241c850f070301c5607a500d807903a0010340d0001d0744070000703041d01d5030340d101500352402c0c80d20441c0c001155140445c4140d8100545100e013580c00030841500914103103103140700a26050b6a6103a00103480042060328038520 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 358111025 1250 358109775 358109789
    0x4180605190e04080f1903240b070209134404060302030702070803030106030c0e03070e0414030904050106050c0d0e0907110f0102030c1e09060304030c050a0c240305040c 75
    0x1203240321702102c03000b0444229048a800301c17450054800f00240060606640086001250030000506101d8906001c02541d9941c003a503801c141e50b5a003000620350000f80711000190301100440001044084900d0700d1209030f40d400b41c00f2003c1d20644280c88004a2404451600b1901d4100100e04682c01120182c0303e0324a000b6941c0d039501d11041e4500403075540500c10a110003c0001491685544100020300480e611159111420810076a0b0350301e0a0040c2c5030300c6402d210200d000141c1c4c0101408100c071460080d01d0412003c28001400c94109a1100d008104002140036542d00c3c140075402c00312042d4204990214242000318030412401420901400b0403088680280c0804011100480000c1c0d4002c0d07690b45054034500070035800818224038004c288680340a40c1d00d04490a454045001808507411540ea54504850300f0706a981d041d1010b00840c401c282c0031070002000e0f60040d16109404401c40c50380412944400d00d040c0e4440001c01d032401d41848009110a5a404103c403c0e03 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 358112275 1250 358111025 358111027
    0xd0b06091e15010e0a1410170708040f0804080a032607080c0c06011202101e050d0e0f0109110a0f15030e030c0d0801050a05010e0405040804180605190e0408 69
    0x280b400140c0b10392000e100425803140452000107900c2d012024481801001540d591040e1507122805880f03a0301c0d51030204007541690800540100d200300d00960740f05002d4400d242490901d5120b41c48242d006400441481c0c000303203802424150000c040a0f9045a002c046085888240201192404d4050028010402c4d9800480d400210007010f4503228680d400a0303402a5940c0c4407048604003115800700d00441c80d0348034800d80180905040414900d2034041189190302c280f40c100c0c0d46c0d40c8941030038841c1c02d6032002207541158003000501e1034580c5d40ba00028550440c0e0038940810303160070020f240b00740d42ca543d040c03098103d451b8800040360b5035030000001042055509501500500550640c142300108000d05107000009615162420a4644ac2e10701c1c0d03214011f0102c84121170148a000c91203200c140546030800740d025690180c090903200b414151544a02c02c00c1d5002100e080418a4450005201c3c92401c640c8142030903003030145841e0128030300380307401104020060001d889010 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 358113525 1250 358112275 358112311
    0x9061305120a030b0a060302120a0c140d1d071427040b07080109020a050a05160204020f1209070303020607110f030d022802070909110d0b06091e 64
    0x5810041a00e1444061011a440710b9100380001d0041c01c01001580c4100c100300300000310540240f0845465800090f40080709642d43c20300c035000741208030424070400c19040012040d000d8018040d0030b41c8200d5200c0440d07841c0c050004101591721071a1100d5030b42c2c0010b0410049140c900c4243d0191500944440c0f01440450b190241121000c840c0c4514040320760f8100303c10044002c0696200e10883d0b1a040541e98030303142110100e0140c1080c500104204108044902d07004030b010301503485c4120910f4588480c19030108081e80c104001c0c00080c1d91010076422090642144041e5000501e2001007462a02e5614025680d03c3e010b00394501f48081c9104180420b80d05011003100f0060040c100c80e80d40d40c1558600000b58480086e818414035031001c461171145c030944011641d40d440da03004201c441d08102d0500010a1004000c0302c42d482707074075419180c039220072a124203880c2c058140424280703014410700c265514000c0c030103071018200d1300c1d901300f415030201d031481c2e0056404040f0084a038 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 358114775 1250 358113525 358113533
    0x1b01030b0607050a05060f0f041101200f07210209060f151c06090c0c0602030a0e0118030f0c0305030a11210406110a0215100b0a02010c030c08090613 66
    0x84200e141c00f400303a02460a081013071010000e00e860080c0c010110300440c0c2c0c2d1719000750b100f16050690300180482030700400e01c80c40d9803203002c5603081900444560b101055035a04800d2910744010501140358016880401041087c0615900d00360401c805024040d61241d000902c05a00200341500c14171480c00442d21580b2403031025007044c4c00d5400c0d1544d44009044014480844600001030498144600828400c00c0c9004d00c09240302ca5407a40185e03840907540d00e0010b90070081410007442c1e96105080780c2c54809004610b21803100c09042c0c80d4010300c50400818042c014103c6900344508440ad1400080c0d0240031641e11141e02c00c40014000c800c556203089610a80340d8004085410f100c072201c50400034424103005a204441c01c001c1e444489070003c0c1039004003e4000c015800940c1307043c040c055911400c0b075008030154020000103480d01d503c000181c000001100040c0c0d5102c4801c12506e40601c0f6802111545042c042060314085450b990f4403800100075406880c0c4844040c0100 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 358116025 1250 358114775 358114777
    0x1060c05060105211b04050c0f0702040c0302130b0405090702030408191a01171e1203040c0305060c040303030509061302010518090108011512050c15090d060203010e091b01030b06 79
    0x21384460420780d0700c110743d01e12480c41014401e180440c451490080840c0380c3d05141012519210000c001e0a81858410303002c00004200d0703261a1424190200000039803600e9000100f0702500740070907100e899605100130b00c020302070020220f200799801080144003080e07000402c8c1c819207412090303304220030035141208107515100751100480072084000300709100c81031240c440300410f0a045444006c507402c0604819032000041e21010f41006208040d283e80c41c00c02550f0040c01b600c8010100359583c2e4850b45445000c0740d20004840c4003003824070400d03600d4016590005110346c020030250600021000c04400207042c000c0c10b00400168072040152240c480000c04080142260450f69442e042a40601200c440400242d032000001160003180e135051a0301c1e4642100007007105040c00b10a0000c4842c42861111000c0380510103a5443c0e90b501c90b40d0b82c081441104056100d524000380700062110180c00d41035690070400580020354500340400c0c03605002440e010500a1004002c03901c6 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 358117275 1250 358116025 358116079
    0x6080c07080d1407121104060c17030f060a120b241002030c010e0105010b0904110c1902040e0a03020d05090103020d1112100b09010e1203030702070e01060c05060105 73
    0x5207410040c0003004903003143d65081c03041d01e180e120844658401c80c1414101c60b8030143d140e070417180500092090b144100804d54003184245501980c4541c20410a40c00e900201e6100244400000802c11113003021507111008107042032031126070400b82d64a03620b080c5070040c9203042c0403075085010114010404070088201002030b00440a824000d00001c0d2207920607100c0b400d180d0300b050711044410005124481c100c8d582012841e0900302207004110280005041c00ba003a035006000044a0b5481400601d0000c0500c000042002d01e0030700c144029107162194010f0345420070b49203407012a8010a100903910681e1901076994000000141c0090290213068004140341410f020441ca0120004100c0b03540079140c1900346545852480c4d101d8070b014020104060008e101c00021355010311141761090030000c03d034030319052461000c00d195030030880c0e90400603480800204000d2040007031040c054500e6140c9210301ca201138948a0341c07a0818415a4064100b107043c0c009101172044803601 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 358118525 1250 358117275 358117297
    0x60a0c05070f03020f0708070f05120304050a0b030a14011202120f0d0302040305120c030a080c070f0807020108060627130c080f0a090f0b04150c051c050106080c0708 73
    0x3444920703e05009580700302040d5840010310a500700401c850b040060f0f0700e03003100d03884e803840c0080038205002d0000c0c200314062001d0203884240008125036450308111000b500000d5025500c9107058180f20341a00d00c10720210841858113001400589100700c00c000c07610741c069411107c8045422005031600146199200385401556000f05903a82e16070010300840b070140003207030000c0601c0044421a403241c42d11070340080d80104140d5660b58056400994002c1d1010707445070400361030780c5942444280c0e4070805ca5481d413001481c1d00456070461001e940200090754018140340440803840d00c441651420307652104035010b01607403141c0c0d85048a400a4000010510002981510140440310b00f91000944400740c07000045400c1c5103441540c000e15000310714448214404e4070340101d4204040c000b5038050301c0c0301d1250003209055015249594000d5950709550300c46100c4008a0407078032030142e90200342010f00400a4135071010318541c1028140e06219907c11042c13508282510410034021 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 358119775 1250 358118525 358118543
    0x150e0108162102040602010c0305060315040308071103030a14070801050922060e0703030f1112030604150e010501020d03050f070e060d060e01050f03030703020d050a12060f03060e0708060a0c0507 86
    0x41045a1b040d04035021141c5c071600c0500441d100e240c20136441d0427075680b40581c4950524001004a4401ca8141e40c0007540c40c00d10300c4506180300b10541c1554412030f4645141511080121641101840e4103903210349a45004c0380a9410903001400e84900601080d01c0c60004034a0240803500448581030541d501000410603048619540e075104c1c95540300039030100d4030005490310ae4a014500740c0c852548284040c00344000407400701100e60b000949a95085640c0704207c40300004c60b00c6500d03020b801e040034802c0703240d0701d8600024645290384512b203081500701000d104c15003c040c1c003955044003882c1000d5440032101400708240d4003660990041d0b0f035080a41c00a00007044540c01da0680d00240c41480c01c2c1c142000506a81c1d100300c01000340140d0001c2074054406110f180540740590003450704850706410318203140181c62450b0062540002800020010400540304012100c0000400743c118685420b80c50b0740c03036580003000e520782941c4ac3e0090751003480c07041c0e00b00c2c0d403460351106000d = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 358121025 1250 358119775 358119779
    0x30d050d1112150111190c030206031806010803070203070b0d140f0402010e040209010215060a080a030203190309150f1b080403080906090d050c0304090204150e010816210204 77
    0x190240b000e0741e010816030b00e001d45000155101d032010860240381400207182e01c1956421480d221a07649100303407641004e0520100061303544400035801524540b02c030300d050401200c092410280d06a005080e150300802030320006840c007140e480f0484072124641500c2c1d8000c00a45800781c02121500c0040c0c004036010400d843c07140e00c05003406207000ba03031628a0178007041d082c80200c0c0304550500d8050390180c5100e10f50f01748120442540518003034040b043c0305903100e0840d0701d05050008100c01603003001c510942d5001c8810009912500c1c03074070f001d21114840c1e07110341340341c80d6038000c82d48042e6032100c00752010300086803c070442c1c1c1e07110070240341c40010080600410203c0c0a0b20103e00054440c80411544040000c00d140a941e0000180001130160b03041540e95521004c1800e034140410310000078030740e800d4406030004199501071306070460314640006182d44100c603d100d044c0103c0c2c8080c0060541d00b5587c0e0341d0341700c0140c1400c8140348030464121010450035807190307003030318000240 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 358122275 1250 358121025 358121047
    0x110705030102070c03060606051c050910150305011b08011707120b070f03140604020702120708070509070f09050d08130308090103180213020a051306080420030d050d11 74
    0x4c41003240e0141004110035a1101801c4540344207401850403498080c0c02c8102c042480c1e0761181d40c00c5900b110459410640c071484080c140c41b5080d101508e45400d0903010000c1c48028055022000070440c07895103110340503d4043d00a80060048034903a25500785600d040d4401002403c0c003a02c1c81c005d180880c584c03980f17029082c0d0b107000c89802c00010804004801400d01a026400e000c001055001040d03680d000d0510000390040036090345e000c40f6284466a8800d001c0c420760000e000f080700940f11302400c02d001c0c0608a000a0404801c01ca054142840038035031110402003078a4017204e20013000300803805c01c030101d40955030701180503442c1c4000000802c2102e100904a54000ba24203024101c0c1c2034035921100c0e4000103010b034002003104034001041c011980240b140301c0741030400a04041c0e20703003610700c0303c070003c2d03009000400c150300188010b100f81e04003401903085640c2c0b4624400d821b16008030b916046a00c038150107120300884d0040f0500030315004095100e0b0004600c0307031124600380c0 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 358123525 1250 358122275 358122293
    0x20a050a1b0501020604050a03030b0a030206130801060e09030304030309020105040308030a151208070b0c040b030c07050c06090d1211030c010902241e04121506150f11070503010207 80
    0x52000c0840d110040002443d50001c02e02e07030300c90307900720001d0142c40340281c0f408d5028000e20030340303e83d11580e40000440180c0d01d500180003031815048215002d5400e1041d0707e400c6413215003001c85400c644108008141d10004122580680c0c945030100360158244010b03502d5005a400c01444400040708108a12015900c420700c00003041d400c14981c1680c2c0d000e1b003001e86500e140003400b00041003101d0f50204400c03104040e080201c1070440362820b50756610242e4141c009072001018109c0009111080c132004010090129808644031440d000e202d03070016402d00ac182c0c40c0201120f1403c0214150389000310306244240900340c003580d69520620b90068000d010140b0100d10604109030361110309280309101855151421aa280c988a81c0c884010681d510443c042401c1220400c00840c41d05a444000c42c0300511400c1001c2c0258440b01504050f0740268000c0c0020240021519402d280d00201d0702403501031a00b080cbc0050380b0351340e90f01070504d00103420154056000280200821800c19 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 358124775 1250 358123525 358123553
    0x604181b0309020a0e060a060806210f01061e06030f0905010e0f0f06010308030c0315060406170a050c0d1805011104080709110405011b0c03150e120f0703020a050a 72
    0x314144c403d2612403c1c2d244404000b036a40d079401031030700107081c800f460085d4074864003e40300505000b6101d0030811017415846070a44240c02a8020300d0320303c0401103003409104050103401d0b500c450305261642c41e6074080481881401c08050312082042c1040e10300c0c1d0302202d61b0540050080c00300e20b0301586003076580c00e810010040c00e4481e84201c400811800324149041e207501494651660b29a52805440c3e50809416001042804c000c41850f076a9080d00400c001c164130744500c000350f52010855501c0d403200601d0701d00a2420002000b5481e10302e00d04490302c80100400006801030040d03c4105640d40c0e001c4000e01640c0703400749141d003c180f294050300446110004036105a40ca5440c00000e440040c2002072002009020a006560103240784503c10f001e03402040070b00580c0c548134030f00d150b405580195100c04540c5511490200640103a824248a000c010950320000c8004c2000714031605144181d115000301d14030741018400d100c0c444d602d0b81c02c24201d44040c180c2e8140200200303481 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 358126025 1250 358124775 358124779
    0x60209011710080d0c0213150e040b060f030c0f09070e03071706090a0309060c150f05010306060b040303050f03180601030803090c0d022215030f060b010e0604181b030902 75
    0xc6203000313007620702c510000d24886a002d401c50001010000824018000e10741c0203400b00c030504131001c201c2140d0070030400d101d02c0c0103656251003410440140184990050803840c06500480429605a203c0f03040b602c1c01d41100b6640701020365102e484c216501031802c40e106926004200001541c4c418003080000d00c3c2e018401983d5541d00c603000f1160f030f541d5043d00d0040101c2c1102c442081140d008030607074004c01c1d00a0030040f410a01016004045400c00740a80c003180f075950300180107101c01c42c0b040401509148803154501401c54070084c0c110f00408110001c29100040050113003030b03138141440001580c202c1100c2455031240703440603003600110341c0104148141500c80e1441e00e00100d2540030f054001e0101072a08021039560a1141c480f071092003000d644034441c042c2040e80404d40c0c840214000c02c80b11806030b2091600d001540c16000160781040710003400096a80d0311202214212080941c0b035032a81d8420784000f001401c80b440d00040202d5403181804900ea4068220031101803007 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 358127275 1250 358126025 358126033
    0x11070512030909130f0803041a0a14010506040605090f04090501110d0e0c0105091306030210020d110c0f060d14010f0305010b0a06051c06031b0305120a050706020901171008 76
    0x5400c600591001c4c0c030040505400344200802001c902080015900140038a044424104414000c841680030070381d0305c2c04c0c00d103680301d2001200c2003911240034050241250700500d00351512000a00314080d050700340d44152141035042210f0f40eaa5400120300c03660000c001c0c4009110000018403680109589030406411b0002c1f6030315413580070400900c01c11b8140c46050400d075001083c0800c824441916241d055940d19020002da0b071a40c070440c4d910f0030383c7d50040268800f0500014a00c0280a600804070350113003034900c0d4595a2541c0300e6000d180180c031515295020b41d0400350241900401c81c4000740742040011440711502031040007a240503800a10080420f80c0c10b000600726035214100006006001030308005206900c9001c000a0384100460500e859440e51a4442a4464161120040b4100420030407034280304040b14501c20a1425082c1525044060300d1441542c0c3c008000c40d40c0040e894444d603004045505481d8003540f420a000e141c550380071140e0200a000e42038551003 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 358128525 1250 358127275 358127281
    0x506090609064b1602030f0f07050703060b12070e0103020d03170c130b0703081512010501140102070e0c0304022209060f0b1c020d06020702030f0a020123030711070512030909 77
    0x3001404c04a001c003036a40258580380381400e0b41401078000100c02100180d08100e008045213040003c1009580110000a01107183e4810000c1c0c045101a214505800c500381c2000704076030b180c0040e411070341c060b20004804103981c13604840c402c0c90b4880c0101540b1101040c000c600c0070b1040504610110000190390039500c2ea01382c40c0c058000c8010040005400d0400100716101d0082002241200a00190a042d204442071404c2d200e090704044610441003e400d160f9680c1000090001e00c0829421045c1342031001040b2000d10008002034003a849420002103c00401c0d00c1c459034154418008104221691030203c004e842280300b0704050f10306044411690345403281c64030b142510304000142d010070565007031204240c8015010703038150b9804c3c0007540150300d00f07004030000701c504e00d405003502d0081840094a00044143c01e250b80e200408105807101080c4801c4a400041c3c0d410300700210041c20034194948150b0340c01071a04585071003100d10603400c001004c1e00841d0022a9030350f4003a6 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 358129775 1250 358128525 358128541
    0x4030e0114120a0905210d0501050402072003030d380109121b060c0605160c0f062a0306051f050319110301030506090609064b 56
    0x2004000402c1c04807041600895183c1150f0752045080d548640152007108020896011a0100c24007103e41e1030780c00000e0501c407503180c41c45407a016040c210b0702107040c2030094451780000c2d4220a140b00d02d030312002200107000c0c0d5040042e140b01c440c6102c010f12000d210322003282181c4403500032050031080c404034030468288a580d4401c2018070180d42d07d4020301e18114581c80b0719500c010083c0e030428443c076004807561441c20201c8010744915118002d0400d19850805c0884a0060448085201203102440c4050b0710001100ca0705c0d812450f2411020300f80c0c10910002c103e0003848410b10545585800c402503284c1500f804c0f01e00ba961801c0140d07565074000e000d040341900c810f00c0141c8019103031085816000c1c3c0c01464000f1a030541c003841000801d41200102e40110004d03421300300d00030004008022003000318603485030117080130308003d050844119542e244060051081355441a5449140900440b90070071070318032211144502401c202e141c0b114031203000d030b90f22004244220000b1210 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 358131025 1250 358129775 358129777
    0x9030f080c010f051501230414120c061b0f060a05180724050d06080109060c050a08010e07020c06030a09020a1d01030b060109090f0b0a0f050904060507031404030e0114 74
    0x650000c40d5012045c01d0640044170060b40314054000c0c00b01031180352003510000b0b0400760000c0e01898440c4541044070300c0402004200c13040808020b60321101c051011030720340c9070503546440c60b0024100351000c0d4000c4028201760307044800404030700c42c203420040b0a11864011034000d50906661100e000085400079071214864010507032061620a030014420501d02500800f00c0c2c0e051402900b409554500f0300700341c2c2ea1960084116039118480383c0c0a000b45032003201d451030400c2c2049483c128166201030030b01c1c44148520000c4240020025401078001d01c400211a070005100c02e6032403406100b03410060801e440142d0040007004c0010403c080700c495624000700c48411082c840307a103165141c16865078000e000f18100041c0354400a4030003154010890601c45c01200801c440c0400c8091085c601d030658005070780000060410455a101c3c000320a03081600420045602d0b80c419406a029004101e40441910421010003061640c440d4440040c85c5d400d030703a6841042c00d0320440e0861 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 358132275 1250 358131025 358131031
    0x150506032103150a0605091e03100b06040f170607020a0506040b06010c080412120801060f120212010b040e0c19180503010501091406100c0b040309030f080c010f05 72
    0x18080790441d1081e6150000029581c010034241c0425261000c0e030010401001d000d41c00a03001c9000400d030541d4900d005490020020b900141411407045480000317a0b0384c059001e1142d21550340c882d100310703958840c0822034011300202a90603220030307034403d10003445884c0b10009205c1390280401054250388045400081907401c0801030050f5140c544585a10310343c080e0201e41400381d0300c0c0c0c00100055041c009007005201c402c5a446500040c2e050607510380e810404800d0402903100d0040c400300d60004d180902d180b0841ca8403400c1c010344021900c00034890030510020f90417101000003002424000140180c42c154200310342144c42e4030102070b142d401a0340003044100390074041d0a2110303105003501c0740300c0d8000b420080c02c00c45c1e58102107030071a10280c10150541d52a04141c0c0c0b140c4800c1e200158221030280d80d0010710f9116001300500410002000812800e90b210104043c1482220000d001d583c0012405008150301d1a100c40c040d8404140b0114035424400007203c3c02c140d520030a84 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 358133525 1250 358132275 358132303
    0x105010207030803130b04030e090703050f2a0d1d0c0f30071a2701050706020a02010b0112020313150207051c0e120327040915050603 59
    0x1100c2d0840d912014207030402010302c54801c850030003240120f0317006e40040340194040e03101c0400700380600c0c061080e0341100510a809260500040c880d02c00d05201c000703a800300c01e0544140c1d00024102000043e40c600d4941482d200a010528102c040d015908ca03010708404092618851400046907540343c226400c0840d900c5082000704008a05040e440c501400d1154058952007680300501e10840d5140e01c0e8555919600000041c00402c0310035043c0f903203d84c490b24a00b803d1a0a00c405114002e21140e42c28905001c010901d42550340100d0546045a42c4240f041d911030310100c0000303008021503420340d0b000030792803020514030094501c200d900545098040d00d210340322076218075a042c20440380d44a403441d400c02903030020940c00c0c098400741c07501141d40088500d402041c010420b00515101602c0b0310100d030311030002901c0010488075100c40352603245001090244011130a540f280b044150030608011a4504010900c4209c04003030f00e1005040120340c81e4601456a51450541100 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 358134775 1250 358133525 358133533
    0x1201092a0807060c1b0b03070c02120309030c060a0c0c18050f010b0901080402011809020301180b010206150109030b1e01140f0906040e150f0a05250309061104080f0601050102 77
    0xc40842d841c89580014240580740202e401741d51200c03104002c1c0d008031582030004030601175890840c5492500c040c100d000000080d81004070030300000762209581d00384e0602ca850300062199045000ea41e2000d007181d0003084a0344110380d602c0307440694041058010b108649090005004140b64400103030582d4400f00703440f41000c00c0b8200541d41142d0190007039040c8122060003072050120a075520000d010841d501503200c1d45000044941d404d150b000243c002800d001188046036400614180d11200510101051a42d11001a21004000d03007010b071681c040c00080040d41c1e0842c803a61820100303201c14003203042c2c0c1d903551610840030800c50b505500100c801c112494030b06d0b000b80000d0300f02600a10001d0071601c401600c520b0200800403ca000010441c2048840c500003400b41d980005580c0081c0180d150070300386078140c45103615441e0092072895a46030940b5119070301c89a112984810208104041d04001c40c1040e04503201d104014030820006804518000c501136048445c181c00038 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 358136025 1250 358134775 358134797
    0xd080901140406150510020c030c03010207030c1e06020a031b0c0302031e0f0a08010302030d180b03041407080c0307050411030601051c0207030905010311070f021201092a080706 78
    0x85020b010511145500c0401d90038002c5017660703810340d0804880d40d058000340310b817029020906003401540d401c042c5c401e91040c49031401007500980602070260740181195400c200c00130707441041c2e814121018040a00c0401c06406054142d8080360480d000124441c140090441017114000e40f04c0f074000340182c00500c86407056040309500f08a80518104032542080d841c203045100031f0300f0000071000080d1700350f0010415418284400c0b03640140c60715101d80010b001c681e000310f100300c441c410000d0070f5100200041c14009000c8409841084920940c4c000d2075480400300c2c0e4070031f9504100c0e0701ca4055004001400d1134036100d41031250f515074031002e09658450005480a1300414414617a450550a003400c4034182c03440102860b82c442e46883c0f1280b130a00000504840f40806202c814000c2001094040341c41081c007110000c0c1e0445400030071200d403120b590b004d000c0c482d0000304030100c3c41806841841c00e251040c01c0d00706c003400d480141e20355540c0c0b00994a070554828140892103407446 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 358137275 1250 358136025 358136033
    0x1170d0e120f21131503110c0706030b030d090515040305030d020c0706030603110d02040e030c0102070203010b0d0320161203170c04060302180406080d0809011404 72
    0x18500103108024800d464500020007554184503031000e0084032500f02040c6810400c8409034441111182d0b509400e05140c50701c0c3ea008018000e031300880d544108a6003205064500c03e03001813482686805565445008145c00f580d510000ea00986c03010a0404074120b01900300040c040e9000702c000d03500d0f03040e824600801c0c07040c401c0640c008980340c59010040440418003c200409108125000040c4e031098081149420300714140c110104140c248402000842c8203440c01a5207144100d60900f130b80003203440000d00421101c0c07894201d5001c0425000d43c000d1040d8043c20300f49000f50000e2002459a10803c14070078914180100426681c10070160150000003062040315629070465103680c02d5080d1107404800315070720098100c0402d24002e410903602c40c1c200d20358440d0310481002d6900303005419525a0055008d803404041e404140c168100440d00c00b040584203024204111054a42b1070494452003210180008180802c01041018005228040d46960f03580103958080d01c0b02e0350703 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 358138525 1250 358137275 358137287
    0x30d0305060a0b030907031205030702010b010c020d1203091202031e0301051507060b03011b0f0305090303060114070c0b030615030103030801090f090c0b0415030204080c040905190602030f01170d 86
    0x105c4030383c611841d8404070004000103100d40702054144c0300e10b5101d26009000034203440d032069015040108019100006845c1c043e20905543c1d80209120340014514108900074040c4230300142005007012403500e03040d41c01100501780f08a030101c0c0c800203520000b040700414803081c42626000032880e001003420140d22400780040c648101404150315400c180024255001c03448150f5404034060055460305030403102d05002140c850030107101501d026664151a4003000344668180454042180302c080080403c49454640c00340750400c0403619050b020350242c10458800b80549014030640300703c6100c91040d03034100c961641d240b007403681c2014492800351141c0700c41c0c0840313241c030365000c00005050181400b000d001d0745080d168685180a50070380316032f0f1034601c0c14810b051041109205858011508103e049000d40300441c80a80300d24020745000303012800d1550001043c45c0711810000d29400941c0a0000d000049000c0d036204c20102061500d440403080056206080042c02940248 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 358139775 1250 358138525 358138531
    0x312151805070513080106050a06080f06010f0203071a1b04080703110d150b0108060a0501140c070e0c030106090510050723071d0f060a030303050a0209100e030d0305060a0b03 77
    0x201e0000c4c00c022413050703035200d20301498000220b580d4444000748660300b0720140d8000200098500344100d03051421a0344003120000d000f15040160140140300000e000f0421205010b034868502c82e04101c1e04090642161426101c442c112085160f0062898821070305490590344040040c151403840e603030781c080c241100340ca00c040d0030a92942d914000f0648000030340310a607240c0c117004504000c8003000180b2080300288450b1240d11100d1041c4101d0740d219415005d0702101d15600360341c0d09400d140c91842d044460344000d8006464000b040203014900300514122802c0d600c0380c4021640b680d0400c040007560212803c001034052003154003080d00f6101c80d64080083c1900c24120790b00240e0f070b40d4104440c0707410910280d0061024920301c000e07800c1c00b0079406103400160301d0881c148500000c0301c0c4400c0d407101504041d140c5005c10700940241e81107502080c801401e0b400054284c23040035000b01c110741c5141d41700e406950380b40c07021a402801103d20518000f07041120030703424102c10f401260005 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 358141025 1250 358139775 358139777
    0x90307122a06050a050f0907060c080c030c1e0706050f03040c0807080a02130c0509010f0e1c030206091209040f0213120209090712020405060d020904031215180507 72
    0x80c03003540c040c1000409a58038000c042c04101d502d4020820001c1d11009042c100c0052003d004005110001141d02c0b0155203043c03411440002150078180303035902a1100e03c02890000141401449000282d1500e02703890660a440c6800c031a59140d0740c5411240c402c450101d207042010484111302c8a0040d98003d11605824403040d80342d51a40b0301d007100c282c0140c038240d0300203000841035107005807581c90040141e003006d01220f2400f1000a000e070207075a03069810311000a8100305c030389010717003034400c100c03000504103005004c0b40060b91190001c1070036054001d8064032010030340748400413445040d0420030401851400c9070381d4092000030203008042546107542441800701c00c0c1180d1140e000204401c2026665009060041100080c40545404840e81c400801040884d880c00510503216404481c0050030b6070b2035802080b690114404020340c40700007101084101500510101210f00da0b0200400c090082511000c40d0002a40207030681018030500c1400034556a821190b40b049103 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 358142275 1250 358141025 358141067
    0xc030403020c10020a0b0a050106120209030a0809130207051f02070314031801020c0c1f0912140a0b0a0c0306060c0b0a1410030204050705030106050315063009030712 73
    0x15540302d22803009400d1f80c2e2803009648490041001c5640074900408920f0840fa04518043c40e003000280ea03412100c01c01040401c0110303054130366a90710111624440c40d840c1d01556140d030300d40f410030749234130321034400c0380c168a017501c103990a0218030310075107001d140e0544840031080503110515034241c100500618107001c6500030001c0d111402c4c00501a40a070400c000c0548076400350400403820300030b0b401c0c409058581c84038142ca45034030492402c2110303005e5080c0d406076201d9003003030070409150307052458140c0304101e0524200300c0004803051088803044402c00900d0503400c0c0c11800e0f075419100b020001201d04140b040400c1001c0d01e00c42e04001401d00c0003c3d070b031685404020142004803125200f13024030545c100203500342401019401612890f00b1803856041c07250241c04d038040a8a805021594a0403408275500c41c10211141d42078074841c0006090001c9000800359005008880c1403442c1e1807001c2204040c000003a1400340c0e40c40040d40b0540200e4890465481c0c20303d030b030304014400d4 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 358143525 1250 358142275 358142293
    0x509030c07080703020a0e04080307050c0c04020c0a11030f030904270c03060e07061b02030a0b10030c050a0617090a1e03021b03031603170c040e0c030403020c1002 72
    0x40070010755000700307082e00240c80c0c0280746004225074060140d00000c0c0003080340c4104000101a181100e9010115080150301c2e05a030703085451030304040c2d030121500a41f002070640810704001841c2c090143c46010b880070811404401d050701c0b4521810404802ea200303004215091410340c00c180000d07031418503c6503400c3c003041c415030007070031404100366070011854205000340410b0f40120040e162009000385203c03072600e03070010000314562602130506d20692111804566050028008032074100c002c3c420355040901510402c4025403204666458007014000f0b0340d8140030780440101c1e800381d11440c02000310520280e00c401e60013000103050740190100e0300000b03000b030741c900780c03808a0603c8441c854030140c0c034010340b400081c650014000401d080d01c48403680d80000c00c440045401c0700d400d41805041e8036040c2c0f003241c95143c0030488801d40e8820030001c000213602900464482e0b541021607603e543e401c10070140b01c2620f0103401608440720344442d41c1805000141c903400c59104440c0268 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 358144775 1250 358143525 358143547
    0x51e0c07022b05061e010515070b0c0a020d09050a0e061201090f020a14090403120204080703050d0e1009030605100806150109050307050105070b060f120309042d050903 74
    0x1400740340c00822112214034291081c00303c1008038a600a54282c00741040759441c4254161050051041e1441242c00e10504111420004107403441c0d1948a4a825081d0409010306840d03500301850150041c030401c15001c0305103110750060011268003500140440f41020411225840000c2c4600d40003819035848807519802407042030740c04d5025440400080f40d00d841003021009060f844014500000045140e480d55013850350fa8219901d070501860540700003101324064000e561000d031071801403060001c280800415034000d103405a5680440352100341081082c241c41141da19000642c0d09a070510018a10b503105a4001d0070b00414400c0b11980c0d561254548041255288110742200ca848030351560456580d6001c0d0030200e02038800c0b1400c001c0028194065248050140c10a403408108141c99600c0301018200c1e0240c04540c0392400e124005640768049125180240c3c80e01001c40c5500590810014954007801003080c000c003946060312000d0320001d080c0388031600fc1045440d20741 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 358146025 1250 358144775 358144819
    0xc05030604030c0b0a050c0a0305060109080a0b0f090f19020a0b070303151401020a02060d060b030c040315060303050d0e16080c030f0a0f2402030408030604051e0c0702 74
    0x71442941c4281400146242c04004030390b001d010552400c1c102020301a10414560941e4420403031481e0002d603d64079100101c900f40c5869010a003a07015402c201c005121803580145e1160f1003852a50201e512608026680e4001850b1104d0854000050050391004000c0d04041c0150000f41942003890715006a12a1580301e24012004031b039803507110b81180400000030f80c005202038504401075902c04400030303440700820384009105500020303070100405a03e0744440d015103154640070380c503450400d8220040f0751040c0025645c10070f0101500180001c5401200180c1e0f03403641d07403142041f008104500282c103008003101440e008600310103000255100c0100c00500705c0707800820715074840d50706140c2003000e2454801040c1d0001600b03c0040343c00030381140e003c56440b40d8007003604216001900e0710f03800c0340d51701801e20600003c1480705010350f0a016601800046508225035141c40103460181d0701310aa030320018070240d4000882d00480031000c6c1c00f078030f030002e80880141c485880b842c1e408 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 358147275 1250 358146025 358146031
    0x312070503120c0714070524070b0103050c0117151e03010e0309040e07030c14030a06140402100e181003081308011107080712050c0a061a10090509040c050306 70
    0x151000100b090403c0c04050014505c1c0d0340010805810300c41e0609010400e42d08068119440c040382c641d0742a42c44500400446d43d45541203008460a56160f182c841c3d124880e51883c240000c01f40c502100b40c2030001044180210601318043c842e00d02c0004c01e2010181146400c04105180306c500300a142d2001e0280c03028501c84003019550b40c8071800c040104480004608490070b510501c3d05200043c060600c1005031441c0c08a420a542d18070000a40740c4450720710018440d0741003138001944035014407040c41c081d41c800c07100360044158400e01154560307a180f50695120b1181c00300c030750154041c1420f40f038100c005603d40040300f9880c0e4458081550200200c507400b20b0141704200074052023072003180080c011082000340303451042d40f81c4090a004844015001901100c526944c1900030f80490b4503007810038080d190381c0d41c80e0b414003074000d1200f114401c40416488072504101d00d0822000310302c00c00251140002141481c080c007007032a0000b841104d09a642c408040381d030f541c04001c0144 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 358148525 1250 358147275 358147291
    0xf03141c0e06160c17011518020405130f140c070f11060a08011802030603120d1404111305060d1e0b1609060c030509190b0a09080c090402031207050312 67
    0x1646407a000740c04005200380504558170381d2408604010304003090b5249070440c7c0c01c01e90f105517081c0321840d04000922956010541c0700030704054040e0811281e8014504030000e0380c00410103640e6000600402d09002c9841414100d404c02c06100022a8441d41c110750501500c010415845880701141107a80030350640e00c04504004010840004a2610f5002e45140044154150700340900407998424400513044142e42c00411051645401070f40300c0045524906244543c905090500c043c3c5a43c0c103035540e50213400d102c981d00201007114007566000f9080580300c40d40808891304c503000d0200300c06107130a02005a080b503c201151704800c0e0b0034000c1403169140c1c1d003099185507010b040d00484d40d01900c02d2126525000c40803c0d00082501c03201071054844480c3c0340d00f401d03809680c0c0025038004140c5203401054202520b64024035001c255803a90040b607440c92413820400c40b0131201194000e41c95407028050380d104100520180407400d2286044a0414045441c03540303000d1400c6806032 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 358149775 1250 358148525 358148543
    0x31514040b10090e161d04021e040603150c09030b06120106030203011d0f06070504030b061c06050702070b0c071a120702060417030f07050a1106010f03141c0e0616 72
    0x15680a8117030002600074142541c0b10030407041d1a02a801b45844c0c001c0c8042d11804503820708420643c1403400031000350100070030811910782c0701c2c640750100737412803034524910138a4082109010f90007100c15209403900300300314910b646d580d2020018410000305042079a552103c10000060300c090003405c000203c03854229590b102a2801c8928022004002c0303881c079448074080c0700c1c20304c0d080421602981d0f002841d1303a005a0342c0e0800300f103440b16003240c80c0c00c07003a0031080329206000c0641e104901880940e401d42e40002e42e101101c2005000703e10f010720349500426000c0000c030f00015584000640200203160926101c80c044030600d0350115a00d0000d0307002101000100420700d401503602c5071a10300b0190031420589058030081c04000c0c881010b10a0002c4c500c91294014000e0030b084040107000ca0b403481d07866000806110426100071580101d6030100c1c2a00941c000c564165040200d00440a03100f5299038100c030044910302095402c40410000752940b9102841d203500c0242c0681600 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 358151025 1250 358149775 358149793
    0x20402030c0c0d0c1106132601050114010207050609180108010e0c040c0c0b06060d09150501050a080a0305090a03060c0c0302120c0a0b0628031514040b10090e 70
    0xb16050244000c0e01404000590704954000350b0340084041c0000c5003540c1103500d4107080309182ca00c441480d0400d00300068081c44059586203540000c46038030b400303a8000c0c0070f00d0340c2e00c9a0300e07a0440ea0a0300e01d203001d43c10500d01400203040050207001041001070001c0c0d1440e030040a1001c801c0c0082c1c00440d00c0740d45071001100c00303410410499101d04001d40e020803000c003c2c40c0b402007440954110082600d8601004511181c0e90742c2c06841d2041d84c1a001004080381c2450701070000303104141c003400c0050400000103558981840404c0403034642c217001c0e010361001903600711055488480203a038040e03030800000c00070458600c00c83c0c0c0e07020b6a948404074413840605011346417400c4015004d038103d0040003801c0b0840008a040170748640d00003802c548589944002421f042000214101201c1d9450940900004240c4001c0105c0f802000794007642d80c1a1840503054404030314503051889100c80114000030088000c3c0c6502c4801f0308840d400d201d40f101c0900041c0e5812080c511201d90221181c = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 358152275 1250 358151025 358151047
    0x21e07060b091509060a03060e01140907030215130915090f09050717032104030f020102180112090209040501020a1107051305040503040e070f0815150a03020403020402030c 76
    0x16030510040c0485914602e490f00000b1010840ca5443c41940103810388008240d003600e54440002c09903074001000d010030440c01000c02d009114402c0c1c03a248402240c0085400c525011a564068940240040000a00c40551420709900c280c038103494000380d0303840005180c00d2910440181c044182141c1c10140d141104040030780740d081d02c6101c00c1924240ca00c500103280000d07040200d40a004112011600907130240d41580104041c000c81d000345911800c1041585001d040c0c030562180d00c4070380c050702d40b03050100d00305e006113032402850031b110318005000340d1f0203a481050300d180000e40100b0034860550104811070010790b411101690080f84441110350040341d4480c101d52401c000b028070b5132802c1e0009600003014220200f2a82d0f407a00440d0a0001c244210b4024042c0c2034180486030a140300002e20345c900c4561980c00003042200441c1903038505004a0052520003850495500302e214213000c141d5000182880038964200400001038549001842c4200780c4440d10a45035030380306030 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 358153525 1250 358152275 358152281
    0x4021513170102190e062205010225030b15030d080105041113090f0e0d02030c010f0c08060f0109081f0c05130e19050112020102010b15040e0406021e0706 68
    0x26100300d20b40d0040c00012100f101d140c0110074030b500341c0e14042c252421801e022401038810311030005401c4076217480e80620300c00b040400804a80e02a400c480c01d030300341040050b104042c0c500c0040c503a000c140c201007001c80c448000355a0081d20b49140700481c01c01ea05d00017450220140d60500c08074444400410092500b8800e0444031035009024600c0c181c50180b500d18181310a01402240d16030f00da44e548400c1341caa80c007140d1280c01480c11220030840c040b06c007941c0c80e000310498040e0341d0701b00084050f154085005000201d41140c880010544403c010081148040502c444c1006012540010344000c204011841d0800f1040040c8000403060282c00070358420802ca241400010041c4204989c650103200c800c40d16840043c0c08103444d5510324101114814001c1d905082c03c20b0000f08001401030b071010800d0307100f40c00070070130b528100c014007884990701810181c4a00701400300304140f003500d42040354480d105801c0146007120041c80420003e07190843c000b20001c0c040365100400403688 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 358154775 1250 358153525 358153559
    0x50604051605070b180a140d1d120c040f0c1715090a0905100f20030a0902010908010905061609080a0305160b070e101706040504021513 60
    0x1e00020300308200c40e1002d0400d101d000310040081c00f100000412828601c0c517008000d071115015586a22010300307002c0e0341c0071908007508100b0700506506c00b5510780600c0307891500c03030002d2101e402d03444003407000c002000000e00303510940b50007000071070b0403a540c170b40c800c103585001d81c03c000094103000110000c0080a0703010a4148100c0c001d82480480c1c1d0804003103011660080ba04440c0c113968000e00b80c0081c22120200a0907480b40340f450352042c0743d03103412507003689518640c20801044190046120032403699643d10480c0f030108041030042ca166041141d1190060410800c1660b884001a086807507208042d01c96410543c24404403440042503181500110302e084030f1080c3c00d1641242d140c4840d0314004051107070001d001241078807044000c540b20b40c0c000e0b42486151a140002812019801d8412449004040c4901130001c2c010803907110608004040248940d4500e410b0000a010140040e6805545080c2050407401c00030000e0500b00c0105e20b4107400b036480c0c440b0845041b0b4090b = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 358156025 1250 358154775 358154791
    0x9051e010e3c040507030602180411090d02041a090103050601091104140d0c0b16050706020703050a020f0d08030c0c01051b091302041208040512011112040501061805060405 76
    0x245050341c1c00c01009442c09000d5001c0125003a0464540c1d10703000c2e243c400c0b2a400185654008030305465200b000301000b080c940415107052204a040d135030501883d01c52090000e03403280f15580b400016080a40c0103440a8424080702d00300640d03001c00061800409a004454a1b4014030060150241c68014030301001d01cbd0200c520b00780b5040c4003040c004240541400c2e4081c03400800300405000d0301350702c441e0091101c22400707513480035000c542220007a6004419103e61140e00c0000801c284006402000c403078016018000d0b1954a900300601c0c02c60015940ba403004240310144045042c00008600502c1d0046c0050340e5016920311842c292040207041941100320303c480c070400c0e0202e200403204904022500486000b5017004903100078050794120b000c60941c003007a0307401004000c034010700544104a80c81450303200544130060a0f28500c01c2d0307a0154500c00c1c0307d010700d0909a4103400c1d800601c120000b061143d22050050300c20319050a1500c0c0241d202c03418441c40f42400d100d07060300200c0c1707 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 358157275 1250 358156025 358156081
    0x605100503040b070509030c09070f02160f17070b220504110409090219080f070e27010209040f02120907050f061315020a03020f011509051e010e 64
    0x801d0f1604981550020000010312200056480140d034091000f0410094001d05982150078400e00081130401020311711009445170201f9602804102c3e40b50000322030b09402046111030510090400890060401ca2200d200e0003a01140c100f540602411000c0c00406c039200c80c902131181024000e48441c3d22160141c0e1901c9031941d082e80000044030266030400e1004201003600f44085204290040c181d2042d00b24041804500180301044003c0c0700400d201c1124102501c40c0716031401e0001c20b80d80346140e0f840c0c55080420340343c0d402031503d80d00c4140304001414524500301180c1a1014010307241d50140d400250280b01c1003003601203e030495902c04c004d0108a0800022030854410441c6141c421040410511146030090148602a0801040045080c0d5a0b034002039514401d004088000d8001d03046c03107540e4020140b16103640306543c0000e03540820300d0200141c00411300a401c1d070307080c07064403000c085003c40007002c024020021b110f155a4903103000301c49907649441d0360204001400e1 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 358158525 1250 358157275 358157281
    0x40512011a0f0f130e061807031205071406091506030c0d050a081201052d04020d060b0706050402040615020a0602030406021207020a031b15050c16031e050403200609030106090605100503 82
    0x200025695089d0380d4080b003c3e90026402a10941e40b0340141c440c020807495100400101d6100003082c01307401042c41000322042080e0034a84138030070607070840e01503402d640003116805840c41c0c0500038000d50390040c025506072034540d4a4080f0306600220701510304000c0d06004100d103003040600072000280b080c08058030603201c60302d040031000041e5550341c426500818108007150b080d5002000404081100c1507807040031380340600150000301c1e01a0301c25407030202c0c0000d1010701e0b02c1c401c0c25030100650240c90b420040e6a5282d0007134101800540c0c240e9400c0c40b2241000c845983d02d07034099520340e001840000b101b1709e00240b0f103061840c10302c00110f1100044400103141904498007011040d8008121940d0701c0c07100030003d01851601d040c190302c1340b00e80c6a091640154200010168905041d24602401081901c0e14407807031100800d0000681119403402284114260f04038000a1040385400000070001e401d45e100354201c0ca550303650b100b80420840c900000326200803402810000d00f586 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 358159775 1250 358158525 358158571
    0x1107050a0810090305160501091a0705030c0a18030503130602030405060d0e0a0501051e0702010c05030403050903070308043507060f091208040512011a0f0f130e06 72
    0x860700c0b02100000781d100c5684204050148058980042407001c0c0700607104c0b154203265019140950701981c548045589007036011040500700340c070400700341c0c4866186440e01020b80c102c690049514400700400c0d00842d41445040d008001d0086000340011340e26280c0e441c481303c51444165005805540c820001089aa2264000c0d60004841110000307208500c1d0b00001c1e04120350b02d88000c0481d460102003080341048001e103400d038001e15801c00281c039901c540c01a822074100360410804a07109000050029100da4010240d000000d401e48140541c1c9a0321000e95801c50340100000740b84440803212410b046e821032200702d02e81d0403000c2020070540c0071100c0e21001280074880400c002c00032031241d503902441415004100080c1c11030100e03131640c24103280030b4200303004843c03040f01056411000c10030140a00c51048904030907450209107a08100300680020140d0039400444540d80c0e40b0250341c0b180303034150704804495404908080e00324440780c02c200d002040040b52040100242c4030785 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 358161025 1250 358159775 358159783
    0x7110d05120a021c110f010c0909090609020918101103062107150e10080f071106150f1005030a1508031b0d032d110304031107050a08 59
    0x2072894644481d9034078954081281420769118580766145461014410703003650202200080d41034a00079180c07030a608542d09420f032a284003605000850102c014070505c105988215a844d101c1e400000d1160f00c242d010864500041340c56000005540c540c0d2480f510301403148103d5075180c480704011034061642614900d010180001e401040010b010300360642c102031004000100da40c08440c1c1c1207548074401d460711000e2030042d40002d440141440200d040445500c1c030300030f8480e102c1c0c50f43c556503400c603003801c40d07002000c15080000c014991488030105010a81c051100c80350b4000140e00188240220414820101d500561141065140e040d5010060320341000d00e422011500c44411440300120000c9600080301700d020024015031030800c8030f00803e4201c0c07114010f80c1e401c0a1803080c1542100c1580408801280300b139510142c0c0302c42c43c0c03044280300a955820000b581f04544014424030340044808402040d402d0f040e03280340810400c001e90040c002220228010307070030400100d4031 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 358162275 1250 358161025 358161043
    0xb040f2903150114010203040305070f061d0105031503010b06070c080706050702061206030106150f14090102071205240f01080a020a061d03010c031515090b070f08070807110d05 78
    0x1002019450307076401e1b03100784200c40c0255004000c90b40c8441e00d0301020514032425104441c08140300031041c603402d06069086484841050311aa8110342e65410306641000600403500e43c19580c80c1d6040083d44e440001402009024041c9052030300c2c204840c451616115400280501c00d05108a000681d1500c0481e00f110344107000071151034481001090140455400c010704a101c2000440742c0320354019141811070800da80c0f4403564a898a203c905130340300d0411501e0058010810a001010142c07a200c1401446130044a00c242c0408060300590a50317401e40c0b0f008070241805001940702286031141c05000440f029211001480d40011100b00d4248036070b03418803800d24050300404550302001c00900c24090300234099800390708402802040050320740380117101000408034850f4440000303640d0508940d1180b5041505143c20b00c0065044080c0c210303110f1403400c0c1400c001030300c040c0c080c4c891513100d094640d45503501d601d0602c92032048880f1881c001c2d072030b010540c40032801c00501461 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 358163525 1250 358162275 358162289
    0x1207260304151803080406050702040f1a0d150e0a0515250e12030915071a1008010e01021305040e07090b01030209030f0f150f06040b040f29031501 65
    0x301e000c00440d42c030b80b070f0010782c2d0380007914085020800058076500400200052442100c04000e126403400c1150100d0700e4204110451131810700d9040c0c007604010343e0b82e0301810f0150600020800c8640724000a4485140001a003900a110f131441081020803070b002400c807200c0c82c2e0807040e20742000c26244c0030030541c01c2c0d01400100c8174000540c250203085983c87d0301d030001d48081028410340000540d80ea00c0320324001d0040d10120b900284001800056407549948074040d049843c0c19041e0010080e8809400e441c00d9a034102d6001a043d0800d03c50f10050b854a90009604c1e0003000d8805080040d8941c041c501a034104016984d40c5540850b03001e0541d0305c00c50000400c1c04489004034021701409400581602c540000384a000c0c1e0001340c2c20071125010380c115032030003060340741c3c1c80750030b5070180c0f4504008803400f03000c03071414581034201c0202036001030030000d080ca030203c00050551740800c03050a604200c100c040759401c154680040401041039008203c2c0b2084d0029403204003070305124041c = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 358164775 1250 358163525 358163537
    0x80601050a05090d0c0e010f080a020607020102160e09060a061503110d0905030d0c0201020a05040621240504180f02060f031e060a0608010311120726030415 69
    0x1210042c024801d942184001620030b010200092a144046189a004002103003e00d180002002c03004465030006a81900f005020740d10025030034468150440c403802c138151b000300600807450120008650b001032018510340002410040c100790304183c009480707052041e08000060143e5410810300eaa0781301303642d180004480780c4e41c0d0901000390141400f500c062509102c00c55040c050000301500b038444165108201010780308106074200d12076520b62101240041c00308010040c002e000c7c00d00e8611b40024400580910329020034103d030307030300143d6014070f0740450800c804288070064044041c1c80243c4041041e0750082514100c0f038245914000c2980d0417141d03030141151180d20540d100728a200c0179007512402c000c1e00303404031405075a5030f802038104414002003141c42c01019a000322050f60f154091564259220036541d40b021420031504488146071092603a0010020070006101e0310102c41030064901c6441d00108a05071510001680244810f005d050503840040c0d6050300741382441 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 358166025 1250 358164775 358164787
    0xe0d08072303060112331d06130e0a12030e0c09180703020a0303020706300f0207050d091d0118050415020a03050a050117060403050c0c0a030f050105090d08060105 72
    0x3040509032112410406203202c1c401c14294000b494841e100c0150700c0c0b00380780c1201e501d0310803002e01f0b58260740e140694402ca2001159481c1081e03110808084819031000c40d03030b40c00300381d0320a2401400c04000ca85424070203052003201a4584135084441c14003c01078490f1450b044c00043c00385034007038900100e0200c1d42c009159521010000400115409451103007100c2c0da905010b503d41009109141c0802c25141102e03071005180703035903051041c444121038a10b0340052004031000340362600b2582c0b0001d601300014400320f4810030084c240e2900c00d0381c9503286c1c0390074040b071100a646e4a42c0d9502f07450540c000103210300501d80806501c9070070a0100050700c2d60340e0341400c0c402d011802e40c0da15030b400d01c00204803900c554580c005510034446440c05001c00e0343d035069280c1d0306600050840945400101c00b05000920483c000c1564a2680007114214404d03240014000c0f20680e04c111006500d8074442d008101c001c0c040c1690210b505406040081c450f05030240c5076140080c8504d04205000841c = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 358167275 1250 358166025 358166057
    0x12050607080703200d1404120813020405180c01020d08060904021801090b0307060e01121a0a06080411010905010c0f02060f1606060806010501021e010e0d080723030601 74
    0x240224401c002500c071115400c02d090610164000c5c440182d034241000d00405100c0c0300c0b02d03032444c02660b2103500444000481001100c461802030252401c42c540700000001613640c500426000c0c1d8124019166203420340c48605103440c2c070145003181950840310741c20300c0e5070347c10100c503651104c404c0d6056803040c0e44138030005008101d0744407030581c42c031000400032510400350b5203c40700041c0280d013221541900c0b0b200a0b240309401070300440c00a6034038404241010442e4000c00b1a55001c255140301245071f1600140d60300ca4690811030004d100201040b0a00c41810758886c0758520a00f0325191050601000a2040100e50000b03040b0320b800c0c3e19102d0464881c1c00031281071501154075282c461a07451008082604c1071001661910f04203c40422030000c042500d60403a0b44c1600140b0212041c68000702e0114001d1000f0101c5550b03443c1540c1c01c0d2042400100440315540c3d50b661400c0c603060001070261140704180a00c01d0018148224000c00f07e081129001031003420200b19403040440 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 358168525 1250 358167275 358167281
    0xc08030606091c050c03030f0301060f030b0a0611070b16020607111305040302060703151e0b04080c01080a0606170903160b060a092a171e0112050607080703 69
    0x39429070046255580341c0c0f4800c00000304007414a10070003d540c0d961400004041c3c0e01d0046098429510100b0001000618010311031004a21100d003404940c400c42400001c40ca94101c0d840341011461408204510410900416000d00b000141c0c05092103c14035000344848140c04009000c0c00c0300107281c8082c407268070350700110740d440201030310210425801d11401805084c0e07400c9000d0700c90b0b030002c1007140d0b00900070307030f11002c0c081100030354007503d40303900428841001102103445022896020034611207a40061014041c0c004c01088822650b500040a0b800b00414440c0305034a0403074144a05648001c4442c07580800c10010402070b243e103907030b01e419481468007028800d81d011a2413070410007480c541901c600402c55102e05015a1803591320281c51880c01d0207000c8241c00410296241c1030380c444252a02d6040c03a20754054a02c915540050300c0c005e956041280483c14200103182001d044041e002d070160b11409a8042110f5803002e03611600a40710405000d1108001000148254 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 358169775 1250 358168525 358168537
    0x18013204030c0f0303090803270109030f08031b1303030309110402030406060305010c02070e131416180b060318030903010f0920030a03080c130305010212010807060c08030606 77
    0x14500c52600f42e0340c441c500c60701d80c940e02c001c070f000c00d10542d030000c0c1e01c400100988034200303c5130b840c8004d131540d410583c41400c9004040103051040d038250200100d511903821281c140d214440131952401d08652113400b00100d180001490f1600b040300d5032889070141c1108040341c4d410f06000c10409901c0c50306c900d43d0300056440a400c544040704100522100d40c001c1c9088900680013000a044015003c036201e0b1218007448807405491804070300f100303201d45246600540545030000b20006101d2000c2c0c107142d03980c401541c10b5a814031052100303607030f1030b0040464803008000401c900380d040e60125000b40001801001c03020b100c0311810114503002e000700e526440009008100500c12440280c00900303c140041d102c0c028008400d013880c005094202100b1007005008040305819940d0403985454002d01c01010075900f030042c01122201d01201c4400303140704000150b100d1051440c0c111504005070b0020503607511604c0e041110581020400c141d46801003034095680d507a040100d034151040c4 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 358171025 1250 358169775 358169783
    0x60a030f08131508040b0109020f0702090603030906040321020303041112101b23040302061c060f150207050f0607030507020d03110706110c0409020102010902151801320403 76
    0x58034071a00c80704c0c0c2c00640c040c412882081b4407156a601c07951341c64128064900d071450310003400c00c05140940390403d0119130040008040368900038091000c51901d4010b0752045415480c400e80ba5600000b030710503a451207841c244000e50840c5016100c404900317517034154444c0a5500071100c0f100703c0d142403280400c030b03000d0040240285121040e540c040b1000440d009000600441001c90031004442d02c1117501c80f10034041d403030078a419074003009510b0348030041d00740c400400b05100482808440c019940100390150b50701c0c1030340b854000c1140c2032120b41040c1d2011900700c040d061250781d464580000740c07520180e50060326103510740b40c04d5030184109040650b10450340d0103514101644003118060103480001074038149075a03030400765411a120302105030281c1003000c0120841c105a8440785d4194014400441d41301e45a0300800c802d40c101030340c1c844004000050421808445a070312025201c001c3c40d111311441c00400944e105980810582100a0f507031604038240c0c003c0c148143c4020310b802c = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 358172275 1250 358171025 358171049
    0xe0612010c020319050403020904120c0f030804020f03010506010c08030925140a030c060c021f080a0507090f050909070e010f05011d130b04020f12060306060a030f0813 74
    0x2400d03001c0c2d030b40d0700010700d1203002550301341614501502c62402d07a011a03078054480c252944031503a90fa1100ca44034500c10f420464003003c1a0085080d801050600501940301e9400c181020300500500500c60244240030707a040c40705000e2140da0200c910035005800000603034417600d920146038100501902803c1d10145514a00008034180600c10001ca44000022500c0242d5010502c0300c0d502d0340e48070181100c01c0700300d800c00032a0b0003148000156440200018540b4061860b007800c0202c41c0407002e400036000c2000c00c107400e900c501c1420781000701420225052880d0070f580b1120340059001c0d4074050401900801e018400c20840480603045100702029950384071081d01c084915507210b164005101a4001c400c3c0c01500d6071041c03800600585984048a44074030400e016204101015820603401c0108081c404079080c040c200c05501d2041007081d5081480803d0310b007000151401d403003000f511030304200141260310f8044401c0e030301803207964580b10882850f000030350170f0358814400a0701b = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 358173525 1250 358172275 358172291
    0x110708070f170f0d0c020f03130e07020706080106050f0706020307050319052a04031a0a11121303020f0d03060807080f1f141008010507020a080f0d02040b04030b060310150e061201 79
    0xd0001d8180301940c41822b8041410b5075100b0080f640d40025200e0f410118603080700500c26980300d60001e0030020741c24030a82d440c0034400c5d5150000c9034812100c0390000303180403003030154655400180f9601201200428003282c1420703035000c0032280101040c4035520351520000105421034401713a400442c0c01100d8460210400d01645961b41011514110150f00e807540c0c20082d004403500340c40030502ca01c8582210755494030b41c50203100302c2e00202602580304022032021008030802025240010b0360354040307060f80c90308403414980040754002c4c00d01500203514000c503070380c1c00088803807009010b581034042c9021107458020085c1602d02004820360b4004007004001340010400303034129004840208074642d0340c048201c0e03c444103504001c1c0040d50400c000350070210108094240700c800160010700e03041c0d85440c040c01c990b0040d44101c8102540300100b258901e004d000e03082d4000d95108081c8081440c200079169250083e000d01d904241c4d00c0b10200e001502c402118450b00e810740b1000b00b0160b6 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 358174775 1250 358173525 358173547
    0x60f1c0305091801120320010c091d01050f0d0c0f030317090604030c0308090106170c1f0509090a0e0f1b0d020112110708070f170f0d0c020f03 63
    0x10b070055081c5806010005445000002e440044030b0489040c2c00708282200040d0b542214120100c0000c0d0400303011340011085449005c0c440c0c807003d1000c58452220041c50300c0281d44c4014291891085581e440000401c40e03a2654003031403120903011102440d40f042c0c02e10788161303410056007089040074a01c2e4004410180c00c41025040c8405614903400182d85003191141e442e031003140d0080000b138a0a40c1200003a004d41c084030f03040305d90000046146170321142e11310300c2558448800c825560014016a0250411480d400503c046000c0407403829150000064124072642c221103000d081c5000010300d03188841c0e4000e1128584a10a5541000c43c0e81c0101d55a00c0d880060060170900307002810f07040340b90031b12085806940c181c4550003640006130a05008102a014030314150408000305400501040010400386100d60080b110891050501d016440c05544248403044800c2241c180700e0b191060581301c40c07803c2418041646028080100d08042c20711101c0c5409200104142141c4 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 358176025 1250 358174775 358174777
    0x1401030b04020a0b03011508090705190f172a060301091a0f3f0d030605011d040902010e0418050c04090803040f0f020d0c060e010306030803060f1c0305 67
    0x1d2402190740420080d2100c02c8501c07148000c0c80751003400d0000040b520791207800303040381d50b0340810f108080d0b0754100e4bd24400300741605003007945521200ca0307850060010a803012880300150110802c10065140020714155841c0c1c60070340101820385019104440480000503501d4204001030b0441d0707281c3d42c0d01d800000c0900002ca020490102030b40c1c2814280341881c103468000000c005086c80c440e0020a4614a81420000903001c1061500001c400219401030f00011400031400024002d1108000300207041381c6450700300a0410084032010140d582e882400038041203412100040c07440c1d418401607964980c01100160494100703009042d4144000c80703880c113540e0103030098601e01101c00040200712486488014205401480820003091480b404800050301c501d0003030007114620b800050000820813000c6508621000b800e001d09944500071404410082c201402000c1c00c42d5200f02690000070030b064003900d9140030f581c960782e03507041c0c43d00180c40301007607c540c0c8214a41801000303 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 358177275 1250 358176025 358176031
    0x608041502040e071d0321040302030a0503030f0108070312050f0903060106050c0d020a0b0f19050c03040201170906010303050a18150e0111071802070b09010e0709200a031401030b 79
    0x880da0751008002039180810680182e40e400502900440d1980040407611542c0c401000c031f880d520070b00c00840143c4027040040a21400354005680303d207041e4072001c03d00c1005810a05260308040030410001c1c0000142000d11521400e2035600c3c0c41c290301600ca098058401030951500c01d54000007031080d0030070000d101589003001550251090010140e13078a140103000103007074028081c002042c0b903203011080758121810022600f80c000604c4d50200c01c3d2036080c1c8500f8007a07003000041c00215a04081c00c04405501016490300c0c0e46840d5004a8446105110150a0203c005403114000d44a540301c01c40c2005144a525800c689a00002c128910140c0300c010100711030b503080240e190700980f1a10384400c00080201541400e2150780784c0a130079080c10340701c100e540901001d00064041c0f2442449007a4034000090001200046c00703181081aa0100c00d503e8075000d0080c100e8820b20200a82030000715802c82e56500d50b01104800521162280180c1403034020004001c001a82c4a5030740 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 358178525 1250 358177275 358177277
    0x4032405100314070b04090f0e030a080906060907020a060506011e2c0a0612060902120a140c04050904020319030f02012306091b040b2203020a0608041502040e07 71
    0x50b50440d0141c1360703a007000d03008079920404248000c00925020741c002d102100c4c490308000c02e8015440380c10380d01e581c0059555201261129040182101003009019840001210100c0050034041000f94582c01070b0f0034007a000d40d844000040999005d01c24041c207801c0c011202c880c0c0000d1a110013060180420034000d40c82495591840c4040c4080ca402c1d4036581c0020555210b0502e0603000b5181c40070742e100d201d4091511240005601d8413a4400707845280c4441a03410801d10781552114200c5204040e480b50480100003401544032401040d1400e540007a101811291034500000c2d15201a03400d41d174210b441021b031040105640000e03001c49030317000c580090003080d20043c41601c140d1040f440a440540050300003400e940b41220545030807440303c002d50038001d0704c82045580158480d410502c07859000086101303401c502d600072103804072008000f036180340d8150b46c0007811081c0f9920a0008101841000c1010f01001040d07d01c0286d407100781c211b503160f540380b80c034580d95003003150f401c0 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 358179775 1250 358178525 358178543
    0x2607060c050105250f120515090702060c1608040e0406140c0c0d031d010f0203191407050a02031b15090307030207150504030b010801020909090a0503040324051003 72
    0x60f0a107007141c04c100518550b52410119030207500f9002c460302c1d2408992071080001071134800590350180e1250034000c2409551001c1c1a4801300d06100e2000c4000e0482c404541c486d00030007644091000684005e84004080700140b581d15050440e1603006507040340c5003141c4032600307100400003141e0054161490041840059944003021035017a4010101101c0040d002038248101c2e45100e54800100c000800b9241d1040b020341444003401c541040d80c2d10794a050f0300009008041011203030080003103928203c01d0080e00f9201900c1d01108d000a0540300605c01c01042801080e4000c0c4103949107c0c2d89580c944840d006983d0140f0b54401c1d82c0d024402030700f10700c14042440c0c1440401154202d0307806400800100c0d1821180d1300384100c1050100d4100b010502000c07002611034030001c2d000340708210015895802c05010000070300da020b041c0180300e43c86010010006280030080e50202c0c5c2e0802080c0009210403440380b910003111019071503c091421041005020041741c101058a020304141 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 358181025 1250 358179775 358179781
    0xa0b06030108030f1e0c07030c08030705120d06120809011416030f140f0c07061715040207141c0206100b0c03040f0803071505010b03012607060c050105 67
    0x80101840203000d840c8841d04100180040d64803503c000380300214944a007882141207881104185030030a0340c603a005da0f00b00d03080400912500301e500700007400311007015510b080200e0755031680c1e42c41c102004a050041c046032520300c0c0c045550000c0000e100c20781c03c00804034103a29054650ba44545980350100b05002c031420800f580c4401901d0104220041501c2e005050b520159080c0b645003082c50b08120900d0380c03200c0c880d0b00c1040504500321800c0521038a690005c2c83d2a8181003964002c28100014036121284d03200c010405180c018004465200f20b40080c100410040d124078100503101003900d4030740303030b01040b800224444107a4085081c4141c040b414a8100d03110340c01a0340300e140c41040181c1c148480031500e002801d044415a041b01d10305a5258203d040310710903070303004015580022a036241440b500c0701007106034891b90300342088558141400c8919500040c00388010702c031706903501400050001d82e0442c44500c400c00490b0751050707440800600300c02c501c03001210a03500b41804 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 358182275 1250 358181025 358181029
    0x305030a02160605030105040504050a1707030e0f01080718031703150a0b0301061b060c020a0510020a0206010b0d09022809140411030a0605010b070b0c09090a0c05090411030a0b 78
    0x110b14150344036555420b16603480c09007080041c0c00098416540ca0041c3d100307140c0000c00d01d00515500d150304640d010303180c28030750801404151041300054010810100d07110740c1c03603900078040d9038881c50301d0a01080d030b8801c140013040e034031900f07800060010311005c040b131000c050740f030b00594868030500a0394075201e1100001d100301d401640c0305580c607015040c8014001036010b00d0002046e10060b4590400d6841c164a0300010340b211680c80c100540c21005100080c041c0500059882e21a030702019890f06565440081d0348010510401003200c0c004180e1074044130441d00002d0040350002c240744071511461220491400f203481c3c020b8031416006600050081c6140036983c00f01004010f82c0405030b4503500c580b101c0251820b001981800b9850071400084e090b485214042c0029140301d9843d681c062908182c1c0c3c05000e814140764080521a280c0310341d8499400640c0300940c0300000c6030740300a680040c0d42e1400b448401d664040d05084268102c44848030255118080741181400308000d5601 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 358183525 1250 358182275 358182313
    0x207060b06090d1e150902010807050c0c100c0b25090b09040207020a0506070605040501140124140c160902090109030b090c12100506011803020d050f01060305030a02 73
    0x203551500003100d21001c0022940d4482000701c4a900c130011115110300540d0381c00603581d2a001c80080d415030741d580070400d5581c0500259840642400d0041c03030304580110b51940c90100c110b0543c4500319105640d1040b41c85140a10401035000d560388401d81040400000314890604008906440e01152041c035507200300c21441c203c0c0d40301c00000d458280d50500f03110103544643c1c010398108045000000302c503160003000388186400740c80700103104c3c00d29160850030341d1410460001c0c1e5001c07550050010b4403003803440328010402c43c201400f4584404000307654061440702c1c846058100425880070b450740100304c40042181003440360903280e0700c9a06103012401020703005400209101818000180001318aa401078034a800702c40c0d0003880c4000044144c444000946419000222002c080700340b00d0250b01c0c1c103da824240410244081c0d860481d80320040e02c0083e100f5003042c40c0400a105050008038401030101c03000b4000343e500d07400c02c01d96075841012603100510070f0305150311103002818 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 358184775 1250 358183525 358183537
    0x513241b0f020d172d0702014d03010807060e0d030e100c050a121121090f03062707080d0c020319030908070503030c102406030207060b06 61
    0x40c07100d410302880688440120030004149884194001038102081010414000807425900c009402a4507000100030709598041d00f07071581c02d00889080b03909140e0000340f100b84484083c44899182010321270700d40c0d5400c00050001e40240000000440e40d15804255402920100d80310142c403c0340b04001d01000c4034607507501400280f20224494111300c0c00007501e0032403560030310345032051041d5500d0301420003850010465209c40a00100c4110b150880c080001c10410903000d01900c0c03943d0041d0308555030b064003005601c0d9500144020140c2d542030001800242d002d01140e04614040e090907120003440302c8141080d074584811103100010016607002500d10300406040180c2c80b1845c02d80301102c1801c412a803600030130038003100c0030100d00c0222408038003940e0742d602250328024040d41040032a8001c179000b5001044401c085800c0002c01d01c17071402201e400000c001546848030443c41c51a44042e0320016800100009ca0540c580c01510a0b140600303410011a503050f42000f84900c01c90b = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 358186025 1250 358184775 358184777
    0x9050f0d181412100506010e12070e06210303010801050603070602121309020a08061c030206060607060b0a060e090a06050306040b1503011d100513241b0f020d 70
    0x40d441400741d01440b081c400304440020b080c4504858184160710b081542c0070950383e20603541c4000b00a069039000800c030800e41c200f40c545440c1d22900082c0e968035184030b030003034902c0a401c240200c0d800741c031403015082d9001812800b41040c04205000c2d0350703c1e43d00a00c5803040640c20100416040d26001c1240400c451150300105581c2800140a22440e00b10304100103110104560000350700c07040380024140c07641c4541d255255450500308101904629504104075581481c146000003900080c466070407040850701ca0341c0b540200d242c031801500003010141d40000ca50100001c40d1034200385942c0450f48101c800d40c0c1950f4030020302c0c0d82101c801c0d214503a4190700440210740030408140320a83c21004404000385c0700c0d05a50080f0382500c000d112400000194030b19540c980341300a003d12059062070f80310501960614a10b41d60002c40041e03000b40c0b60300d0310058504030302c0c8020740c00004a0841d2100c144800c03c541500f1014030b0400e80c040c8804590084c100d0a003c51002c600c00c1070203200b07 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 358187275 1250 358186025 358186067
    0x902030f01060c0602070b1e1b0a080901060510080a06150e2205010b0702040614030a15020c0d03052d0a091a0901060f080610090b1309050f0d 63
    0xb07810021140000311800a95000d0303820404807020030b84005026101c1c2d008d07440b04069400309070102c4904010000c000b0001c0c0e407001c1e004c04005000c071100b2560044410b240ca09181d8444507091401072905601ca81d6204000d4009182707401d030407424142c803070180340200b08034160382d07480e9038100300d500040043c00068070384209203440d107080e50004c410701030f05017480321760000c0441041088407003c0e04103110140004c5030201c210303e09805028080c200410440c03c4212000000c00e91310010740c8001400254500c000040221087d0305423003074003402000300c0f09442034201e00a4020181500e0030420a401000189555100d840e51907041c1c0d640d148001c0041d968544641c1c00404030301d001103600d20081e04580500c480245001c50281c0040f00001454600e0005003035100d010540c0621000e8002034200004455a14510000c550f00b02c000030807044c3c29040060b1401102c40d4011103c50310341a980810b003d00042c8070021504042e045031610064404242c0344134180ca8991451015 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 358188525 1250 358187275 358187279
    0x6010e0916030305120a0e060a1b02070515070f050d050a0905030a020a0501030f06051810081b010c1707050106060e04020f07060903050702120102030f0601110d03051012050a0204060902030f01 85
    0x144480c03194009141b6800040360407502a40d01e0800030700303580c810030f1141c545282e913281054005818002584034001007030580d181c90041108040c107003401c83c4008801245207030a0013205200072446513030140507140045019103014155401003014240010078030300c0041101e080014405a48a0b0024200d68079a032801004401404d000440c030080300d070f01d60000055540754003888028024400b480c9001034500310401072010f018641c032904690b80010703c020042d460450705c0001100003860484132a1400c1d04004040c5456105041e01480340092610700b4410198020010f0701d00c140c1e554012041c00a082009034018041c0c140c102c1103007004010001803e55000c039412a1007801c2c45810f242c0c860b0001000c1d440c040c526064565000820045814000d1203900d606c1030302402e01840512600184903076030200d40800c042450396500109082d00020301c2d60400500070113404055181440c6070294a4640e4504100e004600b000d5000c5103000300c41c02501d11410f460300345441c0a80c = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 358189775 1250 358188525 358188547
    0x30103080904050a06170604060b0301020f040308070f170307030c0504050a09020702040908160b0106020d140306030f161706040f121b08030f06040e03160c050306010e0916030305 79
    0x20101910344c03409555280e40c005651002c01801c0c40d40c0b44d1802c40940107a10749406d202003900d4581c00040d04c66441041a1f00c0008003020a45090740d4210807410780b100107514150703105006007080039155401d8041d2514600b91124011803042c5a01d035410300c0360144141c400e4139140681d00802d580b02070040018000c0d100345038040e0020600047c004a0700c0c142d15100c0c030405500c100034402c5460781044102c01480003040e04a4010300f0340c3e2009041c1e030700a046c1c000341300c441c009042d0032104400001042c443e9504000114207011500180c4481c031401c1001c080c80702c0c60b184148850600200100c0b40307a41c2c2c1c0419424400c1d600138503500816075840e9a1586440044002e0005002460284000c3d6001c0560b0180d51644102901662801c0605003404c6481c8000c0c84548a507051030840010f100020042c1c1e100d1072405000c018621744a4509040d50754455040144c0501c40e220002030300300e0020080a006000c3c24055030440c0880c600d558005440c14040900425010440c18010f1 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 358191025 1250 358189775 358189781
    0x21917010b01083705061504030c051c050601092c12030c0c0a030207060311070c030602090d170a090503030a17072d02160e3103170606030103080904 66
    0x8080d4245041031a00c040603c00b1300c641c4a4600541c00055451041152908110801c2d02c501c0141c01c07449802d00d40343d80d62303980400086005e480e0182000c07039500c2c48540c4c0c00700491004254003200340c405640e101d941c82d4009291310b40c1c0d17004a101c034400d030342c01c0340c00c5007245500007420150b4064805840c581240c082d80c1ea2002e0315600560b03a00308070384400c42034184881080c05200c0e034040d00c0454540031005064444620b01220003100c10081200050004074900013183c0d84070303c026803240442d80c00100d49000841c8060501e4105c22500e41d5201d00e45d100070f02c1e848941e43c40358400d130390303c0e20705065580c081d4080342808035441a200c2115440c4130200580d0112041c40c0081910444164503c09812101c81750354114814001207030381c00e50107001841c1c00410a582010220f80f42c1404500042000b404140c1004240000c880c03910504c102c0c500008103440400d04100c83c01841c0041000350b41c20002504040c1003408125945454400c50b412603410012250405c5c81c5c030002c00c001 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 358192275 1250 358191025 358191061
    0x4030206041208161505010902090904110f0607030810140d0602281206050102030a050d0e0a0204020705150f1501110c0a0b0a031505030604030c030c021917010b0108 73
    0x1003001e100c041c14400d0100143c9500c035200e288820882101081703241c00b59903043c1c210442042c014485100540c4070444c1c4a03031b1140d00550000b01002140001c151404290700e10346030404000180d0405142c0c00c0400d1a0207040031110780d416072941c2d0702d41d4000880314114941d41c040203081d40d0fa00400e10700d8024022000c80d00c0c1740305c0c120500d0700c0710300364000c0402c080703117004280c1040784101c90110074030030381c0300820b820b00280d0301c0c0444418000f00248150aa40d1400c81d81e5151505054036080060040ca280d0150085543c6c800c1070900d240c0d90740b40142c59500c40c000000010760860250704e010b900a21048019010400c0c00d0f1006403140d162400e80300c9000c4c4212034603040d29071381d15902e01d401003026412060356140b50381c00007401d42c0c98158048450314003000c4104199140022280d52203031f003510384110008103916049510403a5a040a5406840b0f10504d840100d44220520202e8400b1507800709002c68003641c03035007640d0b41d4902e09404508008000782c801200040d815003 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 358193525 1250 358192275 358192283
    0xa030201082802040e0601020115030b0604090c12030507050601151e051c020405030c030a150222080102270a0311040f0608072d12080405030a1a0c040302060412 71
    0x204000100e5010120b1304980d12095115101600740075095030203203e00761041c44810f0440d0081c608640b10a040800e01034916401165980d0004051018030080a4041d05485518580c00210707406c000309160440c0f402074070940140310000440c00100510b50380c110025490b99444032043c5000544c040554400001c1400410030005031140030303840300045080046030300103840e141080d00341803411907100003040c040d40c04004210080380d1413403461615000009030140e42c0300300d0070661002680612110042c0c58580c40c10104680e1f406401900401c449100125031401c071011081c60ba982024280d540c0106401205002160101c2170300505c000c0c1c05040462203041000710182160b00702c1c0e00802c482d0708030741014020315a01c00c014582101d90241429210b401c82d803140d0342c503580d81d0b00c0391000b0725510004000c00c010000f02a1001040002c00f1384d5000d049034204440c854510440100300300f071040d40064401e0917100280c0e42546d4020b040e6901300350800d903082c40a010816002c0d5 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 358194775 1250 358193525 358193581
    0x801080d0c0c0915080f0309030327060703020706020606041b0810050d061a0306090712020d0b0a0e0d02010c1d1c12020105060d1709120105100501020c0a03020108 72
    0x8680d0260300e004d001c01c41d20003500d05401c0780385803000d541c0c1007080364043c040486c0c000300042100d680d000002c1c0c1d0440c0c0040d540d8213070480119202d1070840c9041d143c1c215000540803c51505141c1c01160410880380c068003590010359901e800c00003101d221002a90792400d014068004841c07140d10381c0356110700d0702050002025210800103100d01c540d50b8017107441c10380320501a01654162100c511400c0c200783c1c0108880e040c055000c0d503d4520600554804101c1a02040155541c0e914032a0b4502c3d0807a420780303682e0800401c20303070207040c4100310000c41d4410000e1900407241305102d60406007206a40d03586400d15540100c104075403002800d5503000040700322a072444181020144d80c51480b44014120b030355101c1d000a07003501e00041141e445800c05a00f0400406c030012601c001022140307200b41d54920f48000001d40320760002c103203000c07150300e48400c11146aa0f1011548107841090302290f0507000346008100140e40103020080c00103c0d100e011070480c040318103280c9000d00403080c0070 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 358196025 1250 358194775 358194779
    0x6180601290c280203070504060326091509040c0903020102062202030d0203120109090c030b040305210105010e040e0c0405131e02040f1808210c070309060801080d0c0c 74
    0x2080045504403500c0c1080f49140106400310303e01000118002c05090358140700b00391441d15901c001c14840f611040c0f256000400c84040000e00100f1102403040003825101c81d0488000000051f8100004050007146414000c0c100707035000714200c10840354168020003890740e0354800d000c00162440034030b0901501440d501c40040e83c05200c0e0b14500b02c0c050307000710b4451500d0780b500329503c0e02c180e00c148040b030b1403d46200c0220702d02d01c1c401c1041c0d0b608040300141d2a2150300d000c94251150f029054011495801402c0c03a0380c802b020494100c1d502643d40031700604032001080201c0308960403040b9590312a0401c1e00450605412859001c01c000c0c154a0441400d030301e401e60148000003081c090b20f64001c40071002c500d02403041c0d01d03820001520400c0610b08086114003d440d15080144c882c002c04518603803005418114460003468003100d1f0381050805111030115500300203022030119a0070706001c44c0c001c1c0305a81460498007414014094540b200c141035640c02c08214040c1d40142c0c40c0140 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 358197275 1250 358196025 358196053
    0xb030601031a10030c06050304020612040b070e060a270b0c0309090c07030f14090a1d0705030f0c09040f18020114040b0904051806180601290c 63
    0x24140c0210b024019902411050a040d94a448001003540c0c4010342c1c600350500200b07440d022200d0035640c5500344255203440c0e5000060072400307540301c50802c804054003004200480031700c103140200000d49501240041002c200078071030203071000a0b0002201c056001c40300c0100003803104408120382d4840009a40c039000207002c203a104502c0759900d81d10003c0d0508560404441055002242c0700549042102c9950000e1260452095403800c01c00070703c0e46070044607076140403100a91801058268019a00e00ca100e00060304003a801c0d82c00c088800000c2d80c01401602100d2040000d00094401c9a440c40b45041250700700e0038400c0d40140e5141c1007122000c006104481d0740c00a2403a008980500501c001440c6881c03a009800c42800180300c00c015407041c0c0303001d442d0061400c440c04509a0b03901c40009100b00c1d109440301c5958800c2e003040c06070180c00300d104e5000322284001075500c540c0c2c0398003101e40107181e544249841d82c21001c1300c212800c1180d5014003400c4030000700360350312142e066030 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 358198525 1250 358197275 358197283
    0x15110705061f05061b0c040f060e0f040209070c110402070605091e060c070201020a050d2f07060e0d202107030206070503040803120a0608010516120b03 67
    0x210888803a8090400d201e01040074420441c0d000c600700442c488440c3c10480400e00c14015408a0800c0b218035641d68144d8101c14412503602510240082000c4684215150b003e054988101c0d0000c14000d408902c4140440d0302c4540301e10340181c4241c0040c1c5a8071011a4080880350041c1ca18103000c10b101e20155482d0b000070150180100d00200305410480100d5007001e14418001e018076180402c18455640e0119617541d00a14a503866030321590240010b030f041c040c520000038240d0140082310881c0a40240c01c1c50b0f2a0780200720340002802c84101c1a031901c280c26880c0c00e69036031101200304030301482026079480c0761401405207201103000c4e54401d010070511140203400c14880058900d00b5042a81081004104c0d00701d1010400342c00d1040e241d29070701301c0d000c00381c082d24001403c0d00070700000708120b07401080140c0489030b5504001150380c1c400d00c0145c400790710f481c1c1040800a000703101401902d02810080e11103145009120006aa05072003025143c10300c0d6803238903000c54070360b58144 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 358199775 1250 358198525 358198537
    0x1061220250807020a080109020108010e0c07060204030b10060504060507020d170a080a1a09040b0615030906040201020d0c02011205040204060b070303020702030f060106020712060209060f0909010e060105071511 93
    0xb802aa0712403010f8410420150420b42204046071b140210000250fa800a45181101c054400080407501d81902c4d80c0250706c2080d001074002070000900004001460101d02e100f071400641843c031081e01c2d26012240c9100354859680021018050b010151a00d08072000140d44104188845880031941022098002c1040080421000400c1005a603141d00a440380c000340400300034805244100000d522060192025000400060008100d5214403080d01848850003520036103e280201841d9520310003210101d00501820f00740e1506c0900964211030314990503101e074842c3e24040c036443e60003841d0040003641d0190329248005038140b6120000d00c85140683e901581d074105138014149443d0448000d1038180e401000100411580402c41d1800d0705c0250081d000706207824200340b00179004203440c46034004000078900103081581c0000700000603082e80e080314070344e91758030042881101c102d4555010410402151000641c0c609160b04e00800c049400900e0065440800000e41c002c0 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 358201025 1250 358199775 358199783
    0x12020309100f0504020a090b13020c10060807031403070c050402070218070903062702130e120301050118060e01030b180c03250e0f18040b0106122025 66
    0xc1c109004c290305119441001a2201500600c0301100c1d610100d012144444a00e0030900d0340490020080f803000c0c0700481040d030b0f5a10741400b48070340300c07029252658624442150314080341d9029042a001c0401036418003600240111041441c1c14207000103944403038001c9030b0006501c624a80040300c0b021290b40214000d503a500122425454208100c80070307081350140500d2224900c0354980110303481015100c2d8103441c1908200d8030030040d40c01500801100f240e0740d01600d02c081d540c18580d680035604072042640d031650f904002c0224446441308074080e004c00600b40c6076070000d0650003900000050140500003401d400400d4800c10151103064400a60300200002800019882610311a1554240c13070b0f44010340e0a15100b015002d4642083c28900030f01d81c0218000c2c0703a035510042d499281c00440c0342e294081c9400c2c505400700101c05d000e0280440c3c0c0e994503c00241c0c0b5107200d8041401c41c01d2a068a54074401c0901c2041500303c402c100045400440c1240c00c0e140c80c0e1004004c58502c9 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 358202275 1250 358201025 358201031
    0x150c010e0d030b010504030803040f03050d02030411011706150c0a050102120a0b0a060504030318080a0f0309060e090a05180a0302010e01050a050f040b090c06070b2512020309100f 79
    0x10028001c1c25560f000055a0401405000a0010450344c00c01c60350895032000040c1c2c114525451f0507102e50003440b65042d051803000c001c00083c4040c824698031112003d07660610000c0e50201408c00820040e20b80c02e070440e0948069100d580c0340e240080c007541c0307403c4040710345841899807100d09a900400389596030011010034070403d5059401030f802c0701c0d8011128002d181c0e043c4000201306000c0c900c4043e04211020b910007070809101c03a80311028040407015500e01d64017070304051641d1103021108400041790082d0000d40c8a1180c0108000b070200106107800a46455814401400001d0102000e1044041c80c0c03031003240c001c0008081913440b0340c00115000c10486881c1d0708499006000810540c200810007855103642c158007a4070a030f10009503080364030303549646440c00c841e41c0c0a190300802c0000d0340c2014000c0303c00f141441070310090b500d800b015441c0b03520344c0103854040c1c04407800704001c560001c84500c00e64000e142e101c07241c101100c0c00c5840801114040e41c070070400185045503 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 358203525 1250 358202275 358202293
    0x4020d06080a0c08030f030714161101120515040203060f1c0b0109050c0d020a03090209072a210e0a0b120f07120f0f0e010b2706150c010e 61
    0x303c050b006009055000c0030354100204202d503000d840c803000f41140c04100910f0341844151101c542902e00030020000140c00115180c40d04045c000d071401c2d4991302252000c1c0b101e880130019801680d12074000c1c88441c40c03080300080140300c082d40002c0d00c081c1d8031030910b103107540454a031a11009940039200c0510544e41d039607030130107a0071390300180c002120903800c00c0c081280d12020401101d00c0c0740035050005a94500c03d407011030041207052802903018034164240503400d9807003036600940d240010010385942901050381089100010002007400c0008001a001d8003004660a583d0500d141424207030f240f1104001115a000c03500100035010010400c10110003400e0a00742d44140c1e00c201050382802c0558010f17100c541d02141510b85203131540401c070140c00e8560000c1e280364030078401c1030021807444178074039000c0d00c019282d0900561024000c1890780281e01496000700113100c1041101d515a201404101d1440005d5a0401c0741c0402400980c0c96092151106000980307010b407641d80 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 358204775 1250 358203525 358203533
    0xa091109100e090a0b0a050d020117180f03071a091002040308070b070c02010816030e0708100b190b0d110d060302030706020a08030a0506030c1c021003060e1504020d06080a 76
    0xc032001d0304e82e80f1102c1c6090b0a20081c0d8544076210826100308991480f464840b0340b0049446410040c105c0640703c08410900c1400c5c4260181c1c0c0c1c00c1d0307054442c03d0b111000040c0350601d42d41d005880011b0128860488007081c2202e20001d030302d4100e2030b403a007910301041c0120900d806aa2295004803440c101c006101010f101c0600c007429008040c40c5800d019500e900e0700028003021020302050100b2451246188009020f80d0241890941d44029641260790fa804c440303454420b50036451b50382c01e09101c40320040d45814850912000b0040c950701801070709041544840c0d03048035140c3d400300b40d81d510640c850f6a00100c050104518040700120311141503206050070301d40d0986c00380003558000c821940c002040c4205499100c00b00d0b001c00203141e030b01c0038006868041c9a00383c0c40e1b0015448a80da80b40013901040203d980c5001341c6585c1c03900c0018000c201d003261010300c1088010f07002c840c0445d0440180c0100600441e40c02480981000c1c4540e02880848640d54003020b11130744001c40f464100 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 358206025 1250 358204775 358204789
    0x705060703200a030c020106120803010e0c040509130309120f022d04200408060f06100906030506030a080f040302031e030307110f0a060209040f0b0a091109100e 71
    0xb9042e4414440340840d03403503400b005070307006450b0b03840d0526071180b1140038864403d504c44d0004040c2680249000119401d199001d6031080c081d401d0800e12820026900012500840c2c2c11035070090721420b501d03a11141010340300c581c49201182042005480012036000c0404103004040c0140c200a440c031080740f04100e0140b01c07590b030303660a4001d00c2d0084002034000c81f46100c01c090b01036030042003102e80c18800402c40042c000b15010781200204020542c01d00002c0c0c0e081c804c60b1101e401d02080c0c0c0b42d440802504006400440740060405001072015074400d0b040f185c1c100070040d00700d0b0891001a03894005541000224000340ca00204003081507190821800c0080e14041031a0036808064066640d00c0e4400102580140000b01040001440c02003140b04404a41e8a00750781c400034803494490065031094904920440c18840e401d400c010b902d1080000542000701008100b500d031011104c0901500c20151003900010300000805440700101e800b031a400d19a11403d12600581c01c100c44 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 358207275 1250 358206025 358206041
    0x822170d0e0111041806170c0a080705030a0227070e01020c0405131e05060c0301030b16022a060c01050f070c0b01060e040b04020c0d080105220f0207080705060703 72
    0x650703050114100f11900041c0443d0252000003041c8151103400101c030300040d1206512406221742d0140755507443c0308011800107803441084846401c0b060303032100740698072080d07801040d50680000042d6001881c0c035880c000703c121540b21030054003c82000800b400200d040700e810001c564111101e441540e814030400306148422501005142003c5020358002d03062840006c09a02030704500207001c03a07510000482090380310040714450b107041c0441c040039030428070084507964540000b040350600c04420000700d06c0074640c0103191080581c0d030480d000c09480110044a60030400442c5400d1b25a50010300741e144c440000840c140c2031100c9000da100c00003c1020040281d4007180700d00069900c03403402d044540301d00d000540c98a0440014000b84540621a40d10034400501c00e90301000c00304000404082c00c1d110506076030780c0d031070900038550b0328402c5200c3c5150f403c91400c0205c014540c403049940c0e4604000504007942556644038542c4400b41c00d68007070380560104a0a59810702031541 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 358208525 1250 358207275 358207301
    0x30605031c09470304060f06151b0c051323041e1a0901051014010e0120030403141b0603040b0622021b07060822170d 52
    0x2a0342061850403920a5101502c2d1802c88003004890080500f1100e9403c0c3e510088a44999681404e180c98802001e40b5004655a142428000220042c4c2012000038501e03550701d903040781c80c0b42c0d40e104031081401c280084501d5007212001181d56146c0d003001c11008202d0100c0026503020990b45046240005101c5400103070000b41044005441c6803082134520200d0f6681c0c6444040600e416a20303400c180b410341a0b80c0d07090f80204144c800054203ca4007415211160403503190b00c400003400131000c000c900c240840c0c0710101042855120703070b681500510307030039043c804104202c039040741c00c6600c181d20a80c0c3d2150286025150804140520051309801003c03e884051034680811103d003c000c0000c3c5c51b0304030080000b409922054140c0f88900740c0d84500100048600c21110001d400c5009008510b0100b428005c02d240d80020342c1606440b8184c41d440c1d4107965549000551408440b05100c95140402100c000142d00c081e0500c406040b240c0d0580e100c080c100300c40021a414404404 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 358209775 1250 358208525 358208549
    0x9080d1a10020c240a120c03060b04270911090f060904060507020123100b040b0f0a051207031a0306040b0117030903100204061106040b0f07030605031c09 68
    0xc1c082a0002080c0400e054296184000c0d45555403e078400c40c1c4900000000410000564200a680c4403080302200d842c035a10401421003643ca085086501d180503000e21540300700401e0120001e514801154042c00c61000d142c0e00e444a8a00c1c401e440c68014110f070319003134000d5150280d20703045201d1036220b420702417200442c0c540200052550074000e40003409a9580c0c10100d120140300303410003045001c81003078400b603858003901e66501c0758404407101020040c1052021134030038503079401c407800c13034003140031550a0001c0a44a00500c0d4800c00d11030702130210421800c0000051900541d1180c04181ca001944400140301003a2040c00038400724800e400900030000016078004005064800c1c4403440050011101d0100340703544101403241e035040c031403204900d0444001360001c20030343c0c1040c0e40d045e5001c803045100b10703a141170965008000390100d20000e450f49900c410402d03845000344c90080345e81550303000842d0918148440c07080700509030307000c0c07500c505400c004008010304009040e6 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 358211025 1250 358209775 358209799
    0x10b010c0f061a0d03110607020307032015090c0a0b0703170c0f13140301060e01180b0a091b0e0102072112050a030c05090d02010804020409080d1a 65
    0x5041c1c0152901d00200501c0d0754901525a641c00c1202075038a100002d0325201c5130300e50320b0402a1042460020b03481041c070901300040c411034408425200c07500da043d1a95503030400445a801042040075400e9440c0d486180d00c903207200c8050868044c050380307401d03010f070200302181014803201c816a0342040c1c6440c90304001c8480001c0e0f0181e5200441c0524141c10036484d10b41c00c1000c0c0d010312a001d004121100d02083c128261841e8280520480b82074400c52a8200c2c400702c185420f84002e8480c1900c980b00c0003004100c00481d030090305042c00038440c0c0000342070240000150507001250451f03110aa0780d43d1069991682d602127148169502d81051000840f12000003552400c0c00d0061131080079034210386a050340f50b80c654422000707511240b003000010300f00c0402807441d0060041000001c0c141844079442500560840c1c2c0c040c40c01618001164420350010341707040c500940201d0b041595202c172100030907c254080c2200407001d140124268907080031042e03d02009407007551141c4038040b08 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 358212275 1250 358211025 358211033
    0xc040905011113090501120c0902071110020d0e101e0201060815070219150b0609030604032307150509030903100c110c240705060f1801020315060f09031608010b010c 73
    0x12304044841213040582c0d16445031030200881c20703091004070341202e202a4009082070b004140f0309155940c40e503c0c840030903030190401200c120080c0300c0d5004101e401c40c90f07800982c5610746100386000e06000116043d03039200c0306c00f440c20f240c11400e040349a55100c144400075a0500011b21203483c08042c44500c4641600c40341511a2001030151a45544981c0f0380c01c5901c0c2e2005448042000800369019441e10b424003a110070b50101001d01d80312125079641040103200010f88112603003218031010450250b00780b0350000c00c2c0c05000c0001c00e2105211031041a50200070301240c09011180c00b107040c608400c00600007030090804455036801a1890103029100e00903d2581c00402851100c0d0400e6586041c80c154442c0c4140034181d402045c04014490107402207007406400070f0580740080b0307031028510500300e000c181c8139916a05a20000290545000703409080c00c80d040074410b42c603194500c40008e143c0802c0c805001880300d0341140c208142c480a22440c0781803102801c001d0981481551 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 358213525 1250 358212275 358212293
    0xc0c02030723210f15010e0c120709091a0913080910020a022d0d03090816030c05030d0504060320030f16020c01020c04090501111309050112 62
    0x200d8000c04100000c904512032402d1240210a1020740510002e040003000d00941203091160901c20740705818030401114030000e05580c03000300324802c54040742d003801c0803900340b8075001e80f9010146c0010b116451503240712956050044d4083c2c1c48030404d00b440c108045040e07810300000c2180482c0b29918079903160311000c9440d80e0010200d881c1200c00505c0b071411121031301544030156000701599801d030548a4001425407609030084645a29202c0c124004000140001d43c1c880c407003581700c5542c1625410320540030031800381310342019410280c65403081846c02c0100603d00441035034221041061010308000c10018000a03006400340060038180038109100c1c51141380c040594a1141602034900403c080d030680d10710646042c0d0743c2c10100103400204900352612141e259216411070619400043c00c5851480706801070920351600c80b040000802d0307110000d4506540700c02003e0b6040302d00c013000f0440d10744920454039040d402d215048046a00507080910702060030240240031421082d = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 358214775 1250 358213525 358213529
    0x9010f0e060301023f130b25021f1b120209060706020703180e01090c05131509090b03120d0e01050a0f0f2915120a0c0c020307 56
    0xc1080c01141c65030000302c0d00900c1481c880e0381060780f070035040c04c002843c0c042204209651014034440703414014400c800d4281410b0720b80b038005040c403014441c0000e003032050307240c0e12500446615502c4040c1c403a200900e074001c520914016000350000503840066039450f00c41c41c0e82c40300d604001081e0350b0445841300380d07502c0721520b05010803102118984142501160514440034001a8540046140c10b40203500203820480110b03621481000881222194030421600b040c88003032002e901c2c100a84d030060858900c0002088000c01100c40c600600401d56030040c1500b80b038040c122a02500d004106c0280c0d9044540d010303050482c102e009a6000959142502108080030740d120b0300c1e050080010302d083c9411510950070041001031100c0340382d000741218401910248900b6010120b1401191080212208035241c0801c802c0e288407a815038200c1d50050291140c41c0321152004007200030f0b040148940043d481324001c112240ca098010703140640d88a04009240d104140e00007034403a100c1e4 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 358216025 1250 358214775 358214789
    0x10203073005090a06020a081006020f33010f0311030f060106141b01090309051503010b03040c031e1209030503070303090c09020a09050f0a06120209030a14030d05010509010f 77
    0x82c0c004644aa00e007481900c42d02c50f88020115500d10268070054604072048480c0da01c6034035800300c0090514000300b1a039010b00d070030308080c0c4041004500b04001d01c0c0c03c520010b000c00a002c2c0160140180e107821420b01030030220045c0120359140d840c0450000328000d403114040c5d002110b14409400b80080c080b41551514107012442d13860303920710f412050181d01d13500c020000440d01c002c02282819440a004c4a0017940c0304641d45032100c5c2400340c001c00301000c10050350400c100404c1004000e50203190010b120b15203408100faa40c2e1103101d40180c02c01d1420140c1000b00000714104000d2030a6080000030609084105500c0d40c0c0b90503032203004420000c1d05054940140d0f1040054540b000b03400741c100080e0440d12040340c080b00401c00d810074010301d07000303110103c82c0c46107e180220f491421140d090b46e82c0303280508201e030300c500a5002010401c1d0144100340e11030001980c0394210914901250b4011511014511540000e80c1c1060b03000c0707030098480c4401402180c0b41c008000041e5121 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 358217275 1250 358216025 358216031
    0x6010e09070e01260702060703050121050c1215090105130809042a02070b090306011203050903030307050c190b0601030c020f0a050102070b10140d020301090b090102030730 76
    0x15140141c0300c0d0040c030072031400031009049507400004c0881c00d00c07074043c400343d508440c0c084d559018140d04841080c01021a504e91a440004099011403000040350380b0410544a4004e01e9a01143c0707000f081c139541c180d8541000d8442c0703440b40d95151701168050031110091000c3d06150b4002c2100a079141406414900002034811843c0c440783c04c690f02d50f1010103031100d40c40d0a0780d140d1200c4000405040307001801240c0d40007640e008088259412008004c0c050030b056480c2c00490407100030760b04c2c0d080307060001c1880054020741d800d1000d1441928a41c646654854103140880c3c10103c1e00b04411350141d000706191408104903051303036036000340c00b070a0000750344071104426803070003040b1000400140b26030314071403040001c107401800007244100e80e405481d807510a080480c141a50003014000d5420090803059440c11441d13900c1890300250001907440b9070b0f070f2500070700c0310b45c200c41190749130b900003042c01032107607121801c03031500300c1038190030017103000b41000760081d000c40c41c846044c1c1c00e91 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 358218525 1250 358217275 358217297
    0x5061b09100806040e06010806010501030f230601020f0706021006050306070c0212031215180906192403020112060605040b090a080a0317070e01050d0e100603050708010506010e0907 80
    0x140c65120307503420700c017090482d501c0f5070f560903d071030361107800340200741c000b038140320f9400d5107140c241c0550f2881030700d0300c0410070f0130596445d10354200020091885045200781c1d0300300d8040d03040500c151406014182d002c4d107980080b072260b0805841150388041c0c040da100383d040046a40c0d21000008086a040322403066000f03140004234a94020a140b80080d54000018006001c03403592269500780822b6429640d28081c00c5040b40e88003901300d4022502c2d030841c6002403d03401148140c210a4481400001044040a0a0031071a008c419031500b52490503146d0078001e640e00203411404c0c4090221052003140c0c1095001031060080e40705440f1759020201c0c00c0b803255901c03521004003402a42c0300315141d00c0843c0c1401825011030301c101010001000011a807070781e200d06000c03c030071041070316aa0f140119018203e001000c1e00346001c0e1483c01510303c08040004180a0b0f400154010130050421350300b070546286c00c440c0054205410f00c00580c142071800d4541041e0303640d0006441c103001620304 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 358219775 1250 358218525 358218529
    0x300c06020c010e031e03011d0606121e150a03020d140307081207031b05090409120f02010b0306040f03050f0f0d020403061832060405061b09100806 65
    0x2014003111501079500700100311503001c43c000003800d107443c400c3c00301d0703585c200c1e0050f0071086030301c000c0c024244510b80c1d42c80c81c0f902100343d00007101c0e00903a02400076880c000c049011700c902c1070b40c2602d0840c9811a903131001c3c00d08102d042c61141d0084100d00d01d2010243c1200001240c50070540700017400340007842000804d001e80400b5071902d1140107401c0c1d0b5a0382c80a864000265030201280c00c08585201010484c80c42c401c1c80317540d041c040204842010014a00c2080d105a0007003191541d00c1500c1d40c0d11080000d01c03d5150786a07504254981c0d030920014484081e081d103080002860290744410200310120b08407100700341085d500f605006070340d40c80c00d0088043c00d02c11003010002d0391000061206c5448505e5004004403406a0390404c081141a5010070b004034078000c004c0c2c46405050544800101c0c20454000440c648401c0f1424925500d1515410540101c40c2034400360011010040d07417043c0300d10042508070319941c9061800404a00140058444201c80003c100300b070400a1426 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 358221025 1250 358219775 358219777
    0x5070f0c03180f0503150709030204020c030903100b0406091401060c03171f08010c0e09060a030204090b071115010b0f07050a111005041409040305160609300c0602 72
    0x180d03030588003800c840d00c41c20807014004030f9120303450092041a400681011b89960154010342061b951241000c5c0b0395001c001c0607410842005540340000c0103424007987c4c0800800c1c0d101d845841001ca04003803440704000440c0d41079444540e5490810328146840b9200d00e404074156481418190f001c1451410210b0391400c5010441311010000300a2288900c46043c0142c1c0c2001031003c191101521008058203a403440079042012030f04003111a4114605003000e160300c907402501c10b06030655031390005001e49018400503641041840f081c000810b40c07006e01c1e030556100d101300410310304800104070841c1000502c241211100041000c10070281034004542130b0b160803900b1903403085458146003c0038100300454a02c5a06a480210f201078011400d0703508884005054010046e10710042c05040f0000500032000c10000304010030444101c2c80c0300c66075403405158005544152131404240d415044481040180d0032000300b251030240740014516606254580605030340d02c1d40c0742032350107 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 358222275 1250 358221025 358221047
    0x40905010b0a03080403060c1106070f12020a050306120319050c01061701020d270602160b040812071728110c010501140a050108070512180c0405070f0c03 68
    0xb201001c51400414031101401600589018030310030401801910710513106101511103076240d0b07801020000b603880e80200020104007200741400c0342d00302040d00071041280e1180070000080b1303802006200d000e080c81e243e00c00040d140c034030080d071070150a0449020441501c5030080c00700301c1e002039005050b2000b90840c00c0100300810840c0542181038080c103010b90030000000e141c26141c43c07002d1a00c0420940595006618460000b40d00615600c0d00806948841c910710340b01060803c020000404280381c0c5031049010703061998580300803003101881c8481c003400102c1041003048810b01040112282e841d013180070040c1c3e815604648800000030309504c00320b031110140c540b581e40511040d40d24010400c00030030034005c00690b070303d0741034210601645221054000a181e042030105500405010f07401015030700380a42810090390a00c0b40f03040044a0603045c25207407005402d108001000030b60303180072048509005a10f480caa00518010421590070200f00c1c07030001c004140b5010707001c02d0030 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 358223525 1250 358222275 358222279
    0x12230c0909041a0f0421110618120424030b040c02070609050a030f06020319020403080a0801171b1203030f0f0f10060e040b030109060506010e030309010e040905010b 73
    0x201e00e00d868100800c05401e0710034002e805110440015940d81d6081e070307405108a610207085c00c0550082903072551804a400c1c0c00c0406c1c405100c488a40203c0c04001d00c6128070624a403101c80300c01d000e20b41901304030350022040e510b03110500003401030289900c880141d041014030090605281c140b000c5001e00740c0f806800e90040e01d03204804240c96800300d072034020b5890507218024955500c07400e0001d069500d11015100100036040b034000940361b83c000710f41062032901c3e40c980c0801e109623100100d90040d40215150f20b80029031901a54011410a0040160160f980c54051400b400551143d00300c2d40c0c01c0101c05441114402c10303654846031a20b1049444049070f8030703841c00c0403241e8a2102c00740d402c81c414808040004124900e80c400b00d902c0f583c907124012240c1481c01c8400e82d94100e4a05203158095102c01c20340302d071510244640211140030b82e50200d1681030540015120444561125000750000c200c1c4150320f9070803020844d00c42000fa01c00165441807030501c94010054954926 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 358224775 1250 358223525 358223539
    0x403030e1f0c020a080a0f02040213030b070c050d05042103090b13090f15060c0309030210030b010306060e0a0e0a0905070e190606080f100e010f0612230c09 69
    0x2460700c1c2e100040c40307075540c0f0075259400341c10703100c90034107a80d800c40150062126501000400043c185a0054013211940880b10340da01740d201d6640b00006401142c0308000100c42c5403c01c4240042013013400c148071010b041582c40c242c18003040543c80e02102e039030440d012510288a508240c421203060004207110000c09031604c4000c4401903c00c01a413141c144558203110000814511500c078640040b402021f010b80250b20700380c400e640d141d5400c44103906020141c0307070001c0580c4580c4148809080c9558001a40c404141d002500b2a81107030001000c0000748100c40006403a515008810307100e06960ba03031560f0381d40c42800005401041d20042040c0541100041c103004030100031806030f4420585c0f2030250f95a07041c0f0f182220b01a120b070100080005010504041411120f55000080700100303404040c0c6032500ea00e02030303200781d11484504992000402003241d00c58130030f0205101180042c4103200007101201000c2a03059840126000b01c00003113412068048222170b2400c401501038 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 358226025 1250 358224775 358224829
    0xb0a0e040516121107021306090c03020903061501020601090216061103040512090a15050c0f0c1302190e0109030b100e061c1b030b010305030721050403030e 69
    0xa028040d19081c503802c04109000c04400520000703026103080040c110982e0381c01c1880d82e40804c403074000882c0d80c80034182c0d6070790004180490f0034000c80c515039400f03840140e1707200c0762041854a0080b00400c4400d01c000011407115681e039020810703d0456610020168807071560f521a030444103544517008003e41d00c2c0002d861010000c00740914403c07405002910800360420342100e110384114000c0170752001c11110184100030380684000300411907440c00320705003012066800c0c540000c48044482c251b0108004c002103152030602c200e00d0200110095041030000380940803042d800c5030b49402808040040104543d00c1550828002e541101d506906c038200401c0ba40220400c901400c1030318040480028510700700881105021219112128440c1107580c60f4194000400303440c03100348003440040000031410480d10b07c3d000e180030707802955a4455600d8031031101240c500101c000c2e0190795050101060700107040c0e80843c0d1301420a0101903500100060745c120b11060a8055070041041d2 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 358227275 1250 358226025 358226041
    0x311040806010e0108210703030906020d06050a05030a020906040e120d06080d09080a030e060c0102070507080d030501121103150a0e0f01051306020c0a020d030f170606040b0a0e0405 80
    0x6034103c0d0b5407807203020700742e0b62210071240d22000b4810b036034480c0841249428208405c04001040322500030318000600c0da0384c03665078000343e91082800040b0a41c031040f0502c16403410084043c01401d0440c003c0403544502d41c0403400101004000318880d40c0d841d240541e0010080c000c81096043e0030f107200b5580e02e14100302800a120900440c0324601c201440b603c00c80380984144030035128200c000b00000c00550740d0460fa0300c202010000c1e003040c0c003803106501e464002d001130403c131846000604004d81c1452141403404409030409010582810010401c103440404110703155900110403c10780808003011074509041c5105210503580a0387c01c1001c401c0596001d200f0f5000d81c202900d0803c1158400103080c1c80044e030340f501140e0200c0c6981030005809a0042c40112903120a44400b803c181d00000c80c0720040481c2a408143e40740922484c03694001d108a603d440d004c0c104c590b007030400002181c458091401440040c45001039a041c18030b000e00900c0d05a00ca00520030300c464502025 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 358228525 1250 358227275 358227283
    0x315090c0f1210080a0f0605070903230c0a0308030f0c19030e100c050f0703090911210103030203070b04020d0203122208030711010c05011104030210020102030708061003110408 78
    0x3d01c00c60107901805012600c92404215000141c1d04099052a841001e4582c4001410040d240034248041c220000002031441c40960314905060041200301c50954000c05080c400701d4244a80310720503e4206100260f850400c0c5c0b90030080300c80705d110180e07a8404180e1603611845d1740400240c0390008ca41107656078150803109503c20000c00381c50002c0350444100f006c2e14a038002100c0072640034000036403c02503ca000d040241d0282c0360152420741d903402d0398402c803800d2054002c406000000c00c14448070714011910301d240445c0ea05000741d90b140d070324021745030b004086000303000c0041100450f041d5502c4402c0059601d400505480c0701d240082e0144540703078441c0c041c1e0803820f0105041c090070300e80c5441000c011905448091490400255903810b90b50030f1101009050011844080010031802d12804c6882d041d8a4241c56a80d0300b0740c010080542c0c40c0340c0d0100210780c010000c00100c16480301801c0e40080064424462282c81e482c000d502420b501c1c2e00440744940c02080004034100300007 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 358229775 1250 358228525 358228531
    0xb0405061501050c0a17040f170610060c02090709080d1e1d0f030f06010902030702100b2103090402121f030507060f0905040903030903030c02030315090c0f12 70
    0x8803041e10280c090800644041c01070101020903034001c0c0440c03102040e100f107510040c0702490301031030345800d44401d0302c0d4003001d145400298840d00c080903c06120030342003050329000300012030303c201c0d03103403074110010500c070034040000703003c0d00300500482c2495005000e0301d805040148142c820301541c0540c0100a181c400385030310b081d0203444500f07140c041e0060308010400e201000e2445050141c000070301c2a40c500d01004281c01d4441c000c801841000c09000c0140a01034485015a8a0801d0b0800a20b06807503288600003180c9807600d03062542c0e50313100b91014070981040d0690341e0300c041211f0460850040c00a001d800600008001080710300361002c4030700c40c01480b81d045c9034050740c5000b0004110418040180b41c0c0e070000c1000c2c441b803409014204120015481c140340b64545440224050b218804011004251140b42610425405006800c0a011144001c42c00c502d4a4600d0b01d1150201c04507950180180002086905940000f1510302ca1100031026945801002324003011450803 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 358231025 1250 358229775 358229791
    0x3040501061712031b0309070e0a0204060f1b050102130504060b0a0e060c0313270b03062712130605090f06030703140903130509011203030b0d0b040506 67
    0x2240740800d10406552000c4003540d101c2e0700800e010014050180c01a91014180b00c5400c0030502c8419030300884040118400d1228002a040d00e40c94034140f01042c80001c1c1642d2900f50040c481444800d500c8003492080c8001c518140e40c295902540da203600042c001d034068a9940001445514901044039460807200203882c00c100e12569900a81c01c90300452034041e0000715045114409494028040d0030348640b841e081e6440e141c90301c42140b042d141c80f07134401c0b8001922800c1800806c0791840110f0325074144007605005402d6424000f944401005001d0b0a00b602a005610149610410840c2610b0983e504461150b02c007400c10304019080094001100c012040d804142a1311078019200300000c064410407022141c0801c00000e0b070401400c080c100359a500d000704407070b5881e110841c0224840d4010b140d903020400100c0301030201b5030300000d005020f581c00400000c400601e0781152030340c0510b000103c0d010070000082d403044407074070090100203842c000d21040c460041141c40c050030321 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 358232275 1250 358231025 358231031
    0xc090a15110c060f03100e070309030806030d090b030702030c010509070f0f0b0708070f0f1421030a0f1506021606082719030806040509060402060f09010309020604090203040501 78
    0x240304481582c85031042c0280d0740081c418440103110318070b403002641d004503400b111210280e03150460b0580d414400c0328044002034440b54070200385038100c02450342000007a00503201c103182c0d25101a265070514451040c0c2006c000000940707803442071068031140139054009100380d040180c0842c0c1d8501490040100041d07103d4400240b41283c0c0701c0c540100d41a4402d254102003203500c0e94410b0341c02452003a1880740514000c0c4000440b803882009180d44103401c400002c488103105103240460718030101444400104500f031a04445a0541c0d0b0320400c000004500e00c42c041414001900c5540400c424280d5800b00110750305801250505102140450222a01c0d50b0750038100c842410030b50310150001040c5400b150b404c8107081d800b044000051081b40d80611300e0705d20941407600707581e100f0380004208505101d494505401a039400c0490903004118034246600003911501c5080c04030a070503c00058082a0760740a508400481030700240f43c9500d4640e85c16820011303500c204e0741140c0c154a = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 358233525 1250 358232275 358232297
    0x1e020a11090106080f2502060a0608010b0d08180306070807021c0f030b0a1a07020f0603041e060e0307030306030303240501050a0c061a0a060c11090c090a15 69
    0x4000d40c00d40c2c100c968079514126191190071a0030348000c0054841120361954044a840c08110101d410b01c2084140c0d0043c1054900819040121503060b000a15180d040103500b01e07556558034200100e483c0c001312200c0d0707540c001e60b2a11140f4008002e05076050f01800c0108000780d60030042441c400c0c2e04680950f00105040703000c0c040398009648694021900304e80075502e0851003a03001700d4540b0f0b80a840c1c12181d584651800282e072100d404082000072000960320110700f425203020703924503402c0c0c80c0c1d00d0039070815035a600e40b0072840e1206280c6c07018110440340248000e5070001c0705c00c00034040c20380b036a0342d00c0c80c10010058881030100354086400c2c5440b02e040c0b081d9041071550701d8801400506c41007400c06004540540c060807000042000501544022031294411030784c0448141030f00309038640d150000d0065001c800d5001d0302c14000c0214059010400e03440541102110440300c40e01150389031140e4002c113001e20b64409401000c0140003241150405440d20701e58402c640710a55440 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 358234775 1250 358233525 358233529
    0x19090e0d0305010f0e070c060e01020319020f12100306140708160f0302030a0f060803041a0a05162321040501021c1b053a0806011e020a11 61
    0x18003e1142e005a1320400030204417030803030004482d4004030302c0d10b0801c0702c44286407160303001e485103c4032a07010741c0d6000062000c1d0a140304405004082c3e079141c20760034840303032843c00c0f1400c2c000c0e0a1481403c0550400003036000b280c03031124a014591180d401c0201c075048460b9100085070403541e000c0860540e1002c50b104014003c5080c43c188140c0d920440d01042a01c4210065080074146901d15034a481c00d20096102d140604405002148021901d81d441e06040805c000f03150030300075800480401241c4500f950002c1240c5805c941195021000020b0b4901324146000150b100100d08202e40049401294080b81d010b80320044007181801c0e8021243d02911184224800c080c0503034007800d4281c1c0700c0222030f00b901800c82414108800144d040e80e1070410107002440301181c494120f1700d8404c1c818882d070030201001c24541c0d01c01c80007001742d524200203440140c11415060214450004407260711440e000c2c41d241c0c50085280550302202c42d0069542c04802104a4a62065008041d454 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 358236025 1250 358234775 358234781
    0x807030b06010305011d04030e0f030703140d0f080c16120c050c061801030b12030a0801060801140f0d050a021c0c09050609041202150c032d1519090e0d03 68
    0x10003140091b00381c0945075943c0c103039034411a44006070781020542c0c6404805079030600120740154082d20221144060841b4218200b0300b40c1e0158205000b0b0709168a118250b00801c4c0c03036408406045856503441007062051500031030304400910810218090407003841d40900c0002465103d0000c86a01078071100411119004803444024400103e5050f5540ca600c65000080c401c031010300b0503004101c181c0381c1103065521281c1c00c000440d170340000400034641e21440c8240140140d9522070b82010340c4000044090040d990040c0c07040013450541414001c080c0114045564010048112120b010846c0c07841da1044c3e50040d185281c560344005500f0440d4002e983c81180000c0c0204846d0751580c1d90320742d09a8000b109402184900808c240d0050f034801c9005024003000081d00d5128030f405000d51a00001d60070034580042140b102c1000c20700c66000607a6001551010307a45406072040010a102e896411401480503030000070000d00640907510012481f0060400c1d1803072690244810350507 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 358237275 1250 358236025 358236059
    0xd0b01030519020715090f020a06020d050d021b0a0606050f090408071403120c090a1215020f0d0204090203010828020411091207050a080a030e13060807030b0601030501 74
    0x164189264040c16042050f030003058810712901024a151341c0302400b0008076080b0030001c45013a0409150001945400c0c2808030052103188010302e84001003210041c21409082d8441a80c9074011a039040750390f0741c1000a81090038000100c807000c07815410040081e00035442460701900d00008000e0050404031010340c840c54000407030516200d2a95198000b10ba484140281d060100340301c07011320010b9101c00747c0c0c0900e060802c51901e03001c1b84001c00020014541c0104000c0c0f020801400000c0d010701034a0105000c01000142c0303911842202c1580d40c803842d01458841c84c80040c010840710813680c050741c103840090f801c64100111286041d0361066110f26860159500c55050303900502e4590480c0c85a8102c10300d146003018416000300e1400e0300700040c460b0b03403034002402c180710504000d03000c40c0042603d00000c0c0340b05003c0751400303000c0010304030009002d12150140080040f8054112200504002d021101401d64a05200201403800d841c0c0c540040e0038032000081a2000d00c1003070003 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 358238525 1250 358237275 358237291
    0x206061011030f0c0703080d0b0f040509060a32180c030715020709140405010b04021c05041a0c0301210c09020a0c3201020c1e011e020d0b010305 64
    0x46030480c0c20316200e280750449442010136210b00100440020012805072811801040f40030907184903031400c00c13001240e80d00d07449000d24034110411007245000510142c02298060300090b031515500104a05e4502e85664188290401d0011a50001d840401c0501c00c0f40d5986522074007298060b0010340b03d180154031951b140d0320840f0305124100d14141000400d85540c011115401e640d0f07400ca50964507060350898164100508000500c4428094080f821b00102e40441c507190740302e0401070390305061a60a10350f084d61400001c1c1042144074860304082e604100040c0c007031400e49406815503100740070b103802190082d8200d030001c405c208070084807103602080b01d041c400d0800c0301c140000e402c0b210300c40003040398104082010928901e030042c40342564003800c0c80b1503210b5500c0d00109922402c440007a5070302c1005050103c041c003048103013225250703200b00388880c02012580c40c0504907009250500b45d800c03000c03038840000280d00410003130b50200d100344510041e000041d03040f150200c0d2459 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 358239775 1250 358238525 358238527
    0xe090112080417011e1a181302130905010606180305030703030216120f0e01090305031206010507060e1c0309170a05040902040810060b03090706120b040507020606101103 75
    0x400f60440c0c200038800910642000050360a40380c00c1031802c02c0c210b00b06020030310b503a200d00a0701446440d040b0912541425140120104d20b290842c5003210320003011360031082a0464500119510601031248074041201d043c000310080303050180c024a2148190720128080c404a2750b64020454403803000c5a4000e0051802c1243e26141507010354442c480c0500800c0c107581e05600050141ca45071850718200e0760350211030001141d406041a4036884040f814000940710800000c0d03000411241d118100240191035074840c000140c5590280600040c8118148455510052800510840a0310400160600f20fa071240c8056003251040711018101c86101c5285078202d030b140500911340492035241c15464142d4070311014080340c0240e00000402d40008a6031031842c030440c0a141b02619105036001d1450030003011043d503400662040c1424002003500c0302c5070740c1c50f0740d40c4070155120010300180914549a1b00081d2a5081194443e105160b0150044000c2d445480d03003506000001d0011 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 358241025 1250 358239775 358239779
    0x606020601061205220506040308100f0302060a05041a0712030e0a111c05160b09010225050a0306051906080c130219021c08041101030504061103070e0901120804 71
    0x420043c19001784044d80c68103006450028403e0003121100f0b403280500050304c00c0e400d051900425440d40907103400c200040c21007050109547c0c01036040c041780c1e41120016511441294142c0b140e0045071301c156059459401401c00c0e40c00400002c00030300d40324850880a00000c02415003c840b48101401c0890340454802c400107100c0c0c40c9204042c540c002d0a0808104e0710011041050403608803c9075107401c280108030407407244842c3c8401070101108554240364404000035030358012038001000c40b8060140c058000c0103178040210103806d01404681e410754072810240301070300c800c2da03c42c1a00002e5805105200d032581c0706e45401d44650301c000d0150319024008200b064010316148521142e420400000c41903c1d204058000a1450300500a4190000c000c41100c0c0c18481212041c040701e1410803000500d02d000f0782d0310046090800040c00d4840c1d04160700284a090f8907100d401070000140220941c10015040c8201011521500d1513a02d40c40c06540c10500d440c40180510414082 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 358242275 1250 358241025 358241057
    0x120b0a0f0905070e030d0906090b090603070822080304050c0f15091c0302060601140415030903182d12020f240306100206071d0102070506040b030109060602060106 72
    0x700030f802074290b00d041c403050341132000000d080c070f000d100070680401d09001041141c1358001c01d0b0400100000074225050144c5180802c040e448020700302001c00c0385003000564008070010319109403160201d420018480325203028600c2e540280e405403854801c40c21100c1c40d81c0b4061a100d180ca000207000c0b0340c0d40510184a001040c0c000500381c1c4d912413a48540d14441c100c0030101940070310700990041c100c500b007030800500210388807407402a049200308400c5c0454000b0f8480822003484610380000c1004081c00d0450b180d064600030320074480e50120b00002d01c46002081610301035004131380d021902810948500c41d40040b84121080480d91000140152030b01910403212500080d050400340681c3d040b643e4601c407003003c60b01c0002c40020083c48110b0a14184000843c02c081c0000d20302400d041c40d02074650722600000401c206980640c0d40802e9109001000003051702402103a2219218602d060040d0401d02502c02d1143c81c0210014901d440080d26a048442e9501c4030340110046c1c0d03007 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 358243525 1250 358242275 358242281
    0x7062c010f020c04020d0c0e03060c04030f08040503030d0b091e0610090509160e10020a022e02010207120f091403070f03030c0506090f10021b030406120b0a0f09 71
    0x1101002c1d0300520512010588950004009444c500280020300d045142c401421340403240480c14029031109080140d4019424100c0f002e0700c0e040441c10740282c40500d01200603201d5030300150f40502000c101e50110340860f4004400e4140121100d4080c4c1e40d60514032007110030007180d000800181c0501241e5941060020490f819034507145c5418441c2c0c0b01c40100c1d80802c800c0d42c00c6007504007a00315011955500060101c03604504136482400c152016400950b10004200b01a01c1101c4424507980410700f00b0071094444400207813104080401424080d0003500200c8050307900340718200420221a101e124017003850410398980050550418118840c80f0b007100300b2441d01403184203030214094505802103070055100780d80b0800850395500d045801c1a50150061102d030f4007010120402c00d10110b005042c0d070041400c01030315081b001041c140ca0340c04a40041d5103d010000340443e00341c1c0d01440608070511092424402484281c09004e6000c009105a040e5000c400c002400045441c2d0 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 358244775 1250 358243525 358243547
    0xb10052205060a020d0e0103110304023c0901080a05031b122a010b0108010b16200102060108120702040b030a0c0b1803071206230907062c01 62
    0x4641600125203650108800307074000300043c005640420410f0046651002c26030031450420301c0c090010300301180c01001e9078003020340001e2158501c9407404884d407180742c98912000c2d803d1b5800d0301980301c081d85501000704220354890b0140800500229036030740c00040e145006a40480210310386084054400b1041c013018440d1aa42e001d640101d0a5681240003d0300e601400c0c6110440f4024483e88081064003e68642903645c4c1d0411100c0c1500b40e0304280c0d5181118009186190f942d00c41c806128410010240300a003401c60115500c503e6051000d5480928202030b002c50b20540d896150503990703452441c0400003240c00c01c02c10303000103091a820100301d0160203001c40300c089001d0380e11400000825000b03d03013503043c0401c844070075409044280320218400d80141480c00c0c10319141c04580701041001801e4181c80c1c0044c024858124036101044890700500c400385410400d5035180c4030b060600ca41d40c009610001b40810f00c00c1320284c0d04000d5140d150f00318030700c2405000103450110302c81d = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 358246025 1250 358244775 358244827
    0x90c0304061d0d1d040c08060f0a05030a06050901141b1612020d1b0b0406110405030f030a0207050f0918010e01110c010c050405060d020304050703140c040b1005 71
    0x4410b007a10801c10400000003100010385410803400380301c030307031502894407500c44072880b50b030411000900080d001820140c00040a807001128480c62802290983c00146d21550b014410641c21a0034014942e100c0c0340107541a00080c88504644022a0034899040d1354038080f480d01041051107054080c0e0090076440e4071442507050480d01c80c1c0710003401c074000c03020407000340e0000b41d20b103621036512020405a42c1c190070030001803000551104404003030020b0009000c1956408d40b101c9402c10b0006803401050024122a0035182600c1015101d0308007204003030240c4600301020800d031404a1001c02503120107091503005540b41042c12180c0c1000c1310704900c10355610707180543d1040d801e01507603942e070350007010a540d0382070f05007400d50840f200561a50200002440203001c2541c511044407140452084050303100c1d165410503034102241a44002c2210300340718214140a0400300b685030342607004032420071182c141803040c400400712000c070031000180100140700a22222040f034990403c54 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 358247275 1250 358246025 358246061
    0x3021f020c0d0f1b080c01031a04050907090b030c100804110a06090e0c040806060d1e1415010302031015050603091c030606020c0f030a1506080c090c030406 69
    0x1007400b01d24038028480b41500d201043c0440345061203100c81c0780e44120703050640c00e411414603089141c0d841e9244000210f04042d20391510055490008501ca251000000d20411139410101c03d11541ea80251117200310950404100f8001c0386400729007000c148102400400450004450417070306094005c10460f0082c2e400181c0248544034060444042c1840392a0202e0142c2041c004584000c8001e00f01e102c000c904000600118a010130200e401c40d80659500e200d003000c91401c1c1000154a54000741e1f0360100e82051024040044190b10504060a0543c2c0010000c082c6101c6031800c09d01010b5010341c401211081c01524aa020801002240029003585601c07040000e05c0c1e54816a4800b24652004041d90b030803041d01d144a8000d814581010819149841d00107911010f035074500500c40d04030701c0500784858906001101c5501d42c000541c451640d164040c010061515000e140081c0c0f148180941c1c46061500550307016079046904141155200c1da00c6a018001445130b1082d1015 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 358248525 1250 358247275 358247293
    0x201031e050103080405041410060e01091d011a0901020d0e04020903120307090f030c0303140c01020a110c010203040501080c0c1c26071e0e030d0c020a05010903021f02 74
    0x3030355118035806544180916651580b40c00208800e6483d544803408010b4400c00c02c0c400090711080000c01241c1c03943c10203108030074220380182c2c0d04019540c0300081b03540450020941e05060400018140d03080446408079100080003a6807450145861580c0580d105160701c410315402034094000c08580100058540b66001010a0070408070300340d240814a800720031b020f041d076000300c5007001400d00848030250141c41e68031404034840071440080d06000c0c00550403500200402c08403005411900001d541d25a00356600801103492a0b10882c228018000d080a00c0e40c40401114100c650503560740382140c40c0c200740082985c0c40442c0020702481041d0401440304a10089160303031820540310000d03081000c0d0840f079841c56900d01090b2405541004006006030071400101403092400032200600c01051016901400c0b001d490b01c1c0c0c10300c5240d80c2c000041d0b03803105001181510075a26010801d40d5080155003c40b480d0100a6000070f03a07055a00c0005440c550b101e6079081d1902c110740e0195 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 358249775 1250 358248525 358248581
    0xf060a0804124b0306140906010c0f0305070605010e0a0c03020903030403110d0f03120f0504020904030e01020a080f0d06120f0807110901030807060e0606030d0c0c050a08030c0f011107020103 84
    0x80c07900d03c600e000309071549420009402260702d201040c4505442e50040b41c6001d1000034410080880000c000404911405d004d051040d0b055414240d485002001596140d11001c1c1e0000e000f164445040f40c140070349091941d00c079000f55259820044d00940c103090841d0743d0381040b00c07800f0150039080308110341e811001c2002c0660084180d03020b80c8500400134050083c10301540c1403900c400201c1800c013000d10006842c2c0e10851b0707503c04d0b054a00b41035011000d4004134180204000003030010340002c10483c184420100c003c003104002008200840da13940d030020f0062100040b0040d0407200c1010102000c54150310050401c2e62060001c0c078229118440055803014080c0c00c140e541040214410b41002002d00c240b460000f041802840a4a8071400003991000128143c0c020080c46007588020030002d9000c1c1c1d40500002002d540e480f03521503003241e983c0d8101c03200212243c4110303080900ba240f018841d0380900107040b05901d113000015001580075100000c4190014107048000c3c080300 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 358251025 1250 358249775 358249907
    0xa050102030a090c0801050610120f1e0b09090a0210050c07030f02090901020702150c010207060e0d031b3e070303021b030309040b0f060a080412 64
    0xa4940303030340c0024105940c0c2402d51034060b0540080740147e24020902a955480800584020034546803c0c8a94480d00e210007018140080c3c0e0070541c0c03030400c2c0e00110543c180000f880340040950004100d2004030741c04025911b078041e920200c05820004501015040c40c5110314220030880c1000362400c544c0c002450725007500c1e6070003541c104440000d51f108510303050510a400c104400025030500c0880d4000508036803d841007201d440b039000030030840014003034040d2803040c0e4106a0800c9102c0b0051066520384100840303407000a440e0030319020340a5032080303800c0c0c42e40c405559803135582084104040540c2080c68030b20400b41707800d0644100f03041e41000c9880b00708071240c4082c001c0c040ca10729002e032a10b441d640700400004600481000070b0384000064400d020f40c2200e002c03d0c21044040440c51088150801d00c0d04500001428a003164000340340901641c81031110111080800314204c1e000c0d4501401500141e160001d00c010000d030120322a0f0795507448021f018443e180381009010b031 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 358252275 1250 358251025 358251031
    0x1107020306010f0302192313060902120c030403080c0a0207051302070311120d05060411070f0308062b03120203010f050909010606050f0a0915110c0f030613050a05010203 75
    0xf0ba89072090042c011414070300c0300078a020041e0001e00c030340035050609150854000c0005c410310280b4103502c200c0d0980d1034208158100349503079020172265445032100d9000c0e41c00400080c4840a03480042408845103100b124421030b05542c3d141e055854506440700d01d603010301e5074042107110707540c0c3c003080c9070361403c4c140b590b230800314500140d544480d46400b030081c802c3e90746040c190f50016034480c42c0612030b000403070f1407450917000700044079542c03000004c00070301103103a19102e8502c02094490420801c9214000c8040c081e40314402140d551008001c408103208001c50070aa418482540171014642480e6a410340b02c0c0c02c0040d60b0801c8184108101e80099006e07030300c4c900d0100410031007402d1011040b0b0f00910507600a01841d400e221000d8124401c40c081103640c2b04d00062030300b071001e01c12500c51014141c6401c9107203110100d00d00052a0701040401c0c40c0450003503200b403079014a03001c0700d9a610404007802414042d5501c00e01c0c2226000510803e8401d0701071030780d2910009030284010341c8 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 358253525 1250 358252275 358252289
    0xd050705030403020607020106141201020f070c0806090c180702010f05040b100b030f07050a020708070f05090c1801051e16050c060703080f040606090c030b121f110702030601 77
    0x1d00d03880c140c10020320f410f030064424015a40741100601c440c0041c0041c490a100b825030300080002c41041045009124980d144031094101261040c10841d0702840300c02100e02c1681100d1690315109001c60301c1c2d0a044904c582e01c074400b10242c18828801c0030b1400e43c4005980000a5107080642100c0292001128202e0325005010104040f20740300d210004042c00c0d00c2c01c1110b095244c000e19a6800c1c1c00c01910341800d211000c80e1a6141e40e1007041104041c0860100f6a03240540d1400c14a54241c4140940d80c46202400c00161008444802392150000c0700c010714010460018015030312580405c413843c2d4114600040b0b46000d2004a00404c1c04194990301c08080c203003541403a0f418814034104051003a50308014400109511a6034503800030b4140090110340d858900c4c01a00a010725408900001d09096901d203000784c0641c0440102c1800740c900b1802265889442500c900c0306c4100030f1002c403401c411180c1800361650047e1442c5000e130510514001082c2c0009103000b4090384211 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 358254775 1250 358253525 358253527
    0x103050601080d08130204090c030f050c0d02100e0a0b0417010506010807021c0203120703050901060b0906070308100504110a030b030d140c07170708011508060402090c0d050705 78
    0x200101000054010004103010b4002070b8490f19005191680140c04020b0244a40d460314041d9681ca620481c0d00d180d1001c071440f131481d80c0c0e140821a40c49191800d6820b4029405103407400d0810b00c000c510107503402004903141020340d0314151113201c2602c8035690030402c0d003400491441d00d4400244044d00c0c142c41d000d07800300c0100c840b4500b0f4030303030003071819041003900018040d4181e000500351041c04c54034000544c4442000000b00d00e58001d59030410400051402031000c5981c0507404070740545218030003445855141c0c2c0c2c4d41c071002e10503c2c6000303070811400c0012901081c8502001500884c4003074124003400e40d180700280c00c4d90791216411401c64000110308102035054410a00d0060b8154040c1c052940c1e9144040d10000c7c60003840c11040070000340190b0041c400788040c002030301c1c0105030f000410f401e1854099071b9540d030f402003421941c030300341d044410a0211080281281d00d80350041c15556121f40c01d1140c500e6019040c400071990522509150402d6402014441c46542c0d84103 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 358256025 1250 358254775 358254779
    0x2a0f1202030c060429160803060f09010e0703020c12130501080709260102191d03010908040504110c030703020307031d0a050405090f011107060c0f08150a03150501 72
    0x15041030407090301c0c28402c030f0082004200703802d01c44020071403410b031680c12155900f101210041c52881a03a809041101c40d40121008122041010f5402101f080d076038015918140414800403040078004c0c0744c042c2c9140f0b000102541e02c00c1d0010701d81c60501c02c0942c0d0003141c00e400030009941129000b4654220204028003855034401c01d07290780128540b804011440c50803801c1d078101274030f40b51921310505040031104900e4001350103d44c0c6000300c12140c007031039204910009200d1200401817058240b08044a080386140500459a5550308408110710306441c0504100040c04c50031001480310005001129540000b800a8141513019070046c40e591215840c00400c64845602d42105840068185217515154501000f09840b4141d071b00240380d8513800100c80c0342100070b201c0000c0ca5807c091004181200e400f000e054000d108400c01c2c061510a408261964105240510002480000050206104920315801c6024042c140713000e115225294040400c01c1000c04101c025191001 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 358257275 1250 358256025 358256029
    0x12100507020d1e12061d0103050f01090201080f091c080105011808190305092112030906130c09020408011e0c020a02060309010e010222122a0f1202 65
    0x10002030003405280c41d8036241c1a6218028540300c8030780c842d408000c013900e00d5070075402180e40b103440903046805020b4400e900d070002c014401a0309010496082c01529101120035005001c1c0070344680d03050f110700c00300d50b4a070b640c10909000300400c908110b20800c0f241c503c0e1014608000d01c50b0354030329510306180d0360403c00090f01c98440d81c040c040d01c03098904c4007040283d40101e1031050580c1042e1054254100700c3c02c1c03c0358240540e01005130321040c08007859500b00c94048030f039403a40701e84000340d43d00d1810f00191801d1602044600144c036401c09070001e40003c01c003030f03c94a203507071290007420800d0f41c423183e0030800c9030080e03000306074581e55545015043d200c210581c1407603001c054001f4003600da40326400a450b000390000c000d000c0c10004c03012031403006c2c0070f42040262441c1c20300210748400d442c04011941c4c505551001c00c02803030040004c65a0620799082c2941281c005501034075042c80c1100f2411900c0d00610000040c0400c00008640500c00d0070814004080401400f0b0b00c1c0030745401 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 358258525 1250 358257275 358257283
    0x260c061b12160b1f0603060810050402030c0d0f08040303091409010605040603020c030c0f03031e131e060e0f071e090b0303070c060512010504020304050a111210050702 74
    0x1091851041c05000321a203401501c1c050921055020625072019100da00100d103401c0506926540c0940f80d207000031600e2a450303403000c03007103411103022a0f040e8010f14110004642064501035095044001c1981140c10300d001540010b62040c1030b440c1c400883c50302c81c29004d030002c0c1c000b1000500201400c201c80c0c40d0341048496a80d10888084646515110010b4107900c15445140c0a1580100340c1d203150940500c10b99402c41819801d0b01c4080c0028071419031613034411103820382d00d48031a4088040e818240340040748510007800710211008000d481d54440382c007036080740b0201d1001c003e00c00400a2502d0003940071610400005004a001424520741400f45682018040c0160001030890400000c2c50600882d00c48200020302101001d021038290b10845c00040c01181038001c00182d1641d2040013040b06a00402403246203980b243c0402c026403109503801341456110003680c00110b1a04029501c0a980050075035a40120101c40c0904002801d1184a01c1c90356071001c00c22203030780601c = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 358259775 1250 358258525 358258543
    0x605040209150d021c0204060f080f030a170a09330e0a080a02012306010e06091e030f01060806090606030703030c061e05090322260c061b 61
    0x40074011101c8800c000318030032038110760300640310b15030410b0417000046070511501180d9070081c00c144806a1148491200b01503144100c00d41ba10403045600a000710100940d10510071399510303000f180a4202c10f003000c1041c0680f842900554880c848130006000c841c400d60b007540d10411260b900c5d4a0400014420055500f848585c0c500b402d00c96004040049418810681c1c0030814070f46a00c2c0d020f108078010060010030b40c03410580349103130300d001c541c0004105209080981e9566807010303d0b0814000e1902401034280c1c1c011488a0f80082160641c0c80a41981c02c4040d0441d003003109103101040c00d64030700d40c0c443c00c5990494424060b42120a2201960100090f00106001450340e03074018030081b0003010251806541c2c070940308e581d4840c140d51401000346950b0511040c203050810319249d07400740450401c2c6142c02002401a14881c0958200301e410b0f25000f80c0400200172140c80100c0803206003442d441c082d0000c404090341c0c440007d010341b00f4401c10007204845d2004d0b000c500d81202a = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 358261025 1250 358259775 358259791
    0x13050c1603080717101a070210080f09120a050c010b04050a060603050a0902150a1205070e190501021c090306020304060e07060e0f040216150e070f050607020d0c0308070605040209 79
    0x104c2c01c11002801e02100c0504445500d01c82d103281141c0752003000f21601807004025445111510110641e0780d03c04410390090b1400b103204030194961500081d69101440d1a503605c030740d0103101021641d80503a0140c00d00180d0f6100100c0d40030f290310300007011654120303603852040741e840c0b0041c8001c6500d0710a00764004c040c440200036402203500080d998480044105421080010b042c883c081d21580381c0e03070107016001c8410322003424040c101814180320040e503e17015443e090201c09240107049074000850328181c014140c103944956035950074802d101030722801d00a070a0317000400646507100552066000391030004035505034800d001c0c1440040e80c071220400490340440303002d55239411101d98001e0022600160340301401480c440c90f408111801401e0701b11841c0499580400680201c6000704645007902d40486d100e0781308c20243e41d5207018a580000d0213100000c01410040d00f4412079030b0040c0c80d00701080e9641da49041103139220300b10487e041519081484111b00780103440301d03082251 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 358262275 1250 358261025 358261067
    0x2070933091805070b030601170c07030f2309150c060703241e03021c03021e07030b0406060e07050d0506010c030e040504141b15040513050c16030807 66
    0x20b501c803983d1300ca42c0d50207919100035000000c0b5413580e0151203840110034810144018500e4000c04070846604000d4040c0d0110300307000c902d038490a108880024000540240341c401e130300000d201260164029824a1380c0081c1030b10184011015044040c189071181e4100038a8213117483c0c100141511781100702c96041c0042d52049804e01101c030000182075030b0b000c24642c0d42e410311111140f24046034560010f90060a4495044206c1c041c80c40032141182c044e40858594a02c403880c00700c4c1901e0500429403154101010520004011004281d0000e0141b0f001159990b00d42c00c04404505065130703900e0104800041c20b10510b00071b8001d4070b610a4003420036414046042e1009040000340102051050307903503a000404000c140da4400318950140d10442e4980a1110403564804e8035001031284160403110701555030310740102c112001e0320700140a00c0c003002c0340d0300001000741c040600352009412040c080b454a2034460190a00003500913510038140d070138001e101400400d02d1880314260821 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 358263525 1250 358262275 358262321
    0x51008040b130f0803070c02010e03030306150f042114120316142b05060d12021504080d18030225210c06020d0207093309 54
    0x22480c08690019400780100410410381c940711001d081440d070001c0030020084107001b0000e500c0480200c03014401e817a460380300980941090340d28042158001d030722480001d00041000405c030090080c1c0442c51218509254544500b40d1120301c0303180c142c0000310300da8280349042c0700405c91402140b0019401501000d402c200c016151440000c0080090b966004405502188154540c5d0100c100d01159240c542c910709400303140035204031135800100c022405014882c42d0051152134000e400041441025031300343c3d5135a60309a00006842e00c194028562030130403408140da00103218612505245917034690014a0a007180c19603042d011040d0100c0014030b0021350001200c2200b486020761200c4240100840c1c900c0c1d80805410085806041641141c0c0410610150029171403003001100d40494407400708030307520040002d8140040c0c0c0703c942d0802510301940d000700041c2c42c0c0c0032914800500e02d881405c1e51800280c2c50420401c4881508010305031030b40c030a401d40c6c5101c0030b07804a007441d = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 358264775 1250 358263525 358263533
    0x41802091e2e06021606110304060c140106060e04140402090106030f180809030705030d120b0d0501050403171609031203020c07030605041502040803030a0b12010e0705100804 77
    0x101a280b108401050b90405420000e85200301095800c515403016a210040251038111740d0303446094400c404600414000d000300342c100b008011510056003001d140010440300c50040d60001da032203041001c07540885040030f004040c00303010507417200a046a883e41c01e00c800c07a01c007091188640c40b0340b00180401603880804090440d02e0780d02c1c0100d500200480500004c09041e01ca02034101c043c0000c0c2800c00200b0400f80c00c5000084040d2040c541d924001d00d40c54000c1c0c0825003000500b11118030200841c02c3c0e00500b4074180103040c0068002c40c0b1b9903440e0844200b5102540840d0502002241c4018030180f015403012011100038805046080040d000080c0c60100401c9581d081184001081c8664165520010b50000720360312180e41e030a1800040c2006e440c02e844010064034080c0000d00750740211021210040c0c003c51850303a80c04c64143c01064454003441d44018a44111a0019400d0240c07154401c1058090100145010100000801c050f420001803154ad00100008a = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 358266025 1250 358264775 358264831
    0x18030803070f110d02070f06110604060e0a06022107030b060a0c1a010314070605070804030209040203011e0605031005090703140309040f050105100e030d1b0204180209 74
    0x3441410034841196603880e080d1081e01c0410360300c1c0c0c0c0f28440c9000201c070f41d0754002410300480d01c00c40034040b11181c50380d1007244c1490f00502c00d40702c1c552003880400d000840744d61101d40824101c0c015203001e151141d941704140d034009002d24141c2401c0f81942141c040e0a41d04590304041141020040b0741c894030701080480c01800b5640c0c05000c5100d200e5010700101000c2844000001e01c036807651581c4a2402a40801210045040c5440f0341c08011805074010004c030748072a50000b04903401c142c075603420070020b01c0f4010012a050354070b0304541400940101d60100d801c10300a0004560707641050241450906440d081e1079034a0b0800c0103002943c403010904d01d041e2900003003401c20360003d2404540c034620a6003101ea801500e03169030000d5020450b440541a60011038010b1620403c0e240c08880d040030900b01c056051304514034005e4180c2c041c000c18042042c240320000c110452640020341128603080101002c190031510910441c98550b0b40a80e1110750001c4582488905031260185 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 358267275 1250 358266025 358266031
    0x4090f06030512070515010801050f09121603110f491b03020303070929031003020402211b09010806041e06170d02030d020a140d060618030803 63
    0xd0f40000400c10240a010300080c07005041203008a5002e59507411070074002c04048504503541d0b1512404075440e0903000c6001d510b08282481e040e8100350f40c0395070b07880003210306803804ca05020003401c02a0b0002c1050000000b51184080600315080145c16082c42d9852545160302030020340044a1100d809101d030443e201c032041c000c00c140c091400c184151303044082c4005200c1c11020750320314041010703070000c02144200d560b607440000e00340c0d0381d40c240c500d101d224407102c6d05a40004844821040078200c0915801148403950744031543d502d0300420200d07440f083c0f10700c080d0000c00c980c80c058001c1d03242540d83c0054030400c045070a03aa0003149450280202085141002204404601e541d5101d0300912022000c8086c9a000540c10520300001803034144112016100040c0199198030404950030b11248120713005035203010403010509000707500058107401404400c1a4401c1d1660145002d4004e4029041e8000b60103410004003034429800004404810151814144001003400060b250 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 358268525 1250 358267275 358267303
    0x40e2a010804120c020a03080405031204050609010f23030103110102030f041521020a1e050904051306050702030c0606040204050a031b0e0c1b010509060103033204090f060305 77
    0x30035030f026001110015080c54010307600401508011050100c40001042100c10403070444235140d0480d0519034041c0214071815500003000d000c0d0444a50003801c0340303198030880d407511002c0039040c100400f40c111403809c50410001404001801044582a41703054111001d000960401c035840703001e0302c2d2074840ca005031701c2300301525881001c1c01070240030405c0d162034082c00c8159846144518020013504840c0e000b10004140785468420136103464101400f03500207694003803030300051105010180a01406500a814000c0180400320348584200c0340540b480307a0103941d80302201001c052a00d01e002e04558801c0344104030030020b030303501e5182060403230380d00400701300c1d801d82680b1010300c990119521111200c0c100f40c0401441010900c0103204030039250030004c0100c00082e02c02d80c2202d80c11079004002d644060010700c0801e000380550b208028030b942080604109448030301d045000d040170b05000e0068040b2b4240002145d41c015135128034100c0608008251554960340c0d92100e942007001 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 358269775 1250 358268525 358268543
    0xb2d04030f1103030d0f0b010c0305031803190806011103040b0d0e0c040f0b0102070e060a030b0c0f04030b19021309180b131b0609091109040e2a010804 67
    0x70007080200468664155030003820390707889101c0006140040c004148000009516100c030b80b113203941c0114101041260150341d26803e555800503a14081000366021141038030003801000c0314000c0c0d170500158119819941ca8289042141c0007420390104104007803031580080c0000d105422445003500e020404071000869002e03280000c06080124801b05640c125081c0b070400010b50b000c64102520114007a401c403041d1558540b069090100f00340d0309541c1c850760000040000c9100c5c0d00c011034111104000040c901146283c100482d0b50140e130088802190310010403e084445c02890980100d51100540c50006115040b003000803650044294540d903540700d200d00940886100306403640d0182c056001030400903040880740d400c1c03820441d44609800c40c15640008041d0105003200c03611b4a92607911400c010000d005003a00d0111400000014800d101469680340110005400c052004d000a02e46202c80c1d2480c2150150001c0c203189c2c0c0c4250410344c20f0b6840101d09601ca41c0003c810 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 358271025 1250 358269775 358269803
    0x110d06060305160e150d02060d11040807080d030e0c010f0908010e01050a0501080a03050403060203060105090607030c050c0303180909100c120c02060601080f060f0a0b2d0403 77
    0x4900400352508003422902c5001510480700c100440c0c1c110544085003a03000c495550440201c154141c08401c69810404400b1504c00500b4010b020707282040002101140c8112541350685090f04141e114030317456800301504201401c0c0500004001070603500e0140600040a07034496510260021a0b5041003910a058800640b04010100141101e54024003d40b070703101d2035143c041d1905880340c02840c1c1c42c01000081c1040001482a01183c1c5600c0f42400c01c0d203107449040c0203400c01000c0c06c2c10710404124104040d640c200081075a94800e40701e58614042c2400c0107883d20304032601e098004d90040110590708101c544852812120403142002280c0d00d00a0f418141104140c1101541d400c02000494050304822400c1150829060401248244c040d0403651901c00743c070001d01143c0000041a400000902495070000c0082e0200c8000c2c40154082203200382640c0c007101900e540407500358242d00f500c01c003420110681031000400c0b56142612141c0d503104a12000b131242d401c0d6400 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 358272275 1250 358271025 358271033
    0x819031d1e032b0201050108030a02060705030a020d06090e19230307080408070302090705040b030c160506090d110109050c010c051507020a060c110c0103020a0212040f080f0604110d 80
    0x20391100c609011100c8100d01d45000e046282c400040309400355082900105c8c00d07900c00015121600b03040d41c001c04c07264842e904d0548181d8000741c40e030241e80b9004c002c450005481030107501c009003011703040028080304140200d41840050a100d1902c103c0200464003c554410b045465501208220881d07000e281c100e4240313540315601000704003034800706000a6827103010400104680c0240d4401ca030a6032415070884c2e00b44500c0c0a48880c0751014008550340401410107002d0f641da4903040341c00703003d060b502d810b0300d01181100c0d0f0141e03e40c00200b00c10407a50388003440d540e54002000003070080c0030095a03290380b500c201041031810003002d1990320050050404c000071050005070440d62050800c00342c001d448008110054413114201000e89840521900c1e14024109158004c1c00e0003091120044000e9408503200350114400d6413501819805014020700040164643c00c0d0360007850325141c00c0c00e02c02072140201c516040081000301044000d090380f01c900303100700c800b01c04406c018a4 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 358273381 1106 358272275 358272283
    0x601090e12072003100c0306060203041d0703020702060a030902040b011b0f05030f0c0102070203100606021009081207113d060819031d1e03 62
    0x4861000728451036200b0310401094052510452075500019142020505050016a50701d60032032500c0c80c2c140c81408c0050055002071401d1501d40615031700784504040050072550200070000300e0f0907200307a0449910035030007002c540e19940d8100e40280104031a9504900071450080d182005600682d00c61041281242401007064540da81c1c4450603882c540f8125407601c42442003504650107035000d01403404c0480300068550019004251900d01c603050100c070320610304103042c0207103680481c2d0700892012040010980e4a558070380298184200c00e941011400c2d00d200307000d5420b5028016007001080d1504962a100940c0c500104500c49004c140c614020002031142c070281c01080040c2d8610012017000030040d0381c44003020705000101c8100a0b0f14020328550360101a00015403200756445032194801176420000440c40800c0c61544643c0c08661401000f219660100 = true := by decide +kernel

theorem cover : BRFrame.Cov 358093525 358273381 := by
  have h0 := BRFrame.cov_init 358093525
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358093525 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358093525 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358093525 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358093525 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358093525 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358093525 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358093525 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358093525 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358093525 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358093525 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358093525 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358093525 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358093525 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358093525 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358093525 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358093525 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358093525 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358093525 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358093525 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358093525 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358093525 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358093525 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358093525 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358093525 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358093525 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358093525 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358093525 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358093525 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358093525 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358093525 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358093525 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358093525 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358093525 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358093525 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358093525 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358093525 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358093525 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358093525 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358093525 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358093525 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358093525 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358093525 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358093525 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358093525 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358093525 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358093525 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358093525 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358093525 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358093525 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358093525 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358093525 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358093525 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358093525 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358093525 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358093525 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358093525 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358093525 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358093525 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358093525 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358093525 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358093525 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358093525 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358093525 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358093525 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358093525 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358093525 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358093525 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358093525 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358093525 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358093525 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358093525 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358093525 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358093525 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358093525 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358093525 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358093525 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358093525 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358093525 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358093525 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358093525 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358093525 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358093525 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358093525 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358093525 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358093525 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358093525 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358093525 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358093525 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358093525 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358093525 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358093525 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358093525 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358093525 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358093525 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358093525 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358093525 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358093525 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358093525 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358093525 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358093525 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358093525 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358093525 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358093525 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358093525 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358093525 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358093525 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358093525 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358093525 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358093525 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358093525 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358093525 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358093525 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358093525 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358093525 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358093525 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358093525 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358093525 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358093525 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358093525 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358093525 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358093525 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358093525 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358093525 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358093525 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358093525 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358093525 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358093525 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358093525 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358093525 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358093525 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358093525 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358093525 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358093525 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358093525 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358093525 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358093525 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358093525 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358093525 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358093525 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358093525 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358093525 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358093525 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358093525 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358093525 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 358093525 ≤ n) (h2 : n < 358273381) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
