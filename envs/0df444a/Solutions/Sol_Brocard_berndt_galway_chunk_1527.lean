-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1527
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T03:24:59.160386+00:00
-- url     : https://prove2.me/submissions/7b77ab6e-5488-45f1-8704-a8ad61e540a0

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 274460431 ≤ n < 274640287 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 274461681 1250 274460431 274460467
    0xa02030c0f06091e130513060522030201140c0307051b0109140a1106040b120a0b031c02010f060e0a05270c0a0b040303020c010c030509130501290a05 66
    0x1150004c0d981407400b090f550310300c050440e5074441a22002e034089900741d00c0100b10f54040312400c00403e114810400840c16030360125600600e207080215281e905282840003c603501001100144c3d11107682e11a543d030404140c40d00004219802c03819420301c3e040c082c2a5006044100600d501803d20359034500100350000b0f000660000304080d100901010020340720340e1280c0007664400b0f500c40d8054043d00340101100d0440d8000404203040a2811603c070030b0030840584669001916070041c80680d64061041e4841070714040e22912420100c00c00107400e40b00c400000396a018604213040003601040407485511079a04100054103680311540e9105c101c100c101071039121030b40764102400d1180d0000720f840ca0f0050840700a0109962070112940d85d100c1c1e4040140182c100300d00d60909540030f801121136140c03003800c00790706188400c004a4250100c6100440c19a030700d0788010811582d62100c103400311103920000e2a0761031150380c0d0b200103138402c2c3c0000030202b1000103100007040703c801c158 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 274462931 1250 274461681 274461697
    0x150c070b0307030b1e0102120912030307030c14071101030b010302072a0b0f1b07080a05031b01023604051905130309140103020c0d0201150501020a02030c0f06 70
    0x107901ca0910100c020010061810303128001c0d00940400751603c080900c0740c680789501603006118100260100848641202c3d0a158204161f00c02040c10408180043d62040d00b40e41c3d4001050140340400400d200d48604400d00007082c10401074000c103845007001d4030a00c8080c2008580d047c100401200244124640985100c005a01c02444691043c0f40156070f0040840702013209901c85014111500c6110b50240401d90200042c1c21344602445110403d0300346501a103904655030488039090602d8a40c040b01c09800000c0c034010316021620368100651841030085003001480280300154018240d0300c00c004940c1c2c4001403410344410325030259686001340c001d001a0400c0c01c40b1000c0c1e200d1302c410045003141800f0008030580030303c42c075218825030503660350251f0342d250000200510036989a007504154080041d60001e9000f00200d0803090301036800080c0074034860100204924140c1c01c160704540005c90a0009690b002540001920b0101c910400f00030030000020403911417280 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 274464181 1250 274462931 274462949
    0xe15090402370305070f0c0f0609050313060f050f03070806031c050403021305040b0109050a140123151210080a050d0e030105070f0305060d1704060908010506150c07 73
    0x1c5000b440c0c4510300c41d4101ca002031501c1c140071030788078105c080e103103075409592000000c0e03140540c40010549040c0c0301c4800c280100d80016104170b558a945056900000c6885040d0701d10200030800e25a010039050507201742031400e20304001c07070015810083d11018102c0f8080245000204040c0d94061120503001c3d02c000c2c0c0281021100c0c008050710b5a000303884240d00ca80e040e031030280c205000d0750048030310440e0320080101807a030824420740300400015060010160350f0710545200310124100c807501030421094004155080b850350340341068401e580d02805582952405540000d06101b40e07080c1c5490301003401031039598503820f070030740001d1540071181c2e0f84600707260901030000106103006a0401a695440c00040c00c200389820303200c091301e0402c0060380794a01010710710300c80d40c0b1058001200810540e2081101c3c0c441e00088403442481843d2107500203410400a034015188000500543c0020f10075032500c6400200d11400d00c40b105840508000b521003e1004244102c2015207a521 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 274465431 1250 274464181 274464247
    0xc140307030c180609061202130b03010503100902030c010c030203120c0a18050913030c0b011823360a0606050409020f01201c0e15090402 61
    0x344020003a210340070901c07002c0340d000b8014a45a0b500038416200b0f4800584421151906e45013080701c078040e209442e4088558248052200d102d6503000140003402c00c0d2140c9500c1c0d5040000f0542000f0441c0404840e20b0700c0c0615130702c010307180070510b4080740350242880b00403004241010b90840c402c8c2c40c40c5030010040f0400f0452150390040290115001c103607a0351070b500015071034921094240340142a407040964002a009482c80920301d010188a80352000c521038039551031400d400801e070000c80350466111000407460301e00d4410000448040180d110030100c6418600c090158041e0107081c050307086400034004031035a10700c005180c0340380c050b1516040e101072244680b22125142d044410314200400091240303003c0c09241c180b00d80083c0303007116101410f001501c498400c50f09625415034103e2501d01121018000700c8080740a00b981c403540346000a000412210a01c4900e0348a820030b01d140e01010100f030010b035070030a41e00b030300c0060b0341c1d0408041c0701c070741c0000601402011000030 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 274466681 1250 274465431 274465441
    0x302040801020f0a110d090306021b0f0a051627020c030403060b0906040204030b07030504030e0406090b0a0e0705030f04050a06230a0501080a021314040305120106020706120c1403 79
    0x48002004450019500c80a24800046109880d4460741aa11b8005180001e0900c0400d034117900612844500d04881051f2000c00e80c405802c101c030311820507101d6080145803206124003031103094501d1141140b480340c003500701100c01d00c14250000c5a07614580c0b81d02032080c441c042036811111a84201300403640c5480c0c0c1c0b13280c0b12001d400b201c030303040340034482c41c030041601810b15009640c10740e588121500840e945621049008002c000c1055080260080107030000c0d07142d512544002d45404c18000c02c0c010070140904c070a0b8642c41d802140446010300410100701e0b030213020307650085070243e40105035481d14201146029000c4030082c01851610300f00d0030036480b14003009501c20b084100000c000c2c1d5102512b4604581c0d00f4869407010350805185070006180400c10600c1d6500b000e40d00250503130b981d0310400c096100448040700407500c001102643c1c031032078507100c50050036030b0301c01403590605103200202840350168418142a448064410016000b400c0340c60800e40340785100c50700c928007 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 274467931 1250 274466681 274466707
    0xa02040b040f060224150a1a04140a0614160501060e07030509070503190201020703050d03050106110c0a03020913060f020a2307030818100c0306090218060a030204080102 75
    0x948a080b003d481107899102d44140462018481c171001c02440c403056546074680144400140e0041c160b00040900c00071404101c2a0001c0030b000c10300b00039240c0c448d0305051804079202c40f280d000c00d20442c254007042010a511510005508040c88401c40d1100c14404105000b02800340009010b542824008201c884c10305800d40e01c501c0040e03070103000c0c94554040385134480745140141a05904045402c650211200181020076481031044985540d034070380390241045050000a00060b44400041003282e80c132101001d01c103000400178120602440000406401407880000e000b0300d03180c2d001401907100d111046201d01c1d0425414032103082c9100d4440000d5001c401c803080814446400034103001c3d00d03c0510780c400b4400140ca18680400c9403403c0e50410350040180040103500d44000e225513400703101780201c0401c030300c102040c0d210f0750520240c2610f00e903420a285c0c03548107104589200145020820031070100b42c1d0115541c81031410100d010348916080800b41c3e60000548443e0005 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 274469181 1250 274467931 274467959
    0x71707030f08090109140d02040b031e061006080f060d080f0d0b0a12080301120c120302030c0d030c021b03011503030e0316060804060f0b0a06050d0b0603100b030a02040b04 76
    0x1401d070380b007880054844180f481501c0050340047d13000724210a0110060505a000808840c4010211844145001c0141c40c000c882c1480c84445a0002018400350004010303148024007a035052040c001c0c5860103144140c024010301091142c0c803242d00c054288041d80d02124800700300d20356865920300c0540c2c046806040228034850242c0410b0b400015154199803c03c500264004021441c59190090038031035001d00c2401a10506180b400009141c2c040d0100c2000043c8250003458072881c02526641c100074080080c1c03800d0506018040411940c081030803605080f00c000c007081d0086415011900410740c24404501c0d90400c1d10000c014180c12a5074541d030544110211000c0c00050020b01001003035038491742003c1a4048003040018869400034412a50405030004000c880e01d000580d80b25602da0003000840c41c0000d440c42c4040190084440140c0d06072007207803035030807e005000000c1010b441240795054021020882c204841d40483d0020004a6986078450380c40d80c0c600d00f2452 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 274470431 1250 274469181 274469197
    0x1005090108150a02190804020604050406120605091b090a0f0609091407030f0206031b0a0509031b01092603040303020312100b091509090a0b150408071707030f08 71
    0x900b010002801041160080b210300040f182c01042c4104280e400c15540c1140140c400c076800242440045004d485500c150b4004040e90034551805044d61300340442100c201038000040c80e04040076120b10b250b0341c85c00071003c3c80c1c4191100080c540d40d4080c003100420202c5401490241494400110b00045400040006000e0f403100304402c8248079400e40c0d030307008a00c0000c000c1c020490004c405440c0031009150b0000c0390300c603242942001022000300c0f542c42a8100c4012510104035006241810425a140e07000a400200004010000040c0c020761403445400d1040c980d060700320002d60101e100c6002c500100c041200d8a41e03031a441d0203900d03604a07515560001980320009001e44130b01d45190801c540b5140111840d100340041800418440700005245410301000740b402191070301d80860344540c00244001038856001c40030841c1501030b852720f030510080d0a11091041070804a0b46008070307496103480500c0504600e2a071414140603a0000e002e44c3c40c2c0508034010f0000b0440200118 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 274471681 1250 274470431 274470463
    0x506060307060816030908070b010f06170405060c0901030204350615010507020a031505160201020a05030f072a150203010b160203010605120309100212121005090108 73
    0x5542c07600c40888000004513060000c0b502080030700d149043c040d600c5450101d000b01403145c940380c0e0586444403619400c0c0e00071850b0001c1020f04200c0640d20404004040f101d110504c0c4003420580c032503999580c00600700309070400c00002d6140d10baa00940c1254024219461b13190404031002d410341d10301c0c000b03600b1b100c1680740300c29100c00c00442003c81e402d48943d404070810312420f26034200440b419005a1b2040b070b04001d9030030000c40496010f10440c4058001580c0108051910448007004480390740d031036005580c01840124155504041680d5011043d180c1c1c06d030a59030345075000c860381c0d07088054194010b00c00034000c011452008040c0340d00507000c0c11103020b410b03554203040030882c84240b1611b0340099081c06408907034110080c2c40b401542c001400401c00c07580700c0000903540c51054050040983c00060300024504001003900e1004285001a060040501c03640d00141d01c01c904440400031414070015210b00c0c0f04041400142c20007511216266860380090340c0d03507800140d020420 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 274472931 1250 274471681 274471693
    0x2030105090606100c06150e060f01031107030e0a0b040b0310080c010504060809010b03010515040b04060b03040b13080307080f130c06050a0210090303020703090605040515031e0405060603 83
    0x41c0d2031000412a008041c080c01d030041103c0c1895040710913400c0305804846130754451403442e88104c03039403034034201401035002c01040d0b0741464010056000d81c407042d0b4a06150074619480190802c03a016031324043d40500740a05101c2c4103000050241c440e41d08043e0150b10b0109010841e280d098010314403401e40100c20482583d210279010781d58041845c0c400d40041d504000a01c0700740d00c682c0300f4540000d1400004039162100d400041e0a48a084036100d1483c03ca141a184241c80c040c020080301074030035181000142e0405804003454403008001a00c1c0348105001b041079043c20240c02103020f50020401522410b081000030070a400954000b256000d151020840025600404c5200d1540c00b01c00b403d107032032400201742e44941001e0103c1c003c2d8001d0480f808400e104074040c100105100f50ba0041c0e0f5503c41e4507010b4440701668002d001000b600b4042806540c035000180400040655100d0b40c50b55100035050380060034203c00d04810120010600c010040300007451070003004201c0c26120 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 274474181 1250 274472931 274472941
    0x105060a020a0b011e09060b04060f1115090709150311150a03050f0906130b1b0304060917040f09050c091207030c090b0d0f0804080a0812070504150f09051003050402030105 76
    0x647e00280140d084211081008001c02030190700e084d182d5210f10300b031409000c44011b0f14181000c42e1030548914824000c4200182505c0501481d00900030821080081c105211210103500050f400010944c3c100d00c406680b565640f6520500d011401d844500c0e0350344d4512000502520f000d588658000080101040c070064005c60010711685a0302d0040345031910f240c44543c080d003400307801170300280c0c1691030881c00350508000461241e809008080345040f101e160070041140c400b141400031500a000c24491100c13003038510812160000000300700b8ad00c901100e004a8412000401d0340030a221801c2111501d02203050800c0b2800b400a01c0410341d640d10182e0250340b03110030b41c641d210200d90100400075040d02c481540c07a40c0282c62050525481c1c904040c60300316044819112540042140c3e521390729000d0900d0b6004125140c080d042500c0d1100350380c403206001a8001c02d2100703008020180d140701d0700c1094020f006c02001c1140384505500082e0040405882c203a00950802002078 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 274475431 1250 274474181 274474199
    0xb0c0d0c0c02031009060b03030703021605040501060210090c150e1014160503070204091b1d0a020c101803140903190303090b04030e030d03050f0105060a020a0b011e 73
    0x41ca4181e0042c000d0940c08681c11100b90080c08040b030110f0f240ca0b078818100010f40c070104040c1025601c03075001401011504c0091401d80304642c0d020134403944c10040107100c20359012481c0c14480c8042c0c00049003c0c502460941001d52058000440046402000c42d9843c0d603c4024281603900580e8641950a803407c011948018120010284040300300300e4030384120703903074100109040c0c003034401d03030341040c0c0030798001810344a1901041d10f6481c6000400001c07800d2030149100180402e000c4503500f52102d8414522681004000300d000075400300798507c0340c10041c0080c014102e003100c01006018440501d000c15045120026000030f0001c05400102c503c15400b155000107000700100101d005c070041e855403007428110200d0405441c0c18005c5d0000d00c01644060042c0d01c01d0711255961040c1c0b1081c107140035104580b0004060400c02402801c1c3c20404640c7c1c151b610640345160f0790500d50b0b10036460300c01d003104001c1007107140d0000010b10f0390000250041c4803e11660031708c4480e68819050f = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 274476681 1250 274475431 274475447
    0xc03030f02011a100207030204140103020316030201021e010902120f1b0d020402090105040b0c0303071d090f071404090e0d050c0312070c06020a080906240d0c030b0c0d0c 75
    0x3000c3c241d074086420551514204e01807044000044c03044441e525129804074065845800344c01040b900c1c020010320441c9018051411807600703040c54012135130720f0740d00001c0d030b80c8114080802801441000c805010f040c01e40026a842ea009850140301110500c0d2035a0340e840d00d0110b0000f580500100740080403480360202d0b11031900102000914546034007000000c0d40042440b030b060050400002400c04c03034500140040d5101100034603128941603d0241c01c0603081d404280f026201d1041744000340e541c0b95005c641108240042c8041d50f40e0304882554202141ca030700b000c1c945004940010644211717040080e040c03110b08150381e45104071030000d45042c040d086800c06075403c02e20014a8108601441c0d84e44241903141a0240141c0f54480300e040703902000ca070320001004a400c01048205c100705480e0030500600344140d400700c1c022080181450105096032044420b8413940c014404041c401c7d9001d50f4104c1100c08183c2400c2141d002240e10120550032554181000000000c0c010220 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 274477931 1250 274476681 274476701
    0x30118020d1e0e0a020904080f041206020903060c0a0503040f020a050316050a050607231002210106090f05040e0c10180e0f0a050406090813050405012301050a05090d0c03030f0201 79
    0x8806e000351625504c208603500601908001c0790300600c000a07901015940d440c030715500a00d070059841c05650300b8141403800c0101386103001d00082080c0c1110381c2d4400202c076030140c1c022034100b0045030184001540651154411541449080101d0b050002010002800c5070400c0710f0200c81d0aa441c820310265004505004c1c203082620341c162500310300c0d400112500c9008030b030700f60b03602d20301c2d1030340194221f0700182c4212017144098400e0940c0303444d546104c81d02408080c10400706061814851091080c400e00076103014a440c0c0b41d841c0428481000400344038034009200fa03490300c0032008003e00d809100044032030204070342840041c0c1c07494000b0019010341d07420b0510510075a2580005005404058000c46a01350350340301c40808a04100041c03c1011140480300d140c5e603140104201c19200107820100e11090304030064108121070300041c40c00d00000b0b080443d11f500c800706d81982e0310b00904130900d4102000150309000c101c24007801d881520311a413a2581d54640100049080b103150b015 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 274479181 1250 274477931 274477939
    0x3100e0f0a0b040f0c05130c03050a060b190c0f08030415110a1d0d030e101d01080705070506040c05040c02030703020a110d05070b070c051005030118020d1e0e0a02 72
    0xc0400c1c003141e1841c00c5011990701405c00841e1380796480000c51404a1191456001281e5840e05118115494041c054001034010414080d403404c0807000788552086950101a81899140140300300380110403c0210350b0b044800e98191604601f170400f13455100710b6080700c8240020885440301003062090105688a4800c0141407002c1d00c0c13400d0300c16540d1102c0d6200350181c0c403814515182c0d28441041701c010b11942d0384030348000c4410184011103042c0c130040001d100342c902e080d441d90201c070750403605002c2003441d003502070b40c4a501c8155981c2c46558005000c60140c1001c20040c00390124500007120003d860030800185403079422071301c83c0640400103005801910742480814208650123501e02002040345922010541e6486c0c5400f0b059400410500310114030392040c031200044a8004000c1521002d045806500c1c008000e44414015460128010400c0800f2110341d58140c49400c8119103040101000a00c007410301707681580a0558400d0900100c8052003401151a01440d07038058 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 274480431 1250 274479181 274479203
    0x7060c021504030f140c0a0b1e090a0e010e070c0b04020906190608060a0603140c160609050109020a17030a0804021f0c0b070905010813030c0203100e0f0a 68
    0x9401c0056034500c803520606080000c2c0000302c00309200041c402240703071040c12a407100c0440c8440d000e040078014400c40e48a5110b4120400c0100c43c40ca084a4616061100b00c000312504201c6600e15402059401c82c0c01c6080780d030300800c000302c006d0b05c0903060b150280c000e42019034607014210b41e555580e0388000c002e6182100860014107119041d1a088000181110380d8108040710002031150b440c0d20180c00640740074240161401c00c4c0302103e0260000b4602802610090180329940301340c058181e16580e440014801245500c002c070484900742e000e002489140c801e810040d020b806101400c0e4803405c29040000b82d240c104000a0107141c101380055400c1440c480400d6034040e400038803d980150302180d00d2030170300b10080310784040914251035000e02542903003004007003044000c03e000c00b8007060b2001030145a070004c2025500a486005080d004070b40b43c034003241d400d07601040080d0141328054038403244000d6a040450f02084030740031900300500048a0990314241400301600ea00580 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 274481681 1250 274480431 274480433
    0xc0503031309090510050a020702041a2b0b010b040510020c13020a0509060a09030b0916030b0a0e010606030b040f0b10080615040e0f160906050a030b040905030c0c0307060c 76
    0x19820154156005a066031603081c5c032503101c0c4080d14004c0b50048241e07580052040114a41403203104424004a04002d1509158802041d448010009038900f80c031060080d513840b0450304608000000c1c6d02044413419541d44840b50104ea0300f0030302400388a540e84c030503141001d6100003092110100007e002036a80c0440c04100002035118820b0030301000020003802c0440e4942600a02000c90340c0e550b1064081d00c1d500b02040c9411020301340c98003607046411000e02803030409045005981d00460521070725140c010130b010040120750300c0c0031680e50a10100203541900359100d030446823030a680070310005c800540300804403024000c0d180e07802040d891082d12414400c11b00103502c4600601606030328000144200380c03580280d80300c11092216981040321075620300c41c840340c01c840540050050540d40d1036016101c620503001d8041041000f0030017030301441c444e400090086a0161003080000002e06100d40c072540160034204c0c8507c03071201215030604000400604640072681c42003410289 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 274482931 1250 274481681 274481699
    0x115030218072003131401081f05220c0e0109051005030c030c040b0706020a14250606051e040e070812070f06050a02071101080c09061e160c05030313 66
    0x111603e0850500c828410a01000d00003141100a400c580348407000c1c108a0300001410a0001070010a07503442c0c231461144202c4020101314103560003101c041c0c0303483c0610b140c00e15130311042c00200d600b101d04014151245a0704100c159200e0482a80e446540548550038401113140c0589440d0003c0ea04200180d40402e159020310380152040110600e810341c0c400c440f0f51140c100705030036141d81f03500042d80d01d0601d42020340e030100007100070842727030500000c0c002c0c45d03a03420a0b402c14070041042c410454020080703140c1c0190050030b0000e0082c2c2001407845201c4950008003c0ca40780200c2c40d0040450820034002400001c071129400101450440c0107410941500409011107400e08092640b43c0020b4203400303268400c600750040140c54100c20b0402c82210305003030036500c2c1130000d0030081c0304c60182d40208481c40101c0c1510020341c0c0d0920310083d0000d10915039510381d81c121002c02d100301c0c0308243e41007400956000f1030705024056101e000301600c0c1d100d80808031060b20440b960402200c46 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 274484181 1250 274482931 274482977
    0x1f140702030331050d12061202060d0504020a03050106080c011701080a0f0f2f0909071a040f0602030306191d0903190201060609080a0209011a0408011503021807 71
    0x101c0c01c400d0580f11203260340c48501d044c07041c140e8280480c0303560110a900b07812034400d84004001c9010040985950350700443c065108000210a02d141c89100050a40d160443e100c002958014003c0080d940d54000c403d4686500318000740c00950304034107e4200d0000d0b03001d0340e0305aa00c4100903000401300c541e41c4401c4000c1e0715008035441d06408090380b02046540e00411510008141d980f01e103110249080500105611507880c17150742c8603414406813420000d00941a1101221028001c504600c09003089028540c0040d03051940740501041c120b5000c80a9809401d00f9035990740c400d081000c0c0498916640d0151403800740f072507046000c0b221613402ca0150414251802c0e213107010141070481d0503c5000144440c0586c1d1031308020071000c0d900811020040850101520307940d4510b60014150300d00621840001814811100b55440e40caa030071a00101200c200810882d03094007041040440b040c402a44030f4507c041c58202c1000b414040140b0401e49941c50684c25a00e810a80c20161 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 274485431 1250 274484181 274484251
    0xa0309030c0c080a1703100632070201080f0108061501031b090609060e060d1a06031f0b070816051603060204090b06040f0303111f1407020303 63
    0x100441c480302021541a0500303201501a2001400031520703281440c480c501e00c83e840440407280d0402c1003110300c21042517a18242d420515210b46180c5445809038120b110001c1d030991060784644812042c20582802401071910070b884403006540c5d041440d000e000c40c2442a051507402c1a000105587c0411840000340001410002408844180004145140714112401040a10381c051040079086407401000b00400d190089040000e07002142203800382c92841e42c05076071070710a0020303403181040380340e0348400024041603100c0c90301c0c804000e04614980340807203092001440c0820340741103d0040310b10a0750000c40c0c2910301003c0c00e20603c8081805c1505881d030f0702409440c0328054010420500095015690158596040092810807561005a031500c40c0800304001c00148506410341d078100e036010b0400030700a80c0c10074070b09802c102c0810090b006030040382c401d03110403815550004540ba000301407020310a955090041e641d0340310a46000c0c0815400c600440302c40e44981c01081c0d100707 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 274486681 1250 274485431 274485437
    0x18030f0f120106030e0c04020c070b1b150a0c030b061606060506160303050a0902010206010e100f0312030b01141b07050616051c050304030e06091e240a030903 70
    0x40081c0784004104007a0840e400182c0c0724040a02d05502c1044500306000c011201145000b080725500ca40d500014441c10b0070f0701c000460361006003030064030140b981c0d40d80502038070440800005098000101124140402231408840c102101c2c4a407041210400300074088519101c01d0a0702140342c8841802c0032600340e51183c4010480340c0b90070b0083c024125580c2d0100c81b911429140c00341c00e0f2a401010b6590443c0781c041510003603039000500504490304072000044503220280d0303120021049812001814003542c0c0d00108018041c01030078142d0304240d5007000b440e101c54004681148101d880c8441d004005e001045100043c4040381090007070314421190312543e036002161241d009440d42641d400c0c80b40750444240001880184003118156000e4400225400c0c0050030074000903202900304000407800c446107403510b40454440d490014520002452851001e0429042d080003ca002d5114141c00d40101000f50510f0700110405421017410001100c000314010f00e078842c815420 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 274487931 1250 274486681 274486687
    0x1006090b09060c070306230907060e18040f0b0a05190b01030213030804050405010501020d0c113c0d030c080906040e0c040f05100816050d02040f050918030f0f 70
    0x100210420102000b5881043c3c0070404c0201000b0031019054000a0421104903000821006523008510b190980e0103d04003445848548070104812681c0e42c40c081e400c1c4d008800030321050119240c00d000d004d9101342c0c040501d554410740e0a20a546007506c201c000858040c400640180607038000c1c082540b01894014101004807180c80554251580295050b0900050600860403d0300426001d010280020600350f1301419000309680044000a0580e141c803060426155541c110301c440303520034104040b070032801058040c902009c0002508044804201c09441c9141880e0000d81680360700742e1640c0422900e6501e460189034000041c80754008401c01001c64100c84091010380545403018405440d07500348a000c00485440e500a0751007904500703003020281d5804039401e03510888503290a000c9200c3e4210940c1c1501442c1d60100860b40045000305044c0c090b100d020003220021030301414143caaa03200721a0101d507181041c40c035500300304401003440130048002c0504481c80c0a01c145 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 274489181 1250 274487931 274487947
    0xb060414091f230a051e03030409020a02030309060604111c06090e0a030908012901120e0a02030c060a0504150212070f03020606010809030a1b0203060a090302061006090b0906 77
    0x82c12a502d500410f03500880140500320f41c42d0a0707144100352030002c3e101505941c1c285030004000030310481c44070804c1c02401d03079009480c2d101402610020f2014000c15920f070001000043c0d03d0390401c6070082c0309440b40100240782464280648000400e60270040c600d4940080d4124031140400d404800100d03441c0d1100190516880c0f0540b090784030510302604100c1028500284200103980c407010060307040c4548102c40403000b04103a450040070902900f2202c800b1001a200030280700c01c3c100045162605149103014003040b00c008a600c00c030142c82106601e1707410000c25001c0c000900c1c0c00103809200900008005080400c0700c06000e0045034520908501441007650041008aa42e090045014800c0580401c400d981000382400d007034a4903e00303008174030343d280100e09920040050009411205031078052002c0c40c411f07000707419034105141080c0818044c1c01e280108900522640c400615004000017501050fa0642e0751445015854030750702c0c1c059604090510740d80141d0801c00d10b9 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 274490431 1250 274489181 274489231
    0x618010b0f130b070c08011a010302070201030b130e010b0a03080d2406050d050c07020d0209100b030a02090901080d020a110f092a09010503060405070c02100c060b06041409 76
    0x760043c28440c8405554000f20301e80405500401d5019841036810700c03059a07444808481240c442d84002e00c0c006845244900040b00540041860582c115043e100890114025908100c0311900e940c4000e119500c40c0000340014540a444050030184080c050190300450a800000c00e2007048441d080200507005060007180e0341070740c00a40402c0000034100d880e21034034003d596222283e44d1001d0304002d1680c0100d00ca185a800000748103151180000d0308000912840c4000382c040880e00310384a10301141100c0080d4458641c4030320602e440e81c000910410300044040809c00250302506422000d40d540c11000009050f0703031070340016240072400150300c49284461203103d00d115030f02c1464482405a2898440c40d43d40700c0720300c4c4020400c0042d06c3e608603007180d0301700005541c00204c0e03030f40d0810125900d8220341130003580500007541e440c42ca50b0307110540ca48454004c6000300064134008081199911452080c0340f40c4180492240c407540c5031442d81184d020a810003c0e00b503100c2c441c0114 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 274491681 1250 274490431 274490467
    0x501060320010e010c0210270b0403061503020a0b0306040b04090b0a0b030d0906051309110408010b0105071205071505070906020c03061012050c04090b0105090618010b0f 75
    0x180e002000c070104600541e840550111251000e0a1451460a42c0d0300031490100301c1300c05180c10300c62156035807005102000802c21210700705214402449403034403d40040350703100b0b120985005043c07000401040c045001850100c81d8000c010660162414154107429000207103655481a5540403010701034485000f00c1c042c6510441e008000c625107403201c2d01c1141c1303084450900a5000440540503a600400402c0a41e030031800c20a44038103024042c981c60824075008001c0c1e1509040c2c1e207000e20010040a4010f4a0101000b48030321075005004681c14000e031080540380351100551014a00e0282008182560090320400022180094039106484041e2140c1c0c00044a80c4001c100450303050008a402010403030241116040c1a40120b4500209010302c104801011000d20104503041040801f4100c02400901c0307020400d080040406c82e00f4070a00d40242400e50020313000d45440c40021901810714520f4070303c56400d190141c805a00400d221054583d82006202d061000300540 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 274492931 1250 274491681 274491713
    0x105010f1a0903071206141b16020604030c0e01060815060a030f24121203110c010905010c0311070b0a0c03020714030d0c09080a03080403171006020106050114070f05010603 76
    0x3c510015441e840c00a00701c402e00702e08240c0a515810a0005440c104500000800152012235868000c98002000c0104d4a920b00035448180003400104001244c6010000c482d00c0d04c0c0c2d8820701da03985030310540d01541c044410022004070120410018500b21703000c2c108c950914a000503d814182c0c030841c0468109914034010401d14111200010010303400c03100140c840762a22004540190f5184018a110b580030030302419101c2081602440c007d40a03505888180c0001340140500750500900070b00b4540a80da000034105801201c0d0094104100c400444e80314400018565844210b68005d00c100150325082607000c10103400030a409088051082406001843c0e4410041010200b2540000c01c45401e000743c40030200044540824001d008681506009001d50307654501150003000f12205070811034298814010052241401c0d9420385000b0303002040708a450b0001901e65580c030b01146d0a8101301000140d0004002180b00c2e14218420780011444649075900c1c071102c0d0140e520 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 274494181 1250 274492931 274492949
    0x5130506030a06050a08030703050910050c0a0b0f071b150615020606031513030c0206070606080d080916050d06090203030a0503040314030103030c020402160209090705040e0105010f1a090307 84
    0xb06004da441c001c00d80b40001d01008004516000c69903030064003d009281d41c140c1326504800c0394558060080c4100c0c1e06416098054480d009090710f880f03107001d40152403050b081c110b61030000d22414040c1299480700d081c54150164003019030f075a440c52010540a2294181d9215100082d10180260002c0708500490300036150350b160090601d40b8094581c00e800d010000c062090003081d490300798040060540501c0d10b07490449284c00440c21511864400410f1980341201c00a84c40c0e0022485030607941c565540c42207281c4404a00700c1e40c030841c04620500300b451004007003040d841d2a4420640d00c91140d500801e040c285038001908580185030442c0c08140c3c000100402c00d03522980b03401048000c5c050032411541541c400500020039558001e0080740d00048080f48000c000d92040c070071640c0204804000c3c584407444644455107840340900540c00c040f0303035206c00c20060154505848500201132412850b00c0c1c00356101c9110000c0340344404404000032402c60320305100480240074645 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 274495431 1250 274494181 274494191
    0x120a1205060901051c0204091e1e030c1b0f09050105030f0609070512070e0406050105120f0a0305070311010609020c0c030624060f1602131b0e0f0a2607030b0705130506030a 76
    0x80ac100c200d403c0c140c4605031140a1544040000a811175488403a40343c005680e0300d4208500144d002185805030044441540741042c001048012504102d058480c04d400723613000110900f4001c0d80e2280b05444010391034000c0d000a101d03604010310803100185100c3c0403a40706580e50384400c01c0c075480c160b40c11f50f0300d03035110380043c002414582849448001801c00800140c1c1d2020740c0d140e00d41c1840c00008040101c006001414540318074007102040c0c415000030006940d48a640c00300960040c810b41e46035008483c1c16440a02d000b01742c640c0301c5c554001c040f4480414022401c01000310304030416911110500120344483d40c03010140c5080191004d038045269514010403c0210800074030704415802c1c0869a0180701d0000307284038040310300d82072409040c0b0400c00041c1c0040f140c03402d01ca030410403a510004844102070302c0c1d155024070000505009600540701c2c2e5440312458040a05070300c000c0000305504070710450041846000850310310454030b495200042d00c3e0742c0156903400700f2a03207034 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 274496681 1250 274495431 274495433
    0x70c022d030303040305030c030c0702040e0c04050105010903020d0b06010c08030a0b0108061e10033e04060f0807030605040c020a05100203010f0306020c120a1205060901051c0204091e 81
    0x4910250380c0808030001c60a520b0b042d039004180388001802121111380105c04107514080603010380305080e0703000748284031442d8645c203083d94903101300145a01c994240000005d0950141101c44181c079000390035501005509c1c2c45410500d003016040ca41003003205c1c90042c000c10b50400166028940155021800020860005083c8000500010301c01c0440c406020403213641070b148034980c40400c1d14454046068540e003a0020400500580c03c4200c0a00d5000714005c0880c0307003104890307850380b0208180c66409805007028040e600403c404200e50160241b9018051030302c0f607034408410710b8040b03045d940300c10100c1c2c180c840c0c0b03401d507001680c0800d001e201040001e01001041811074181141150f24041c02041101c40c41c1c480030f485141c0c0040c0707066982c03a06110184075850300240302540d600c81c1540040580e44500c070412680d030f2030080030540314640304e801107049810003404264540305800003c11030b1459120105d0f07000d681c41412400242072580b4035500360030114101001c042003 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 274497931 1250 274496681 274496749
    0x30307021c05070605040c03060e0102040614040e060105030a020d02070c06111506150c010203010f0f120308040605220305030a0c09260f010501090c0e2205070c02 72
    0xc03041000c0c0e100c2400200c1d00041c1c2c80400d88030001d4210b080881d25072154141185c071440302e500082d006070700704501c0140d0700b44150024401c4506964890302800b44402071a11035001d54050054030800343c0c03020030540e41c428809580c01c2000c900c4010f1030074a04464590072a40810fa00b03c07990500c2000030450340c4d0b04162080b030158090405096101c4045910400580c4003c2000c1d118031141d10807500d14072048000d441c210b001800085540396110103100c6210174480c4110310701000b40030400301d5200c51424540400c0303a419140c1d8011a01c450f600e01c1c001d454024001a20524441417208100c070b00181020b50080c0240c641950784d0030f00713400880c10b4541800c80003041c498015020840b40c0742d80c04d810045a060301c081e100c2c0c40700751101e00a061040c03030809031003258200000455030402c107070310860050302c060f21540d2082c6182c005000b09503d00c00c04c2c402144003110a10210818a50809980040585400e91990845a000508003072000c05610b008007004c41c0400c581c042d03 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 274499181 1250 274497931 274497943
    0x3011a1c06141f030c020a15151e12020f031b09180c040f020c07030b0f01061b03031a060f0309060109020405090a0e070b160c060521040c0f0803030702 67
    0x5010385225010f42c0b10300448030001e0010282c03560406607100c0c11038800c0d41c0b082c08030500895100303051006c0d030b0b2080146800509100c1c20303080d0509000c9140092a0071030b1f401c40032900a44100c0c16403500d0b160110342c0401c0036075140141e030801c6410004290075601442604180f0030000e410311610314000040c000c2c0954000c261039440808100315041c070001c0001c0c03015055400b124003062508903000e800010f8040c400c51040c182c45003070300c0842040344040e580340c4102ca8600140545a9071000d048032a11150751b00c800070f40810036a0000403e03c42c0e0007440103508640c1c00000d46c1018030000c18541d60110300701c52480280442400b645a2061110ba401460300c044154140740c00c0c54009490300d90064007031030641c2e95698640088030410310a0500900c5004c0c84140c440e070034440003860b50340890500b10340380c40c0790302c20116056010703909407429184012284140300c4441149200364140280c0300352140c050341c82c00064015942c0351060068254600515120300b49188080d01c0c2c10 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 274500431 1250 274499181 274499219
    0x601060e011e020313050a08070302090c071b090b06040e06061b030c0313080f1e1002070602031501020706050415030b040e030c0607031109130e150711060c03011a1c06 74
    0x1480400382045604400030350720040d25011038082801c1e8580c08010b370018810000c000f001c1c0001e04e0385031405514a003104104032080c0810500c40344418100b0090503209038050007400c80d00c2c060110b000c5042540280c40805800c5c4c1080c1008a82040c002c1d2558026106000150340001a004070300b10500440c14002c0c100032006004003110440d501e6180c4400c07141c04140700c40e10381400c0c1501030081010b1032207404030000441d5201080d041c100f0107580100c44104207800e0b061004890b03940b0000d180001c4a1440d6110b80c2481c1c00d00404000170300c0c00d070001d20109500c84108469507a42c0780702d0207141c2c0005100560390394405c00400381c02e00100510309800c5c107180450607107078052400e0403035005460440d1109545030308241d0401c024541e1081c2000580b06145141100e000e5114489010f02c490362507090a003629520129900d03213088036030781c4249a06000400c02c281e08060158100c0c191030300d0b62428414000480d00c41c2c2c5503603100070040d8903100c0400f000070881d001110b52002c = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 274501681 1250 274500431 274500439
    0x1803100f1b020f0c1504030f03090918020a05010305060f0414060103150b0702151231050a120221030103122a0201050d0603060b1002010e0601060e011e02031305 71
    0x41d0343c0000d580b0b40f66040c0100960103440748503141c1600d40c052204490142d688070800c2106100700d401c0050000c0350900480615918241143c0c140c540e200d041d200c16281d0042c6008a090308180045020741405031045801c11881c00000307a06076603a021f4121031180840000c0d045192a200040c26100d601aa0a6000d180c0c160180400062141264400c41e0140c0e132030716003414074451068003445110003032400f40208805011806007902141d0b083c5580100f444413144030909035011206214550040c02c50344a401401c0024480b401a809400154016280c0c10802503011107050399039106035100303a0720000018010000d0940710301241035220f03e400018002c0d08001440401009840350f40498042d00c1c800045a1045080381e02022910200f070080554a24122001c2c0c2500d02620340708280030251030084520500c203030785143d002c00c0000c2506034038002c000da50340d010340c800c6181004055a120300303440c201e48004007900c100e1540210364a9810720024680c0c550150022486 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 274502931 1250 274501681 274501693
    0x50412050301050d030804050a12020307021801080304060311210405010e060f04030c060e0709020403030201050a0b06070f03020304080a080a08151f18080607090f0b1803100f1b02 79
    0x3e80e8880c050240d034080c1c1d050034241950380340d07030800e907140c11043d04005100d03440760049101e4442e80407025103006442038914100c0304001d411000d494034424014001168800c0c0000c00a0307a04c240c0003104000c0d00c6950302ca2404080510348480e801441c0007020041c1844002d200c200082481540e041480b03a5003d0b00e0b1508056041900643c03018001a040150300041c45061103195445041c40e0102002144d01c102d61311202c94003c1d40180c40705030050b500c0c0000180184c0c5190040d0406800c0003400b103498555141d0300c802003d00301c4c4005800314402440082a000400c11001031918007408240d52151407400008109420051100340101c4154103030303148070340365051841102c40034040d802048500341e500441e0100d1414059200356624004002600000410780354003070f02c6181e9a0048007600c0d404081645007003440b5580b001394041010680040440f42c96004120004041c1c5810b11801825507060b01d040074280c00d8103e42d54000349007501801d10031184551014005008 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 274504181 1250 274502931 274502939
    0x2030103021804020f1008180f2808041e0503150705160b0414010c0c0f0305070c0902030f06042313080415090f0b09030607120f0906050412050301 65
    0x907020070001005542c0401240c0490110b64500da003000360140e0161100000404540c00184004001c0ea9001e101d001595500d101c00e08000c41d5441c003950740c800041180d003200305260030040b943c2130754400d4590005184100060395100c01480144124041c0d04100f100095030100800305541c0814400e60018040c00c030304001070110240d01040f1420710545455803003418280d0701c548880010103070182a0704000401c000e1003680521400074900802103400381d0002500ea410702d0480190070b0060040950000912420040c01890320651009840c10303030b24414401642c0003500d81c5851100c1c5181086081d0400b0320038403003007040c4140006030728100c030650ac4000d000007510800c508000c2d05420701c181304090084800516086080742e080f886609002803070300300c2500401485080c41c00c00003401240250a0b100e0602d001005025680c4170200c09540350f00003e8031070384840b81c85054040c00000e10f0b200300360350b04d40250004101c51900c0c3c9400f00402460f40c0125050010a00041c0 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 274505431 1250 274504181 274504189
    0x90b010c03030f021b0102031504090c091a100e090c0f090d0c0506030c040305011803080708090115080c09180a170c010920040c052218140a0203010302 67
    0x52109805090005810f203c42c4020b401074845c0310700307202154404492221040d08154001c611481c8004131b0b02c0c200305055420481a14464100544801182c600900a04040d0f0340300310040003030078400440f80050003012a40340d100701561100483d141705101d0296003425111242d20040001101e40f411400048200d1b0764043e000029025000d8100034404008040e04403402502c001890b140d16481c1140c40d98200c4da1146c04101e07019401c03c203001038401c50a200300140d0990589411a40756104c05d8101d8035048010082d203040d64031043c10400c4107030805002c0005d00244c030080c0c1003001c0720606202620f40040c000080c0c01c0703085211000356000100340e54041c0d55001103001c50707811044c1c00718542d5000701000b0105a510301054a0100306c0034a2058003c030b10308003082c41401d5001410401119403210301c900104000b04205404d40780c0b00142c510114030002c00040103640c4510601d280703e03240d000e02c0554180c1e20001c1c03481380e80f90701c00e0703441e84001000000d614560441d0b000c1 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 274506681 1250 274505431 274505447
    0xe04060f14011e0e0c091503041e1b170f16030602031b1204020103050702030a0e100203041211090c071104020a050409050702070302010e01020703020a0b0f0c0708070f090b01 77
    0x10400d240240c00003e20003800c1104050040c00071030205015070512050307005060f03100d544505c1c07188110050a07900d030f00d64001a24881c0c3d0300804c012000c0b40021030010041c04c158242203d15646009440b49100f40204411f4091b00640000e5001400d40100b403515001f2112001d1030340d5440800c019948001320b10b8940241d0b580007401686948403101c1084403800300484240c40071704041082d800000644400503c643e002741d8092100c1e490310a4260b0301d03072042c1c001c69400541c0c0d42c42e03009a18100301b00d00c00348407449481102e25082d62212424181440180c04989085100000281d1450041c640c40d4000d1503040400c0d19044581d079607006d0800c40d00313950340d014603000b0841100e01402138003030710000e1034450414462441c2c4a10020344501150004a010035086000b41d205948005000c03001d80358007400600300b540c20703c15125181d4024401c10710813851f0030480300e581c0b600c040c086103000303100c080000d152290410100d41c2402a9540101414514180c01804d660307a0103802 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 274507931 1250 274506681 274506689
    0x3031305010b0f0a180209060c0c010f08070813050f010e030304051c020a0b061306032109050303090603040609020d031806020102120a090c1e0306050901090b0115050c01060e04060f1401 82
    0x31200344c00290045c80c3c8064010301084686c000c4010445c00c0316401d01050444121400340d9414550080b007907400d581124054860a000541c454006018084584980b42c0424000c004545020349100c16035402c2d501261500241c43d040403041c041007203010045e2125030101c132820520203800340b4000968a0035100c1000d009000880045203290b1103801700c0e003e1400011b901030140340c2d182e003400043c414542c40020544daa42504030001c00d803080c4941c1c001e0b503030000d014500d45002c59003001050341000c5c00a603130140d40c03140250700598a510311400e03628802e49400e10010315480290185480e142d00407425640104004210588161410f55100d0b0b90480c000811881908040c4034a45094120019210510503050449416007402008491054038244610394070b07581d17118281d4400d0a401041641d0803030040c4240500343c92107240b00441443c0030b50070031614503507103400d46099a2011003180840010700c0140251401500c038090002c1605201c200d10100152a8030001441 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 274509181 1250 274507931 274507949
    0xf0406230a140d2607030e030a0809010e03010f060f03021002010e0d110c0405240406080a0201050913050a020702130b0d11030703150605010215010303051804090503031305010b0f0a 80
    0x1008420000d840b0790941a0204030061350003d002080e083c01c4085e40b007450240c0115413010181d440c10f107000207008664640c00840641011400700042d02e070480c81700070f0554595203a04111030089051b07c07445000b400f0001280b4403c03071550045c001d0020390151410116414840ca16580c030b0300c001008400f05815190030500b61100c86c40302400e022106180c3c640c45410001444031503040d41c0c40c0020001d9020011803401c06550081204450851081c00001e80040b4900303405580108080d0001c1c1e03d001e016800914441022503040329400c503407520206501080301b805500348040c1d0b60341150030340b400421041ca44c86000403c05021804014100d03110100000c0682d2806d0000d40019540031000910384500c152402000d050790f4050180184217100300840b8075014040818122505a100c4c40c1c60a0140101c28048a6407045050340041d100d4400700d00041c0200300461144d84485080ca8a804a42c6412030039103e0b01c0769014800d04814a00450035560900d42d5421241404 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 274510431 1250 274509181 274509199
    0x6031908090d020310060305010507050a1707020304031b08011805030904090201120609091205040f0b0304020102010b0a1d0901150e0a0b040603080d0c090b180f0406230a14 76
    0xc00090000c21050b00c0080d054021408550b204d00e5964000c001034a2240c00244102d0340c2d2240121140e00410000400045200cc00032440a405021544d0454010310580c1e16041c1c82e40c0340c900c150b020007101c0c10010030004908000401081c42050105a0801c3c940141060243c45155507405401004d611460740c441100d000c40e0f0280601c1402080d2804051201035680c1034190020603000b4002d0340c1242c0c0300c0c034114100c0d500c50800c50b01a9180d060b4144441420900302c18800d400050049042d590303100140d0a642d9140c1c141580200030300c1a64195031011400e01c2140c00901034083c407066810010039240d40400c0780504400e841d0140c0c1481d550742c3d5401d6803080509414084290000d2401c000401400040741c0200101d132030b011010300003040541d1f022502e0311800d00c199442e403203081c0300607403911180c401b51003d4400001c0c0b05521403166103001904580941d071203000003080d0648144190445251401486402207446400d03052808c20f0240c006044840c0087c030818480d = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 274511681 1250 274510431 274510447
    0x9090109141b040605060d020d200d050109141f03080316032412031806030203060319020a05060901030905010c0503060f010203070209070804050a0506041514190e0708101406031908 80
    0xc4d404ac0b8850300d441a1729022240600003c19400c0c4d02413901c1092950a0000210340320b003550046050b8000c0c980030034003466071800c00c005000c0008600c1400c01d408203010000101d0081c0001c0c60045d17000c070841c42d042c3c040c0a02d002c1e040f01d60141e2040c8980c107500c41c0800782c0e0703441c8012010072103003541c0454429900c1450116094000004480306102c5910008922280c1c1907001e1407043c60168200d070340340c49101d44052291254410002e41c0154000001e10840c184400601301003c1d041c10040b0345030b10030303075115820b50703030001010000280003104001c1540f03420a100108954207001651030404250003003000c91600500980c203204450001ca81000020011480c0c0301750050182c400314103080c80c1c41611407182210b01039600f42444c01034103807000019805809801041107240d10007408507030700c2020340300e00c0303c03041309500036001e000591301c1003030150001c0c0d600041d40004003004104101c03107143c130002d4007883c026400114142903034905492500d140d20b070411100758540d04c031 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 274512931 1250 274511681 274511707
    0xc100806041d0109030806011d04090f02090708040521180312040e04172701020f0706020a060c05030907060e0d060603140609030f0909090109141b040605060d02 71
    0x8020395110741c01d00d50385014942c2d10701903000400d800d20a640c1d414440d100c440046a152601340c0c2480c800c0c03280041c1070403907440e0640c0510040d40c4600c0c20740c02d40c03c1c05c0d5000607980c400e0444144020036248070420040110520001d0904030025416548009040030f00c1c2046000c1c03500c02c4c2d13021040000003072802d582d081150700210010480e6860740d8030303150607038a011000269401ca0701844000fa0300200c0307103241c00a407201381501103250183c080040d8401100010240e0b100d0741940104800c0645200080c40030b40f0191565400030082809146440c0c0c044400400310071007040300600c240000840c011441c074003129010b00c0c1c4500118844d0340010040040000c009006602e024000000c0106440e414003012019000b0340c2c03029038540c1500c0340c80740700300354031401900000c00010216240c292886070300021200c000003140f55165482c01a021542e0702c2c01f420341d41c881b070780310a400804d40c050b04404e588107450502050f427401c40410480d00035101c02e42c80b1a900410b01c5455400 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 274514181 1250 274512931 274512941
    0x30f05072c060403051f0209060a0e010c0c0b0a0e0303070c06080c040803191706030c04150806280608060f251808160b0a090b13060e01020c10080604 66
    0x840180b80382c0d5030316500c1c90001d070b80d190041d4043c0c0d618440d60040c05002019842524180705014018034a4062480401c41e06035901c030741a181444020185440403441c00307100f0754040d004140d4000d40d02d07942500d02404400c0d20380c0d0071501c0b030b9000300903820000b02c10141e0002180c9503820500a180c07600d803030315079560085410140d900d06c8003058800324100058503103024100582c8034010000c1c40d400745024270750812660243c2552103134092a05da0b050540c4261110001202620200740d01c84084030f09041054940000c2010040d180300c580310302d00181c800c50115807190401c0460301c0d017600d1640b280b40040c00c812080b000280028070084100c5c54488035031b842c03074040c000007221015014002044503000c0520380c1051200103d00801c001412000d90044a04070380c040510701165060140d016450610820507080000207043d2140f1000c1c1c03a00a04000300000b403d41000d1009040c0361420103024110351208840c2d00c1503407284c5c1200d41908403240780c203141560b15140460b01404c = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 274515431 1250 274514181 274514267
    0x120b090a1416050907090506031003080c070509010e01080705010f170414071a180102070b04060e0301051b03340c050f01050412030504030306090608030307030f0507 73
    0x151010004000010110b01c0740340900b00e4512000d038203510760050068402c000c4500030045888080184030610780500030b503a1098018104800203a22980c0e0881aa006042c114600da409014103000f5441d1024000d0301401c02035240442035850100e00e1907450705503200b01c40c144108211084206445104041942c40c0c00c00c00440d20390070545003e42d1502c0c50b2890000490180020109069100075401d0703280503410002f40b42000440c400c2031442610240b00c00741944154100060b85810b400c010b0b000410761a02c0300440e40b89114285802e54800420f00300044000b10501e00c0040c402205581d003040a0075401210200150b51290f00c00c000c8075150b04d15254168004030016a115111142e140d101c0d40a450600c540c818103242625020380d0003e148000030b020320700c41c1c00d01c00c2c1d103c0790380301340285004242c6540e517640d0740045840b00d41150150b90800410088415018050010202c031900c004006034030b405440109049407400566021160b040b00080d520702d08141e81600030 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 274516681 1250 274515431 274515443
    0xa11040207023304060c080c100507020307050111030432030d0903110c061b01111306180605030a020a050702040509010e0f060606030114042306041104120b090a 71
    0x1004045940b841c0c1c0f0201c0c41d0038100d0181c00c6601c4100401244094038101d03030f0103454411201c05156210b54a94000c42203100d4070b4802d0329010011a15240230351806004190041c5580c0c1905040ca1402d6a105c12228201540c0402c10310000441544c0c2085152002505101c1000c908401d0700d4985d00c202c481180b42884041046100f8403000c1d80a08080c1d84a916102d042c501380d001c205448684c1d100d0500d600400601140620458034040c603028071609800000384201010707407140f20341e0410b8101001c23a074142d400520581c0e03001082492565208440c0c03044071403401038024050b11000300401801600800d40406940c0a40c06545071254024404d20032803904c0356803540207102c0345110744404d02c00c41c03003003070400354012620301d000f00c5001c0d00c0b80b03145070308010b0b1050081240b00d00185e00b10b50366001010070280140043e848480c3e06454200150400504000650b0050b900188014030100010003500e541c0200b940011640044c07040c04941e500140e913070400140c0e01c405020 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 274517931 1250 274516681 274516699
    0xf072103092102010e0f2802180601050403050708060f07110d050904060503030301180c0c0b070c020f03030a080103200a17120712021b030a06050c09032505010e030a1104020702 78
    0x6406c402241c0e5074038015140d8600311140404031100e00c0c240c0e2041a0107908403c410f455050702c081e004090340e81c40302040c14454070b051b6503981d402d0710306400c0303912140e0b4580040003803041100c1d0201d180e0303800c0025803414040001d85814841d441d03800c40c86070001070140c0020302d220306440720b40015006000081c1520303181e40e5281c0080710201074240506540c80e01d40000413101c14000c2141c5804c07190000b02c4a0300e5a580e488056401c0c116100f01070746e000045e141c166505030b504000070158082e85a99541d101e514519003a02219140402c400320318504004190968072030703000e0b8004544000340b210480e1070009510034106007603c032402c140380301d002070014284450110484c2d482c04140d821143d1042c601322827034040c040310028440d4141c10040c0c0709008a0115080301e504204400d2040d85050b0720a80000c3c58100ea084042c2101d0a01e001e4140c1001c2003003220300300074882820300c145640503c9002a40300c0503210030003031542801904844076a241d540c16144099809421000 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 274519181 1250 274517931 274517953
    0xf060f240a020c100203070c0e0a02040306020a0507020307080d02030d09080d02030c04030b0f01050901030f05100c03200903150a0917121018090303020f072103092102010e 76
    0xd126a003100007913014070b103420303041400503200200311380e0301d103402400080c809410013606020110003c2d051810441c1c09000100c0812580e03c01031959a140c1d07117034155500260320515042683c0c541c8071103180c0d081405d0050305660007004032a407210f08180005401301c0315203410101805092542c840c05071008c4100200b1003a05401001920300840c500c60300c0741d44008a4490000d0309029594103d000c400040001a800d8007044403514401d50a41c1c08206501003030004480082d61003030006600c55002502e510780007042030480c107481c03494242c0340044a2020a80d65140e10442e00d00350705401000400c0344429034005c80c0c2590344030042380c00e1389801a030301d52095080048110085600600480c4094070b9200801040311800044070114070911140700d0000c0040070416003d140d000c01c041016110864001c04030940b01d5840d03811010030841e800151240306d502b4440c149464081c142021404660702c10102c0329000390040c0d000545683c0c128054502d01f80304400038032030303444450 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 274520431 1250 274519181 274519183
    0x703030c0c081b060f07050604030905040b031c0f02120a05210417030a0f050901060f080607081302010c06020a120f14160519080105090f060f240a02 66
    0xc0c41440c02011460665521112102d03102c0c400c1c0c0c032004a0f01030450780000e100d42488800783c100891490192805c012503a1105400d0110480e03040700003818040f0284440d25103880703000185103054009280b06000e5104050710007640c502c0e12000c0c803111030789040541d0320030044046503e511003a42d40d111044080701503c01e07008000c1101d00425031900ca42c64000078689018031aa40040e880020485c0d980c8565800b640098a003259464544400e404201030f18003e840c003807000400001081441c001040142d07102d140c000c101240c0244050280c107a50000711240c12203170811200001c1000d07440160b0308070440c000002c00290002c03c20b04070654100c454450b40b000e00d107005001c4d40003400c07050401c8909180a05242d4054800414440c1440641004240050b030130420f15041224050030709069680035030100260a83d0018482d500b040440c00350052000401c0003110f0030294002000007000d0b01d40b0f41d0240001310b149541207040d00c003844c111140722810860751400351700002 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 274521681 1250 274520431 274520447
    0x2d06030b1e03060a09080405060f1206010306180e19050a02010f3b1810060504180504060b0603160809061612110406030605010806181302030f070303 66
    0xd00c148051841003003020301e019529024210014003038502d980e42e1080c0d201c0145004d0b941a20003070000c0c04003048588071a401803141c11092140192203159801c0c001e031021000400703e034109428580100000d040c861002d1180040240010502040b4468000e25110b003000248075015a009007190a014000c00d0b0521014000c1c0d031941c401901007807007500c43d103400d1b991a0306204c0c2d18a100400406024111321a582c48440c81040d2196080307000030fa856403840303032001c50101c10105200308042d050014030300422aa0a140c1c2c20f042ca8060040303e00b0b03c0415070000302d952100006010401a07510281c2c0304200141503a0700d0b400e01800c01c7c410390f80041c0d500b0300801c10030070125140f20000104a841960815400a24907458800031200281a04001c50b0b03065114600060180b402e03101400180800d50350028125140c00d000520a40e40070b419103002d81c56445100140d0741620241d42c1d07100680202d560420800c51000c207240450011141c0d031140180140401015401204 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 274522931 1250 274521681 274521701
    0x914070c05160b0c0c01080f070302130e011d18030f0a03140903041508062b1406060a090c0f03052706090d0207060e09040309091a01030c0314012d0603 67
    0x205c441c1402110019100e11406450310804071142c00300041285100f80c0042801ca002d101101d500269a5190203900e6002a00040010801074004803031a1425400c002d034403020703c00400080c8680c45407130507141c2c07003004440200110000342c4c80c141980a03401240d128800181103c00c02c1c030307242d0700c803a45035000f80c0a9011500303856030082c4415840790710014002e1100422240041e010b0100381814141c00c009044080d00c1c0000c41403021558498040841040c40409000c99140100c02c1081c2c1c0350654211081f40e81c42c041081d001c06902203181c1d100c485803030400103450b03102c08130b06e5036202c90b0300c5030490f0b15074040e00118500014049030340d40c0202910003c07a4408105a8400d9854101500413a0f0002d400c800c000002072400b4071105800c05d00074100046015159171403241920340c10300c00b03854440142c00d80500c05503818403811004406c00e29040103030007110854401c5151062040111081c5000e18010591000d00c0c511031082d115040c00d80f0340982d03540005800350051110f = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 274524181 1250 274522931 274522933
    0xd0603030f020c01140c010b0303071b120807060506040e0d0504091a10030f180609120503150607171306110a0c030204020a0c0c06180914070c05160b0c 67
    0x1d03185459030000450701c22941c4140c4901d4242191706242c40100d42100d0b484134425901c2d0701802240361001d1004010f602c0c01185081c04244000014241e501429440442c10001c1085447c0210701c4036002d40f1026a8020ba0102c1d25859038000100a0500e4544c40e0485001d8204050a1980c01c06c0081085079002d0b0414020000007030380199081e940c50780d04a400c1440020a01500d0380b20758002d480c2040d0f043e00c0000c4107442c851240c83c43d04109031013107400b0b41d40d8940303401c00d0060001c222100c45809160039480c500c2c0841c0100c201c881048061030007400003013050010010300307009190302035094030354641c1c450070011850030765910140b01c0e0780301003003600140010f4407001084100e0ba0a170040305240d1300038515824032000398810340c400b00800c03207031029020000d03d05030018002446156580e544044411219400e0809241d0002215070724004104054225040360242c1c0252a03007404040f0303020605081e0306101d0790007070021640301081e4010030702d502040058464140040 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 274525431 1250 274524181 274524197
    0xb01090c02011401030515040f0602030a02070201031a0307060c050705030d080f070203040308120a0f06180c0804020f01050702010210020409020d0b010c11090c1c050405010b01080114240d060303 86
    0x2402e083c801031007800013914a4100755940c020714400c820140350003e00c2400c00010f41800754075014100d800036034510181d03070b40008408066690501500002c01c1c0b1010b014032a40090100003603850310503109400c28441c613901074605009090182a0090601038283c43c20240b250400400c625400c40e0303551400c01c0c140011940c0d0910010030344007581d50042c280352030240400148821403030005d0030034140303a4a0340620001d180301402040010070a4541d9450000300340c907c00420f80d07204184003000c0109850420025a07102c1d2800340403000217082c0607030383d02d1301c600040b814030703201840c02c1d980a4000640090039107012750003407042d003514240c10801c42d0b08507401140e01c076481c00b00181040f52888503090f80ca203840c6100c2600020038840d0149000440c1900d410024140701182d504255500304110030f000c030070f02480c1418242442c01110b5981001e80360104179030140d101e64040c1c041c800880e40420b20701d140329951460043c031a6619001e0030903a24000d00050b001c1200010b044c2 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 274526681 1250 274525431 274525451
    0x61c080c060c0c0d05091210050403020c010509090109180c030308040203071a030f06011101150e06030a080301090c020312040b04061a010c030c05030d0c090f08060c180d0b01090c0201 81
    0x5001d035003043c1d15003005801c1124241c541202c41d40c11030701002d0f911110701d90005030006410410181e40701504840422907280c6410040e09000d0b25078a85414040200100c00403503503410200380c155920071030700284810340c0d694840880912102d000700414400312001c8240754016039020722503442103003103421960300e81e4002e032a200e00c02e8a0401e2a15414000314582003503940d0303690341c410010700d06010002a00420b035401d5418266034440d000e94090b5051003003002d02d00c1e82d103a0000003070f8001e022b40c00d01c40d5902e40749488148924030b052580c3d0440034a04da842482201e000800d90300340700c920360074942007a10440e10203450840b111860400720034183c25030381a0340c04081005844152488643d61400e07594410340c0d40045407140002c0101c103030344850520546294244a6580154a40c00d12008149900054104142a501203410003c030358510204503030403541030a064682c481c0c10000801c441740400303140205414003100010481c056180e1100c420821194001d205005030 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 274527931 1250 274526681 274526701
    0x5040c030c0812120910020d0605120d020604080a110a0606090f09030207050d05070801110307020d0c0c050d050c0d050616090317030714030c070215160605061c080c06 74
    0x3c0207201c0e070f16260500190310344100b500001c681c0110107000359160001502c0c07459080b42d0007071200d41c00c0107550310400e0140d0f0901d0810310307042282200050041102d01d000103036035114001c2000740340480000c1c032195841c0c810f8003101c21108416040365140710341c2c1d241100203048107015280f101c615080a200c00310b00b01d400341c0303140250540c0141149600303080c00d00124030300000081d14603100c0c80000044400f0b00740701d682101000045507503140c3c10606002410900010304d248200446255440081103440e651001100d9084920ad0030341c7c850307840c0a82c10f0100b19003500b40c0c8102040040424054049806441810303030a015030300c015841c070381c1920311540f2804050400c1c070003840d4140c07142c2c4441d0015908010681881180c10340b440441d0080e039801100e941d81c0d1407002003401001c609001a6030302803038103004011424051155542d00e00300f08104805032141c0d841c0ca010a4035922225042801d4070a00a10008402e940382440c8542d648055000c601d0340c41810700059625070 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 274529181 1250 274527931 274527943
    0x106120203250315032009190902180916080a1115120106090303020706080c03040201120b041113052e0905060406020a3c08070605040c030c08 63
    0x240e000c0e5aa1400014071641a528624180d9031414559141c900618402c0580d00304801503200b5400c8006001c000c0f251142603c001881b5175016040d1a001d1282c0b015181545004100030700400084400b0207000003500131200320200b0244c00181824880d0048000c650100741c21540411520515030b601c890035540c4194000190005480c0e01c0081d01601d400c0301c0f000141540740407054103004800c0039001e112503003a8010004502c000b40d007001003540501443d8014105801e00220380c0c40d04140001545c8002400203042080c441000640d880c0703a5841908411400381c4100a132070030030740c011070b03244c0d101d580840d60000c900c8000052914001c00950000316103c00c0d681c0400b5403100e80221000007820740304007408068000403075152140c001600041146900070311a0300e0240c02c161036070351800d21410041c91020141610034585090b40000b910080d40c6007042001e01c40d0504490702c3c025140028460380c1800284001d1000c5110250103a9000d50f45c6000300a90b02d800d12641c5107 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 274530431 1250 274529181 274529191
    0x90b030c100504050402030c040302190602060c040f0501080402011110020a030b040e070608090304030b13062307050d021201030501140a0606120209030a0212030c120310170f030c060106120203 85
    0xa24200014002400c1c170f500610b0300120441d100c00c1c101a103981c000b52500b821504c655003280303a80e180801005078100011781c2c00610b00c402c05803030942400240c000c0c900c0076001d0340e0305111180002c40e04592140480c0310340040800300b5a481081d0051030400a90b1203c6600000241030035091000c03403600c1d01c101d134201c0300300c0d10040c2101c624001703090b21540c0d4000c02c07507a05400300f4030000000c1182c0d0102944503950340e6027000702030909460303d00219074044100c0c0d00d40c80c011074140c0d810800700c18079160f040b00c081e080c0142c42d0f904814850000e40314000e0903403000d5030900000000c106054204c4000c80d41046c12013004c5903100c00310b01f0202c94441c03182000041580a5000030043c01d070f4005e003124900501524116400c0341c0100d100d064507189590400d900010b841000410240712400720b450500d85070724a9420540383c1151580701d42e000e000c1c40d8103002210181c4c3c0c1041080f004502940090030b90303446024410134292108007d20819001c541c4070390708214000c14500c01c0320301c42c0c = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 274531681 1250 274530431 274530437
    0x3c1a101809050c090d020114070b100b0c0601030b0a06170c2407110103060b070b16210e010603021309060605010f02191b030605090118210513090b030c10 68
    0x4d0a400130014403003c0c200d13007603050265800d91441e07250340f14001400858020880e0322070364180910070701545102c1c1d900032009044240828943c1010101c0c890381160742142100d8440d84403090031100400c01356104010703c0082c01c1c032400c0000004240003a0901040741c2c038500418003002079540000003900c0052811800b005018000f8108082c0a00000f8061400184032034a0f1950720105a10400058400902c0304080207819a6800d0703498104440d5403800d19219031403c2c603208414030000307044506407a1100440c0603d100c095000100030350b00101285a600845070b5008010119600f040d81c00c80d0400401080075405440381d11003040d079a50040052088040c0c3d40c0c84003c900c0541100c0401c0111000c114907401d96200398040d40c0a0a00003440f0308195041e10f003111800040350110b9485a250344000ca04840040318100f0304481381000843c141000c06c80340c42c803594004181e4840c3da2200411800b441d0350003125a100160215030140381000c0c1082203200b180301c0c02d0000 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 274532931 1250 274531681 274531687
    0x1e04180c0605030403031103091e010b01020309130f050708040605010509010608160e0907020708010b0312250515070305060a0803031501050714013c1a101809050c 72
    0x7201c0e10a000640c1e203c1e0280c90005420300b100c5880200350342c41911041426803181e84c0d01d9510071100b003505c040c10203002000b00080c1c3e2982001135100d0044c601c0042c851008103003030a101c40080e8121030010901803404100600e0035400c0544028025941607406520700400803495082030040f5074180d44442d1110301d0541e4030300d40751000a140b40d04682e0100510300117151015280d10006900802c4141c001d40204e90410584a0855607a183c40038841da100718198907403080508120386005800e00380c000006250800c0c078000720740140321300400310b01c16180603682d01082e1070992030040000759000d1009486840400040e0145805071207266041007000c00c80c0b0011141440c3d1030110103041c414200916a03c0f41240c09518402d442081e0b51107140d842010340c0c5283c0e24240b00701402d403620000758503401d4182d00e00f4080750318418059a071406400740e03032641c070810000d10200042021240080c82080144900f07a20440b5251801c0301020109144903280112031181c0310341c4100e00c3c2 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 274534181 1250 274532931 274532939
    0x603032703110d021503090f0705060409020c0708120706110a08220c09050906060108040f030e1c1202060705070b161704030513060f0c020405070e1e04180c 69
    0x34499441c0d1801c554003210241c220f400507200d114806040f04c55000301c0940324a0f001c0c05540c14010000100e1080303401101d0107000176a10342c8103071800e0300d2402400603291a407142d5a45d02d012850380080145204048120220071942d50092400c680301d000c040c41078900200c400c03150f50142c0b072a0800440c0400001070342008401103005c640c00d071240d0741900341d18038944440440f4505900416802c0380c4400820071305900800c403150b00081d0a180030b0a0501d05902c0d003400b4070035482001000c04c812189518410f58600321105a112180104200c412442d45230415001030019010341c0940960710008104500035000d545100d608072070001034564130302006161100c40340003000b080c40b40d1041c0c00650b0308a01445180300718030a40b2210703501c2440070403a00307003003440350b108104104820032103c04003039200410f4a200d03036042e14080b032541c030380d1901600e2800c1600e8050350080800c00260400c0300b61300f0012040c030081524200003400c030030051100da01e8900f603400b820404001e00c0c100 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 274535431 1250 274534181 274534193
    0x1718010e041404112407050601050f010804200618040b041e020702060c01020307050a0207240810150201150b0702030c0105071b0f210c060f03060e07030603032703 72
    0xc04051401480f4064880c0280c20381502d010380001040201c1170089004820030004001c0c032405018101c8071106ca100d60340c00000e00e0a5002003000342000c45060b00070300800181c4451604030b90004007600c0e1500e04c00300342c9210f80b10740c0403000d5210f81c0c101a6600402d042501c5507041001c924044c0140952103007108002950003044100d81001080000018030002803020b14091074050752425074585003070100900c1c000c0d09801001c003c1c14100160700c508a403094601036840090b0500c60071580c0c442c51440c0b9a0100c1d503100c84207a40500d030100390155819032103010b1000c4003e07030b0048180d031a659500642c3c000c8010080d0560302c800f113244d44540c02000a48605071049010000c1c0013141c4c00700b4041c0002e030340d002040307071a09540300b400490f00c101d241c00c14084c142e64078070080d1301950300c0d003455031040d620803501070243c80c4000704c4019200c4d400c000c014008a00b200441f03401d090310000c008080c13a11043c0c00041150400c1c1405404922091b0220f29210300ca80c2b11250450300c0b40 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 274536681 1250 274535431 274535453
    0x1e100905031c0203010806070512070c02030c0307030305031608010f1e12060507031b08010e06120312070912110103020f0d0c08010501030c11191718010e041404 71
    0x161501d00c82402041c0304100c1ea0781c0341c2002d02c10310400150301c1c1d502d03112045103003810250500d410700c00c00b449941e001144111446521080030724108100c07100d9070020908040309242d44507054062690003109064200300214050600007a070300c0d1032802030007011910b020081c0141c02115220150801030101c040d40c1848154404596024101e035540010116154a10000319a1b281d2a6401c00c040c5a4240c0300e0004a076040502010401d0b120040c01000d015050080ea815024190041401da45504030f54021425582040300d07030300c078807071040421011000c58071032000400254010800c180303051500b00505074090b600300524102d8800540187d00800e142d901d02001c1030080c104962894040c58410b12042c1d115441994104000181521552602c00003804021001e413904c1d500002905144401c407101ca02c13030000c1003443c0c040c00b00c1c0d180f01603030641c0040c0820354000c441c020300d20a03201280c00340c032040030120800c03040c00240d800c007502c48840300d030b02c440c0010003240d180082 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 274537931 1250 274536681 274536683
    0x60903110f0c06070606050d06090605060a050913030e0607050c030708070f03060f0b0a031505061903020d020f03060403080708070201060e0c0304060603080a09060315050904170d050c070201021e1009 88
    0xc0810300c20f1f150302c0030954401003da0280d660075140c020000520249101d404e8200c07009940c581d200c1c505280201d40c9080b8058032000540c056100c001c81418402c051423141e040000300500d40d160b40608100d0b941e801440f00d07040c4070b409014000102c0340d00000784141120307110300d001c034401071841d10303050018048005405100341c0c0740d52000305603955050f410005540300f002e1001c52071500f0714a203012180010000741c000c8100b0184400c02001142c0d001044a030304a41c086044426480800c0f500007500002d2505441a14203000c02c0641120099110310302e10b40d2411042e54440000300d007601c0070b501c1003880518801c800b14810602101c020f6a02a0090401140e82542c0340e94060b0130394804000d070b0f0b00003240d0b502c0034442140d15000d2442d2400302040c00300030090070f00740000c3c1c07034000290005002174803500b01a0b03440210017081e60081d1011400c00c00142c0342448988441ba441072404034010701400b10640c51001c80300c000303040950f1241d401080442c1980c61504020480410 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 274539181 1250 274537931 274537943
    0x408060c032a04150207030c05040c0e090a020a08090d05040608040302031e03060301060504060315021308030a09050108090d0206041704170706090608090a0605150409060903110f0c0607 82
    0xc1c44904102c0d400b0304440032106080d400d940d18070300480c4c1001360b104600c02c04219001485d08002141e808036242d000c2e10021140050858520507044d203102210115980d04441c00f903041140c4809a5400380c101c04a240d10340786460f98903580715686880062044901088082c4420b2015a204820300b5074094031078011a4a8040305000c03540100000a90744210250700204015a504080c09108001c00c030544042c003c103425541e402440c070a0f00c080710380c0560f5003c14400c40e446500311103c1c0051218009582d665036151100512003541070103900e02144503000420004100002c0807140004141d000c3c041688990341e400ca84000704102c0c42c03030300754414030010481c0c0d603001005545003882d820082520740d162038409003c022541d030006c02408144810852032080c00b0500070501c0358402c2c400116984c1d880a00000582c1d07000045130042c1c5070034170801c1009903550028400f2030080e00c54000039903070100800d5566844d001c120840e5080420301000714140b080c050140940302d00 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 274540431 1250 274539181 274539211
    0x12020601062c0a1805042105040315060512010504170403050d080c0d0609050915010303050414010915020109020a090203130f1a07020607030c0e1507140304060e12030408060c03 78
    0x30840c2400365400032821404d02ea42ea0709010400980441801361120140c000c03440803000e810018056018a10018000518080c2c400a03251525804823019120080004c00c4400d80280d0103802003c0441741118800b0341c0c0328424a0250028080c3d5085a41c0440200042c031102d010440d1281c0c0c0141030a00b00501c1440448054101d500075136004d800040b030009440d00d8001c103904d01d40b1003903100f0808100c4003000148086031348501110305560b1014035060200d01300d000121800701d0560f122014041005a02d141e00d150706401000e1414000c80f881d0390302c107848551a01c00c0b07200075108680340c0903034803282100044454071500099070007442114001201d1008156403042c00302c5403280140c10440070020303e55094440c4030307410240b910f03045a00e490702c00040b5001049406510001c4e20001c070303481e810048020a80c00591348040203494655a540b00f002c3c0228203135403003861066051128041d00044000300b910201c801d0b1000609685c0c4a003010b02d9050340c80a0440e40d42a2019 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 274541681 1250 274540431 274540439
    0x30218130b030705060307051605030c0d0f1d010f0c1a01140924010c0503211006021603080309151501030e0d0206060118090912020601062c0a 63
    0x2415038504080002540450780c005500c0801d410001c0c241c220b039101e9407040c07007403144190f84403068450202044204140000441c140b061a5001d06500c85070103214107118000d090740d02800251981010b0f481c0c004000079040080c0000001182d61940012440000003000e20720500d68011071a001d0280c14529684000d03000c405134100340c0000c216200c4c0c1c00304402050903e0b00602e5441507600d500c169111558062000001091144007410803082038030b41c50901009100b1150070035081c599650250001100d20100800221009192140c841c10700160090000c60b4610396280142e085c6d030111421941e9103005604094010869841198001240040c8201201d8006c461404100b02ea407500b050004041da036280d86d2812a54126017480350f06540c000440705e0b0040400d003081c01c2019400c0306200250041da034880307040542008111410300645682c1c11035070001c1c6070b00b6200560307281c0b8402d881d28000703d01450f00b06490342d03150701c2c2d0001d03051014402c05000108603545032a55 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 274542931 1250 274541681 274541689
    0xa051510051f2604080708270f0301020f04090213050901060c151a091815040501060608250207030b041a090106051c050a051e151006030218 62
    0x40481c40c01250820810032016440e0450901078160b00841101c1819054884108003c0780c00940000e01e2000c000c610345082100301816a01c0d80d2404c408800d0a10f031840c1c0c100c9032040080001c540c00340320b540050100908040c000c1b03441c0014003950cc1c600d85071070300c2c925038000d5000203003001c00f034884140c010a166503211413650003003a0682c0c955010756454200000841c80c2c3c3d10010113241d140c904003151020001c5240103841008079030220b016a40d1a50601040c01341d018122403038000d0300510050390245454681c01503009070001c01100da29408242c480200903a8429101e581c140e0041c3d103100c5440503501c00c07040140c0305541c9100c2c1c0da503540e0001034200fa42c0495401000c524002c424030300c20394699a1000103480240100d40c5820003094046188076102d0354545160076082c1c042c00740402c40c05c0034142d03000c0110340441d038925400c0d22078692000c0c400310b12030061500303040d015000007020601401c5c3d50f140c400c400030300d8940107600035440080702040540701c0c0740e604065956 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 274544181 1250 274542931 274542949
    0x3020904030819060302010806011b050304080d08130b16020304030b01090501031a060a09020705120a020303071206050f01051c110c0106080a081602010c06020f19020a05151005 78
    0x121a40300c801e41030600180d0814140e40b032003100d0f0a1545041da00700090b13a4007180c9660042401e00b043c010f101c0a5209140a2141070a00980300d40710000300000c003014001058050b240c0d587e6582213054507440c50241c4041c00054018045d06905804a45400c3c13940006041207642401264542583c99903103041d4140260312031703030190703a8440c010014021461883d14421032540c900d10b07140c0c540000010302c0900b80c0c0c0100d8001540c04202103003001801c20294070102c44500c00103440300c0c1000c9000303585e41c1c021900f40f00003682c80540c8091190041c0a2603090701e600400c8229165070500044581e03800000f800034065405080008140703080d0722460500c011451492665024910041c071b00f07482c0281d0019407541c1c4190703901d10208011105860150324290300f11f40f8420501e0004986007030308210007911840c03002462125400c4460014a0500c4003a18040d00c9031090103800da8980f460740b1405031081d00b0610346c0e0801c01501a0140b54011901182c0800d440c1d1910003180b2102 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 274545431 1250 274544181 274544183
    0x10603050606071e0b1602100b0103020904050a0b0103060b0a121a0d05070503070f0f140f100c0204150b07060c1407051b030f0a0807020d0f0515070e01170c0403020904 74
    0x100444c10a001800005960a5404824658000300100c0302c1d503002595220704400701103c1c582d07507900418082c1e10a40449400c65070050081c0300030706006107004010b2140100700350200780b070400c000500e0307100c000903203103201d4003601c03103049a2143c241e90310050000b112a000c2510304d2050b000b012a030350405000c1a283c05480103289607402c0c0b4082c14030342031041d000140318040c0c0a03000c0244004d0110800280c40c1d20403002c0d2004110040410840e2900122499000b9008814140344550008202070182d000f1074090200e140e0074503402c012078819024140303414004101e580d000c01c1c65900701e4140b55009241642044080160001403604820400c8410341c000423640b110300c0a11101c00089808100e02030015240c7d00b451443d6034891700c8074010a8a44042500c20665440c004404820364200d007002c5c0710305881e03140c90780d201c1c500e0100714803e203820400860304280c40344210004210040e12102840011b9603140310003a4001030001c01040c100708008001171b11500c0d1a01e00072 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 274546681 1250 274545431 274545473
    0x307110f0904060b040b09060a0521060f0709060507120305060a0906140109140a17010212180d02151803041226090612060d052a0609060301060305060607 68
    0x184c60310002c00040e1480c0c0041c1364411a04482800f5150350b61008040844600700ca0549442480c29942400c601c13400000360b02c02d02071a0200010070101c501074901c80c20140d42d518a00a46902c021b80b598020103401601c83d1400948030400c1c50702913841941c00040060900444603a90130250080e900f80350071407410070052095000103075811884600240803240181d904010031240420724550350703440b81d8844412501e1a40120314000e5040b00c04030051800130b403070513146c48002c05284005a4802c12a40e22420f0440c012842c800b107070f115603e014204841c00c0300d03103a030b26541e0050310214148107840d0104000008458401350400801c962150441c0700381010b0f29a840c1040906040d400e04071a1000c010000300c03030303a0f02c1044818400c809040c00c6d0b003d440d1072004c646880300603600144140700c0c0c2c981e080c0105044190500c01c0005c1414011000b0101009100c3c0340d018804041c1d81112050005014042c000d030007166111310301420a0303050060740d860701c031003982d0600402508 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 274547931 1250 274546681 274546691
    0x1060504170c0622090501080601181a060a2c0f010903050d050310080f1006050a03080405040209011b0c08060703091a091c05030f01050307080307110f090406 70
    0x1642849002121106441c0c4000d403030b400b00e14402084641c03058102d089060014144089000003411a0800142c00040320070412582c507034400c182c2d110703006c0c00348003c00c240d4401034031010f2025004101c4160302c03246c3c103030080b98250414005150008480c00c000d000b8941841a0944c002070242c01004110340307102040c0d241310313130700303000c807a1220050550402070143c105002180001401014420307561070712603030305d0303840c0381e0019451600c940250200e4065229010401c910000d184040381803000800c21455a0700c80030003103804040e100080601e107003480100141c0c60241e02400900a0604054180c59840c1c04042460341910b001202c0604000c10203110f4903504000c09644070015003401c010040142d181d0840700f0202c09907501510003c5800121078003010301036206500c0300c041614400361401103014141e40c100b11803465502407403030000922803500103440e008036000c18015525050751500e410002e05084140745800c1203544911200b80d880c0c4001c018400d40c0030b1070001030 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 274549181 1250 274547931 274547939
    0xc030b0f010f020307080304080f041403060a05090709110c011d150c1b0705040216050f030712110f030403060207020f191401020f03130518090613021801060504 71
    0x90300429040390981040300748a42040301c941c001044070582504544107a40b0307036450b45042c0e2060312035601e03844125880468005600c4030300505804a240342141a208990394460210084490031981c0c0c200d5548503400400103d0b0300d0342d200040560500700200e1038105003030039650a44252500a100c00041101c11885482e02800107014000308040c0c0d0072460f050001a1031482e029000d10003031031210b498640609a9810480380c40100800ba2065480312500048490380507000b0030192440e0003460000c4100030804003c40e0300389580040c0180c0c68050151084909172000c1f082901d2500c60381210310441001000a4001140f1441001d6660200c5105000d03000c0d074a090044e0007052007007503c03100803410011050a8a11010307050748411400c200407072070100100341054003400001211041c001c015501c50040e9003013a5078164980f4030b1034160703c6080608440d234005079000302c0081409443c00030300703218210303000030100400180e500300071555030842a4084400300d00e00140c204 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 274550431 1250 274549181 274549189
    0xa030b030a0b1603050702070b0d02072003120702100f090e091605040c140a031e0504020a06050f030a0c12050f0f0c0c03041208040e07050903011109030a240c030b 72
    0x410f80c24240742c1404103041054001e583c60b1201d0040c00c039100004100c4000841c510350580f0303209900020a03c865690000d038042801d400e403075403640a8010b600404406110504c01c580705541e006c2c100405a20308080c0440301d14400321103007001c0140c1aa000110103d001c150310f07004613010806003800c036078807010401158446500c414056030800c000b000380710b90068000403840c030423803025541d035151540f412001011001d074050200e4400880d00720700660340c1e60000348114800d81d1820070242c0c0343c2509480501803900400782c15902000091031081c05074120107441c0b5010705090740c9259204442d2010340f0344c01c9070381c803c04111400c02c0040d07465400001f1a0060300302051180342464414025841e0f200d070340035440100031950810010001c48004a5004014698140800e8241800000c28942c482c25646202c4d600344610b0039a41c800810498080c100700030024085c82900c0c1c0c2d44c41a900744e0b81c002140e001e9010078819140c03828240510031101d001c3d07a030300041a00c0c05400300 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 274551681 1250 274550431 274550461
    0x1f020d140108030307181502070914040b0a020903120a02210a0c06020c03130f0806061f0c0f1e05060a0501060512180106270b01020607050a030b030a0b 67
    0x9011035810300e00108005880402201c1c1c20061502c0c001060703810044840c1c07849151a480709401d200f82c41841c0120b90303130108103002540c411003c240180c0e5802e03110141060015503000d08001b0208003c10520300d820303401805000c0001e801d456007070148000c0c4521f942c020b0200381c00540c01000800001040042c2c0e0005207403000755000381070400c0b1500080410981500c0107046030303070004000c40300300420415101001e102000c074003c1d983d110b00301d9800b08500c070310914089214503404038225141c81090f41c085801e101083c8540c00010300d0040794403000048013510040010001100030510b402e000c8002e121003803500d0032840a4501e00f4074078102000b414010b2403841c1900501c030b020382c08406c9800c2c01865500185240c0c0700e4908001442c11981c01d0030107550701e00140000c10840b08050004089441c2c0202030407840c00005c40820b4036141208180140c002000051445008202500b01c0202c280360018520f05480082417400d80d80c02001ea41c00000c8004101c40d12a0404c44 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 274552931 1250 274551681 274551701
    0x4030c0213051603020702010915110d0206240607020a1e05030303150d05030c010603150e011e15090203090705030105100617070c061401031b05010c02121f020d 71
    0x10030040d0f45040c8200125000d4260585010550005103a0065a1150f4003c002904410b01d00407014440b0150281c943d0b02800c800c8882e038041c0c505111403075400888c12074441c40e85100e20240707200303c0000c043d46c280d03c040301c5075500160610084002d80c5070084548042c02c3c40350408680c60728018000d910103601940315038481d82c0104200030b0800c003e02c4113072a9501d0b0030798541c0c03a8043d0a24026095020704103412441c0d600c0c010000061005290300004101140c050400043e8030140c9614243c03015840540002c034005101000c0e445000c0d0310100107004030b05012240180c5a403041d1050740d100792a05030103640005018400c515080c803c5a8108119400203615685000c2d80500a120920011401c0388650000680041d00484030490303078603408541044289c8024180010340c103400c1c00240c4010340601110280001c00032011030aaa00503103034864800b840307500704556189842081d5050b070103101c1d01c2200307042402d044000d68100106003d0780324280d10440108582140203 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 274554181 1250 274552931 274552969
    0x801020702010504050603060d02060d14060a23370b090a061112030f04030f030c021902060903030c03040306050a0227031c0909060f080606120106050904030c02 71
    0x1800300140e03040400c0302d003200c40aa610945036515500080d00c0b10340c2c01c40e00603400103000201940d00c4245175226095940c814068419143c94203024800c464a0b240a52000c444581e15240b280b0340d2049a4a40070800042c08001c2c40350380300210740380001c1da0401200000400c6150301020820760074044000e0010b5855403401c11282c040044c2480c640781c0300341000e2002043e4030942442c0305021605001107580d0100341e40382000d08049000010480301580041c010307454004034640b00e80030f0100140d010b603000b007a03079150740d540c02d82c2d01c503400075130403079000104101c0f0541588082c00608800e030600c1000d942c40b40d1850400c038007034030402800030191a104111488040e80c462a21030011012000d65401c220f071903c021030318050340b01404580f500e5920208058440d48142c074182a500c0a0070b06006259030f400d589125000d55016003074094018800248280c00d120026285201c860360010420340e5454012440c900804e039020b80c00a0034511854040d400d04151038900944111 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 274555431 1250 274554181 274554187
    0xb060d0203030a021b060a0c03080a290102010e0105040327120602091003020a08011406071b15110706080603070b0c0303040218151504050a0e040c2102060d060b030405010c0801080102 81
    0x87c4024100640c600c402018042c0010200f042c81d00c00340d00491100d460065020043e50b9140e034403020319030700044d0042c0103600788031001c803544006024203401113a02d501d8038080d4075400c0d000c04821540080d0b40c040348031019800000e03000140140c880c4807a0048030016902d078614028820110302042101c0241401000303180303030056200b43c005045403940003001003070b0130001c0300040c402d00c2058805081c1842c8113002c80c102c2110000002e0071035041d510005403030b001050007039541c81145100d0200b1500b05900401007580259012603100d04028103035108a42c54216160041d0403c2008140c1680048100400c5007492402c00c621810031511004082c03500315100d50740e2003e102c00150103466008206204001c0c0071040d90007904004000340b4040e622441034120b5203604a8081e00c51210070000003800c8143c41c80c4402042c044499080c400c1160f9400303110595000e00c0120f030881c1c2d0385600008800640001a5004521030380000c21410080f40b0b00034901201a0400e5906034410 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 274556681 1250 274555431 274555447
    0x3100617070e04060506010504031a07030c030e060613090b091605011e0e04110a0201090b0a0509250306050f041b0f26010612060e15040b060d0203030a021b06 70
    0x2c0031500d90301640c81000425540d949600480d81d902444d400101a40f0361142100e0156002d45540d078441d00b00faa6042143c5c0d102800700318151400400c0c240e1302904400c0100707805007440c0c0203101d00040401c80200d5031490787c4d624a21001c90407a4048490f401002048200c0e6006c40c120340010042441d00395007058811400003c01400300c0109028480b0b400440d10f80c44d01c8030f4000f10034500c050102c203138480840c100042c0c081c05003103004880ca868a140000c08010103032007400d00030022900104a4418292076481c21044543c17039a00300f0640c1c01c1d40000c00600203001c1c03e4810340c512440085141003070720340921381d10000e144580c0c034800c2507070b010b021220b0440440401c0340d41c00551103c07142184404803203491b209841401d12035003444070201e003607440c0115a41a8500c030300750811250f218190400d8039544004c2042c10465180703808100407030b0201802c20741240000f8110401642c0c02ea0001e0300c0c0d40e01001111000d6046204441c03003a090300c03402203452080c2590014030708024 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 274557931 1250 274556681 274556699
    0x50d140306040c17011e0f15050a0306080106170606030a110d150c020304080d0302040302010206010603090618120e030a0f080705160902040312030b131107020310061707 75
    0x10040c9a2405541d58442098146100d15210500800910481d04045d41c441d007034404841081003490542d82c14001c400034182c1c050116101c04c45080307000c40100001055022030744c0d60311010300001050b407100000f1441e03d0703081c400c400040c03428103004000e030038000c0d0a19050503c028401c62180e0400076192021450190002c00542c07070880c5d4882c0c0d00c120b20b1518506405101034101c000f28504a81d01000c2c1d90000300034400d503540d2a0480e9401c241c10101282603101d2404000e0058200f040100100d0340a9008501e05521418010070745100290014940524003081901e414000201c1c1c043c4003501b1507c21000c40b04280c01400351120305403900d8020b408406001002440001000400d0020034840409400312195800691564648121001c1e403c5404281c0b04100758814181606000307220349a90450064105807400740d11400500044c650464449180c141c104019001680c080c81403103d6080180d13000242e1034248100c140c039941c80e01032101c80d0350b072040300103020350701d2 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 274559181 1250 274557931 274557937
    0x90b0f0406030606080f04080a022b022a0108220b060a08030705071401050c07080309310905030f160b16021c14070503070b160e01180f03050a050d14 66
    0x82c04c004a20749d41d51001e1412460a005c101c00900f02040403003440340c150703400e0122404034004942c2241c2c090324100c401001000c0d901c14468001402c3c1005403001035018a0309907078482a4100d003034401c404518004a001e001c8100708035000c60b004001c204041c6011016000a040078000441c1802c05c0c42d6246a039500310341c005d2014031411101030000a0b8403a5046983c42c4600d8030a0714445540c4203460303a60b9410500c803407407080011508543d221035546107420014101807020800202e040d880b100700920300c034242550140010401d850a2074034500040444248804641501408900b080000307040b0150402e18070310701031105813155035400140107590100030a211118191010419501c1c9613040b20300644a400101d04c2c00107108000c005403030304138015004816903644050410038099130b400c90400104501c0800c0320083c1d403065084801c604203054964900940700e180070f042c058016402211254072007080001004424044a02010b0b140e081a640f94002034074021606c2c0 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 274560431 1250 274559181 274559183
    0x40e070908010e031602151c051302280905090c0f0a140603090c0301050109020c01050f160309060e030d09020325050f030109120e0315060619090b0f0406030606080f04 74
    0x40d10314418002590344100c49444900c80c426013895903074074004421242d6189005030423509030f01e0700700011984200d4042e01c42015900908080c1c1d11130b0300d1784100719025502115aa0070b41803050000c5010b08852240e1800782c0c00080003811091401d40400208410200445010708a40f80c0f0070014a1803061802445441c02c483c840d84982d5008400ba2511400c600607503495170030040000790b0707480298010444518600020710096542540000d4116010b45003c00315880902e280081284a58060b600180c411074002c10700800710002c203407468000e1084220a16a140581411440d0070070842d0b00c0d101200441c50320685001d60308100c058190700c6810701030340300c090562000b41c0e420751010300e820350700040303443c100b11400c100244040752804845000e4840e43e1a030751040c034410780041d881030301e00a202610b000c41007001c50440040814645041c4001484082403280c2440044e0140300c6a0790484d81d111450214010705480c4154000424480c03404140303c0c43c0000030205540c05 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 274561681 1250 274560431 274560457
    0x106030b01021011030f0c070c0504051003061e0e0706021c110d0810080102160219030c03060207030f03050105062b1505090603011107030e030307020402040e070908010e03 76
    0x50032000181e09080b10040c10b00d4000745042d000c103c0d403a00c24009140600361454002c4a161b482445040c59803190794401380c903114020808110b60310b0316411031030b8441d503519114202d05a40b651100182d0311118102010124803414100c1c24150b00d20a00226812400c014450b040c500900a0b484008181d090a0161341c04160141d205004c0ca0305800c40407069412540c0400b5510301c0107080f4402038990118020440800141c1804140244c61030f507540c95481100803d01d50382000780c95610a00080d008107100c0e90000082260038403540c000798081c102c0540e503000c2a140050001121050020038940b03400010701c185d4a0b240f0683e2500c03408040c0040352108080e081b00b20844070002d0440026042c0031900c0d4101c619a40d20303508860003950002c00303d44484080600340c600909511104100511100340400e03c103200b800192040501500d20713186203a0045016680640c00000c6646003840a02c000b07264821003c100a08080d40204250411507180507124400d1401880351 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 274562931 1250 274561681 274561691
    0x3020316051306081e0c091206010609141c050607020c090c0405010309060b03010c030609060e0c090d14010f0501030b0708060109170102160605041719080717010806101a03010603 79
    0x25482120584407030030f50705c86500c0740349003500c0080c0c280e82c000d102150144521802d03110000c10002520341c1651041d4942c000c0c26400c0c0180d00c2424601403c00e16441569115030300780c644a10f40c83c507002139014101402140c0380500b40079181c0014040b40c24020340d00401044280b80c680c000b41d4080e14005d19000c5106815810900080c0c1074240c45690716510300805070340e10300c1e09580081c080707620440702440115a10803040310004001c0780c2c082442801001480142c0c41d0110345c00041d1882800410542e06242c940b841c00c48903003030102080c440d03407840180244002140a298440c0851500b006146410f400082044010307208141103242c4151003114070310000e40503a111400ea201c10390311641141d080440191801340d03030944451a030350b100b40218008000465400c00c20111210700d09084440040380c0010000740400c081142c5c452250404c1049020700500070300c8003400031b010070300f840f241c21805034485038003000120340442015500703440c040b026203044410074240010703 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 274564181 1250 274562931 274562941
    0x7120503070c052d0105010b040b0a02070308040914060d030c020f0a030b1014150a08040f02060c0c0102070605090112050c07081309050a02070b061e100302031605130608 75
    0x114100c82d018010018007460001079440f02e800214a40d590702c21556064403292010116030807a4400e006208102e44204800d01100d00c41d01d00400340300d00c040c41100c60306540c035103a14030550010f410040c84240c0b03c0e200c0b400304a0101021503001081120031032803a0901c0d660140c211002ca600090281c081c2c06c014240ca903880e041c1d5940210b8100344015107901e00a4002d800000850043d80d0304a2108000303400141055090343c810952222110342c689010003000f030300c0e001c1d00103000311a2080c200221100503203888015002000001c0002c240c0c0c0102c10002a04001d00c680081c000c200041c00390b28a0340c2e82c801048117200e14240c0c000217080e1200364420400340b0503c40e01801c01000025049001140811094125110b9000412090b180c031554030082c1d105a020160000c4900000b080144c034008808080e9208004280c06240e203401010494692040003007101195020040104c400403001c0d64820040084c40d02c649403100c442e084c0300904100c0e003d80c0f41003200040c0012 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 274565431 1250 274564181 274564187
    0x705010e01020d030e12070503130807060203070b1f060c020f150d09080c0604030513060219140f01061e0e040209042a12030f110606130204092408030712050307 71
    0x241902d0111b1001c03941c0300c070700741003441d42ca80c0110950083d00d5106c080c0010340042c0845c0d4a07055910541c0650300d007890780d44038140046409020b00050051507c00246020030303010101c0e008220f00d403500030003184540100152200d40040d03090280c00c003e20400440501141100c0710b03003136925000200300003681810110381c00b411010320b18511aa90903c82030541203009060345560080d811340c41c0c1522050120385a0441150b1000140300003050400003c004602859407065900e048410490043e504142901c0b00303507000582c20740c0e50001c0007105c0141c44640304050010075408002c3c1d410301e5400700f40c1284008002600c401d003058003441d104101031079801a644035998101050759200c003007081150008a000702c02240c44090001000c501842c1458040807a4001801d11965500d05105ca4182d9021051400e290f00304400310310308049200b60003008400b01d02070180240d40c0700c409100d04106800480385603106010080001e03d81340b000039016021880c0282d00c940f9050340075 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 274566681 1250 274565431 274565443
    0x90f100911040c09032d06091a011e0608090c1c21121515020f01020417011d060601031d010e0a0201030b060901090509131407080705010e01020d030e 66
    0x81e65105040c45418076410394019040b006480c0242901d6501880381080b092012407000307481c2818001d000040001308005500940301c0d20301905211440e1004c081800d42003420903040b25840c0402d001002d40c07902010301c1c64101030102818440d8050803d142007555038180fa41100c1d10500c882c01d400715589ca0000e0750b1703000303032948044010640c95410400c041d810b6a0740107403600107440d00080e9041403a4500070703030846469240d006d07200c0c1420018003100d0807019461060030f40c420b01c2c5806000107000d00c01400180020101520b4901300b01c00001c0c00e41c1d45081001e20709401d1465811407519010510540102c0300742000100c0c42424034650070384d1203400c0301014042d40313858bc00c06411200482c03603641040c405d80e82000042e1200041000390300840a0340360000304610014002d03400c06068054014171683c85490301404aaa01e0300000850b0388084005508840d0003080818020008400540303401d007004040110041c0000b5503c2d240350910700100754441c0d4840000d4078060103c = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 274567931 1250 274566681 274566713
    0x20f0c0304030507090b0108070813050c2e0203040510030b010e041805060105040509030a03180b10030b0105031203060906010c17040e0105040612030c050c0d0f02010206090f1009 79
    0x1681e455070740d40d00b096900c604152068640c620700705031000d0803562199000900c84e54454480004c513444168900361a860380c88000c0703c0e42d11403060784c0005941d0364803c0050b064a200e20b5420189a0300c41c0c044034028802400500b90350081c0001c3c421a40e80d0003140c0580c41c0c0c1c03483d0002c0e085e0384002c0100c40c044e802c0c5440d1600549045103102c00c90890440401405004804646442e682d440600080390070440b40c02007190400d110100c0c8a0744260014040d218a030440e000501303100340ca941c00c2c508000d85442102d5503101c8820400c001550020a004000440c06000303850101030303030120140700081050b03200f84459000a50300f40c1c010143d21303020340c1e0801f40200d00044000c502c2c05640e0701030b01a24850300d24410000583d8502402820150345149a1040082403d96802c0e0745155000300c045500d401001402d480e551100e000c0526685d009404c1e040b880c5215000183c00c100300030b0200c10140d0840405400c41100000300e1b40120343d500c080c0041c08010a04010714042d80c1070071 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 274569181 1250 274567931 274567933
    0x2040e18160303050a0e030c0f040f020f160309080f1903170907051306050f060a090909030e150c07030b060a030503040801051509071d0d1202060403110a08030604020f0c 75
    0x40110502d1351190290044403415210403075642d04c040101995240c0c00c280c41c81d440b00c60300000403190704064002c032000f4100d260b0054180030f68a40c41c908a508040001041d24100103c2c90342403652109040000303044102c05001c24121035807000b0340300c004034288092100c9000015904252088034000d940c854481c1701d011803030801d5418661590b20302d22404d44075500c05902401e10790094403c1c02c0446100502440300390807040203114507508003026a60070f0094126000a6220060064000b014465924824420398201c20400394403254441c0802e214024026003e0844000035544240c0307070441c0c500c01195031940002405000b40c5d8100030000c0c040807800043c1e01c2c00c150030050042d02000701d100b20704540300d4103211807007604464803400103561002c0107483c80d2078000b065a0104010300078008414a0382c803103402030307904480500c0c011f03882102004149944046059103000000016003402d8410723480742100381c00b01401a0380314a50019284845801110031510764502042c = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 274570431 1250 274569181 274569223
    0x40b03160509180117030a051c0e16050103060b03090a03031e0f050402030d0f0f1103090d030503061305010f030204020d090c060906020f0316082101090b120102040e18 74
    0x202c03000c03503e032000e00c00c41d000c01011500c02283e044012098521030202e590742c660600140c4542110203400384000c00c685e2954a6a2003180c1d641d0500400742d02070700300710361403503458a8100018102d03540d5a00201500802f0700034480092004601c10a0640c0c2520340442d40c00c60540403400721424000c0f1501c4102c0c07400140c0102030134540c006510450084080d41c3c550100c0d0358060f507030101c8143e4a00002003004c51900b201c1e60203507002d041240181400c807410100302a02061042e4000b40003a4003042000c81008000d150070140c813800741c0d502c003005014951400300103565001050100a200340d0700460402e40b14544c41e03224240131504a4194504555140c0c0050301d0301c0c0040c0520030043c09440300045500340c00004031010106c032068a07680e0380225854941e6103802140c090381443c058650306007115440610b01c00d0103000710f807400203001c400a004000d81401501c0004110364014007003002250050012035070700035a9020580d0384e00d80600700305400d14a4076295804013807000 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 274571681 1250 274570431 274570459
    0xf04090204150f060201060905091903110a0c1e03080901030b13050f040201120603050c121006080102190201060e01140d050a0605071d150a09090609150b040b03160509 74
    0x81c0341c0c0c0c2d004913101e50b0003c000e075546a8650b202a50000c17241d210341c5600281d0a15504a8000341d40326215000b803a100c0c580e0540c00c452281050982541075600042018040c40144400c070064110b0032003140e08800561b1560313861150078040c909486c1d061540c3c0f0844000252100c10001c14582507802c010041480e0811380d4142200c130035142603000605124040c213480401c0e11460040d2900300c3c00034128000c00070108940e58904040c1c2c1211070041d1074011140785064050000904884000540c840201100a400300115100b0007000c680c1800d0040243ca50600c070307a141903c0d00800c9000308805a040807529102108000402d58890949410700740303e0580d0280380100740c11341d00e0800d041c048098001c01c4616031340c6101d0740300d06501c0c080e88201c0d80c840020014050380341058803d0076078450300b00085910706d0b8407522190303032a10418072804000e82295800303003280070015406c05007000101c0420303010040040c034103544100c2942c03014038011020348901d543e0041075007400e9030708 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 274572931 1250 274571681 274571699
    0x80c03090a120303240504020306130507020604050c0d0308061504030c030305040303080609040b0609180109050703060609021e160204020d1b0e03030702012003040308120c0301050f0409020415 85
    0x801c0b031040d400a4a0075034a40188203501e4003481c0c07000d940812110380306040100700710082d40042c00302d41c0e0000740460444502c103241d008052088115070040c00da249098101203081104c11041c1c1c42c41068540240030009070854411500a4006e446c02c02c07101d0036004170041d9612030b03608050700701041c00000008240d4004004c0040e68480d40e00c00301e2a80b600420f00c6680e0340b080c0c400a201c14148000140f07141042100c03540e00c909916003040c514400f14510300c0c00c40341505001d807180e03041100c092083c0145c5e409848001d04110104514010742e66144610050b1501d50390012501b00044100c8042040758103d403580d600140704541d1640480b0a401c020090032400c11620010321101020f8107006440300d64000901501840c40c026403540111054401c00010710301c6403032a414568090700c0200701a201543c86500b080d82d03078540340c0c204100c450600509200703e6000030070051149889038122482d890320151808074450f03d16100240c064002c0c03015060081002c0040003a079914 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 274574181 1250 274572931 274572959
    0x20c070602070b040e160903020916030b03030a02061605040317071407061d040f051e0f0103030c030818060c0d0b06070816020d060c02060612150103080c03090a 71
    0x40036002c4a407800d9941c1d030349940c1d074021445484062220b0030001351b250100107280da0f000c0c40c2c180c81c040c01c086440307a00080701d40301c00750741404c0e035409052083c040b09a058850000d03884400c40086040c1002d1075002955843d0042000d80e60b0601c800a1100481c015011f903406158060520b00e41c0c0d00c000e00c80241c494100c11815074403c600010b4094000101207003440944130b4959904402080821401101840703440c0016006541c9134070004641689100c5d050041004290307808000601c01c09110180001402c08186002024010400650007080305102d980d498180f119641d69000075800801802410b442d48034003640d402c0001c401755140060400d80c000004c04c100490f01c84007485040c1c00f480c01c005103581e008009030215604a82030107840309100401d101140c620584c2c818003500c0b4402c003208050f03444801840f00900d004080d210300c144240bc018122145019480c10301104107202c05400c0007000a01056030342410b0040300c081b62806002c041a441d9200d00e1601c400c1 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 274575431 1250 274574181 274574189
    0x601050d140d0314070c03080105060a090815010609080f031207090504091202070b090102060c07020f130b0a050d20010e1005180402040b07141f0e0d030510030b060f04020c07 77
    0x64000c13000481c5980148030185040d40c041d600c00d00140e09200501819a206507011001d0100070240060090410086000511011080c01d0643e51409a02500c2c1da265031300300d5000e0344c2040f045620348440020545020b400147c0601c0a039855000c070980700b00304c4c80d40196070480d041c4005035043c00640340161040c4c02c929402c0740d074100d0b074607140380d9098082e5030081401600700402046240c5940b8002e0a41e0a000608c01d03001442850006190f4941c0e000000f0f81242d1948442c03102481c1084020b0002c01040c0c8540c0101e2005603a07499100e1122203121b06503510110841d200d0b42d2151004841c2c866001e000510a100140307000341c01c81d00000c014421482c2e000d07401d45050b08240c0203036011601032070340351400c1c080155138081d664204070a07101c580b441000b0a0109090100300b50305c0c490082d5910002e86101010b810500b0302c4540f4142405041c01c0c10248000d41204a03040d204076038001080c8640da845000001d0b003501401424036a005c0e0000c9503028801c0000700d420800c607 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 274576681 1250 274575431 274575461
    0xf020307020f07060e010c080d051311060307050702090405070f060e120705030a081c09030903021207050604050d0503040305060f0f07140a03050705090a0b190801080601050d140d03 80
    0x2c04444101c20ba071002035004601c0003440d1819200c0155029504540310b49100d01001400c00540c2ca0143c0212343c0d04075600c0d10222003048030324041c8030301621036801d001000d0340c0051561400c803102811074441c144001740591114170008043c058180841d00203805002c21035101c5a07039601c4014640354503d0141481948401c3c03504022200018007c0102c1d00050054107420008c3e441e8000c05400c04c0512224080c22401129408025840385443c0c05e442500c0301c4864a0442c018400c0c5502c045130302c000303070707a20100c0c0510160f900c010503541111001c8a000c294141d40e841d1250850007203034001086840350340244031110000d42c0c00c003071240040ca03942d80031955030008100da001c022181075207013412003041885e00540c842d1300441c0c1c2c414a9410100e103842034600c04180012102c3d40b0000c0201ca010610302e1060600e9041400c03222810314003c0030035418510f1081e00c0b000e06104081c418540741c0700b44010418541505000d211030081550300e20700c044140900038015a00182401d = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 274577931 1250 274576681 274576693
    0x3021f0f0e0109020f0d2303070605070503060108011a1201031a0c070b04020613030210090e0901060302010509310605010912050a0605090c06040609050f0a0e0a020d0902040f02030702 81
    0x360000500c03c0032000d079001041002c40010900038464181da00702c13000d84060580e281c0200c480300603804910000d240940082d41c1e65109402c2010480b00c002e0649810000100240401682e000042c7c5041d1501440d01c5044c103015103440c040030384142d52059494a401000000921514a01c040410b0811641d2480d8650b54100054200c0c07046c0c0d01d0042000b5030b480080350150038410090308811610290002849440b0740008138030b0070014940d840001d980080034011750600c8040c02d034000904900910a45046900181c19802080290340c0100700440c8418240280c01188412029070305a2140c5c81007554036105000d01500e009040c0410390030703080050085401e001c40141e45070400050203c0c2e08a55807560042c000c068815010b51050518500c1566a0100140300902c466282c441000e4900700c240b003656280082540d2040100780c00412180c080d406d0404d900400b411401680e640307020070982c000340102c6002a4000349460500c0031801c420740d0080d409a40e0503021a12 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 274579181 1250 274577931 274577951
    0x2a091003020307080414070f0305010507030f0b0109030206030c0d1107120f05040b0c0c030f0a02090c0a0804080d020c03070605340e040905030a08010315090809010c03021f0f 77
    0x41030740b00c1a15280005010400010041b60703008000d4448150b0710340c1038030f0f80e050345c5503180b90308405d440d00292890f964410501c4040c68041c45240926030031030400b1700040b03405200282c43d00c6030780c0c40042c0c000d4800000040d0611410400c407a2002060941084807001d88401120550403010b000c481644074103070050180381c0900002c00b140b410b90380c1c4240ca080e050003c01e000780c1d0000401440c05d0b109100b10806a03903010700c2030020714085c1900130100d80701079004002441c20054402903501004000c006c0c80302c2c0e84051101ea02036003080300e090340d612141c01c0c8140280725101e011a01400046a80c00c1000041c1d08100d000320801c6818161007002400101c9400003a491415403d403030040c104880309018004d41d010582c001071000409100c03684600d41036600140c42200019135501c0144104404000c110000440382d03038042007200002ea039003112034070032a070a003030602808a44602c20140300b0040c08c0880010340f0b409800103507400d4105005003a0340c1d26112042c81c14048810 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 274580431 1250 274579181 274579187
    0x80105030f071a22030627050d080915240103180308060a120506090105130b0a2703030507020c0f0306011202010e0d0c0302040507050a0806092a0910 66
    0x8400c3c2d42410032844940d00300d88800e00342507800700030040c001c241940311240d100d01ca244150b0f4000c500800000c2a00c907030000b10305409280b40c48a4a0049000160b0100441e83c0012005150304050420b80e4880d11494130070b5103800105003d80460112032420070400403904038001001142c10072500f103401c4150001034040d6603200c10480c039448828001e004c0482e1290202d40d41004000d0610030000c2e488081d42003041010007400e46096014070140b0600310340920070035905c00481c04031078072120002d0381c0d031030740300d41025200ba02c0791922514a80079604841d080b40001c91201d0045103114500c0d480d000d00540b070100c1d45600035009001d0f55251604049009129204005000c3d0060340e00b0704429900c08004003e00303a0420021550f04070b80758444152001003280201e650840c4240b440c410042501c034001c01200400c8024001c94000c5900720754083d400181c1107400000c20f50754007402c608d040101a4603d42d41d00200d4824a0007000084000d0604003420f441a4804ca01644810f03 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 274581681 1250 274580431 274580443
    0x5120703231c0507020103052208070b0717010306050a0618090308090309010203250804030507140409080304080c0f1c0207050415171f0b0f0a0302090a1e0c080105030f 74
    0x3400c00f041041007107100540c407a5000d41d5202030540c1801040400c8040c0c982d65180140c00119080300d000075485044c80102c1c0f090603400515454034003020b001c4188111540da006110082650f42c4980200d14003502e250403c5001c1c060101d1120203a04501e08d0720800790007588030580c042106c0c45c001c43d0b40c2c2400882100c080380743c1a0002c61504000340f49240c85691800c04200080356044038044c0050303580b07c001c00c01140210024034440f801c10410450203024030306610700c00c6241403484000989240240e981c4186c02c07450700781c2c8820a403c00c66081500248400085008002420b01020403c0300b40080a40d4654211307810562107005100c01c071038008110701c00114154404105041601d0303903114214500703400b0380d0f041c0c5042c0138006440c800242d228191160711070550890b50308000c904044081c0080b20480a154a5034000c5080b01402420040301c860b21040d107202e03030960281308446180f200c25000c00480c00200d000401c0d1107001e0007180c0c1700e401810381100b195840000c0b4 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 274582931 1250 274581681 274581733
    0x906010e090606090409051510060504030201020d050702010e1f14070c1214030406020c040e010b0f01050a1106040b04051504051506040e031c0b010c0c0512070323 72
    0x1d10070503403680e50030080d46402803090aa8041d40301d84425000400a214016030440d4109401015062594a070b140201c9942c0200080140a120030000360f0380c001035503005031001d070070002ea5a0302c050004070741c2c00d2180001c003a04500004c503800ba4900b1710004c500342905166451a044060504001140e4401c5910150038000d400006115002d0110580290b69100b40181d034a20691050070a041d40c01a602160141e08100f82c0382106007498010600d0a0403200e008220340302007400000c509500c1c201f00c3c01d040000126412441d14003401044003030307500c60000c0320858030345441d1003e000c14040790110341e14020050340030620740c4c51031502070040c0d502c9405400da0b64144003001085000003803415500a0300c1311040340380c0740d03424801000b0107100c40c1800c3c0146008c501c3d000c01a55501820a41089610220480400c0410344004103540c42140e0081484455041407498250181c0001d01034030110074054024440802140e040c451110082c1c40c6010b00030000c804d5203e100e03c00c = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 274584181 1250 274582931 274582939
    0xe04021305040b220b03010902090f06041a1809010b0d0803011e080607030506010203070c090c1e050a03021305180703151409100801061707150c1202070308180906010e 74
    0x40414100b13540c6402801c0d1010024000180d12081030300090b007000d005032410b803d40111402881046e0800d40a4040c2a18031702001d903001c003e04402040103400125426151001400082198040290818080f040303000304000f640b00c2250514040b180e000307101d80c01426014071100c0030b0004492001c1c10440e0f200c0c1c005007426a840d0304040c2c01501c4000c05985c11800100201c0b070019100d6507110740a004614030006a0015450000e42446100c0501c1c61048000089002c64164807004452400b03109240c00760b111040d0882103044601c094002c070750f2040700900c507911855005950715210341140d5a060001d41c803c4c0c90075481c07105090207403803c000980000b15106090035000b040e00103456035180b4484695881e0107a0031074072503070480c00104604000c111090401001140040c01020307090840103822884003a04445440400515120110607007003070480c000d1082400454211041c203a8907042001e1800854145418140c0b140f04160042811548108011000c40c58050 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 274585431 1250 274584181 274584229
    0xb0d060f0512071703041e170c09180a082811030405010804030c05060406060519080712021503091c030905060601030f0204090614040b0d170a0e04021305040b 70
    0x4c1441040420480d8010f10007080000384805c6e00319142c80e40c003c2c0d4011094511800d01691280050071074043c46420341c41050307545026503941c0c2c01c5a0b045007800c0302c500d811035444c00c401401d003c810000980f8150303000c11004d00e01c0940e404003490200e20490a00c0500984441c141d8041c2034072801000c3c00c1d44280400c1c03000d540101c0016030854040d0411034195801e5903600303454448225021076004e81c0714036007003007035042c419403552500d20b24181c107801039410258059a101403170b00c83c0d0020000402208025510788820300b0707800d0b0001640c2e00769645440d0350b61685e1421701280741000c8404c42e250751883d840c8240700f43c041c41a4000c0140c1025110720300110040c050364000c20610a50810000403002034074490030005002c0948170044407945030701084202c0d450340300400d00401000721404006040d0700c1100d18444820440580c461419140440b0313403115180600d07070403d00c0062500c9034030201c00084003c503402190244400b03461803007400001600394224002c051058 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 274586681 1250 274585431 274585439
    0x80708030307180b0a170c070b0c0a1704030807080a3e07060f050108010204080a0803070504050909101d030405062508030906010506030402060714070b0d060f051207 73
    0x350001c0c4003046080c50146001c0c42d00d0310104c901d5580424110780100d0540048208100c80401c0c4040d405100a105c0300e05103002a00c50000c2c0c1440100b42041400e40013508040042c01294010007043c030b0020840001d00e06460050000c0d042135a605000c10403aa0014007045181d00400c880f0015100d0000b81905144940c50400c8140460b4043c0284919084c40c4c4100d80060250280b60301915000c07600d0440040f501c0d04441c0181c1115240741d004110a00c04451f00289035006151701000035983c0e9a01c2d60411940c0d8090b44e00070395400400d1400748074103240b00040e0200d84199400307042201e0341e903800701000c0c80c103e0001289031b41d810510042169203800000760410100c400245400108080003401c4c0309240c1a00440e1010404814480032036801c014a502408059440c41e01c2c6050076000948035018000c4001c1094101140c042940081803002030001e080b840b240c940ca40a0200c450b0001e80654054851042210340d000141840d1405980b085d018600c0b028006040c10 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 274587931 1250 274586681 274586687
    0x607120b0111120a0806030a0506010608040f050303040c0303021005060a15020a05010e010203070906080403050d1e140603150103170c0304170c01030b040c09050f121213080708030307 81
    0x200344124107001003000c40704507108040c080b03150706803000c640f001d0760392000040203462180040c0066009030720a00780c8070000b40002a00d24103680342c0f814291940e5940307240504001c0700b4010014650700000c020f01041000c84840c000543e8420380a03190700d4020411400c007100c00484e41180d0105c40c214003001000c0220012010341c90062040d0342a04109450300d900350303680000c2c4040969800010040f00c0b031b0748480700d18042c024520305030200e0304294074010024014910440b034915540d06001f0380382185c101e03522300c0c44108103405018201d98400b0071101114200c1f4064081c0c000ca0211030082c0c040030844a05032a4800c1051041c0d26003101401c4490b00300740541c01842c44204000305158480911481100301d1260043c4a1415010700042c1545e00018100e40200c0c01c0c400d45d450781079049401907060f40e4040e1000700e0710502c06000559450f0070103040d400c1c0c60003521011304034a03e0080040101c2b01500c06803109a5079039604169030742c88a842040c0f02500207001089940d44 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 274589181 1250 274587931 274587941
    0xf021c0b040f06030b25050a03020a090513090611041d0a06080f0304090f0b09070c050c220507050c0613021809060f070230041214010509060712 64
    0x20040c000050403882d4608400c103c658a800690792030003001c0c2040f464074114020f90130304004180c1d4a00c141a989100501680902c00140060540109103641c10038420b515620041a0050481141d501c03003015070300081104000545402d420300c0c0c08184101080e1040b201100c98012065050311101c0c040003812038000303000d01ca1081d440d020300042c0704074100a68512003044102641c2e4807840c00480c5002c849800885d0300311941003442c4802c0a40c1c40300f14260740a11a410414241e42d200d107042d5040801c24074a0640c46110b0700c500400c1440302c0031980084134082e0004110355200c0400c15151801a60340f2181c0b142d00c139400141a810b460306122582ca4409401f0340c07110071881540c2032410030100d4108a0b81d13401801007180d0b4074458149141c101250740042c1400400c160f0b9103102400e02d010340703040c4071100d207030104412070a0441190000c05050500b00400c1c0300520f0a840300c5e00704216110782c550b0034400401c1c5800c0700031410a0094070349458007401061109a0100540 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 274590431 1250 274589181 274589201
    0x609110f1309020c030a111b0607020414011707090e0c010c0c0f0b31061d030609011b0512040b0a0b1201020a020f03030426130303050405040f021c 65
    0x600401e000003000c16050000d000c4800e5160082c40d01d43c000207000901012800709101860f9001c8a808503140100e40c041d040c1d01c01c0142c0d500381d6201654000305015100c0300041c0082c43c545070000048141070b0030400ca01010007401680c0d88d20355a9a0018182d85c0c04420118054000d06e0400d1781c0c943c015480381038020b01c140c0540348138595440001d5008000365221340d000c880c00160180060601310b00390b2207080000c00341400258101746101501c9146401507000b0321000c1c01390f050010036050740c0e40310410001011121a03180054400c2d0281145aa41014000b40c41d0584000c5070300500a594103e07802182c8420a0f40d103e45408482e40b101070705c04c039400c82d0364802245c22612920400314111801c0800035036141e6603040d0085c80c064400340c0b1024079401c10f10900001945410099000c4c2c0700d88400141c0652410140c1e6407184100f45542d02181e039680b50000815800c100540300700c0c2c070112000c00054a011520707030140d00c101c0144c03501c81102081040600307110707544805008 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 274591681 1250 274590431 274590457
    0x23040905280204060e03011a120f060c041509081002071502070f1103030405011205060a0f0303030c021606021e210706050a0e033004030e040609110f 66
    0x340d0712900003a264104188048400a40c00007024000303035401080c42002d000d02580208488812000055142e000c1580c0d49480b9804400740d031024071604104d01d003400d031101c000b502c0003800c12214030f4070030343d02c18420100d1180046180741450f9000e25002c50850780700c40007416503c10070000d03030360003980701020443d0902c4084542803220483c5101400a081c89071201d861030109030b081017110384001d41d1506100340e0042100707014a03640200135565400d661a000b10b11750712800300082d0440d0154000e48081c80c50000c000007496410341100b41203694039000e82c1c1442402e41c6655150800501406c809030307001c140226031000c91600540c1c542c080d840161744501940e408031008460614001003000785c40032881d0350602c41e4610800380c2060521000b0000c00c10300300d01041d01e07802021080741c406802c1100c0e030240006012101030100c0c602d480001b0a40c54030b490302820b25021031203c86d0040d4900a0f01040800d0107101d00c0551615a0700f0b01401c01c0000003000d14136501c0802c051070702d = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 274592931 1250 274591681 274591711
    0x8010501140d03021f0603170c0f0303010810021305060c0a0b070c0b070c0501110307050414030303010e1306020409110d0b0d020303250212010b1003022a0309190623040905 76
    0x3041840f40300c40c0e245030034014850749c3c40400000e00c40c41c107020591440c146820400c0100810040040d41d142a26003107070b40543c50304182c00701423881c00400e0303003d035401400005650107480701c04594800c0c454805c10200180e502e80803002c030782103160200018030345c460800203d05640e00820b15080340c244101c0011071030040c0003400203102c0d041035602c0008180041828031110301102c00070190803109400071815980340490842c1e0000c000b5042c0902c2040f6810301d0f200f400002c0e01110081d1041180a100941030701c001840e5aa004900c2110000d00d080b00980991400c01904010160000e004500348901d55003a074005918145000200022140440d40142c03141c0c50340c0000740c80c0c4400000380c4040c2850038482a80701c00c500c03000c20148104590800d400d2100c01000c40f40342d540404502010745040754a28601c00c4640050b030243c2d913045202c003021012100f00084da8129a070702441109105002e4400001c130609000c0c20a000340010f01c0803034841c0d4884c030b03400b003412403034180 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 274594181 1250 274592931 274592933
    0x70518070c082802070f08011a060f1e09120a050607030203060d23120403080f0306060d0f050105010906050c03030103110d0b0a020a02061e04060504150608010501140d03021f0603 79
    0x20aa64070362906405600038080030003402494001610062000d907000348020000c0c3e5040c3d1074a0032842c42703494801d003008500101205254402d030384601c0c1ca0321071181c50215180100b44042d400c00030240d44a10341d04d41c0090b000c03035408100d22980c3d0368072000901241e00c03035040940284d080100025041a0a080024040b5102c0440d0180d6001ca4200900c440b40d6840380701070031300000501604806408102c20030008041c50f04a8500c4201c0078802c503143d855580009100d8440c200580780201e0402500c0c500d440720b140d001a04880c0241c81e50360f030303403580c0b0ba07c1554103000b942d075425556041031004202194181d20520840f4030010301251902000d940c030002809816980540055030200341400c4a80d0100a00794000300000c0c1a4519504c000c1c03001c101c0400020001004941c841c4003203006c1200781031242c480258034180900802c1c0d11441124001c100c244903013418089104150502c40c100810032422403070305030380940266510000220a00860646881d040c150b995074004 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 274595431 1250 274594181 274594237
    0x21c1a030a141504020307500102061b030603010204050303070c06020f061b0a0e10030209040501050f060a230a0c050c0301060807092408070518070c08 67
    0x1c0200d1041c0e0449284004001c40d1524143c1d0759100c10b14044066428400941c2e00018114100d90100000c81d2190310304000c0789125441480c042800d401106e5200c00d161002941001c1c000c1401d02c5040144142d540b004999408044d00c03103015828801101c0750841070840d00940c0d000c140500054074141d51440070a155a0041d10162030325515810288101941400b141c07605e100d10380001c0c8903500700141400c0c414014048049081140011084a802c0c022000e035034030081e00810f01c856045044201501960150081c0d9104600c0e010000c6040d10f40002e00b105000c038058003541c2810410b400c10b4610641810741c502145103800102e00003092050010202c0d29016980c410455610f845d00918281c5026445446030341400b1040c080c5040005081088070090580868120100d250401c1c001100d0100c115107030030700702400b040c440350000d5410200c071030079030302c041203d2120b90109032140701c02c1d40c0c400c0000d07441c0030598001c109100302a140680584e18440c009048800d122 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 274596681 1250 274595431 274595443
    0x7020f10110706020601050303033607090c022b020a290105030102072609040617060c0403030503070c0c0b1b010c05070f080307050c0d0309020301060504021c1a03 72
    0x49000074600703a9900c0315180c8107010101c000c040d40d0000b007500707504041c0001c0e100d00004084041c8901100880001c0409010141042041e900034100880483e80303055a11075896000e17502d007480c282815400204c0c070009656070a1080100060704004822034031440d64102e03c4180c404501c106000300340451841b09496003025100346080140840e200743e400c24a09059000340c0c03280e4410300c000c6000c00c0c01255a03044080003401c03106200074a0142e488941e00405103e50b4109142100110311444000e8034501070704102340c100c900c107030342d0b8007101d0041d407245010040000d00f0920204110758061403050351207034410000407080719118583c13100190402d4000c030900b1a1580081c0000200a1140c0c00d03020342245442450700c00540ca0301610110040c0340106000f5001000420588c450404ea9524084440584080c02103420000740607040101007603200c1d5280000c005041d1505201716030890061003040d00d40095551200030080c1042e1015141c50b081011540e130160343e0902130 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 274597931 1250 274596681 274596709
    0x51e070203011a060909102c0c070305041a1e070b0a180b0a09060518060f0103030e0f01110105010f18090302030913091a0601030e0c090c07020f 64
    0x1068a4004900415094031010580e500c201d52030007542c00d000381c98550854544507020340e503e000b03035120308142c1c49126a10f580282032a56451000110320f000c881d4242d812084500a481925101d10b440e075526031150749401404688200004c0040320090424404581c0303008000900300400b100769180b0540300420310014014002480100b007000d140d01c0d954002652000801585040d0205800d4521600031b000d440c1c40c0001c40003070f9a8280c01d8010441e880d034020300c02d11081c1026808078a124291030815038103405585c00052800b4581c40c4054101c030b41550b00e060811000d40c050040d40400580c00b1810801001c1c1081c6541c05d0074043c85000b0321001010b40c0c0d016150452289070300010314400b007211406d205503500402d600106841c02c0e040100d031f4000c0c507410101201c60060156030b20081081031410060b28800e00d8030441c85110728003e03242402000d0550003200e4031455900f11580c2d0041c0c24101084003111000094485180f01030a1080358401e5040003a2000304807400c = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 274599181 1250 274597931 274597987
    0x30f0c080721090b2212050f150907030204180b04120909151a0d090807030806091303050a050f0415033215100816020a11090705 57
    0x20801c010303440c9045188036118101d26080c5441424900e01d50314502c42d104449086050544001c9140340740c40c00c600c401046c066040c805808801c0c035042c0d482307491079980d50360f80d80142580701c25100503840d5410301c00c3c07070348a01030300e070f03c509550801c0001c0911a4000e0031560b0f2034410180001e40c4907004600a038002c01100003141c0000c500100400042e400c100a80d07400d005070075010118070380c1a10140c444103c08a104241e520080c40354034001c4612405900d414600b1210500281500400c951802692401c000d07945050070310005c0714003a00e00150015040c92400c0109110700098405201585030061038020010200038158005401405810b0021142c41045a4261045041d4001c1114100f500502ca080e01850400302da0004240034252450000d000074250141008600320f0040c078420b9000d601d400300174080b48089610314558886e581841200310b00005225150781c1d805812042c2070007035141401410b401c068040e00c1031080500014171015400c0b001000004544c81b = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 274600431 1250 274599181 274599203
    0xf15040e0a020a050111030304080904020f0d0f0c080c120c0c0d02071d07081501020a060603080d0605060c07031e06050f040507090203010b1611150705010f0e0a030f0c0807 76
    0x401044800c4075258441c4e4180b203c810804d42114501005072940581c006070000d03292030b062000f18000e1301c42d841d0b40180800300040d20300328490080d4400120414144e1040000c1e46200000b500c04480c2942d4400e815201030003100c003000d1001c2c102d6513018008486040c103111410791600c0c0b50041c241c0b520340240e0030802040c4500345000342500000c0800ca010000700c0d091446001e03001e4600540314070a905803403c1d040500f41d00070406038019541c0030303608021003580c038100b08800e90011501c80440a0406d000000d462518400340e0b144100c2c20006403000c545540d03a2020081480400030140880400044011032828400c0130b02c603940c10060500c0c50f182510703089091600e26004041030742d1042c001844912034410680d01801a0780c0c0e4200b503900804d051a40701c840d43c4200142e0b0045161440d41220312100016102c800d10880c001d200c4518419040c0c001d44500b203440e0002039102c11000e03004648079120720890b107556424a02142441d68882d00c0b0304c2ea000c4c40702618110504 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 274601681 1250 274600431 274600433
    0x4031a0604061a070b09031207080907051005120601090b0d09110d1406070f0c021002010e1b1002060f04020603310b01090e0a08030718090c08010e040305030f15040e0a 74
    0x145c000c2d404070105000d1844d01e4025414030392400406000001007058a40002d40b00d40010413081016143c001c3c4094039010240d100208168003108580c06030605140c04103c01d5405038403c4410380780000c0003e4142145030001390028680380b5130030340b2480d1400c1041420341c0c5800f40302e102c1240c05070384039412600400c0388051620f04003400803800c10110314050070311182d01c00c07001c100041e412038158041c4070344007004901400400041d96050b001f14200c060074120360f290031800000060340d1034102d5021006040ea240e4008403901c1c41205101342c0080d006140c400d00940c5d100c100039440f2020001400f44804201034580c07059400440e182490038180003500170f20500400c00388505004502c1e60000740e07504c6900e80c000050034010003001203680a402100200d401307070440c4040c0c0d4900356070740900d00043c0c005640120045180003001240007814502030501c00c0f5096261585035464031130301e10035054030061240d0800302000417098004e40d83d601450070402d41c4400280841651 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 274602931 1250 274601681 274601693
    0x7120804060e090103171e0310080609070803040e0903130f030c0e0c09040c051905070209010b09030a24060311030106150c0224190905030304031a0604061a07 70
    0x1a001c1500c61030109004100007108400700d054030505424100d91940c60807d51040c07d401c00710b80c2030281d010b01200304851095000c2c03c00c030860320343e6801c881c0c0d1926a80401512450035005c1c0c104203400030482444843c502410700c64101d16110116441c0030300c003494000380c2600d1a040f0243d408a0201c00b00700303102c220407076000604000c0c028140e80b4102104c0741403041c8602100c0750b008a4650407030007036040c0910259401d101503d01c47c9036100f480e010300102243e1003988128404c607213050011500c0c0d40c0341415a06024006030050100280b25122001410507980000002042d90310380171342c410140d406080011840307a054928600d141c01b04260a50b038080d0003c0d003050500d51340e00f04443e640000b40e4058250141d5400203078003242c070401c15040060f42c1d0142c03e2000b0026881601c8201400c81100c4000c07640d40c0c4542180d1074ac0e003011385a1203240310240541030401e007a1801c0d0b034a400c2d0f005030000300003000080c2440d614074521503092034070190200e0813a40821074500f8403075 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 274604181 1250 274602931 274602947
    0xc0f160603020f042c090a03110f0c062b0903112d0106030803041b080f0604060c12110d0f021c02090105250c050f130b01020712080406 60
    0x181c1c00e05500300b190403800391481c1d0045101e0140202c10480190381c1d40505000e480e00b00c1034122a000249152680d4955601e1840483c1200040d0401c0d4602041c0c02c00800c01d41d92400001d40078045400044003004040d40160044a10000d100d20701007050020301e02e08030400d051135800104480b4014200030308100102e4a51200c1da4000c5002001c0f48000121a654000d16910322000d0400d004c038040d0340140740e5604000c11b0850000180018010495814904141c81001c050503561b2200d241d59241d03540d5043c0c5411661080b80454002035442d080100f0b880744500d4560040c160740f01003c030655030000e4031603143e41e000261110804d0468080d40014011091043d89040150001130244074010841c2d0080c50b6404030360351500e41c3c494400c843c907012140d0710312482100c06000342c1d640c0710020802150661600f070070000c0c2c0d0f400c15011140d040c100c018a0540c1e00000c0070644c0024022091016045010f40000400c0100300202c4140003240100c0202d0b48841c01d10501911080e = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 274605431 1250 274604181 274604189
    0x61309140c12010614090a0b090901150c02090415051017010605010503011e0e0709091a0306150a15031505040902030a0807030507060e011a0105160f080c0f16 70
    0x301c0401c80c1000320185507a209044031000d140074038440c41140018a80c034020b00544507800185a500051040c81c91400703800c804004869007441641e903000321943ca84030030540d00c40400e06060880e005403a000941c560300c0790040484000d84004815040f040700e0b8102c1d59100403410ba10402e2054501c400c52081514030b0700b0f8020010107003814000781103070005114081d8101c01c07402c0d19069282c15a0a880001c107030000e41150340303040c070340750181150005006023050186080201030b140c198070642038110300c00c00380c060304c07090f01c0d500302004501300d9808460760856558800002c09044202860303819401d55540008d103e001d0038212844500950f0105102c0c5080c41c0d51480560380200d6920001c0d44d10074030555078eca620b40f9083d40d0500030080040c001610744494a4070303400d419044801006002041400403841f24001507a290054901c050b40000071842d20400181042280f50880d40c000c1508508103030205195a00d0440001c15901c0103401c600f0000003100309249149000e0 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 274606681 1250 274605431 274605451
    0x100c09030204020a030207050c03062202030f0d020706030e120304030e0411040b07020f31060b04090c1704080421060f0c1806140d021b0c1504050d060b06130914 71
    0x9410440c0c453300c0521002103910809441c4981001d04640e410003050000703c610b00d00355442040c40900280d1980d03018409d030303000300c2c5c1009040815414041a00008900720104840c110707143d0343c03402c40d0300c02040d050701078015660f058039040340c50000018100620000150954450032481402a90240d540301a4050485000182d4264401040c06003d20385481040070b40886551100400341c0710b00e90050030741480000d4080344111042e00040d1050a503a242d0140400712521840d0004804030340180000d1401c4c4001d0001c080000c081916101d250329928104050700d0300c0e07440c125401d040c0d02207151550341d405c0c0c410490304000740404104003c0940c14959180850180481024444414103c2c100280310740c04030311030b54191100450b1115406c5451842d5016065031005140301142c4120303c0f509400c14001c40003000c441c160703180070303003013002c918030682d20b440213003031030710390840e0306c19020b0104125078401c05070039500402045a000c20b04646a4000211a660161104c0b8803 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 274607931 1250 274606681 274606693
    0xa0e01031e201207110319051e030f071803080d05060a06020601060806040510081501082515020717100501090506010e0f030304090e030409051602100c09030204020a030207050c03 79
    0x3810526035149a01144904013180303680c0c0c102c40c5d00b5045100b1515010b0f403104a6981900c603031a403241c06803580009000c060000b03c0741076994255180822101d91102e91800030015130854030032019503404102010180070141c4e260340d034101468001701060520241e4074420800145407214200c0010001e50010380250750600a00420701c9400400442c050b80e00c03a408207001d0707065040300000800c49142507414a8802005110981c0400c0c4038001d401d205d11034904800c10507000044026644500000d00700340d2038110415201c0c0740c522011010b42c0034200780041d0b880039046000310210f405070b0103000f011442c202e01c1c804031175044e00100580d614200c10405142d8011004614040081f21100303d84c0c0c1107030b80041e103944500e420440541d0b0820805021200e0300101800545054000900c101e070f850311103070500300c11155090300c0107a2000c03401d08800c0003181e208192080940c40c1041007a9101d4000c1420382e07114040c02c200090b0b002401c0028050144a0551856012405004 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 274609181 1250 274607931 274607947
    0x1b0e04180c0303032d020d0b030c06090d0618050709050703020403170310081207050606030c060a050c010b04020708030a0c0c20040f090507030c09110a0e01031e20 72
    0x35101281c0402024160340c0c840f440e405e0840142e215500021460b25400040d03c01c81ca01c2c0040c0d0082c141c001c4070542000070140c0b142c1750204201190a4014000c0c5051075980001c1066030305d40000d00b910f503903549208100392200e550302d4003001d2900500003000c03058502210071046a100400380b9003050301c140000d00000303045000e06045a480d007043c00d83c907610f907103a282c131203c0c649611501441c4a0503088441c04000d200c050407403180a42c06881d1741d6518882072640701d0700210b80c2c05a02c404100080d015050084024100041d144000080d4483d44003004c40c040b070f4400d00080e500703aa0007000304092480d071406602c0028070135192500705191a030740e400361210360508488002081032030641456844940c082c49032070000c01c1c0c06010420881c00e090362105210700054880700c0e018403000c564541540500c05845001c3d440842c54000106811500117040d1120035041540328000701c4541000303000ca160040907800390010701f01c0341140030118600c01c82c10744400a00d0382480112 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 274610431 1250 274609181 274609193
    0xc031806100302010518030d080907060e0f10140a030204030c080c030c060306030c04020310030303060b0a120903110a030216060215040b1b04061e030207050c131b0e0418 75
    0xe02201d070f081c00c0441d02d540b83c0c005c10594024540c03072800d03094030880702d22849843c1c2c8403000034014045a4155206152146802c41740d00c6103149041c0e80004a141071840c1c0c50500c038030301280c1c3d01c1d00352815108451402820804c2030340103425178400280c021500384188440308100304020726601000704004a440c1000c03e440d00c000d4200c46100d0440480000d1082c0c4040c0052a11088010821580e0303140501d0220642000b5000c240c0c0000d00c1e01d00c0205a100f00c1108440241149854000c1a60f81408028020f407040c604210200308400404002c0d140080003110142842500604110b440300c43c2020f010035041e40c801401c550090306503202068481d1605604176800441d003103029903a00c070b00e40c034140d1010b000070300c0c00803000240000d03c50f500c049004040200c0d4500590704c3e60400c0d00840a0740200400031703055820190741b0301124035099085940190b401d550119483c43c0c1d50340d0111201264903d8240816881d010800451030075204542c0802d800031a80d11014003561500 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 274611681 1250 274610431 274610461
    0x50108160c060609020d02130506030c0d0e0703080d140f100b03062e120209150d090501150810060e011203090506040b0901080901050405210d050c031806 68
    0x44050000c01d864400078860b41e40c0200029000d03015040d9610841204484001d5000e81c40741010084182000306551030001e08890107500c44103443c505200000d2960401403005c01e10481c054818400000f0000f80004080d0a20340d6181e01c002902903841102c503482d441c0018032055980741d0074800c00c409004503201d003c050340c0c0b90220040e100d603201000700b0300420b040b00c0201c46656483c00844403400444c4002c5101d400035584e98140c100340788c0d4002040e805082e0115504c404441c11180742452144003809150700f0142010403103141c10f444690850780e0012039030410b120468010b101904c1d042001a041b241c02d0384041115604c0c00d0724013078010b10706000b44040c031000c4d80c0103582454807a51300b0f5400350500503e1540e45555445181e0a140d0020001602103140c4500140c0400410700c6050710a541010180030b20141c1202540b0b0380809a1200d4407042ea000c2c09014030141092144920a41d40090a581c0da81010405040c49a8074515511960360000b000c2018010800c00c50b = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 274612931 1250 274611681 274611721
    0x32716090f050a1b11070b040b0a02120903070b0c10050108030307020c0904120e0a0b04180b03010e1b060c010e0a02091008070302062109010f0b040207051209040204080609010c0801050108 83
    0x504c00908514195500741702059108107d02e15000c240401e02900034001840361100035021039500d00d00c62140042240100144c2503410f4010107020020721b1450f42c000c2818031800300c15944855160550081110300c01e0b00910115880441088182034040014110308103040758000198a480c0d0340d035040700d1810603004010410900114030060312603400400c05010100100d944841e124400c554050308840f0020546030300348602844a42010300c504c400003200b520140c00e040f22803004000726050700f020820380000c130401c0f0f50100ea11082c854031040351014030141c03007440d500b4010085118005001030300c03da500d1000400000000080b10021130ba41650f902d501d070030703034000182003045001e094005246842401c2000070601035000440741c0e0407200f8104914404072050200320700800a004005900900c106c0096103500c4019140c48040180003514103903e5601c9141410002c0c0c44d5610560344402890179800d800041d814054282032810002c1d0b0720300b10550446035208524 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 274614181 1250 274612931 274612937
    0x8060709050402280e09132105091f0305070906120b1302040801090b1b180117070e0a060815120c0a0312080108010b10200f0f1002032716090f050a1b 66
    0x640b220441c050025120b030340c0c40040c001c03100b4140d0401500bc0070b040e58040700002a141ca0001001a80a0b4543c0c0c0140c9446030b81e1441081c0c0c0040381d40c401022034009003603210010811007091092a0300050001e088040000324018449180000030200082d05480c00e20002881c0500c409c098101600d20403600100d1040074001108016030b50041d01d85248403407044240c0400c204603400020107045500b041da2080442561810212008002900c0f4551044144001d500040ca8180c0e09030400040401c16143d19201d04800611010040c2d402240e05025a095250700c0a403c03016440c0107140d200b00a0210840d0440042d2880074614452010f1208001c6142c61a003560401e0b200f11520f140100c0300d1469824005603a0340a4a001c040a075110b018552506120b00d4000c1d0780c01040100502d039104600240103042c40410440e04c3e5410b440b920141300d030b42e2101d180d0040000c0c445010002025030a4045590070b45100500c201d228904102c401c2c05100c20b4000710040c8000185 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 274615431 1250 274614181 274614233
    0x170c210a021c1704060605010e100207050409291f060c0213020702040603030806030d2303090a080d050a06080109021e120105041b08060709050402280e0913 69
    0x420283e400864003540110000c0610041004201c503130b61040d42a64001d803952090180c10004000349444103441d10350040c2c000381410031081c1403035002030300080d11400b000d6428606512030301e1000924640d022000303042074030520400c60041c614079030030390707081c07a858107409400d140e40604282807034a0001e025080310401c100710314201d0740c117403040e0790fa000340140031080d40d90030001d10f683c0303007540c440d4402d0140460008200340508441e440d0354100c040300403d4290541c1c00101c80f500003e00c007031100d00907a12510f0000d10000001d2000510401000a40b800d1103810002164134541180340143e00d401c50382c10250351450384d2510b001b114a83c07191244140c2da000700d01c00407405001ca85135503080c03c040c44200180000c11860f094220400e0301012651401000d584103400c1d21518082000341d1803d02c07040c02c00e500208020068142d80000c80344409204503104031589003110b00241140d145009145801c2d901541c000000103030b030f2039403982d4985413240e00351010414075119507504 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 274616681 1250 274615431 274615483
    0x5030c03070f0c0204140601030524090702150403033206120c030a051f0506060f0a0203090a030b07020d09060228060504030504080609060f060607170c210a02 70
    0xf4038042d0100d95400380051011800c21281c842d00581c080ea05140842d08190014941101d0515040c002c0440552149524004001403029415015003008210700607a40c20041202031140031070f0140c1d119580c00100a0622400c02e4089441c3d820411221780c0c0d041c04825107125903000701d603000942220482d543d405010b01c041d24140c80503001d02c5d0540030304503884003400b40110305200d071071089510310802000103400c403800701e420840d100b6501402c2805040030365038003100904050001c900469290072100c1e00003600c0c1808550007100c0301090301c42000841c0f0340c1803000410700c090078203180d184a0b080c03d101035140c0340707c1c59080c80100b950f400360709420501e80345128059074210008021500381401c00a01ca6482402200074a100b24400324005d680d0010f03031640300e815500404600358440c0b40030407280e0b1b80441d0302980c40c15861000d4a003c017428100070842040600024910f50f000b0304903604548080d59014500000b050050041c65038000c00c40c4095801c08132011002000c0c0 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 274617931 1250 274616681 274616687
    0x70305150402370f0503061501020303190b1305041401050f070e06120a0204150c0b011211090c09030c010903050601030f050f030315040f0b0a0b181207050406050105030c03070f 78
    0x45404a0f054000b6050000034041c08005084060321419030507140340e42d68284000e41c00890803d0840e005a10400018100100100c0a101c80004000ac04a00141c1d401d00084819820f1240c490200395644140810408180801545801c0d410000d01c41c91801c030750b00c4580e0031401060b01050188100b501d8011f50781c0e801c112080c45200b403d03100075074144491498000e41043c0030355240b03624140d2840c1d00351409080c118044a074421502c1070380e0380c2811000c1042442d03520048440748030700d500c084100e9868034141403140a113584c03a251202482000c06141c1400204010305020000341c050010500c0030900c5030649400c450b0031403103400d29140082c90000705541160044c0004810300109000001103040c081d04101c0f001d100121051280d481201c5909a215078400288a01003054804540140ca490458070022011200388000825061001001e40d2051a000341c00d080c0850714042c4244d8005d82820710342103046140414800c01688030140200051042c0a11500b50880c4 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 274619181 1250 274617931 274618009
    0x13020306010611101a0120030f090409060c020d2a020f010215040c0905100e0406110d0204060503010f0b0408030a121d01090b0106050309150604020909010305070305150402 76
    0x99001c008205c202c000c2c9002c8000d81090900d01030008089040c54401100a14400d548804075040590320741101b1344450525640041a01504262540344c01404104c0318880d0204030202034000e41308130440200300601450140c0b2447c050091400494482071180709840004203070f043c5c4105c43c2000400300180c0c034200c00560131801400d0070008000411244514040c21100c0c001c0b404c0c05191134607008100103e00350700800320b1358540b24001401280442d0005042da0600342c203012b1602d103101c0358031300c2646d12a41000010440c0080100706154501209000a1900c42c0520342041e050100309038891041014100030443d501d0580040e01c0303000d500c1449000040f00c007002c0141660b5a6032801f03804000416a45411040c00000d60f00740188122846454444054521401d0010844070b1461024007080c0e0815820700c984030568844a07440c074065805680141506482c6180c078a1404859019141c142c1000b9001c0c0001600c0c0c000ca40583c010280d140340201d24140300c0c603409291 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 274620431 1250 274619181 274619203
    0x1150c0602031b03071e03090b0c0a030609050106110c09040c0626010e060f031506011412040606031412030f04150911010e09010b0f0306010c05120a0813020306010611 74
    0x2e0000501a00c1a082031841000902500c424410780d08014000c2c0d0841d2320009000d0207540305240021b1020500400030145c00e0010304001514949440d20342e41101c809800440115802807204100034808200d8246a001c04503500011860180d581071458510ba01c540c00034030014600b25012038200e80824100b41804003c0301d8213560795110010014403003614107501070680000d107441130b8103021411600c80444c143c6000c40c180c450342d0044402321040c0d40e500034000818460402d020b515542d5184c001e6000e58030101e44242107042c1419003455103420000c00d641b040d082e00118664402c1981e41c03258240404031080e907202e060049034840040191411645401307400f10800c84881404a032141d0300380c0c1c070354000d81100b0060080b00c900038056a10306c40700c14401b4400d6001480c0c000c40c0e0003541031401c0082040d107690f489141c030000d4500c00c007a40780c000c210202083c5e400300340c1c1980040d02e00c2c03c64180b02c6081c2c010948824041c0509401c000424000301d2422030100701441c110 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 274621681 1250 274620431 274620481
    0x1203061f020109140c0a0b031009090c06180e062103070c0905060307080c0f0d0222050c0405060a080403031d010e0606060c0d0e1801060e040501150c060203 69
    0x4022500c0002c0c02000c2c06201140c00540c040f2400118500008100141040182203040303424107040700b128154000030014000c1a024000105841c800d5000c1c80c0c0c40d0314410300f045a043d0f4100b1701c0190140c03107480480c0120700c0c41c80700100000c03402050960340000c8181c80d200440780074010800c034112100a0041403a1100046007010480350160031390483e0013242041042d42c488904150711240f1510501e1200d90040005d205035103401c882030500c0000092003070300c0404440d030114103000275000900314040490142100c0004050140315406603003008080c0c80c2509001c0000d1a07401013040480030001c060001030201030007503004014260700c1c42e299440c400d20114003207001c0d29a22181c00150700039440885c00908000341901d025036100d2020304507a00326094101c0b080807079442e040f948124524103800445900c8070465028004036520710312504a600144029208180d00c440390074243d03600035001701c540c800b01801005612240140c1e807910745da0110704101c400385500801ca = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 274622931 1250 274621681 274621729
    0xa02030f1b1b0c040c0513030201110a06050f07120b0901030303050720010c120b010806060c10020d02030a1407080a0c090504060b03190501030f02100c0b01080d0e12120306 76
    0x540d0000040e0080c3c2c00c4403c03142400346604000d0115454060042c1620040482c80300500040d80100c02002e0400c403074400300c41c800c582d66140c58060301c03025103000c41810711a03400d01c0754081c0d2149105a00e5120b4090034800e03401594041810b000d01440042c007016915030100d4201c0f0b00c502c01c90013081e82040142021030205480003070003400e10800d800007003601a1b039003160140c028003458607403410584400246541d03200521a550340708041d801c1450240c015140f602c140c4e18409032902010304480140c492825645200840d0b4402202d0f2000100501c2004103040c5c1c00340300c580d40f20313013105c3c0b000c141c02c0c0c0340104c02d88115050b5000140d11504020340403e04400b00c002440c070071120101c54564507410a04268121102030101a00051014201d000035040045100d801c0c00703034074030703101c9003102c0c4bc0c1c0c50344410b4540a8201c112280c00c00700180c03c0d440d900422080c1403810485035241104500c0c4400350707985501300060501d458012000903015074404510a00801e92002c000e40 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 274624181 1250 274622931 274622977
    0x30e0405090c12010e0a030509030708060109140c070210050a0903021804230a060b060f18040e0c010c0605150312030108120405010c170c010c0908060a02030f1b 71
    0x40c0b15580089418050001201503507001c0b203050160703889142c0c0700c0018210001c1c042d101102c066101e900410341600c40c0c030342c000030010800c00c0341c1c0b030003407202c0b000010307030004989401070240c0c4002d04544034040042c0000e0015a0b612414290041918203066648094500701aa130490355070744007a50044c141e052106c426400b0780b404a10503403003040e500301103684020801e07030180c141c0e1643c2200b80e40a40d0981e00003035515800585040e60080c050360030641c488628075447e40c8a000c40301c0c0c18000e00058160301d41000d0050040d05c01d903030005040340f506480c00007000350071048005010706444402107003440c0704030a0701c100c8810000c0c061726140060115401e2031a407080c481c40c0e1403846250788150110401c101680e00b581c1e41652903501b45080380d00c505035030b28207511200ba00300c0000c1102102c41502446004200c6441c0c2d1900000c061400040500303140e001416100720a00402c20003001c0b8203a2521250322003041c1c02c5904010700b0481a9240900581500c1d10340312040c64040c0c0 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 274625431 1250 274624181 274624183
    0x9060d020f0a03060905060a0c081b1e0c070630023001050a060c0308100b040801060e0f0c0f0a0c05011d0c030a050c040c121109090a020f16030e040509 67
    0x5c2524011811035190b911030115070400ca960980002d8009182c031000b1a0701c04100301000200e105682c8549418034040c1360486844143c5183c611403d42070008150021400c244110780003400f01e400d105040b11000c03035a0766285100c0e84000c100c01340c000a0320001c0c0e00300c641e040c1c4900d012181d0042e218400351507029a01002e51503004c09160750311300300010b001d1805040f018242c621655942100c0c40c0c1540c0d0a69031000064141c5005000550300030030b00c580c001d0050802480000c0000c1540345c5044556060120301601c03000002508008002d084e0324032004543c4002440545e0941e03945034984221645511380074000c0895080c02c24069504205007100c040051185081c0c450312042642010f565a5124074001c1150b08640c0c91480d0901d0107901c44204544c0d07604121540410158540e03049503013444030196448008540440c8905008054960001901c01d04519119586101401c0707402a03140c111500401080d9040c1054881c180c0803c0c2c20001400600440c10030707812403 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 274626681 1250 274625431 274625441
    0x403030306050a0b071a0402030c030a05240105030a0311070e0c0406090503150a050613050109060e0709080303040807060b0301140114040207021e0109030b0c030910020909060d020f0a0306 83
    0x40c0d00c01c42d0080e401084070607131401121800360344130001c10070441c20201c165408490090050741d0600a13040b03505556102805400c2c0c0361031050000c3d02d0b501501f0222406146c1c03d00001c09104c06100005101d40c2c0c80c00502410b0340340e0141007910b461078015100750703d0030704c66400000b030403080c410500680c02d0070380b00a80141d803019241c444150382c940c1c0506559102007000c28a90000740c0c40410004d010750303400660080b401910607500c1e40d003443d21020a460003a84450340056588100b080120800600c0c3c1e5040701c0782d440c02c0881180b418410b10b95070300010300080c001f010000341a90800119a005803544680640240b00c054443c803081e003c3d41d4030910070f1244104040b1150103403403030a80300716804107500601241814120074404000c01c0b0140070058140049418040003042031601c18070300c01e125110403e0750340e107001491035003404414001c080c283c07801404600cbe11680e4101805500407002d0b100c5821490890001460040400d066690400d40c000c0012003482615080 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 274627931 1250 274626681 274626689
    0x1c0902040f050606180102030d0e030717030603070303110a1a04020301200d020d180c0311010309081605210702041107440309100b010f0c0503040b0403030306 70
    0x42200032803108514042d10411580b90f0340c80300b01003207981860304c0703072480d82c6408203018030450307040c2450700091340c04407100d6215402c82a4400320b1020200880b2213011030811008540040c2541021300c046569180140402400d00002e40c95004542d1002c101c06154283c1205404003a80c40e0b580c0a0003000ca0261802c0c0d01950802142e01c0d40740700c01c5403c100030900030512a5141c0102c1c451840d000b134010810181001da1a41c03884442981400036108095019014110034540346150524808070601c1155052605001c410303c04902c048003580c01d150020f40503c4807582152620605010203c040c0e6009507455403000411044c1640107803d400d403080e1000c0241801e0125030080c1405102401040302000c01c5240d154661210006c0796400c5c090306030031036003041d0301c0c54030070a45441411540714418044100000e030041000047d00350515802c0420601140d980002c242036445100a014003034944c540308104903080045800409031000140c0c0c82d039440c1e26000f40508101c0c45 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 274629181 1250 274627931 274627939
    0xf0f060f0e01050c09010e01020c042a18090c05070b0a0515030106050307060c081308030d180201020d180f0f05010905060301060f1809020a170108010b0102070306050c1c0902 77
    0x7500050a1905210f2940103420540c4210304110204004641c0700030800d002e0380c1103000c0c007a000895031702c07140540546800c802e0008049681c940a05440c1d24000c0c0780d0750810841803d40c4464800c41c1c520a05040e110820310100f01581120740c02d448510400c0002000550010104a00101250301c034600440002d00e0003a03a59024204050a0f250b550183c40e91540020100b0803900307001c0d11100e02c1880c070480c01d0506081100b21400f503801c00c3d0f0b5020b5913040d00001032031151f18040f403140141d0800d401010290b003814a8000035501c1480b2004841404041c195807500301c4c158030602c03401403c0d41500394400c980c0386ca014640c00d031124441d16020078500800841c3c10b1030030348240ca042e9805070703550300707a0104003003022074003c0207140c0000c6201c4040800031030405260b0000344440c004648580500326140c2101401c203d10581c014141ca07450907031010107030ba07400700d1100c0031260851004120707500c488030212014495000005a9840113401c24046c50b601900880c1e40c19008031 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 274630431 1250 274629181 274629191
    0x206190903110a1824030809040501051c030e0111070f0302330f121f09020903030a050f0c060115230912070302060310141206040b040f0f060f 63
    0x14180560340c20360b8050195883c000451502040c001039000e60361210010700405c4451010310482c000441890f00150f80c2d0102c00201e110050a080c01030500501d41a2400d0110a1500ba42075284040c01d42e00101040400100f0240c50b030311400c0134000340e44030241a607881d90382c1c803111000c0314601d03407100700c2c024294503e01c1d85030781d6024100c0c00d844400c00f040003515103803140c494103041e40c0848150400c10105000d007842081500d95107620600d0030000c01f44000748080d6074080911002d5001c0c60009004212800782c03500e002c001e0b20040b4101c1d040c400c0e1184000d19905d100c82c01602c24106140c41108000942101080c04811710350a194446401c040c01c0b1703c842032101c0104c0350a90300805004c0019000c182418103602c0c071030700e0030318064030342c1c040e140c1d80021a070380c0c0151034181c0311400640c410711502040d14140ea039002c01c00c5a10036115941e1212568a4610041000c1d2100e9020350001e001e10540c00140304003142e0010b0444402015450320308000e107046480301e0756030751500c = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 274631681 1250 274630431 274630463
    0x309050106090516140906070b0c0c01050c040501022a010c02041407020a0b0a020301080706050a031d060a1103040c030f02030a06020403120806010809070b0f040e040f1103060106090e040206190903 87
    0x5401112400c05010f03040600c0c8c80760644a41f0b01c100e1018020000d0366104010035005003030203204043c040d041d02d0018541e5185084002481c020702484642100c80c41d0380350104d100c07031101290025452003801c210301d8200c840d0000500401d0011403c200d4140709008000d04290301083c811b0904d485004412120784035005514101e002c00d008041e52030303002d1401405001d0103040030703224003802c518000c0384041842603c07a843c5200264440c5055018030f050021021441c0038164170f41052801240c114035098903008071080d40c0d4840039041c070a105440700c065480030b00000d5100c9801030015541d550780c9150092040042e101202e002903a606e001c0340803503103e461854003440d04200200030041c109401086240d100c61903a040c03810080200087d880b81260050f4032a502410009000008506007000b00e5018048618848d8100b1030041c85802e4200211030155410000e003101c8540c0c5610119005100f0700f010035414840e201c080e0001e840e80032507610142c0f44a18800c2c01c44002d0 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 274632931 1250 274631681 274631717
    0x203010e0f04110103020f0c150702190b060618060406080402090a0b240409091506080607020706181d090708010c0e040f0b180a0507020a120309050106090516 70
    0x1070724000c110307003d0f04440e03040d150721907005024142980303101c483c94065a184001d141103042341d10f1601e800030b401c3c2002003068050110702d503102461480540ba01d851035590199409009101a120381e4020420710b60071112000503451540000d4480390b907582c0c5442020300003840880b802c13807041c07061000081036600d99000c1d1300003101c0094446400c4290721054044410301014402021580910001941c01100c0c0100180c0700e000313881001581008402c41400d40e07000d50003a0390150710510510a10583c0042c07600111a1286400d0b110700e0a400c00000300280203500c4038900d0541c44010844c2c11555644c007a0017401c5042c1107841e00b660b2240118240c030071075250b580c045400c4404080d1242451b800810348842c540c000050805494000501c4442c0b500c040c81070f10020a004028000c0500c0c030485800070340e9400104940d000555075203c0603c0d00c2c201001c105611007851800b001400d40050015041e0b200040c0410f292a0341e104c002e000104001500082c101c60a01580e040 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 274634181 1250 274632931 274632961
    0x61905150a09020714010c03020405010201140f0f040503040816080d110c01140d060b190c081e281407020604090e0f120403020f01021501090b06070609060203010e 72
    0x12000e0852100075181601c010001e401220040d1159100c180908150003000c0c070036000342c90710300d0310300603202ca0524000a00312048104a009242003410070312058400d106203241c0d0107155a074400751540d6a80c54060b0440c0101e0f03018034500e1169803003c02440c9100ba800b07c0903141030604841a04402c0c400803181104080e210006030307085440d1310b0380154820b0549104491f07030f22810510b0504d602c03000c4012030b00e071903000d011001001705103100e000d107510301c052803400781629044c501c00c201500c2c0e84141d4401c180317044404104101c034403404040c54805441f418000040d159400400721925800010100305000780000c1c02c45408140c034032040780540309516005020b01e8201810900c441004114405029140384500b240c036103aa410100403600701038000c105070701d442c2c03861441403100d5001c0541740300381503400c22004514986c2803c1e166074119403d07a03001003400b00719800840c1c4148200d00b8080d150b1410005050144543e6400444c122200700102a01680e541c1c0d04109691f2 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 274635431 1250 274634181 274634221
    0x18021003021801030209010c08030a061e0b04061b0f0506010801050a1a0d03020c062206080f070c03090b160c090c0f080402031002030a140619060c05030c061905 71
    0x35000311640c1265110781d01409131b0301018141510581c41948400318641c100311061952584c9800b001c1c0306100441c03070081c1200da42d4049254019040c03000c07603000707801a40640c1041010032036003207001d01e1300c3c044100b004941008020388910064102507455840134002c2103802e40c20b08020400442e01480742101c800010055180503082c040704005042011510a030218481c8210304489a901c00c8000e005040416180810880051140d88142c0c1000e5205a003031100c11000c108000902d0b01d1a6917008859140500a1503078034901030300c21401d560004110403c000c47c0b1300b40e883c244213441c4240d260180104c1083c0d1643c0351610410f68220042c0100010300701c50050500c14050641e242e0030070f100500791000e1010000140049800440da203440b500d03260068600c00120b400c1c500754100c182569034440d403401807a036a6203c000303644503034810024903a00345c00c14007a0504c00c1e82c5844c02044140c59050078000d414a00740307280c20142d449440c1c5410b000c1008901d465944910300 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 274636681 1250 274635431 274635457
    0x9060a080703140f0304060804060f060b0d05040512031602010e0d0509011d0306070c060c090605041a0906070326010305060f150307080d090e0105030a06090311011802100302 77
    0x59003142c0d1103200c2c01c443c40401800c03a01c245100c0342d12500082c00900041c001c00c0d0f4910b08146024140301c810f65640500c000711a618045e0b092042d11082c0040b64802600448041501e88580c40c0991801400003c1141ca5550203c00c0c0640e41d00c01000c95030714045594002d000300f02801c0641900c1d00306000900002c00c8003001052000c2d40260602c1c506030b000e10010203000c980100109040c84012a105000506100d040d80d080020a01c2103c105c040359103407401c10642401c101410900c0307680036800c110780a0160f04440112a5400c5820320345029112a4559000d890068481c0c00594015824108902060051102caa41034981201d800100031304041d190b02007100146134010f00030074940484210100701c561800c05c545402040500b00504007171000010041401d035081d04217144121702000108078594001800010681e041a0700241e0004a031a003501c03001c48280180e14075500f8a540c08080042c0c0b0000d40c03001c1802901c00480052003110110200d10510540c0b0b04c1e4 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 274637931 1250 274636681 274636693
    0x302030106090f150c23060105010906050a140c0a021513120b0613061e0602060105040e0a02060f04181418030d090203100908041a040b0301090c14030906040209060a08 74
    0x420b216017100c09409006c5e070941d820b0039032405603002d8020442898080c80d41d00c4100100b01c5540d000c0c2039a401448586400c1d800e1140242c030080810016902e0080f07039900c046080d01c07000c28103000c1031440f603178014086990391804544004058011445901300882c1c40480041c804000d20141a12030b5400400801c041d40d840741040050f1041088207448507a903150082000d10095945032180d2642d98900d000e441c1c6041c400902d480c0058010364025801d100032200100000070383c4400e0207504071909612070105200c2c144a50089522528405c1281c4000c203880b04026407102c400402410b0b04030b40c0a503900c0301c860301d14a083d441100c4081d80b04005516070203c1540c401e6041510090540c0d00b0a90050702701406e48012400598042c2c0000074100409251500e560103000d0026965a040918005d60000240414400d03800349944036040915468824440003104107150b012268607400c1085405503143c0080381c0481c0541040340201c2c01a14001c49404100e803814070040030 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 274639181 1250 274637931 274637969
    0x1b05120a08190603020108071b0803010b0904050a18080705010219050a0210020901090909050a080307090608060a0308270d0c08100b090a0f0b0603071e050c0606060a0e03010c0302030106090f 84
    0x40c83c260700c81c408275080b05481001000044030803006500a080c2803003450b40358420401048100c60020300301c0e103002840c00382c1c80c214200c00b00a01034201600041040d032104140c1c10020301a10400c403010800310300041e40c080a154200380034103807811081c0d0803684001d00c01e0b0f06020880c171030300c0b0242e40814924181009a070031940c1001c01240d02c80c0c002c3d52940c5007113035143c02c25504203131844ae0104070192028010a81c0c445500c0c4c1e40700e0001c4600d10821481c64840c2c030780c1031103050140f22400c404110001e1541c03410441074010000c014082208681d481d0403c043e54040b58064480c280c0150302c40164440d10318000c00400a000a0110706580c8414911a00501c0f01c41180f22555032194500300f025510b0b540694400c1d43c4640b2070400787c2440300c0404501c03030b610418460910a050045090a0f40c001a00e245e010905559681e1344d05082c00040d107000c40361403030142d415030802440255444e8160061030484030b0640b00c0244180e16000c40d161142070500a0b1400c4c5403102a0800d = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 274640287 1106 274639181 274639187
    0x1204080318060f040f050708060702061e10090f06030206030a0e0d1404031b03021002011a0d020f0d030c0206030103060515040b011b05120a0819060302010807 70
    0x410b462915078580080e65030060000740400c41c6140410003080810000c07400908036120440705a80f400140003035954008a0329500039800d4140700b184e10459512030240034864507041c2110b4603003080002e4000304903c2c949846504c2d100e03034000000d83c0b2440004c6010f450b6010740030036641e2540205528001007a0700c00410072606192065001c00d17002c1c1914140c940c80500300c9520312510003245c000401540010f0740c0950400440885c090301540325031180c10301190406411080001044121485010041d400032818401d4610918100446809c540d11030b050510310401a90003107042c40d042600115045c1d59507800348440d802012540040d400800c94050007800d01c0e146c0000c1c4041d15686600078101c10012061042000034092883d408189000080e01c2d88661400140b621000b40e86d00d214500c600134600c1451001801101c0540e601070311030b0103c588900d1011 = true := by decide +kernel

theorem cover : BRFrame.Cov 274460431 274640287 := by
  have h0 := BRFrame.cov_init 274460431
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274460431 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274460431 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274460431 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274460431 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274460431 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274460431 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274460431 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274460431 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274460431 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274460431 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274460431 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274460431 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274460431 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274460431 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274460431 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274460431 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274460431 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274460431 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274460431 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274460431 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274460431 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274460431 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274460431 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274460431 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274460431 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274460431 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274460431 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274460431 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274460431 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274460431 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274460431 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274460431 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274460431 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274460431 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274460431 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274460431 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274460431 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274460431 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274460431 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274460431 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274460431 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274460431 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274460431 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274460431 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274460431 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274460431 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274460431 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274460431 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274460431 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274460431 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274460431 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274460431 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274460431 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274460431 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274460431 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274460431 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274460431 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274460431 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274460431 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274460431 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274460431 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274460431 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274460431 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274460431 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274460431 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274460431 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274460431 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274460431 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274460431 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274460431 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274460431 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274460431 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274460431 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274460431 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274460431 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274460431 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274460431 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274460431 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274460431 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274460431 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274460431 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274460431 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274460431 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274460431 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274460431 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274460431 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274460431 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274460431 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274460431 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274460431 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274460431 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274460431 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274460431 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274460431 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274460431 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274460431 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274460431 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274460431 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274460431 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274460431 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274460431 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274460431 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274460431 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274460431 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274460431 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274460431 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274460431 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274460431 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274460431 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274460431 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274460431 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274460431 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274460431 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274460431 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274460431 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274460431 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274460431 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274460431 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274460431 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274460431 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274460431 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274460431 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274460431 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274460431 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274460431 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274460431 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274460431 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274460431 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274460431 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274460431 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274460431 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274460431 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274460431 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274460431 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274460431 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274460431 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274460431 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274460431 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274460431 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274460431 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274460431 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274460431 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274460431 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274460431 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 274460431 ≤ n) (h2 : n < 274640287) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
