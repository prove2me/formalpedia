-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5530
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T16:09:53.130088+00:00
-- url     : https://prove2.me/submissions/1bb5a959-3f9a-4bd1-8866-882f689e26c3

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 994424460 ≤ n < 994604316 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 994425710 1250 994424460 994424467
    0x9010b01111b0d0b090a120305041a060a080607350705030c04080304091d0d08012c0406021b0c060a111f0209030106140a0608070c0b0108010c1e080c 66
    0x34603da40085020b00344c0324140091200600e000103030200c110341324000001003085514001c1d022124100e9001d4508d0308802902c0d5002404d5100055004200400281390b99880e014000d181c4403040346c0d9440454050800d540013280030035589800d940580c0e10301c4151031070100702c11710f205c01d01522510901070040040b82080c4070660584002d030030014200c03138545c1d50b642400406401030130003102c2064603042c03034660007010200f080614516035440c0e0341102d07440c0c071103180c4900c0311440424050030398803001714511042d11501da50003240114005038899440310924900e0000341410741c10a0381c00491010440d4480e5015943e0b100e6aa00b00001050310f048200ca080120110030882d540c00c00808411405001d580038004004c8150000c02409807285004240b07000c10702c4541f80d20202c070403420000c061040003200d5014005103000c114029540c0d41c0c0000c2c5000030307040101c060f5100d4000d6651aa80302170501244040c8048042d020040020041c100e80c0c009001100c0214001 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 994426960 1250 994425710 994425763
    0x7080702090907032001030501060320091c0f1a01030f06020304021c030306060e0a060e041a0a08030c06060105030402010e012703080913060303080109090309051809010b0111 77
    0x203011880040d600300b2070000b0090001c4170900505130102e0740182c00f182c82c000001c00d074079101e842507100d504061450700404044100784002c69400142c421507010110340700482c9145020380385100d20074421241e2141c00c45052405082034122401c0c03045200c00c0340c900400100324540641910341c0d40150006a60380c0303c82c00810343c1250f41c0000600c480000e07401403002c01d5415404803040340c50554501c2c603040760345403c01581c80342c1413149000240b200d13a603080041c501a405208180300030001c2c8081d02500c5d40105903003402c190710030080c2d904049060001868103100b401e034010130903e0018550301d07165001038411488078401c28108006100001c0e00311a0a8085c582240c00003038034060999034a01c0c0100007580709200c468018011880a109000040d00426080d2071b40368681655076820300b0780140003800405400c1d82000140b840c0011107803100071241c100b10300b0000d0744640ca8503110741d48900b95140801c450341000f981040c009110240444c461f0702e0034055241d01000b42e802d5 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 994428210 1250 994426960 994426963
    0x406080a0f03350604140613051005030a2a0b03040b0711010e0102040303111c050c0307060603060506041d030d0f110c060106021525020a0501050c031b070807020909 73
    0xa008608900e49000c03c6441c030110a405110721440c01102d041c824650040380034a4444810b440640e0090206201d001d28121250000c9600c07104807130790b040c81c0710b999070002490306150b80750580e039a05e940003145100c2a007051040051a0584104440d40d030f1420904103040c0c032000300060051a00e44002c13491861080e03410000f0410540001d000c0c2e000c000d04118000c0d48680700480118401030500b00d1a0580428240300050002400c21404040c0b41c07000c0d10241c3c408225850a40020403082c00010300c0741c420302028500400c1e00160501e414010f010072185000c2c1e024203039281c8142180c141100010845100096090010814141f1080b0680c0500000c0012400348400811104041e040000707807036040300e201c1d5086641200c1c0b00c18854000b03510648100e501e9a00c1d24070180c08442030484c80400074201c078411102225402e07250542101d9060300c0d4090034060020a20450f5244504894691042c0c141c0b0304e481c14146548042c0b6610500000070701800b8a10001703000d8410 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 994429460 1250 994428210 994428257
    0x108070e0a0b1b01050a0501080705040605181b030c04030b07030213181103040809010f11033703050106080108370213090501180519050319020307020406080a0f03 72
    0x307103c0091215092580e0042e01a04090048800d130384107080001500349000d004860031070b00042c6c03488104900d000c50004503030000921412a21002c55070498480c02054000c0d840346180e6000c054071103040d890720720400c0130301170885000c05006100e01c10008010800c074400300c620b003142d4038264820505080c006400c40b40c41c20640f905012041106000102d4024004403001366280401101218020f8800d414889180c81c056401400000c1d07101482031200038804105c9002c00c440600040605556041e03400100c4000070f0b2070b2310042104980100d0058058103a00e0080c1c0204824010a0701c48641e518201040c40000801d40948075030f6070800c152007084d005071580404004070030031000600088081181c6035864a000f400c2c0328002e8003241b06138a540328000d085000d90042200c801c4000020058511f400108441c0700290700321070400341c0c1c0160a4024544500081c0108011200701da884100c1c140c2080d05210001850320701c0885503141c1c07508005103280b444000102c020710 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 994430710 1250 994429460 994429507
    0x100c0c080a0c0504051006090b070206122703162307030813090b0901141813021c03140703020a1b03020f030c010f0509030a02041107020108070e0a0b 66
    0x5400c980414800007040c01030a0711400e46051016442e590404024040c46d03202c2c1500041e40f4203414080c042404008042c4280020200b50901c0c4010070303d00041d0b0f50903030b20420442040400c4110444989040c0c88480014101031350411081c1018840c071449104002000c4282c01d10100758a26110703001c6038150400c2008031500d141c0c6078686004c01e070348906215140081064000240e142c80750003101b0480c00098003040480e440c003e1440140c400304a201d03548450300400100d500003940300e42c01c6c071550b000e0f900442103081c076005001140c9520652403c4400d90785500c180801d4120700042c40c0302030500b00d05a510440303801e0880c10b1040952000b004030306c00000403207405e03148800702d4042d04d000711054007007420810205680d0701c0c407000100f0302041420320301229890250340a4030300c4c01c00160035200000c2d80c0360300207001c07900c0b00308410410b090040381200035541e1051401c1c2d400351203400c080017001d0528001900c0300050784a60310b680c000001c2c02101120002031502c2150 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 994431960 1250 994430710 994430713
    0xb01090807060804052a1005280306050904020f090702071a04060e1905040209130914060c042912070e030111090901030b06030304082a0f100c0c08 65
    0x141c0c85140c000c183e0754055030b00b030794544600200359103224202d200e002044500c0071801081644000148144580100351050521100b80886030611340003000c0285050100400c22089100092001d411108950407403030080714448100001615000320102d1100c100b16070600703030b690b41c00004070700d040c855402000303600840003510324148046802800680f0a10b40b40c250380d045101050007008149005003540b10b800e03640d0204281d06140d80100f00c010405044100c800351802c3d1024190b466114044449040d908262022450709000440d0800c8000c05403d103040d150180d00300110468918070103211480e001c0d104501500070003228950300340f010103402140b61010f4007900030745500004901a500f400010b020903400359044600350300005062740420303421a01d868228000040c50b40c3d409d44020040420600380c02c02202c000004002d0000460161801002000340314007414540242c0c0c0c0125101003a50f00c1d41c140c04032902c0d107894114203240c118100349404c0c2c041c0d80c0c00202c0f503 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 994433210 1250 994431960 994431973
    0x21201021608041a030f070320040e100b07150507020312090c090106051318060f18060e0f0a05060409021f1e09060f030e070f03020418030f030b010908 67
    0x30440920081d00031580105000c411044c16158041c00300d101c204c85410083d400c09000a40c100c0c0a64048420700405a85114922001e4020303018650f20907080031070092901002c1100c40c52150014030043e011f0062030608200c0d4941c2d42065a04080d0030840049850b140003480c0240700f0410350300c00c4074200240752411708148003d20b484c1e07228003011314040ca8040c0e00224400e4040c4080301c400201c0100c06000d020f00d4000003445000407107400404494a0381000100741000d1103c070170161041c0500382d055080c155903103000311100ca5210202c0e42c0a51030400a0110b045940194000ca078681e01240780da503903000040080c082e41b14006c2d4040d9848c019000f4550140c02c02c21160343c4161645d000c2c036904c140c200c4000b80c02c0e10402d0000101d1441e000d2041038420200103130a1426820041030200c0d100c1680e071304148407030b007180300750711800c500410030351800c1d00594000840c90090203102111603140200100381041c000c47c00c0c582c035041009440e034480c060700802042090b0540d0308 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 994434460 1250 994433210 994433213
    0x160b010308070311011103070c0302070e090303160e0d08030705070b01030c0510081b13090e0616050a2a02030a05100b100e0904030306080105090705010f050403030c0212010216 78
    0x7541c00c190025400600d600b800c0d810403900c1440380d5880313a05055502400c1d56a071540c215040c42d4100b800300c0c01c41c002e070340000030281900d00f41c2a02034000c0c0c4014644900e0040300c0311340000035005800003041003410010140b501c58020340c03503880f82c005100d69540e50b5217107070640f040e2044060007000382203024000820f00411020300e03000d4401c102d803080300c0c002700410103d4040c14240e9180400c3e1544080c0855050035010080410340c10001000041507500c0348900101d0700c0d2102029241c2c0c0000081150105152607103d200c0350403030611600f8142a003200400781d01043d03092441d2a00900000d100b010001c0012440707a80d40101181c010481d1490b0850701e41c000345404e40c09a80c14000c40710f0079807414450320790b0710750013039600e1000c8400c6000800c9100e0101900030340c1896500d100c04158000c2c20300035a4881e41036080101b001500e014001030030942c2003944942080024042400081d6222038504a5590100c4150051680c00c42c0120b00920503403084155035084180c2040 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 994435710 1250 994434460 994434473
    0xc031b07060e010605120c0d0516030302011b0816200f03071b0b160606030c06020307051005220c121a13030e0103050406111317070812160b0103 64
    0xb82c01c0803080009000309a5982c1c180105800850342410032504100d13104000d40c03d14030504041a40200201c5246c440d1074104e800e0f900005410940042c1d450340192601907010700707601c607680b0200345402c1009141520101c000c08824004800400c42140446c08401c050b4500203500d9200c0704c030036034005d40e4401d110b540d540d5001000c200c51418032600c50840314849105150b00703c94684074014078000c0f41c580780d00d104100c120004c44e041680c07900b011010a80704041400502004c1d00116651851382c1481c40c5030889600d03820a05031f050108114240c00e440c901000103e040c00c1100c00b592541d850046120109a001040115551403000c0e050205100951003d003901c800c5441c0035480d6041c1d0014082d9410101502064000c548203100d9482075200b503900c1801070b80c0c00184040103008003081c66010383c40c5000d40d022448018402d00c2300c45050200700240740c13801040180c0c584404507454001c4007410003905207012170b00060040400d9000d41d82e20b644542c900c16550b8403890080c = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 994436960 1250 994435710 994435721
    0x170c0304050f030d050702010c0c0f090f050a06050f010509010528120603020906121c0206062b0305030712060909150213090b0103020f030f0417120c031b0706 70
    0x1a1140c0e4110003040303001c0c103010131500c848590507176510b4070340701040d001034450821140c1e0465610648110010744103410001c9cbd10044d080d944008508401c03507440480903640007800c0100610700d404820030040da54517881d8443e8200c203003821600c994401005881034040c00ca14000710b4040c810303c4c3e405040b0741954030860500c081e00c0d60701c0c3d12400704051b00f08541403400b00a400080d25004200d40c1d1901120001e149602201102d50040c410364080682044001d00203026038404003d0254a2419490034103801c00401c021004001c10068645448034a24002809000000002c0b0300d0403803161420300410700c0110700501c81c0035564152640107101070941074440d0081380003200311005580c021964024020010840a1410142103400038003043d005181819070810100c20001082c0000d5840b4129220b41c203000c1e4070305070900c2a0403c82c43c02e0042d00d83c0c9400c0124503000a8032809860f0060540d0012540701da03a807ca0f00380d8424419031280c4440d0070041074920410103140c204 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 994438210 1250 994436960 994436969
    0x1020d0f0e19050c151909060909140414150103080715141b0c10050a0507051905090d020d080a120203100b07020a0f0b0a030e15060904170c0304 64
    0x1c4030610081c0407042021006010b000621030f030405a0000010300d0300d0003019800c103e03007014181ca0098025108841601c440076020701141541c502084038540108102004009400c4144050f1280310540442040300030001003810070f003841071501281c001c000802c80f800781c6030304170314841d42c481c100700e038960b0843c07078044a1080808460140000c03480c020324411146490f2007a009440c0d404428001a10384820300b0030048041c001408429000c010214040c80a0303000007513641000e20100050394401088202413100401c0035208510b041031500d280c0c07171514540540c50310350a9000075070074104054042d52050040c1c0c2d5400074404520000c1490486540300d4203da0400d11000005030b0208903103c0381c0803002d4450030007020040c800200b8890380b009103244a86030301c44c044052054031540100c00b40c0c04000c114061090781502c6031188a0103044001d01820405880d00b0041c92001803505016500d4900441c007040342c14244e9012500c8102c0030b0540319020343c84031a640fa0003a109 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 994439460 1250 994438210 994438213
    0x1005070b1005121b2e12050a150504020708090d08040e0f0717040c09020f0d09030e030f010603210309050d03150608040b070f020a0f030504141c110301020d0f0e 71
    0x1c0e80709a40b40007005c2512580645030710003c24007859400d050108044042c00c401d1003107070f000780c0e511600340d40305840c482d2400b46000100007104007070b0307091000c40c19048207009a01c1000503d020600c0c141c00d441c0c500c0e40450b006c0907031078150b00d40341025028aa00c16500d00840c0b40078021201c840200b00c601c82c4d18a0b0343e514507042c40183c8401e24010013030b203000c4d1000f09a50800c2c000c180e5103800514030040d0301c000142c64001034a6400c4100c80f8480410340c00620420040c082500d4288250682403851070028004d4506644501000340010081e1180d0900901c85410f56240281c02842803540c1101c01d483c1683c140301c002401501c020740304242004080800410954002c0b00301c1030196403c600c18060964801009030703600b140d034590140030741c842e40f000354000a030200e02d0034850a2227650b80039140c0340b40100b603440d4100350307005051280030803066010400a02c05000140190084034001000d811040409c0c0217104840c005038031981000040c601740c80e0705800c94898104000c0 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 994440710 1250 994439460 994439503
    0xf0d0902010e1e0603180609070e09062404060918170403051e1501180605060a05120a020d09050601290403031809060303030c030b1005070b100512 65
    0x704200001851440024410f0005a4610a1414150055540728041c501c8141880480c1c024580c58104101d500a407240e001c03540c24031410818108154200048600038102414000078902180281c841c1c6003040b01c02c039820035150f9035a503401807030043c54104000c00c23040c4000920100c08881241c03007902c8982221801d1401c0ba1aa1b01c1100d04032a00a4050110070100b500d0b9080e880f02d0044032584288181e42020f1190310400700e03894000e1901c450302c82050710091640c0c00550342150702041c4100070501c00f4004103500101220010725201c00c60004c2540c0c0c600c4500c000303000c0d562010503d0341c0390200040400c9030002d9513a06803990b0840c011100f03003291254014112140c0e10281c186202840b00b040020700031441c40e02d100049080c0d1142d41500c440d1440111030503070340142c0010b03850703d24034481d140d0188546c107807200c4166110508642840e0f406401803003080d0b0024a450410380000d50001c1c2c440001401400b00180107030a620801d0075129034404402303100312100c02594 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 994441960 1250 994440710 994440737
    0x70b160c0803090316060504030b0402270403020c04060308040510090819020102060f0c22090f0222030507060e0301020408071d0708060d0228060f0f05070b011a0f0d090201 76
    0x38001c40f1b0041d03460902d0b260450b074451214400241007241c0103003c203501d0412a642c1132110001200c1d5005400b030884c545070400924100c0f8000c0f200d402079203482070500101c2c011f03d0403202a15815122000034020710101107071403086070390104032540250000040e210215511082c0007074001d03400c552441e01c5982000d01e07096000d4480440c0750400700035042c12480092120703c84402425001c012199490003800182c5448080307102c041540020a1350700b000703042e03800d201004005c1407590030041c203540d680380e650030281c060702c01031214005080305070f903400350100c0d1f014040306000e45174840c0c0d4820340f87c1a880b0707690032000e010104a00010740c1c00ca1040c80e065108a0004100b401885803e400784244411002d429404440c000c00f905507c6c01410038140001b021140ea800b404442441002451045001850030411604024200214005000c1c42e0306444c2d003850f02404c403035602c0100c04240e118040b00305504cdd41c0d01203401ea0410115920440049000781c071100b03811000f0 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 994443210 1250 994441960 994441993
    0x20d061b1805030703060c17100504060e04110f151201080c010206040c030b0714120405010e0f0709180b04030e0a05100f030f021606050a180302070b160c08030903 72
    0x86015168265008004c00c0001c202e140c1c200224603003403810002c00d04130707080c0c2d1342d039440c00303811101d9407003a00700c10b0340400690629109840c01400c80703580c0301d003050800750b81c2c007075280c124030a601d88900002e402c24030710f40e90b591081c0060a100312101e0780d0340b503c40c000e013074030207440911a00105001c2d071000b614480d4000314066100f00c0c2d11039202e2204038103540c1c40030305185000d0982810021800300c0300c4044c40340036004020b88144401e000d002d82c07802d40342c15800d6400c201040d0100f6041060104a0050002120402e5840030b15021855001c0c1c1d42841008807003030a400b500407403840051105054201c0c0150f104808140c1c0c80d0b03200b154a4000740003c280d400340780100050700d44100d20b0b694511a07400340400030b1541801500d8036500c0341c4501c0040344862030070b4500c0390341c0320140484152540700d01d1a14a80d00c41003000c800801e0f440180d155081e40c42002c800c00000500c3c6060030000d0001001007175404410460a9a150960560380f6003022024500a00c1030b0300504120500 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 994444460 1250 994443210 994443257
    0xb030d0e030c1002030d0c0905040603051b0411091302090612041205090d0b090f0f011a0f0922021306031101080412030c110607020c1504080a030507020d061b 70
    0x150011883d00b031a041d8006d009100340e5500104110b0700300400300f0142c0d11801032800940c015001071a403c4c0d03046803041100600f90101303070300c00d40c41d1212aa59580d40310054a010800803610030800e0064070b61054003034800d10400a0344098000780c41068003d0080700c86000740e01501d009020752a010b401940c080c440e8180407644000500210b0380041d50b01c558142d404155402691480d001c2459a02e14003040c10f040300c112030351501e0707802050000f0112024129002207807864040c00c100004506181c3d00a890900020a426a4aa41c0c1d5100f54400078041d80e015111125540b0b2800307d0a008001c1c50104950340a41520741001e191700c07a1860328055900000c13407035044e06466400750001c0c1881c1d5100d00c20b00c99104000c82e20007200f4480c0e01c2c42100aa000740c241c0d000741401704201d0041e8208170184c1c180b0103120502c01041c0004500f0141541410b000e40c1d1411a400010455450b5444c0282007a081051844440c02d16410110011104c4c0d15207410950440a12449025 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 994445710 1250 994444460 994444489
    0x50d030903080c22090507034d03040b06011e09051c0b090708061803190e03031c050c21100f0e010503330402040b030d0e030c 56
    0x200b518000c106101c559030020002003003410400120400004034007001000594020b06520f59a2020008415014050b014681158441e4824015201c1e01510381801001814000106030701c200e07030071002c60811141204a13500d081543e12854649072101d03401000729a44d5000602c09407041d00000321a200428580006856100d10799081c02c043c00344110750b2a001d5681070319040715003c042800c1105181c000d102c07900240203414100700400c0e240500151100d1f0200708210912002403601005840070001c1d52603900d002e0280007c011602c400d08102241d82c140030000d403195401d00f40503c1003c1c0703070b4500b410521007a80c136a0304183c200c1c01408144a02000b00c4074800340b000d038a155010f9400040030b000001c20720b0f20b41c0921454804180c100030743c040e001d00010302c0141380070070082e9915088c011041e072030328104130080c1c034604024000744504090160086811592160072041008101900301c0d4038410750440000c24910365451988d0081c010034441c100203080c01010020800c = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 994446960 1250 994445710 994445717
    0x51b032d12090102090613080601060206010f14060f04060f080c03060321120721090c060513051f08060d1a04140105010e0124140a020c060403080304050d030903 71
    0x1101100c0000070558010710046041d50300f0001c000c029921384000d403003000e9086612007009410030788017900e801c5040e00400e055500440040086001c051828820340d400c0002c5880315080c504040351150003854904610400e0101e0040f4489901414501c00c400642d27551400320b0715220060074140c882502c20503010740100100c14030303091000111040911850710007510304082010b009030180710035110440020104a030388506c800760585040301e24140c1d454100f103000c0080c2c0d50158400c0c294441c5a0038014049102c9002d07082c0b00ba080c00003841c016110f2040802a24070b1200311075800050880451040000b013846420721090031981141d00407172842d1012000c820400f0300b0700005100b10354150b10301c4c0d002c4900e0b01083c0240760007480b003000c000d925541807140e41e0304006030541c0c0e001000c060b0015014100c5521166046500316190403c41d41c414184808a007030503071000c04242c00c024005400010408004000c1d03200318014400c0d100c9500410100b00c0940300b840c032015000 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 994448210 1250 994446960 994446967
    0x12090e1e0a0e070b1c090501020903210702040507110105160201110f030a05040f050106060504170c030a1115040e0601141620030f0d0320070b0403051b032d 69
    0x180c0c4002002048440c14115010013482d217218042015103000301000c0701c003a5008158565917040c10000102605013444200c8000380d41680d20074524022050082c1c892a1244041443e242c02015811816400000207110500c0c00030540c0d5880f6000c1702401d4015840d0100000c05401802d09031544680d001001c02c0c84c5459883c5503402404020b002500d81c0e00501020400145c030902c82c4d00e0081010f0b4030b40d50b0f103642c42c00c8889568040540280740143d04040ca42c40000e40d4042903034103e0551003070b12110303484040800b10b8041b0941c480ca020313031040b0019000c190845648003035841410301742c3c0d400c0382c2c49807040f401042c41d000e007208980d03905c202c10380482d00080c4c50000c1708040710000030319170503003400c0080064617100280034001c840750850b0f4030400306150303d030250000481020070680c101c0e2441c403098008034420010064080c11500020404051180701101c009030914044c0c43c40d1071880d1800b040d1682e220074005408409000500400030800400e21601010082d41090a = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 994449460 1250 994448210 994448219
    0x70b091e072301210e070f0e04061d0f1c0c0506070e060721030b0f0a050105030a0617071503182a27060803030412090e1e0a0e07 57
    0xb001c10046880d50600c0f03540b8410380310802520070750b0180d0120540d4085400711001104030309000942e001054440100c007000c0c0702000c13009003a140c100d644020002400c2107102c1c651101283c1080c49028240292691500304040010320110841d500300503041000e8102041070700c00c2055510010701642003040000c101c2c50146905c807000303131400380c0084c0c07034800a0380d2110600742c8504248403034501400c01c4030701d8584e4035100d0302200e501c1c00c0d034105881405000000701c00651a00ca02d03810844008005481103449420940041203004000480c41d1000e00042d515406180136507010a031099400300b40c1d6602ca40550b510000719501001180303012512400d00c0c0540a0f40754020302007110604210701503071004a8002009520680d07a000c004070355191074014013114a5040181c1010004e01c94070b00080122900683d112401280c03500c100b00c4140d500e09001d0b07002c41007858011007080110f441d00e10700042210310100c4600d420799501c00c4081c0403500a10401209580404801d20 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 994450710 1250 994449460 994449509
    0x4050a020d0309050301050c0d47060403080405150301060c0f1a16030b01021b061c02030703020a090905090d0f0203040e0a0b0118060e1005070b091e07 67
    0x290706009203802035819480d84003180c01e65070166036403807892800180e1014001841e22403d00d45928800d503802c92950324400318a5010800b40c00310a83c0154a0000112000624265210b000001d06a1611142c2d0303070501c00c1e10b9070843c0c4101030059010310b50b2004100500c030100d0f0305848440e26003e80002858541c5e000504c28502c007150041079114052501842000c241d911806452149a401616602c4010155000b00a01505651103951540f094074214641a40d114006403540307929074030303284450901c00e10f00d200d240181138400020300454680c150002c103520010b540390500c103c0d680d0300000080b1032044480304d00c01e402502500709258415010782d2008810791040701d081a1302da543c805c52445064031702c8401c2c640e58096030b140d5540c01c2100a41f141001c55400750705949000e5000d040c030152a00003d01c1204202184c1421a0150090310b8800e41c00c400c0301942890464803080d5140148000c01d0500550210041c03444100024401c0139500b07030740c80b0141100421001d68 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 994451960 1250 994450710 994450729
    0xf031203050c090909010516020304030308061002160b031b0403111003060503012f03010e161202120901140603031b250303080106020304120f020f04020c16090504050a02 75
    0xb00094001001074034550341d11000440d000703440c050b00014240c00d1641c01240b00c110300d62103a0055400c14002080421703040b03d010756006400303481580c1c081400d10001c90a100340c080010417502402c0d440410410a00c10107103119117101c007045961103031b00120540803170081d840018031403525103556034203d050008411100901500f000b190f0561500000f0303096940c04031030034680040808070280794040c014042036960661030041499941030000c3d08401c10001031808002212525070305414601c507018004441117412021511010008164a0190016600b0882c03d600f004031600c5903941d00c002481c00f4200c010000c40c41c01070320754a02008003000fa0a0310041d40103214881c004211801005035403000511040f00c4042d0a600d07000d0200305060700100211f500c00d0106108420f510780c640c00805421601e0401c000905200081080d10b0706c14881e07400600101c2c3c2c40306c01c5500003c4940e07110a1070000b00100c1030304c955400003140d408850103003055001c10264030140c14101580e = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 994453210 1250 994451960 994451971
    0x919020901091d0d05210105011b050f030a0903060c020f0709150f1410020a0503091e10020102040f0522020a0c0807052404170a0513080a0b010f03120305 68
    0xf00a5951410654903003010480c000801c0400c2001400060211108001c1c000007884420310503440d50504000800c9440307442c6408410300e000d807418105001c0d040040101c0d1502e12422a0f0390303805107100080c2603468911040340c01c00e003080c1680e451580042501c041c0b803100900141260b5240c01d20400103403508044030826a0642800407030102001d280a8024000d4421007010003034152091103110b1498030b205000315084404000c0010740088100ea04c0e60000312545001c83c41004100d480341100c0031030780c40d80103403585a6540c9440d0103402074000c17510300c1c0c98018001a13580c000e01844401d00c50003400e1103555440c1000141040da4050711140020340b52035071080c01c4030f07030f169104c0d5404503e0941c0c0c04d41c845068484005015140114003d2002c203456001b400d007661409005050b079a00c05200d03000114a5069451117941075800f04c04006a181400c540d80745c101c5503c0705405841620b12400c52000420700725000c0c10020100e9a008070005d45282c1e55078021070041030013801 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 994454460 1250 994453210 994453241
    0xe06062223030d120b0d080f1210031e06020d0e0601050a090e250803070f0c0605210417040f08010c030c05040b0c0c041a040b10120b060c0105010608091902090109 72
    0x741c031020840010182510140c001003a40d0f2710343c0441a205001e810003408548114421041400000c0451080e40c16801c048516588907031900c0c0342c030001900030500c82c1c80c0c125181104420342d012002410310304036082582c03100415070702c442c0c030013041d0f51201c80c400a003540040c9604458000f4118030440340e554240c8800e03103a60b02c2d0000307e41554000345041c1e507030144100c001018000840c0410005002d103040461030248030f803500341c040c1ca24000403440c40ca48610700050500c001d0455180100b070754503c503a60f485846200c40f14803030f0428042c2c0c14440d8a13104e00158842d009100e204a80060740c6c9440c2c4c2801c5c5001642492076001c111001681d02801150300d01548680c010007403241d200e00100303000c4808600034042101c0040c02c5607071003441c0304c40100700442d4100040705030302140e403031022400d000c1c02000700300c0754030800f040c00034290303c2c100001401c5a40907800c58010504401a91826103501a940c551203c1d502c030003075801103c2000401446170164800f0030322062000 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 994455710 1250 994454460 994454479
    0x1061505070213050705070501150608070509040e120a0201060e060901151407060b010318111507050a0507060f170f0a1503080307030b0a0e06062223030d120b 70
    0x4029003138078025100038005c41c1005c170303907001040404e014074a00c078581100c0342800755140c80001441004050009414010001450092621160031180780d060491003201e41d0350303000500b0130480d5489840c4400040d441c114004c244800d903d01c20714011800100418200e909000803860501e200e050314105201f010411242e0443c000805000d000d4001c20002591070603c2002405881042d6094480301d0b054201000008640b00c07174281c0303410401d03501501001030b07100a10000e845034120140481c880e107000302007008400500b00c0c003035421540d507224550340f0000e0f003a10340080c40744013120032018100c009620039070f480c0d501079070240c0c040e900031a01444d0346545030300100294000350b07a450000030810188a402d030240c40e125040a540c880000f07490204042c02140d009031140e4403840c400286d102120300003401082044a4180c0c00c04150760743c0da0108800d10207501c0205400842d50482c0810a240116a0040d00300307240d104d03c20710344200d0719076034010010400c1c11a8000d0110 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 994456960 1250 994455710 994455739
    0x6062b06080703020108010b0a0f0f0e060f030405150c03070c030e190306150b0d0504030e12010506030c040203070c0b04052508060c0c10050c0415031409010615050702 74
    0x600a140051000e44042c003015419400018002c880c1604042c03001c030001c12510803ca0b500100391500000c0c9803403d03a406140700307801203614030100420a9840000420f03100060b00c0888011030140b48075508642c0c9900080a030340e41101b83c101c940103864282400051503040c00b030b100c545680f9100303241c408800300c20400028030070750b0483c00d20480c0d2480c5503002e10030040b05d8407803060780103103416041ea43c15151610003072480c45420b04d5010040d4075500400e08042c05090880c85112000b0100c041c0c51920500305c4e4000d01c0201c0c1c50070b10a1044098030348c12030402e0320849007d20380566a00c00b00a03542d80300c03690b400e00c1c09002221648140125001c08009154815058100b594160b40409107000c1e44989081d4001c0e11a102d000700401084500b00c10000304420340040c2c00340c010a403559040d10702074040c0110703485070780540320001c5208200390b410340c0404801c140741040c0403c0c81e21601c83e51401c940160080342c0158511001014180b8002e00141c0071032480180320700449480e0 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 994458210 1250 994456960 994457047
    0x40609061d01020d0c140d0f020d2a09050607021e19031103030c0601060f111209090f16141606092105120603011b09050a050303030606 60
    0x1d014044209940c041039200118099003d440848034551804c101c3c1940c008040c4a41031140703404440c041540c451081c12268132130340560340301403070107001041007420707025041c6000400c00c2590a0102046555090128000c4a414050300c80c082c1c4141e003060540d41c00d024000d040ca46c0c00300310141c12071203440040d540d0780d0316000c08950140304101c0d0092a501e045044908c1450005109400900110b41507034000540d281c11102145070420443c94600e00544200510440524480c0200d0561090a000c0400201113003201071741d10004950b00d0515601c5aa0001e0303a075402a000d102d11100b4146e48111a15407a000d11a000c403407810000a509606001c0b040c00d08503031443c1c90380051800d01c4550100200d0b040e20070149c1100c6107071641c0c0c000b00148100c55411038075445400201c1c9c2d60362425480840351800d903030020a0035443c0440054404000780c4901c0d4811000e50a001c01c1e20305011059074007500700502035904200c421a01c00f402541c034102c1c4400101c10800324000c20411 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 994459460 1250 994458210 994458251
    0x1f0303050f16061a1815010c38060a06081e180708031222150e0d02010e0a150216030305041106030403022e0c08090c0a0303020604060906 61
    0x4104000500345a1400c1341e000c15940c0700350071610441c0315100103404c0040c0c4584295125140070700742c05001c140c100060300c05100f0104003a018609203030f4070107000d20b08040310200803030151004860015100f4524005000704540d07040e0416083c0f1800c10201e40105001900000d940c00c540080801c000701c1c0c10f40c400720440e400480c10009681401c0c040b1814415503014000420103103245c03641c04a8003001d894005450b0144150001d07170300709051010120b440c403034035500070384907110f2611101c0410f003d00304002909000f0300030606c7c0c0d01d44181c0144a90500d041290f030107080650420f403550020907920410341103116800b048010b1590050810224089100703880005860900e41070489519000cbc070b424500031080ac105102c00700c3c0d00010400305882010b611000c01000c0780001c032002101ca04207070400e050a04024980f00d40d04944610300c29003501c0100c07403507100c403002000300301c0040e0b20001d00960840b10119000c40c02c260019000311780515000b0555200f203c2144a1461 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 994460710 1250 994459460 994459463
    0x60f040e0106082a030307020a120303020405150a02010c110d1b06020708071703010b040b070f150e0f0d0e060a0216090501030209090c0108130219030c0e1f0303050f16 74
    0x88005508031300318010200b600c680450305034002c5080c521190702240300c50701c041c0240074912480407480c0e41014440d80417540039003c040c1803400102c0700b02040020742c1c3c0003000060007650a050b10750842500c01d090304501100c400008001e0760030081c40039130320240845107103001c0c7e801360807550010450b280000c0c50064480c000e0315603120610704000c40300e580f082104100b081c03410001041104804c40a8505a070061202e6030b55403000c0e80703040c104900740008010080f1001640481c1419401d500885021000500ba92402002240c3c40c1c0c0d26078020b101d410020032031131465031000e810501c0141c041100103004444406044600e255042c0c0001e1303010500c40780c0c0314801401141000c100782500b0a42c0140200350070119100086c1603403400a00381950182d1403100302c02950340307981000e0000d15614007006102c175280d06000d2243d081c03d004440d10000f02c1c1d8041040060803015001c03081c0a19012511054156602240d080d88409200101c0060501ca41511103503440d00582032070f0b = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 994461960 1250 994460710 994460743
    0x5070c120b0412050304150506040f05091b151e04090f020d060605160b0c07080d0207140601080c0f120d030914030a0929070506040201030b09060f040e010608 70
    0x245054030300030100060b80c640807420007100388240b100294818084801f00041d4050105142d0b80b030700041002095050700e00708905040905002c44031501161207050300c80c6804652809513004000d1151a1034501d0a202e6044000c00889040e0703800481081c81003801c105007a894035580d05101d200340c40c4060790404240350700080c003151108162003010700406050030081d09042c003041302c3e0025040707007a4001c1c0c44c001c03001c8000b0314000084002c071143c080d841507a490300d030b0380c02e02140002500801002c540700d4449000c03a0445170340028019040710f00243c000c200110340311080c0022607150b941001e41000075070404080c101010f02c001709160010342e400044000c0203040c80046190816a2040c25810070040100901c1c0d01c04408015512940b080c0704040100c40794031007d0010107041c4041d507007004038403a000c020010480a0055000b6030342440026060410400581000e480480e0b018035540c5030b11815043c1908044502c05000000084495540d8885400d02d25801d9403005079 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 994463210 1250 994461960 994461983
    0xc060203090c0907090e061203030727030f020a05010c05030313020409060c020f15270a0203031c06090501060c120215090f06150303030112140a0f05010e06060105030705070c12 78
    0x8400f03e40030340c5c080400c0b01e90108403456003406a8490ac006404501044841c0e140050200800b40e5000b000c12251100c400c1c50310b0b941d0800d602020b00c03001c0c089214403100c000004596102d8000c20840340d8101018510790789902846a044000310700040341c1050b215840c040120b860b900c6010710322034154014248041c0e086500c02e0074405041d650121001c0b4440604c803240c03106003004045440ca20007090300ca505400c26651400c003d41c60002d5051000094402c981404c3c564001805204031005020483e25100804140c4000b4000c0000041c20a403464020501458045680413040e00666a10745070511444003001c3e411546001f569104510b0400222001c104060340f0901c0c2d0b80f003001070b80302508002904e0707200601c03860103401180c2c1031140501400a54082c0c4610652049500c00c061901d0024881403c1140659a81d443c041d01e01c190301c100482e00d98441e033700595406295984070641033340c59801c41c03001a20f964000c103e020410100c2e003250b0403184c1e40104038403102c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 994464460 1250 994463210 994463219
    0x6211e011823060409030207030b161107060c0201051804110c0c240a050c10050a0b0402090a0513020d06120b06030d0801030b150415090e01020a0c060203090c090709 73
    0x2510382d01d1400c00c10402c03807084116031108544008940140c0100d40200700c260190404070710300081500007605200c142c8040c800e8240000c2e04524050b240c5417900d040d0009c104003d5616148544030b045c01148103c0c551400541c460030007801e0440a21541c01c1241e080407000c18105c54084101404a03400022003030001c0400b005a803c054030201c8421805840c01e601203c20050850781002308a00c01040c0f4800c4640240c2c2501c168888071001c4038201418203c4d0300001d8035003a0344d078000892a105031a440c506090084501c4201301400c02041e10b483d04c1b060280104050b404225055070a200e03019100089005d058014419102154030640503820300751120310001c1c080c1c030301c6075200383c0b400d00e21035800010850449070410701000c000d507550640d4810341041c0444a030f51080c43c0032030054540308101c0c4e03500c081d910021070410130700d112010214200d100c1c0902c51008034002e403540c4400644140c0046500154150a4420b079113030410104d0500442030b90383c60042200c81c0f00611 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 994465710 1250 994464460 994464509
    0x130306090c080c0d21020f060f0f06101704030e0612010f09200d022b1b020c0d08070501022704110f07050a08160302070506211e01 58
    0x24040030100d0702540070740d0781039844060075071340c4100d0b591000d80b0340841068120700a104c9141c015a18405523105807900c008000103074a800c0340d503000501601008075600303003403171f2103c80880007890721013450110b00c8000c10014410018822410401c4600064000340c6032503001d81044820055103440550614a084845800f00d4018141403481c0c02030f4410b864025000500c07072200f0b040913841d41e4140810401c0c01911a0340056400301e01400009a074140c2c14074003084c916030514100300103003141140314140301001c5407000001a800016076105614101c048256018400c68805240c1f000c1c0b603984500ba608010401268040354040d54400c4070244000d03000303074410031a41040002c0d15259003d5040c0500c645072882300034041a100c0810404100c6603040c3e0b90440b0003036440c0c0d50020184441c10161000c120014091500c002541c4e06001c0169515107200d1414004409403415441000c4400207000a001840c042c21203413545000010f02c1c1d011702150050180c4280e0319540782d8 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 994466960 1250 994465710 994465723
    0x8040f0c0f080c0f2d06070c05100f090510051201120302070801060f031106090d06022a06061002030d02030c0a170f0115090305030c0a0308011502030f130306090c08 73
    0x20700504e4161910b100940d0740100030030403100c0d5000031454064a0b191002d81e00c1500c248050f03003007031000a24a041c841c9250b10a803c035201243c014148220303200d030880b800c03001200e80c503010404c903540900030340c5046000b04c082500d140c90a10305242c44105003090000080c0d02c041c1d072140384402810107140d030500007031014002000090002c145029005007111489110140400c49546400c0d4850303603804048910b40507004201e0300f0b134070095050030070080d4881501090182c0c41c41000b00d600441c203000702110a036040003d04044d07554031040c840b0718005005e804085010400540503042036502c003550041c009a10344548500b41200302410100640d1124200354200f074003040185101c0500c4107054510000c3c54552400280700117540401c140d40000340240408212175103440000a060111117020355100c1089076038070301e00c0e9015045c484801d600113030400c002c8012006007890040a003544190810110a6600c4c2c80d001c041314400701045642900c62401005030220402a4 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 994468210 1250 994466960 994466983
    0x5010e03060115050d0e0f06190b060711041410050103271103010b0406030813171911060703031a1005040509040507030f0b0a05010e0709030308040f0c0f08 69
    0x50900307504140702c40541645840c82c0200304040001c4c005c480d92080e401691b030440c5100100c9400c05c401c400b0071911460b00301c81030b94040301c02c061014110b100d01c0c000c8034009400a4010b07882e0150680360b00e0074007000000721540094441d050500200c03483c044403031007101d292031071199803410040010241c0d411900001440319201c9441d401000c807220340349400a0b40b044c1c107200c0361414200400e0151613807084242e440341c940400001801076050082c440003600481d10602140c49000f0310380d00314588030244090b50701000401c420080003107400b12425005154080a6003680ca000a40d42d500c916030440000f41c039011008261400b55400001045c2c01322000400000001d40046c00e0313000da803103020303c2084004042002d000050200c07502858010810890414807808c0c01105130380c0503158140754031b140c4800041c06c0b07009511054041e19140e540c2041d0340703103180c5046804000203041544c804000303900080c00030b0385013440c80000700070311410105941d2400410509003c100c401c1c = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 994469460 1250 994468210 994468213
    0x1180e0c0703020d170c0318030c010903140a020706140405060a0e0102010e07083d0207120504050f270a05150901080703230f0703021c05370c05010e03 67
    0x5e015502804044c212684800c4070b03a100c40d2a81c2d1030084100703006007034414000c03c500001074000a621010341100c86150300940303400a0a00e03014000c80300c02d10038020301000607040b5100034007507079114200f28600c1c83d94070514070741450f80307030000600d10b9400f0110700c1000c0740044100a141d07580a0103048209803070800501106460840640c0e1105089064500b0000200e400d641055661403c5125504456000d20b2405020302403024002c1d844400141c904050800210720340c40d00c110f080f81d0949101402e140741840c009000c3c0010f0260201130f2201e040052011900700024612600303114034100f02001c100c4c0e0803d200400306146040411500407801e580052082500c005068000c403644688030701416041d0b40c0768081900e00303550ac2d860030790082d4500c0000703a0340c00007400e00a50f8000c581c0000c6c4c0c10301c408803660039008042c1005046070005500c06200f80d0303c0b406c0e6604420a031610301c030b0013000b250350000c1070ba49440008403481028070780140302c0fa50b40701c2404c00800c1d4041c0c0 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 994470710 1250 994469460 994469477
    0x1403040308010510050c070b0403031713030e0607020d06200922060f080610090c1b0201030b0604090e0706050906220504050108011e11040501180e0c0703020d 70
    0x44004100041c14002c41d40190302c0d1000440360740e44a03c040301c0c82c800340c003802c1ea58000d0310307a1303004c0070742d940607200030750004056440c40c071500d0f160404000c0c00f540c03284180415120143d40c05031804007012000c643e00c4442886041c015031107184260448a104420000702080c3c1041d40741100080d07040c0b051a000410b000b8540030f40c8480e0705c1407421800c0c1450038984080c3c1e4080d0f060140049030001161288103201c00241100b00255031402141e604858091185c0c0b98801c0d0703001c44d9010319103c07000400c100001d65440d980007030a000e0a034010300d404140341e120f0101042c5290b010760302a21201c0e584803200c404500c400d001d954050211464954070708084000051464080d0010090031850301410b00080c28140ca42c17284001c08014109028940c0c1d00c000c000d008008200f20f401c0744500361034401c0508802841420005100c03140c42c1c82c02c20341850b00444044003004242035002c01c12174008160710140151991252900420040d0f0b20059460000d08080c44880c2801c00d110010 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 994471960 1250 994470710 994470713
    0x904151202060f0403050106030f152003090c030f070305010e210c0307050a080307030c1814040605041805190203060601030c03180b07021522170f0406140304 70
    0x200c0c52086141d40489100d0f0311010321803680e41d100d01c03d0f039100405c41d40c0387c00710010400004150285003d40921142c2c0d02490400f07080000755142010014101107484028014840d6220065600000309004440c1c08000c4500441d02d00b031180e00841c4200e60004030108208442405140f500d80d042c0b034040c00b0003c0703020142c0036204441401c1030040100105864032140c0d03042040c1c071340080e040000c07901c0c031401a0828090b90391003910018002820300080203a00b50045140c0032282400c0200d800d6024501524040c10104800c030080d4020740f920b1000840b5035541c0079901241c3c071003e081402c00c20380303860000d00e01440010580f0341000e0a240070000b6a0300442c001c0e900c00802c1c00c01144d90446590101c0041a40c1810176145e402c8103000e480500002c5402d040c416130241d021036002c4510300287d2000302d4000c4484112180310f001c1c14201c849400d0b9800245144108e4420382408d004581d0141c035600b102552a2944201280c10041107501245804100380c012021a2079810035 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 994473210 1250 994471960 994471979
    0x1e091509050630041a0108060f06100c020307030804170601060e100903140a0303050105030a020618030a14100b01030c0813030e0a0b04031a01081b04060308030c090415 74
    0x540404142c807407030303c041c884042d020b1204100103040001941c80c00d0ba10f024900200313034100c0d04008180010303040d0000b0950343c01c0040c9490190a070009a114203941c2c24007080499401811504108401c040b00c540060b107027048418007461040c02403907103a900700640305034844801464201d4036401580100003550308981a0520300c7d1065910141a00c0703420400c2c0e42c48006c0e540010314542182e002241344ac00085504c0e40c0e8079220755024041a6030325020545c3d10621080041d506c0801005203100d91a03d4041303070386040704050141c4001e24a0f82c3c407900f94030780003401e21050580000d4919180145944100c2402c55024241048010381d01d0720000c120180062254022000200d21403040c98018460b9401c02500105030494007038035000e92005982091000f12100c602c0a5020700292400720f214505903240c4000a00103480c034043c20387c41c101a4007081d160000d5442034080003090030200110f2081084410f856501e44840062101710b489102001400810002c42403062814 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 994474460 1250 994473210 994473217
    0x406150501090b0705121b0708070f12020f0306190507170a02030a0b0a140312040b030415020c100506030607090e060d020f030607021f140403030c1e0915090506 71
    0x400410b92034140c10302c0d0042c03400b44824a0002c01b9840420300810808000c92080c0300c4088182c160740405030303610403d9a4440c024007844500e5090010103200e00c10024070702001c51400141080d140c04005000f10b41489001da494071100b0461011040307040d45140a40c030b420418610701020000300e4040048821240075154801560f00040031580d411059000100b4002008002e02022070340c945041090300d14603200b0b18000d0049040441800d440042a01e00321030181e85180d2950f5203543d5003504030a1700328194402940d09105400d0802d2040001c00d905880e50303440042e550607d03104240ca0448014002400c01407a030405201c0854484401030301f04c6070039121008140c2c002e1002418100c3e0032001c490300341c890307501003205040e070000d001d16040b8030b50706a58130007a0310404070206852010360000c044170040c202250001c1e00c65401440c2d00c0e219480c110010103d03103440155411110160040080c10200d0305024500b0300c0038611001d000241000e6801c01d143c0804100b4a00 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 994475710 1250 994474460 994474469
    0x8040303050414150a1104080304050111150c040501090b030709061d3a11060703030e0a0c032d080a021e01050901140415110903010c0305040615050109 67
    0x19200c01c042410801c2d074000b40034007900e210082e1081091165407010b010300301114140b0925090010003112104008121403c0d280d403c005145400c0c1020010f41d01100405c804140b24031426040c004074007050a695405030001250190b5100c4c40c0c03a000404000994100e854203080400034040b0131500f01414138115074041c140183c1c0d270819a24041d054030051107006402a00b10b410105403200d01810040b000c0070b4202e24006c0e00d24071292414503500d20b83c0c42c002c0c800c408401c3d4000c082d15081c40900002803191070040b5806503da0005402c10740a80740444910320900700500400450100354030b40140316a00000c802400c04d1007103041d0583e10180134007400c100180d4104098800e04c038410343d2428401d400c038844c0e50400b84807402000100d941e00f030705500c3c025030115032000092030a4010340d002940700200c5103501c65440001d0940d0900c140a4600401c0401341c252001c0c014402520110f4400040a02e49400c002003601c504c1c00f140324021740d84c150240207982c0c10014540589 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 994476960 1250 994475710 994475717
    0x10f050c031501120c03020909070806150c0c100c0201030515031f1b180f03080910020c2808010e19050c09190c02010b03030a12091e051606080403 65
    0x40002001a03070b5245800d0055810b503801d00c84224a03046e016001810180c0058031100c1d19592051000c544510f41640e00550220450740c0f005003010880c005050404051401c1c2c0c0c080c44507040000718140c00861460b000305026090300000d660301482001c0d4420280c2d040480c2440c1c41d00000380d15030210501d949140f10304100200701a998650040240302d000c1054201c2d07801401e20054035401800c001d40c215801000008030366040c1e00f150b52000c596005001c2802d1000c842c04010440055119103021842907001c1103600e40d8840040d0070807040c5400405000445600c80d8400c2c010481d00800c2190b8184404006034220004104011280f550b1255641c002c051810b54240071070040130b40d90040503d07061000c400008058226454035401c0100720340ca0b90548142c0c03c0e10345006096a158009100e50503c10307000300584100e1115403600095140c0b401e64490822071500c600041c030382c000c603c50142c01c000c0c081056024010038070304044001841c0010091640c80c00a0008080 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 994478210 1250 994476960 994476991
    0x11406070515090f060c1606050c0d1b020d181208040f0e06091e060f031e0a17040308040513020d09060504020901050a0506160c1511010f050c03 64
    0x1d2080500c450441a03150115141543c00d1070312110390746a40781008800c05000348008030f007241c3c81c1241280c40e422012240f5101182d00c41d102c0c0ca00620000b005070b02021300402210035150030754230031620300320a4600380c1498251900c41c0241342c103006260650600400c40804541d480446501d00b040f13a240035400413040380107283c500c82b140200d50050340003411841c03021540001001045d480350340e041e2114201983c0c0d402c82d802c82e010300300303e02102d04035185d004100182846544110241c02c09422540c1034016a00f00d0030091800701c0b021607498204181801c10071414198464080316035007260b505144c11a2500d0620b880382d8403589202c0c4940144118003c0d83c079805440e0680d10f07040c0e00300a9100f1604000b4040e101c1110124825911100085440e24210040000707070390300a45540d0030500064500d1003c0315071004182e030401d03028840040c452110800080e03004926685040c006040a0386039420f503090820b6211001e0b003000300f0440115031010580340c1c00b401d805480182c = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 994479460 1250 994478210 994478213
    0x311040b220f0e010911040b12071e080f130b070c030309060614010e09070207030b04052e053d030209010f0f0b0a0f0807020721061401140607 63
    0x1504910b98031200d554641c5141c001440c01c1e0001d0751604032010241d0a00421090a610004a00c55401400e4001e00e06101d00d81c03400c5030200c3c01c1c99210503941803000d0381004058500c0130704c0210a80c031000152041c000c11104170894002c00e5080041911424003030031281c0c0c0c407600b20740e100901190800c14524862000d141c80b9421103064613401100c1045884d4807140c0301c912480041d42c00901007003400d05010390f54100200d90b58403a04050340601300041c11542d034050b605801030810741d2540304241c0c1036910311301c41c211001c2809490550344088900342c4c040c19410340d00001c0c802c2e00940c80d070820080403000c001407848420104030a6184007000180010320700c444190700080e420691540c0041185d07030000c0c40b0981a190054000a1280d50720440844e8610031080d02c100000d0320020080a1180200310854002d40c4500654806c25102c0c040e950090400c030440c2c0c514540b80203d0402800041c0c401c402840010f03081c0c6280c01e6040c800c600030f41440306400745024242c0050300e40c0 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 994480710 1250 994479460 994479517
    0x5031803090907122d0c0507060203010f08100506010f05070609120509030f280c0305030f0904060905090717010f0531030c0602090d080304050d0311040b 68
    0x1c0c10100010884101828500b00081510000384081440380e40b600100f100c5461441203100321021080d09490310500d148146003015002c0e81c414501400410b02408000611600295001e4088920044510361030200324510b0400700c90740d030064441c030b031000380242c5990203012600309001500300381d56252624a0000c0003410000000f4015807002141160308550000c01040f100200f28100c1d0194001140d10075140c0051812010139040303014040e03440e107880303100d07510607850040036202c074180eaa80d01c45070700310b07400382a400341d0b11680051440c1d00d03480d291041e44040c00719003000704264a4051344c215680c844a025100c0462144041c05445a03400d4210340080c0000060038800340c00d03c24003426110000282e00688a510300a491711800300356441030b4203003a01690752090084490b20348600940c41040495000a81d00102d01301041c868001580030314440c2c80100082c106941006041b24880c11018405060400003000340103410416584c000c2a81070040c0303061040e24403983c = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 994481960 1250 994480710 994480717
    0x40c06030b010e040212040308101d070c0c0305030a120c080a090501020d0e0604020a0e07080403030b01120c0507020f0102121c090b010803071209050d030819060807030c09050705031803 82
    0x940d0312a0000606c407008a10004102c0c0c0520701c0303074441854944541071600c08040f41030007600050040c0042000380c440200f00c4054201c0c02c20300b010010f1b8045a1100c620095568009075038581c030000d040c4031800c1c2d118202a01c40b06d02c0150410040800000050410300d002e031501c080703d5212444031080c4042035040310441c1d240804101b016000701082035469800444099209a0301d03108005480c038110410a80b00d08065a00d40d40941c1d00c9607030540041c549804000d0410160380712000c005441c3c0e10650700c13644034907100d142d107a01044c0f0402ca079280c0030b06007031811034010f08044000006500b003643e02041d42c010520400050021031000240700042c400f5010450796000050b00103804401003188c1402084168100c030340c00001590a0710707072846403031b412402420300c0c0000b080c814136650fa0040806a40707582c40081d2040d40e001603e216800a802030707048a0400c00400044051000050103290030501c45460048005069400024881d103400601d41d65050412003051084 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 994483210 1250 994481960 994481987
    0x305070e090a0b15070b010b0c030d0203070504170703111c12080601090e040b0403120216030504090b010e15090a030b09160b120c0a030213031a0609040c06030b01 72
    0x140c542614100e9011406403d00c10040c07405083c0300c0024214092655080b6030201d5001055413080b6440d066040135a80d02408a640d91408203100d450820411400254000c40090b541c0c1a180d505208429007606159180710069511811040000449400085001d18000c4070010140f02d0341040c090260440c0c100010440b0064104402d0103070f41100d84280102801e86e03401c9040b0341c40306050518480c09545c040c110401400005001911905000c02070b958000c030f015013803540f405410030b900404044100c010420120b0309000c0700c5075a02c85c4c41000070091903c103401e084401c0c04103400051441041a0758440013816541c3ca440c0d80301034200a590100001119280024002e61100701d14501d00d04886602400000c4402c454000d0f03400d0045030303d04a01050700c480c43d1810b041e03070040c003d2005141e0240201c48004051003e000f00541c0910750000701d400c104910540d404100400081c0f040c903081d000e100128039812142000e403110390500060281c02080103a440c0d8908461303 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 994484460 1250 994483210 994483219
    0x5101d06010b030f010f030b0c28080405060c0a050405060a350c07051c21050a0506010f05040e1f080a06110333040227030c100305070e 60
    0x15849902c00c006520807841a900c105590362900c0e04521107210610019000015203008502d0000c240001000d04002c50449076505210b0500c410800c50f011803420001b107a0140204420701c40b0038404d4581c0080a00340d00d902d07041c030000000d44a8001c500940e4041c60020031070301105400b901e00040b90480c00111204032211254140c044200340c80f1031001024000c802003180d0101d00b034160340700c01303521201820b00e1061010042c04070424090768181000510305424404050940d90070702c0a00c0451004139440c980311412605842c3c003d40f409042010f00c1a411540d554402c00b928241c54807d00c0000103522524580088410b400680f0076190110001c00950110009030150310144104802d100c80c040ba403200215600085484940e100b152903035820300305113106104181c08804100b070018148100020030304070780051140c50106000004160b5040300050440071450f14110000c22100341118081020100c40100c400d080c59102c1c80030a038a6405012252500c000140 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 994485710 1250 994484460 994484473
    0x1050c160b1e100f0506090109140f0a120c080c0919020f0f070519320a1b0b0403030903200d060f0b120601030323030901060e06010201020705101d 65
    0x103c1d001c404443c0303445000e040c5950802e0008107814402d050385c5403010305840366102c031480c000310140b00c2c00c501035029030301c0700d518008881240c2c2c0b6154910084c00142c8003011a01905d40340c802003003040e40d001450b0030707801101d5040256480e80c0ca2154080780707104607104643c8007100400040c0c06242c0403004a0607002c41c90101c0004981c0181100b5809401120458101c0010b50a00da1002680181640d101c50100e40c0b41c1c1020340e44540a1401c220710303000c5466030426042802e24400341800c481d800030082540c0311b407003103000b030580181001d800e00b54601807440c0c1d4040e200171030340c1c80000c0c241180b03050294000840d40c1c044520140018009050301d0615251000042001031844040c6514122280030b260038460b10300104081494010143c69083d41c40503141e01703d00c48491400000c00720312099969202a02840c0100341c2d12001042ca281489800851901e000b04880d04680c0305020100100c0c000250710002c4501c51303a000185400400c1c1108807010000311403200500c60782c0c = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 994486960 1250 994485710 994485721
    0x33a090312051e07030e1011070611090a240c02010e03030a120e070302010903110625050628090201051603090513020903030304030e01090f030b0901050c160b1e 71
    0x10a0400461103420f650900e60307600030041d0129612036a1420003513000c00c04d12240b1461321750250034002a41081030341090466542c42082c2c03485074500d82581c60340410500f9640c1402c001c1c41014180102c400a0781c12003000c0c0280e0160140c551140810060054030825640142c95400d02e8000240c10b59940c4c550030b081c00f83c156414101c18400c15464107962403581c400100e0398200b507a505a444410261468850286c03070f5000b5103000f58004010006d404074422945501900c00b00290342c105103619080c2001c5041c18001040807042c001502c03d02d0740c095000c0700c0010703d50748562030f00017241809400102d4450180b01c051403c540705c01030050b01896040854101180c42c01c0380c1c094a60a1003000200070b13401280c040c00e81541c018000320b0002070041a05484611062500440050383c0744001c0e842e07204580d2055030000089024440c2001081c090f8035404440b280c1864074200062814141601c003603071000e44000c5210300400e40c3c806191412070300f042c018060707090701c0b030409 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 994488210 1250 994486960 994486981
    0x50901030809010207080d20070e04032a0206070b0a110c281a0a020c1f1d07060e040e0304080f15090601090903110f033a09031205 58
    0x4074030043c0584614200001d58060010b003401c00c00401e9038032481124503100c082c5102801d004030441c0140520071010440207a10600188207070300139507886400e10a4040c1110443c1c00390302c0201040c003520300060016841d890101c8030040e910942d608415550390f03c62000074000920054024400002c044240100005124109440101c0c0815100c2c1d00c151160302c045941181c01000503074011000c1210300441c6100550010380f6420240c5801810401a41007201c05030900000a080c02c950500c080940d101e4000140e0340c1605c082c0141c0d40d901d846035a175a11a214000800c074101018403d85e8407580c02c840001d11180084a4131385d500c0310460394850b40181c40c411000c1c490340c1c5a94500606130300f000340c060796880780a071816909000c007000180107210707802d50520001460428050b80c041015180030703890310000d19150504c1000003017843c507201c5641601c490307075024041402c1c2c1000031003c02003540c2540015901003a4038055070543d079401140503501c0d1528040080042c0b0 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 994489460 1250 994488210 994488217
    0xb16050115140f04140c070f0b0a02070308070e01020a02150904020d0c030c1706040b0f27011e150905060c03040306150e040b0603100e1c021207030804020a0509010308 74
    0x1c201c07030302c094a010880901040f80c03400c64213840140c01c00804699002d40170001415450700641c10301c288d0780b40580315001042001d6903000821540082d44105140d03100188582201c0340d0300c1e000445000a00000350384042500002e4440c48610184e844035521003400c8840d90304002e0f00c155151094108128004c19200840c1c101080c1064024040d0621941d0721420351003480c2070365082600c804007407100500554403484c0d080702c07044101c0b0120740c1d617025000740120300c0518080c26120014591009001c410391060702c13000071051800b2004404494101e06032010b15070350100a1454400c121161f00480e84140e80000300082c00b0243e1601c00700080064a000b16428000b21003440d08042e0250322500c80c04081452442c0440d001540d0b4008058115000408031800c3c941c9402c011012501107a1004c3c00d5640b0110100510500803541c039180030407a4000b0340701c40c41074049400680e03c50024001c04200c18100002c0c21551030064107406440083c3c40c001309581c50b032401c10034603070 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 994490710 1250 994489460 994489499
    0x6141003021e1803160b031308070b0a15121113090f0303200714010b03011503030206060402191407080a0e04200a0c050705090907060f090b16050115 66
    0x125007544100003814005101541030210701c5d07400101a1801d441405950000340a1018121420080b6808075044101600c51a80103000b07003036185c2003030303000181181d40c41b10960300440b4040e641005900b10200603407209a8101414001e200d040b900003908000c03c0c1c1c1200400c0900d010011014000841144840e1074881d440c108413600b40300c0a1108410541148030340c0c200f004000800000c6c03070031280c1c0d1a10300440710010030000c03003000000307003922000c90740020340003014441001819410801c031a04280e05075811442c10720300d0040c2d10380c0b0f460741200c02418403494500b10300c20352040800701ca4519803c4800ba45d201c419882c0028110003803111058807a41c24050503800c5084034080e0640e650007007200c500d2034030031000429201a14015004e882034098402c00240686560b07070218400d0001001401140342001c0020b00782007040e1308003008016216005000c44841c606c01c449000c0e9043d8220801c1c0d01a510700f0038003500c0c44064080c4080f00261340045c01c4120b0010b0050501c = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 994491960 1250 994490710 994490737
    0x70e011d0103050304030303181401050a1d03070204180c030b15010f020d12060302061308010c05130e040606080f0607030609020a080612190b04051006141003021e 72
    0x6210300560204039801e000142031900204010000a80654031406000040301400e2403079810f1a11070b448004805129560165141c40400035001120310582070301c10a0720500200b181449000f4965134059548000e01581d92414121120048880e41d400785c40c2c8d21410f44007015440e450705114141054441d010b440705c0101c00e4017180c2d0302646c80212680e6442d40140001100170008841e69201102c07075241e540c2e903581020000da101c00000341951100c2100141101d0f1502c01d10908540450036034008219043c0000000440001c11240880781c00d400b08907140d44032820028010060f986c01016588502c4059041440c0d0118400d4400d030130f1a201001070640d140b1000080c0e03c03580d5a05800907402e0800100d44c0c3c030b4075520702d141035070401044a0326000f0310101210b54030b841e06010341c0c000031080108130800a003041410040420f246060012a2402c254400050031625000d8860310221902c1d40e4881c1c400da06803010509261516148036240d051203040740e0b07005083c01c3d0110f = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 994493210 1250 994491960 994491989
    0x70302071a03070225080321010b0c03030f1902030a05040209010f060926070308250b16020a1b050103051501212003010e09010c020303070c1103070e01 67
    0x40c0070681c1603a02c1282d5640180c525000400901c02c3c40350250210000d0f020300154000c03030b0001c402c2000d0308040c18000500d403c040d10381c220703801100074164842d07250079030700f0010f2003600c58001c010f42c1e40083d2803401c0c1140c262078030340c00881008080074903801c20510201c200200103640e900124000c500940710303009640d0b211242044420303c3c41c003401c400701d819188100302280030300c0c200040c0e00d0200484040000c142c041d079030f03041440350f600c191903610b070114444421a101c80c0c21a102d20030804a100d400d034030169503600076124020201400034400c246020326041c000c0c800034800300d6004203080b80c1c2c4032022500000e0140c181c010070740040c0c0382000080d0144044141342100c00c00585450021070b801d2480c00000854101d000e0041d43d496000d107449000e08044050382e06501c140c0d1141d20f940c18a2880d80400400910b0740d04907a040004a89082d40c02104998218045107030a13481503c04e81449070b940c480000b0b01c0e070381500c5a19000a0307080d07020001c05041c2d6840030064a003 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 994494460 1250 994493210 994493249
    0x611030402180402031c0e06040303020105060109080a031223312001090b0d0b1201090f0303021b030c0f0f0a0302101a1201090213020708030f06010c0807030207 71
    0x1010b2021500250158012504503003015000c0342e07080901c4010b071407d0040301090030003054158006070300850250303460341c0c140700c803940c1c1068000d00540b52510007003e0040e4142c40007400c19074225200d046e050b56550b40d04200103078445036111000001d52a1110030309100300e81d0080256201d00030400600c0c1c6900c1c400703101c1d8055001c043e40607002121201d80040c03c0c072501004151511f40c250510a90080004100d0010f201034010000710310400110401c4805c00e00c1168030706d1604503107160349810104000680d000c3e42d22540207801d880d005072030b1180703d08201c5450b00c210303105025600c0f01041c0d40110a500003808482c20107002d05854985031410308a80d55864441c50050142c0c03c02001c080d0052601da20190030350101224405040d0101404610a85400c0359040f1240e51076455600542c03c14683c000c48040c40b0030000c510b2b084442d00c50030060300025051503050005a03020564a0384110145101c403500059881e5803980c651402135580d41300c0d0b1150491686c169031080c40d = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 994495710 1250 994494460 994494499
    0x160516051c050c040e0c0307060908151603050907120507090f0e102f130e010501020709110d02040611060f070e060703020f0708030a120501050d0318030611030402 72
    0x1d407869000c001021040440c000300400761261315104100752144c1d8400c9105540c0401000300282103075150350101c1d07420202098245583c1c2e6080801c44c5903a04140700c032401065a100e01c6a44003441c0008858a0740c0020505218050340103c0e1079070702000860041c000c021658404980009a08011082c1d00b000104261141c00303840011a410050120855007016049100310700280421b400e000c05041c0c0811100030714081e4080120500030404051440310840444043c100c8111051025850500000e56031105401000e0f17a0a072500b0036051260884816120040c1854806644540d1903c0009282d60188501c071215480f500001c100251541411540a03191959601c1c000180e14800e02042c1d034045013044007148107030600c0d0303045000180304281c090900d50000c1d503610100c06100411809045040507400c510f8440108003076541d2000c401d0030281d05040039903090300221040d0090103006d82c03000d8401420036032000c8141c580100110301c514400c4800420b80201a0681d1 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 994496960 1250 994495710 994495759
    0x14010f1802090103120c0b040f031d091f08250b030402060909181516021b0103110d050a1b0516110402070203011409072916051605 58
    0xe90042d05520060000c50f50301e000d160740c10b1800341040882c803901ca03661410700102c1180c06035140e04404003150704150784401010b20400b000810b45500400c0a00001c1d4407400242001c510045454820710015140041010041c000ca00a58206141c0c0e800c403110020b00044105507410603070310b0041501a011410b4a010315006003e060400c0822802c0c450002809004807040c10500740c00350800781e8080006540e000c40c0c5280e06039103801c10400040600700081035500954209003148982c0c042010385c00c801c801001d11300880d880041c88102a804d208180f110440d42e03041034104420100c141c0c2004100c1704986050112400e2800011525030190740380080c3e8800a00a1550210384008020070b10000010710051a00c11181c1c0000c3c00c4512984103511600b000344100800c0302000c0c0201c00041680304841d900b178841c0300410321951001c0c0c0b10703c0104e0b10000700c0d9000d829540c030a040440b856000d03040303842c0708410080c0301c20b940703c3e0352050910030202420501c0582d51255100c = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 994498210 1250 994496960 994496963
    0x3061302040e062e2d0e12010207030203071211060f09070f0503031c020903071e0503150c0703021f090c0f0b0a110c061215090c0301050909070314010f18 68
    0x2000031380a03403088902c82504002000c02e00c06001c500400c0d02401c0c3c24007070380e51042d504ca0030307120b100f00750a200d50015400031883d05e0340d1040c06010f000c82c2d0007104503148584d04c003603819407107a41d952042d0350201c4409407081c0b080c41008100aa55030b01c1c0060036010384a8078044402e5141c3d91103a42c0100c0142d8010550142c000b03012110340c81211552158060b02035110141c1006000e4000c24039080703075640017154014648003603003a90380036640504003402068001d010340040c606000c1018034800780554003d810002000b90602d807003446922807000095040d41e0700f0403a01d01514020300300020065607407420f1100c001451042a202c2c40c003c4800e1a414a03040c80b00c10f51080d500203007500d40c540f8081c001c40c850b100d0190f940c04010b0a211042e84032030506400e1203e40e140d101c00681d44114000c6690070144103a01c2c01403000d072070440b4000c50f5442000d40da641034240c2404070310340c070080c90906401281c2459644c1900030800c800700b4100100300365040268040700c0d280c500e150 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 994499460 1250 994498210 994498279
    0xb1e01030c05010e010210020d090c150203041715070c050c0103050103050709021315020706081311040203180109081908040c0b0f041e14090609070503061302040e06 73
    0xe0411403540504c101100c8024140140c45006403d10801000d0f0380c09540c2c032007900c0d07540342400c204002c202c21243c0d020700010003560300a0101114060750302d00c140c2c01004103403a500d801140c42c2ca0001c00500c06040c60400200d1100c0c185070f0000303040c1c01a005001c443e980501020001194032038412a4126034001009126603407610401c40e00940c05046071031451030554001080281c00c2c0001010300f015030780d0040598a190000040511201070300070341400031220700c1900840c5500020401040007140c00507542d40350354610201c903000c62001403c2550808d141c0c00140038a120207001610012381d04400c801c0030342c00c41241d0700181118010243c185071441406920860320250900c1009900d603140341c43d03103c000c66440305581003102d181030003000d00207108a0f0f4114070086d101120540e44200785040440018003260340007030128040020100004055071b94240c3d8880076801c180204644c1e50307482d40d121201c01181101c50a0213140c018a00e1003c9038592210700c10070180702c15 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 994500710 1250 994499460 994499483
    0x12160806011404230c1e030103030f050c060606130e070e04060501110604060c020109080304060c0905060313030e041104090516020c060403060b0a15030b0f01020304082e090b1e0103 80
    0x8050300c2c00f81c0c90140c0400c50708101401003079000f0188400800e907246e160100c16032290700d180350040000c00004104410400240181c038076090000418940013503046401c1d507111140c0104210082c95254400810314080360248002c0301c2c1c000ca0361081e0064107135018045161514019220703a0b82c8004289500d60150000801103034855200b40c403480b042c1d100200302619503855242181d007003903400307032401f80c0d0302c81080f0300f00381d00804108014181076450608514000d881a07199005124000d0140000036141071981d0343d031a408020b610944242c26a10340d6100c01d04000140402c9a80003d80f9041d581c5600307209000048090542c100107001524150035652488041d041e05000103800403008000440d156412a00e02e6180c111240d40004a240d200c00400090b408011181415901304000a21070102d011400103260041c05040481300b4180c42400c514840c1803908440d916440c00714000708000350806018000c241c5804503a0400e0b160ba03000c00c5042d0320a11000b40784090f405c = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 994501960 1250 994500710 994500761
    0x31c0e041413020d080708070b102c1b0c0307020f0307030c150e040c0c031b030519180e04050d0302030f061201142a0c060612160806011404 62
    0x100a05041d1310b204480c254181402551500030302d410140085890724524404c0004545040405070000c14540071000c5000e103101d4a60900d003101c03c42d4140d0b26500032000501c084000c0c0b00e800c1598101e03400e000781d60b40c2c0120704084e03c940149004030320507003084003100303024540041e16000b0340760460705440700d10b0701c0c1c84803c030021003040e07006a0a01060541c00d55540c0e4941c400d40c00000c07440d488a5105680c20b10b0b00a01803042c24200d15621513000c0e203d1800310390300a080d62103619041e00e2510340d0341d0210409071090b00204c02102200d031a0601d005c41c0c0b800c000c61460740a030384a40101c0e5004040c01e41d041d01030340030854203a5201c80e50724001810030700c5d10b105c881c03080341c1048000161041441442a000000454400340b800d600c0c0a1210800401d1140f40c1c80103820920728a810040d0000c8850f480303500c050189403141d01b88030ba440b28a5901800380142091901200c01e0003e030356001d0150301d40000748101c500b030a040c0d000340d610a0030180514904040344100766007921051 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 994503210 1250 994501960 994501969
    0x1217270f070b211504060b1809070c1707031803080702090c09040f052203020613020604121202011b080406050709091a091006020706050702031c0e04141302 69
    0x115005840c1e1a0f142d00030103800207810703040180203030750a00d01407689050001c00d0200b52100381e808088099010030840319083c402d1022030140c0c1c50116030032032680e100d2400c210703500d082101001d0141407200004c0210951268006e02250b031181d01c40c158511480300c048034006202c0d101c05030401078104aa90011b02d01129060760215200d1015070070200f1820200d011100a00805c0c051140e0300d00a010003100407241040c84070120300a00c0320310500c5940c0c020745400e40540b01c8102050941021001c664421064502921102500b10f04580c080e0501c3d500c00d01d0701c65130311000744d464444020240d444000c428600c10841fa22280320986030340d40d40304003c11005025074104078803454045840303c0302c1d000f002c6100700b9035000705488801d00410841d002101809030322460b040002c0030043c0503004248081194102e0520030f450380201d00209051040c41e10b2151140c900c0c00724603810781a0858401d405c4c00c0002c0e101000808000344a042c06c20106454076110216554a41401440c1 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 994504460 1250 994503210 994503217
    0xe150f0d060c0306091803080906220c030b04050d080702070e010b0c121602030c040e0d08070507020604060314072318040f2708071217270f070b 64
    0x20782e031a002a40659441441c0300311001e0414070140c1c0a81d0058507414943d120042d039410180308805040350b400e2602440c1d0b01c600c040c80c038000507001900c0240f010b12400002040007550042c506a007a071070107103031203501c4041942c1c009000c01ca01e2030200300300030720009020007580c40400b8803101a03420000c842d01140c01c030b0804882c89100b010000c10001c0c20385030140000700200c10500092204c03510400d4102610001c035207004a2400380c441991010028074501c43c210f4500340707440e481d110404100e52030701c10414060342283d0000b4002490f2941a4409103288043c28008181600d502034105d44103e40c441032003802d28404400b9120010480d0001c002880000229400010b8100c012070142d4200d200f807400c200d41c0d00c8500181f52140c0045000d900444840412031b542071642d2401d04074054034902625081700142e80c08406401003480805120043e010b61070325140840302e1102600501918030840c0003c4080c811810200080d1190b00c2c400141c090010789040c5a030a044640 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 994505710 1250 994504460 994504481
    0x90210051812011505190b031f030510060e0402181509010b030f0108070b0d0b0d02062802010603021f03110f0a170601020619020c070e150f0d06 64
    0x41c6039940d04101e9076201c14840039403003a003000224140050046100c420845035101c14000e00a030072070600c51070215000e041c160b8a540da1429100c0d01c400c0c0068480341c10105520401c0003140b00088248240040c4181c0c03058414074052000b0342d10707204007410028058800940000d5100c18035100100e2000d41c559102c481c103110100104620707800110802c03003e070f000c03000a850020600071003206c59000360f030140401070000c02e5054600003a8800e644110b00e10724440700d0b07507043d4600013940d95017020944e640e0010315171500d0b5900180803854900006030008801b83c50101c128000e54018001c0f07800f1a80c000f022505003611010041e1110031080c5440c00800d641d8008181086040c04054695078600e240280d403159588940030702070050248480c6281e00c0c1c4c1c1000c0050a83e40010300c281e0000b01810131184081740c21728038070043d0291101601890041450114a8003880180075120384180c1e800525551180c9d400c0c080307005100f031001900828411070510110b0300b42d800600011 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 994506960 1250 994505710 994505737
    0x6051603030f020a170f040309090e0a170c010f23040f0519110102060c04060c020a15052809050d15140403120b0603011e12060b09070309021005 64
    0x20040c030181d01d422a4081c2d2601c40101c0c0740400c00706a0310178401d072801e90000b80c6202c1103a89081a4402802c018254807030500c0342034598100145285061064802c3d090348540d0880781c44005450b207103415000307104107003055841d2030502e01c103142140c011054107154000f60802d00303902c10007011120120040094810320080c0d00f038031000410421405c40c00e0540e0008a408c0d407041880c1c0b40303012000600d211030441d40400284051440f807402100c00712000c508000341440110b2000c640b640101d40d00030402c02c0c5118111116441e00302008250300707030561604010302e545608606a800040301c0c0440b0004490100620003801c1c00700d0a405040c0c01410050b00650045040101340c0c1c80400d540d1108e014504144400c1540224a101080181e0303d03050060042c0d000110b102c84c0414402c07010b440e80351080d1819030300c0005144202918144140c4945109203040c0702002e0301c01c80c0c030114042d0503030318000746c0d400303100384074034050140d00400704991094840303002c4856400814241101 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 994508210 1250 994506960 994506971
    0x1006030e01060b1806042c1605250c27090c1e08010e0106150201050f1906081c0f050307020307031d0904030c0c06020d080103080d14040807020f06040605160303 71
    0x55240907441e04082281411f9021050346684560703808400c07014201498542c0000030302046036400800782d4006080158060b018128010300c90001ca072000000a402005102008160101701c4030074941c0c01d00b0103040341c82c80080322810440c1224001c0c04090710703950030703103034140007994031042c0700120f0450503440c0c44681c50b04e80300303190b0031514980c440d9401a0340d070706d00c20090b0540e042d0155000202500082041c0c0c905841c90945050004001c5001d1100402c02140360440540c0450b000c0e0400b44c04071102e4030007031001140b1441c02041a4000304264001c09941a80709d001200c2c420041c41d40a5400c000c40f86d60195800700c4144e0a00e1401908549082800e44a038070300c10b489075000740d6480314040c180303003021003a4400e070303410040464102a04803450b807600314180724110ba600c0883c0c0340e80c510764040a60000e00d03c6201002d90100b0b2682480b003444042000b8144060080380c1c515282d901590400038075108510440c00400c0c0280107021110386903e1002c5842030003401d0203c1c6 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 994509460 1250 994508210 994508219
    0x1030311160e0a06081212060901150309170406030e060115171003121701140109050f0d0605040803040c0602010b010804021c05030406030e0c090906190e061006030e01060b180604 79
    0x1485000f0050300000032020405c06100c7c5280c104864200606032803450b4030b94105540e120b180701e0f8060404043c180c881d400d420800c0400040c00041c400d100c450b2540700c42e11000700501401d40c42715101140d03c40c1d0704c00813550380c041c1c143c805503040060f1108504205248404511000001c103142d0000c1018540000451548014401c1c801441e82c0e070009158401464403800000c103801c845c0c6487c1048540c1c000d00e0360400908402e96004681d0700c1c841415500000f036900850040040035181800c05110070000310f40d0140d801113118041c0043c40a840b44c004908031045940e41c580020420000314000d410301940c0e21603c030254504120b4044a0b41e1203440c51a40641d11440c00240e0320300480c1c4000206000c141408101210080d00c3d40c2000e800c2a681c800f0040c040d20340a41e8441d1401d40038000c3c0341d00c04602402180280c0381d040c0303800c072104100c0c6116803052401003800d2940d10302c2021410f00c1460180c3e42480740314bd041030911000090440700c03803080150405001c020104 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 994510710 1250 994509460 994509463
    0x140f03030405150c120c010f061512110409020c1903090b030402030f0105011511070f06030e0f012a03050405060c03070e091005030d0f0509090a0209040f0501030311160e0a0608 78
    0x4181442e010065550381d504401b81c035007190002c022000200d86814424002e691400684403102c1c0c980f450619901c6c8188200ca01c02442007014a400071000020300007004030840d0040e00c1c00e0455101a40d41001c99080f1698403180c035104010001104840240481c0c41d583c00a950000d001804681c8001c186000b00ca084500a82081e540f40d421007082c1c0380055848450301114400410180c052545801c0400c8454801c0d4021705040c503880e0305603400e68460421000b0885503100009104641004c052038840b0414041105525800010108500c9000b4024030380035950200c003e002c0c90f92a615101095003002e0300450402c03140034109903040d23881c0b00e80320703001d103144254412440d89043c080514207040d580c01351042c00990044080d00070340002c1500e07045041500c6c40309699071a8200d10000303204000c542076215241000724a00c5414903801603041c0d900c01c0c0c81340f441030710107100300c25034540d0303001c042c4606541d81a000380808150101e080da08106194030100762030b5204c15455 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 994511960 1250 994510710 994510723
    0x1230a090509070309080d0c050f0409140f01060e01110106081e0d0801050306010311010c1a06120105090309010309110306190501140d06092a140f03030405150c 71
    0x80015040d1000340540d2424400c260b4100780c150408209454090303071100b4031070180040c1ca0607200e584610881c41c1074051802c41d84603903150824999100d85a01c503110003408404a220303401301048002420045041d03070b2150681e806526a29464142b260045500d4080861040030a5483e2a80001c0c100b9003004000c1007038420503c900c0c20000c0078010146071034041000c0c0c4040007007060040096032000300311141501c1d004054100c51107481c0005135990500064010626211070f15a1034800d40104c49030b9004100840b5244c2c0010f5424000c2405c1c1ca07020744101203950010007241407198003039030010524520a050840466504800103810484221043c940404080e14a010b00304418420315001d00344d09040005080100c101240c440c3e94a0903000305180d42d00e441d03100610900015100e904c4998050404e003070b00101d0b070a05060341c005c0c8503900d81c0c03d201030b501c1a15860180c41c0c00c0380d00d050207801581000c0ca040c0400481941c0c1040c010f034696405c220f644030717110041c13040 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 994513210 1250 994511960 994511977
    0x12150e0c210c0702031c090b16050601150f0804080d0e100903021f050103080702061809090f1011181302180907020a210e1201090201030c17060123 65
    0x20303611003c1c280140740c10035041c450b4401909040c01e0a00343c1079034100440344140c55a091045840e00c6000c65032035120118070b800500240314a500005219520440c003024a1005640c0e158280c0d981100c01d580300c0005441c0203203842d40521503240f0403881c640c00051a06843e03030488408140c510354550484000c2a0260b005802c80b200d074443e070550816402c42d60130030111041103e989103031110000360041d07001c000d1007206c1c0010a40a48001d480a118116100800c08052410280e0351656510a0f102c0500303c18094000e2207007240b002032041940d440710f81d0304035520f401a1081103402c0315001c00040d561000341900f9014040015101400c2701c3c01515000d62800070504041040060000f4032001c02c540c8403091450004060300020203900034080d60008003041007060030780720403501c1c0c0045034000a08400f11a1000c2c015044107040724003e072410050076818402c00c84101410580a01195800c85c000c185194828004030b090855140e2100e03d000203607002040d41c3d40c1c8142003 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 994514460 1250 994513210 994513231
    0x1a0c06191e0c110a031205040f230609070605040308070215070308010306050c0c0a1112030f040306050a1b14090409060203040210050a230c060712150e0c21 69
    0x15000b00641001101000c451a50f008001d420965600240901e09154580300c50f0303070b1030300e01140800030142c40407112a580080308600301e40503248040d0705d10900140303001349486136101041400320007007621402e417601c0d41d4400b03140034115110040d45900c001d07400c90b0482e088594a040c0d0307285c03200203400c4d2107129030b80307003000343d459070030300c5010340e480608416480390003080407008030349000450b20151a44080200a00000d100004074081c500d08102c0819000020b1020451511400200252442000c08120940341c4205030411180c0c86084014030340c07040d80c44c0182850280e42001c250455081840d0310700202400403900b51912203c00701c404540100501085107080c008042610000380b4295050810010f0300410b1440b002600002040e0700410310350418006008440d00c40e021101112600d003080b40d002000b9500105602410f54070b0200d100c2d01201c00c0b243e01e00d08840c1c920280003604d40f1141d030b42c51060741c08004a032480d000031540100c010700304c0030540c82c4603101891 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 994515710 1250 994514460 994514471
    0x10911040c0233071d01260a0b100507031803020904020613050312191805040207034b02031e270312091c051f061a0c06191e 55
    0x2813804da080381c0100c074581449a41c41d41100d40140c83c5001044c031f000c0d070000b403100726201c0c01510f00080000d0085107821204408000114540205c01440f403c0d200c0d940d5440200d40740104800444006c3c04000d501545003070102d005840d094016102081d54224100c01055480c0002803514581c000003101512000c6081072441c28401c0d00c0380b1200d401c5040054141081c1c400e4011512100c1c01901c1c4241d6000c01d080381414400d04a014020300040d4200161520880382c140312042603550030b030b290b1030780c0f40d00c64410b0069007080e01d02010155001541030000c5c2001741092011416010030803504203100c54aa4502100404184200d00300c80540c1e01072044401c2c541052520120814114170400c0402a103031030300e09222001003d210554101d0204034a03180303082601c4d00b09400384035110b42d041080c0c020000c4d40400201c5800060b0f60000c54050148025240150300030f803061b6410810014150854240324000f00c01c82c090000954441403222481b054803c412021202076642c4 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 994516960 1250 994515710 994515737
    0x6060f030f021306110c0a030804050a0602070303020303060907031107060c080a0e03040e0603010b06181e0d020d020604050d0b0a0c0207032d0c030302010911040c023307 75
    0x148280007a1203080001076180c8070050f110340400c42a24440e003010020000d0b0381201d494024040000140d40080010080540da0f060000043d0402c0c068184200340000000030f00a00008140088940c5038001c3d40c210b40d0341200704820400b0080c00d1600341611000e1a810101c41c58008081d81c034800d440c0041c0301850841c0003801c801004214440e201e10b00303141d030b0140e004000242d40440e000640c41c513200d80e4465012030b0140441000c43c0781c100ca0701141d007003819180c00c40b06a16840081d40d2481006840d00340406440b503410915640160a2281000150034800740290300c9600180090b80740554403008a0401d00304040c007a1480d10b260800c0c808241902e0190f0700380900c051000b08489811516601c0e0580038045210000301d54888404407281c0041921036085070704a104248400e03a20308010303010327149403a022a00f0400030003090b441c1c1d00d824400e070364000049900a040345a180000460b5041800c0c1e1000b11f03040c00c640161a46218900c9054881d400ca40e0740c1d07038801b0380503 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 994518210 1250 994516960 994516967
    0x30126150c270607080705070b04060215060108040b01090507030905120d1503170a0e0612090d0915030e030d1a0a0b0315040906090516060e03010515121006060f 71
    0x898240301581c81c190090340b80d01d9603904180c0d42000d07000440366030760780164500340b4070701400386d40280d1295101040008015801085036070490102002060722603803214011a00301d107013154000d01041c1c1e110014003030181c0e564000c551104c6139003400194a0400d4443d60701c0c285804542141d141c500103078901c200d0b4030318092072070a5540c034000218040e04503a181d981c2045400121501c0b06004100c0865491244030910041c6001400300c07a9200b030302c0aa00c520540b81115152032600c50306030000c2690b446481254121009a403a80c0e00282c1d404000f107004e45949400384555210900004408407242e03c0b550010800130300c042c00c40300174000b02b0b010800c40f4980c00b0740c600b07000c1402000303202c000f80841410102411078001440248901d8034000910b400070000c0c08901c100300d51162140c01403645007050710f41c540c584424500c0100c040609850080f03074100c241040810100c541070801c000d18201d4443c900317007501c0d94000e9031140d20080350700310f5021b0390020700c450304a006000d42 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 994519460 1250 994518210 994518247
    0x92d1f0f0c2d090b0406020307230d05160206030c0a090e0f06040b01050d1a0f06070f02040c11120d050c0306090601141c1506020102030126150c 64
    0x155420b0005410500e8100c9040300c080d085002000c541d214140d003003009203e500c0706406000c241c0e2119444a446810081d030300e403c04101150340303a0400c4a0785212900b0200008010034010005009400b4a00c40884640c0c100091414200d4542d01c1c0000050395110082e41c130540a048a640c1c594000c810010200481c942c4142c41c07030010b100c180304104c4c02c24083d0300c1e80034200307031404641081342100484651003444c1076951450f2074007a000d80045448102c680c0e0001c4122000b41d00311034100304104441c800d82d00000c0c545095809810014242500b0601c0e050540c0d0070b00c00d90a1101100c1a403c0c61305500700307201d0701c2e02c0011700a810108a4802d00d6080309100a59030300b103242010200300c01130400791040e811300040400804c40c5520030303401c03540704900c2c2140c0d400c100c0c015004c2c003401401070402c0015010785003510215030030344144207407412a80c1c504418144070011020a01074405550a40d0071980145440c0b03210070104007811501407018810310650f502d1541e81211600139 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 994520710 1250 994519460 994519481
    0x70602010f0c140f0729150102030405130509011b08070201060f03080702060c1c090e060904030818010b030a0309030b060f01050a031806090302070e092d1f0f 70
    0xa1154030705046122500c042c0c5220001040c04565681e40c94240300c443c1001d00803a1814904800c46c02c1c420410400701740034044c0c00403030514810030300104010391b00e0b40100d00480781c104480c2da081c001d20b400305420543d0004c035040000642d080c000e000303c0007000e1302c3c03110340e60102d4a440180300003a41e0922440c001040043c5503042c9031400c1d580c17500128491208040e01c40c00c804200090740c4e41051281c0342d0550a600300d040740c0032440050140802c6000e104d10020484084000f500c135083c5105403e11865040d559051107680f40020182c00940c1c024042101c1c0d03580d2081000c40740c404002c0c480d180380c060b0b1614041305103075140c25820000010030650041c0c103407a04416560740c002d02507030030800b5039040115611a040c40700c0440c120701c180d0060304641c1040b401c07105250300850310340c00b0b40f0300a55001c1000d0317881d0303542d607544c41c0070b40c1070240c00c00607040b0f226444101448080502c01e00d2590151898281c844900b4141c0003c03160035414000ea85000010140140f48240c80046 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 994521960 1250 994520710 994520717
    0xd03021809061809010615170f040c0f1e081b0f1212070303050601020318090406110a0206010f0f050108010302060306181e0f01030f0204090302010e070602010f0c 72
    0x400926580800c8051030440303a0040c10500046802a40d45480e0030345500e9500441c0d00031031402c604101d01929081c0b1030b403414207400882814160b07205e01181c800041041404aa440d00c4144036070322000c0e40240180c4624800801c0414040c0d5401d008000428440c10200008016071010303c3e030440e0154840f002ca5448400e00f4009000c83c41820b0304101004c0750520200261200401c10024410030080210300035400002c001301009005460558080c1d50101328680d540c2c001a070742c0c0d03c80c0c070320810740050b40c0c0c20140c2c609180c01030810340d116108450104945410003d980d0305a0440a02500540c100a005000d121010314100d0010100143d031030590074136103400030b0040782040c00301a004090000019540c1e07213440a4100d0002a1080460010b1410501d0364070000d0202c84c110b462910400007040d0001080344810381629040035003028614206d5080100a040c007001c00c405554031010310703071215181840680b00a040d260008504100b41c0c895030402c0724014074051061 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 994523210 1250 994521960 994521967
    0x2040b150903160602300a020f010b0d0c42140414040f06051221031902030405070306051501080f0c2a030f04090e0109080a030f0b100c050d0302 64
    0x190394001903906413003a0341d900c006d5a070340240303141307000a42d8562180600f1050001d224120160f0014000c00300e100154001c101d11010841003240c610302c0000d01800c3d03400056420701c031404800c0c8680040760310b17070b05124881060210310141c0000051140c0c0b16191907804101a4003074200c400250076a00e544922443c050410030481003100d6041c203070a0085035070f0390554140d03000395400746018010042080000d012502c0d9420340d21200c4145844000c2c0610901c0180080344030240d034040c0500c0ea1080d4804d1040424840003504000c00984241c85940c200001240d040e00ca11806190410300011810074080000750031018042d0511605ca4026000c00070328468407800e99a540004101c02c3d250f1031030800b00d081c44500c00c1800c000540c00009504a014016400140101ca01c10103051101102d00f42072182296000400034094805c10040d002e1030324401d500104c03000010500000d40c0320f6869000c10200c00300300c4245000304202c00311070020300c5420400321491090501e4254503 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 994524460 1250 994523210 994523219
    0x171e101706061e030c03031801020d0309170306190608090c01080907030305071b0b0d0b030d09090506030106030507030b091903140a030b03010c02011b0f090e0402040b15090316 78
    0x14400000043c8010a1000031041e0555810320500001d04402801c8035102c0d140c025041140381c840110080c05882070207951395505000f03019030031030715411103669104d0582c0d0b10f903584001e40c002050250b110071150108060740365407a40c60800381c901980c4004071442c1403d00e95282c030500385181030500003c5c008001000000240d49810b403581032901d1a291486441c040c0c0c1d0000d0400c030040a43c240071940400c0c6041c0395000381000c1a0408420b00c59602c02c9818180ca4004e50501c0100141001a040c4225601a082190440d82c050000a00199262030740741c10014140c000702c42c59180b01052144008003042090018a1003100142910855039005056280f464186000425005c80c0050009010b40d119031610300000d40244641505020000d008161160a4122650700e0826038070645102d40c981544070012501c0e005440e505000c800302007120003c0c002c0381d00c07030780380e001100030b64a8050802d002200c404040640b101c074540100b44c04c0000220b103000d0700c0c9048100810 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 994525710 1250 994524460 994524469
    0x171c030902090112230610060507230f070b070209150d1415130c09020306030a030509030a0206040303090f09180f140607021501080607171e10170606 66
    0x141104c0d50034802200e283c0651600308a850400c0f001c8507103003040a003a21500d01e9021074000d1155014030305415600340c50310f2080d512405100c0018040c01091aa6008803002e10802d0300c840c1e000071000c1320345c06188050401c1c90700d011501710301003a40700450480114200244601d400c04e11a0420b00803030300d80c4001280c4405034414000d8542d198280003851038100c10b0011110001d000e50710828540307401002d0406130355401c0c00c22549000c6d000b40005100d4294400d803800307010024041d04803010551011074030307900540f61190385070140a0b1742000598030100240011031181e1503030024145800d461443c0140283d00111600c4d042c000c090040c0803d0181100c0059449018081c0d480c09909007011220207085140c0c141c1c3c0303e06018010400d4000030a000540700399007008c6801da8031105e140b03880708400d84490300454070300540034454070302c02400160301058610381500340c00d0030340202420018041c1d50640d101c07800e408041c00b41004d50030140d8240381c5d004d001010725003006000724 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 994526960 1250 994525710 994525729
    0x90a0905120717041518081f1d06091b0f06160501091b080a0b0a09032a02010306080a020d060213090207060204090c020d020303070e0109171c030902 66
    0x9508640001030080401c40780845008000d00510742141d00c6a03158001c241c2800c5c19414290b012401c850542a41d40040002460940b45020301500e00040e0b0326165851004001078590341c0c1c6929001c3c0d45030140030030784032103000c650120028203250812003605400c0401c04901000b41000c0a0240300c10703511102125224003006540341cad60385001e80b440810074103a555178024450350a1040030824056101c400140024004e01d4a03070800f6a1052081c1d500d12401c0c0300101106008000240840d109610004005009042884c1c1d546444180c1d6841501417400f8003c4450003d031440b070039944d240c4104000b40a0400050000340720310340005003800d41d200002810b6980026500c240b81d07409603940c500030b21082c503056403520014500305000e500b00d0700940d18481e01d0300e00c90f070703447d80d03c0007807000a0181141c002c0c51840c2c4030b141c0200e59002440c043c545c184074400780001030303440c032820079201c0e4130751a00e015060360810f441d003560380c0308000c08401c0e08040c1010052000340c2c0d1080d4a0 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 994528210 1250 994526960 994526983
    0x10809060610141c151a0309010b10090305070905010b2205030115051203030103150e07031406070806030c06040905091006030821070c02010f022109090a0905 70
    0xc45841e990ba20200c40744864100c00c050300d542e010039100c14a54000f11034440c2640024011300c4508040c2c2001464491130b840303500b004445050b0031250341d0500307000864000d805c2030300100301d100d05070f0045425030207411085030008154240810600005020303c2010300791007030041c0000d51501210100d9401801c501b01450316035017080c010342200300b10000000f024090000c3c070484007108101c480b02031840c40f8590250b03800c1c0840040000001c4101c07416240c1c004021304042e030408008500502c44a14420318611031440084045100700801c10300d1114008010400c5142c0104024081da001805060003903000701030b9049503545200544050303443d00600010180d035035280c600e20307088440703502036102ea10300070001c024806600c004251901d85e0020040d00214081454044035008940410028044080c0240190f00c2107101d402190740300d00c101c46c102c0c29070b00345031010354031118900d800c9110005034201da942002c2c1d403815842642c44c81d0401c41c80f003440c0c840707503100c6002c041c4 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 994529460 1250 994528210 994528219
    0x60e0a11062206050a0e0a0b0403030c050a02040f0218010206150103091b0909020a0e13110d15050114060c0604080a0c29010b030411060a120e0109030e0108090606 72
    0x40d094899086090040400c5000325440d0003410f642d40b07006805a4090a41040010090380d0300681350309101c1074150850b06840c01e858a82481c0d51812a612000c0e10b0341119140607c00c1502c002d40d540380141c0ca00488a90740040e500c9030980301030740da1a146e00c184141076400c0001003050501c1c103021440b401500c02c0c02c0101d0b00124514115981c880e5011490740064059540410102d055511a1032124426910800541d071185c100c040455800c071500091941c83c04803000000300e540844010000001d4619038054103165119150000320000c2c03d40510340e198010002c0c00103890700c0141c000c00a68215143c6055002c5081d150341005001900e102c82c0090381d84900e500c0380300c84194064025070031182542d07071541412030403180018100013001141c000482c6a41100c02140d0045901c0210b12441c01501018000c0640001c0b0b0aa010301c01010503482140d8950300460301044031704400040c00210701d18016200d0060844a541044022003c0000c2c4e041c1c000340b0150081c82c00c54 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 994530710 1250 994529460 994529467
    0x60e030a0b010e07090504140609010f1415091e03010606030b0102030f180a0e0709050f0d120e040207150e01020a0f031e0603030206070212090303090103090807020a0b07060e0a1106 80
    0x20401e503000c821983c0130541040c50310001e0764a0305c2300b80742018000e80d000c07100e0707020a981e140138400220b50306005d21038804208071084400f0f403518a10090710702600d0412a800c2404040c00290041c2d20766100c16000200c0610400e200d140078810340020b0704440c02d0030013011180c140002c0d607034042d00b4102c000030701001400c00e03283c210031203840e84d4a07940101045201d40e00e0780c199054018068900c1d1010661840005c1064a000c801c600322005000d40800003220442c0c85149494545941100904c0301010400609840302c0c0010001c082c0145020f40c1c001581054a0b021250b600e080c0701016441409046501a440340c50584000001d01d804607094aa02030301c1c0c0ca004045520716100c1ca40b42440c0001056008a6120b104a46540036528281d181c824150828410108445c1d0b01d60400c01c01001c241d80690321150070580129000e60420905078082148141540c22420032800701084c00410002e0724000e111014150f40040c2049166507aa940d40c00110070644512824021 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 994531960 1250 994530710 994530721
    0x5150904140109050a0507121203021c0e0703020102060604021602090901060503240f0405030f13030c03061e380d0308190204140108060a030516060e030a0b010e 71
    0x240311044001d94a000800c00e01e83c15283c5143d460381d5001c801c65060088081c0000d00d80d0651201d03225154000020340041014144110000c1d0f0107071546032200541c1c0352000d05908054804c54284484070780042810300d0a600000e46131401c003e007454411030041024000801d6401c0e0403001c01a8195910080c0b030301c0314418a0301514164011507018451031480e40d00c4080000d0009000005192400000c1d440b00030707030010b40101c115000303003042d881080810341d84a002c100400c0d0307038514040c40200040d1266101d914408503640140c03126500ca08081c0e060f2070000b20300840413440700b80200300c024100100f000314a40e00344100300703c481d1490146900b414103200d00e8440032400a0071020040110725000d001d0060070348031651074004042120303100740040c1c401c079015148402142225038030550300461762007900801ca160804049507002000032810050107560490451000304ca06040c0344004020038010007900d4420740c001103042001c990f00c0b0669030305417586580b00700c44641c0c64 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 994533210 1250 994531960 994531973
    0xc0f1f020c030d0906021314030c130905032701020303070903122106060305090a0804121112030408061e070305040813060306090b18070e1807050d0b0405150904 71
    0x750040d0040740f40c10036007048100881d9900070301c847c410030007000c81c500d0340301c09210f0500881c42895603015030101d00313401d0241c58164003501c18101d4486000c0b030440b2166039080d0441e0040b0420590b521038108462402c46072a440700e00d201d030000c0c07000b98154039000000030041d4040384000340030243c03a400700c07400203441280314201d40c10311840b8040401c840304401000a24051081c05e000034030f40f07c046492140300cc46d6840d00702da0010728942c01c3c5414084071441400c04c85900700c607007441c068001082e41d1180740c1c920307180215a01c0039540301d0385428402d07401c0107001044080100d900c4848086601c01e09030700b20342c1020061400088543e20387c9800b081e1032240b4003040300c00240300d120000701d03e94103800410540c0e503a0f11003845030a40d00418021000e03034805402c01148080800151218840c268080244000510310b1002800d000c03212a10350105861417000504005a600c540354a10f000c0c001c07202c4d109075010413991030074549820300f56003070820891181d4240030109061050 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 994534460 1250 994533210 994533217
    0xd05100b040c201005070c12030501060c140c21010b0a0b070809040605130b2b020603070c0605040b1602070807150903150c18080706080a0e07030302030c0f1f020c03 73
    0x104c0400412150400040c003034200f0300d103001e00f00c451170204151203940c01d12030300800341214043e0700e07401110130050782d800300034003102440400344c0e2003004d58506c241d654801130329540114001400202030284404103080d01c0408800b280036121503c400c002403204c00003124810358112000d00e44440750070000074090200341d4001c41c1e10442c8882c1c11115002d80c0d81c0b1208451508a6442c600c80d50402c41030b030020000d0031a10300401c0b03051a003110150602c00011980715981c1e150030071b2007280d10340d10703001101c0c0169000d90b10312030038408100c050004500340400c1702c10580018080c032860a1031041e81c035003003030140801040140d080040d13118090501a400346503c0940d000e0741e0911000180700034044902e85a001a050b480681c0643c0c0c2800940004d54903036a02910503107043c13010645d00048042c0903064000d5a1f00980e003400d800a000141c055446640a107036140c080703491081c9426440c034114100c0e50080100525424100040728030390401030740004d81c0390881ca01ca03440c103602 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 994535710 1250 994534460 994534483
    0x201090b0406061503050907090e031308060a05090c09180307060608160f12060b13090302010c02010b0a120209181902010210060501020a1b050d05100b040c20 70
    0x110a4800e00c802c102c03083e003160084d903c0002c01c00c0500b040c1d212046059440030317a0540f07a16009003000703110390729007034000d00410102c0343d0450f4501505400150026201c40d84401c0c0160002010b00c40001020701076543c120380c800000388041c116650000e42c00101c050008000070240800b41622104240140c0b030100d41c02801c2002000c0c2c0da00b18013034550140c1d09000c0b00c2000e940401040700c14210718030a00366a09405200d0140000c0d070b5403040102041020254450301a6807030065001044c00f0740412584241e00108904000080281c20360700101216446034030195814000c00081058801d445901151070005944501110001c0d01900d8491500c0e0f034000c0d10b022924030841c100203041340d240700380c0c200d0f000307184020003400880c3c0c1c1c1d600850340140c104e8175404c00840c248800c0c808240a590484000da155030b500040d0703840c9a40c45045840d40c2105542c205080810312641d81540d4007510b051158009994000300303101c1c00c03205008a0480e0540f600601071004024021004 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 994536960 1250 994535710 994535723
    0x6040e0705120705041407120c0c02131e0b13020d022109120415031505031b190302030d080901150b040305010c031416030e030301060801170607021b01020109 70
    0x10b5103510344182e282d8030b081c080c16018130308080039108203a00c8200c00d1441100c4c507541e4604060006081ca20181c03030340700f03002000c00c1000800c6130301582c0d440940140043c004000014242d2201611180050307141d1030801c00545405c1c5c0511454a401c490b401c20002c620b0380c01a55201c4002030700d4003d0003111108401025495103044090301c02d0a409405400f01d2421501d00300c0c1c0d0700001004510850052070b1816418030071b04840c582c02170300095161150f86084000d200c1c0c9500100e03107448807031001580d0750b0074624010441805c1c940c42d0449030441c04840034460a041d40c010a555020b100c81060402200400082460b9000e500000c00300c0c6036130700340402050303940462400300e82042c002921194603040c0940d501c88d0285c070464801d001c00c4070304843c0c5a61251981700c086d026030901d85080c140c440441e5444483c05200841c0681100c0e1034901007941490380703031a00d038010310f5141003590b400f40b018003801e81d07000104100c11900354510300c4400451140100e016002800f8014800f = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 994538210 1250 994536960 994536979
    0x6030e1002040e0603120702010e0103110c010c050912010905060c09010c1a01051008060307030b0604020c070f08160308180d060c020f06060f0d081b12041802030c0306040e0705 78
    0x40d6811903d1441c01401d04504803180419505141c02c0d1a104004000b4042071042e1000d42d419400781c1c00c0048254906e490790f13420807060a00b4103082d00c1c0d4070344100c8001f820000d0100c85a1801c4280c1002140c2000001c00c4184450303a1055030b6200c002d040034002503804113403881c3c0d0340e00c158600c2400951002102c18500c2c141c08112914960038040d062098441c440390800307580c4913140c006e10401d4001c0060480c0c034507580300c075501680040e060a402940800c0743c0240c4d1802000300304028480c02e850b00c07029914050390b1509103030f03100529105e40c0c0c0348203201f000420f151f6420380b0075010b070fa2900c0724006900c0c0310000f001410b413200004c100c141050751038400150045907100e612800c41e000d50f60b203540c506040003480411801c0640d4441141c0f6000800719404001a2032000388070b4038110313044a81d1420a5190564002000903411400a414080f100f240c0c10004011415442c05500714205801000d10340d0100400041c06980d4030700c02d585811000300503071030013014040c28110a = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 994539460 1250 994538210 994538219
    0x50a0c1509050f2109030606010e030c060a0c120f02070b0918040809150a090e090102131205150606072604060908070e0f04020907090e0f0106080f0103020a06030e100204 75
    0x100c8204440d81c01084002c0c1e86060400d07001d2007030449200e108006c0140c01f6680d030390b03001518407150410320103403d0b200d0700c45c0d01580c42e2620401410074115940f1000103a0923703245c2826940718040e80780c1d003009030f01d0700c80101d22a0001080d02c241d030402c2c0c0c0802d4480c41103c0c040381191a048802d041d40000c840240014829100d000b030682c150161052104182d100700405da60b8442e03400110001190740204125041e40020203d810004003c00549030a000902414030804503820940380408a20328a80c100b02c0d042003030700c0c64000c05000000140ca0801c000600703d005003080a0640d1141c000c02c070b215400c4040c403000d4488403042d2220340700d941301c07440100414801e008076602c500c82c3c0500442d1840c5d209c0381440c894001c0300244e00e030380d40e85c96081c888500e03005000034040c1302a95002042c0c03250044c0500340300300307428000c0d000f082d85000030042c0300f64400303040c00300411007139070050000d40c0795404040c0a5450302e08001c940365401008003890170803a110352040081c4041030100303 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 994540710 1250 994539460 994539463
    0xc0b041b091a03010908030105010f0c0b15011101050126010e010e06100905060f010e060403060e0a1101110c011404210501241802040509090f0d050a0c1509050f 71
    0x8240aa41c61440300c076a6034001030500b2548505c1c0b000e0102d040500040004e903105000d0940300d021140380212410a99a07035486180400b036680110403009110749030002d59210201d508400c1c000d500920884d4500145611072000000b440b0401d0361302e0090003c030040702508a0756541706880d0080180483e510030084d165002074941d000d5403603da407070020385203901e0f002d00c80c02040000c001e0004050100d00540380e03566195041c0e44c2160080c400040440e03250b110340303403401070702e000a0300c07244010385031000d49006070100b094180031103a440c03510030310000106000041400c3c24802d003503a014450414a600442d48058074212170328903c80d049510044008043c03e200301d00a1200440c40c0100200003801a4820186031481c5581080681c03041e045515510384606070061805031100041444418100d80c84001a44040624403607440204618500d00c405840d0480c141074400c4402400c0010700b9402030004a110320304140710302032540c803621203c2d42c0700c000c59409500100407207 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 994541960 1250 994540710 994540721
    0x11090f04030e03030a0e0d0204270b130803040308090709060f08060108072102131a090105101209021f1e0306301403091f0c0b041b09 59
    0x310700207401032000000c2400c00000780e8400b1002a140d0340040c22030352050001c0700d50703900000d0780c0c0305448a4440746924980841c440d00c1c9140700300381460b800c4a9090000074184042c0031003105001000c41d072008200318109032500a039151800301c10b6507c07a100030301d01d00016600120306003458940000303241c079604040d42040381d542005603909a80d86072500e6807100c28910814034120020003504403600c4e100100021500c0c030003402803d291300451103040444452500c0c58484d040c0d01e00c081d003064507050003114011b11f801c4442c2034220401b0f100040461069000d280309040e10352141b001155620810503081560a0103240d8070185d0040c40100800e0074a008602d509114023a0150494171134003031882a6004940141c2d0180d40c0504514074041c03007400405c190401b500c03182c40014014040c0e10b03554030740c048011601c4640900421407403440c54049010039a401000c01e900082e048410b0000454101e03000760300c250750300d00300a8000c0d4079003209928114484100412401c2056020 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 994543210 1250 994541960 994541963
    0x60e0a0b030f0d0f0c03020f030d090302191509050f25060906140a030f0912090b25031403070306030b0f0f01140607061506080f0c070f11090f04 64
    0x1121059142c1101c159110140c2502081c00524a0111001440d00500e040c1100522030700c1110b100c007010450b0380d07045070444c0e0441c805151b283c80482c0d045c15410440c0e010040f21a407050b00c03003d1025500c10b400010305407104003aa5446513204020710400b40408005d174400301041e540280201b801c0c140c02d01904503540010b4242c0d000c00440c000c0d119902070ac090340d00a80701c4c0d00b841403580c4203e000c15040a0240300800d078650310300183c103e00a0040074440c034440e20350001d8880074150701504001050700244036098043c4100464003440000708603268681740c0d84010b010380d240c20122500d10307107955032014000c400000e0200043c2c0c558400c030200c074040e02c1d0820598442440c201d403d900c069501c1d41c19466458010701449081084c0ca151882006098915250b0389590307640580300721044004501d0a001700801c03a180e00002c242da070161070000c40315a1803405c5405600980503002e0003070300b0740c03100800b1078003003081e6085c1e0311005581c010b02c1a03000e454400a10380d25240101c50 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 994544460 1250 994543210 994543213
    0x61d0a12031116090513050114070906020c060f1e0a0c0c05041802010f090807030822030f1203020702120d02010c08060a03060e03090411040816030b06010302090103060e0a0b03 78
    0x1e0341100c0302d1000c1010210300c0074003c181c104080c98102040090318026040c01d0f20746520441e01d0000501c240300760700d0f00c00804c14a80210745401807018104800303d030700c00c0043d90850780c900346054ac2d034881114219183c01000c19114550401036002130341e00c03900c61120003000000c41000b0560172064400000307100385481b200d100d40759410301068488240308140c910003210740038001907005520701d1030540300d189440c82156588400c518502241c5038424cd9049600141981075881203d0031445000403059600b000c55182d17941ea40b0307243d003c00d00040c0541c2d002d003125118a500c20307011503607480c0d001008858150582c40045445001c0c2c80f010384055880d241400c24001d0240d01054407603940100600e250600c1e64444402511003903082c040300307020030032203134031036a5940c40381000c24045451b005840b242054201172500d81d07445401c0c1702689070310034100009030480c09900d910020a18015071181e140200503005040b0700c3c2c102203140c0340c0c8d0608006181c502c0b0390141080c48400c40 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 994545710 1250 994544460 994544477
    0xc03142b0c03020a080f040203150a0b090a06050a0608041e140c0a0605090f0d060c020604030818280f052109030a060b060d0203010f050a170601061d0a1203 69
    0x901c25403ca206880c060341c085960000007a00310304200485a40c03290020301903c1c014003c81164030f40c00e940c111661801a0f5444c603d210301414040681548408150420001c0c6030a10000442d45002ea1246a003006002c2d4009410001003000c003641c02e045080d00300d070230250303945015005690f03418081901c9101d180303c4580385140004403c02100d4144e150182b0381290b0005202081e0718400c2d030319800240316910f0f100014070912442000583e19030162600781094074005045036800b0380b0078851480c001010201c1c40c1d0000c140220107941c9084415003003070302055443ca080600356406010016801084424000041400c2141d14a021510404e980701c1241004050142e44e410503016071000f03241030000b441e5035100701220700004019600707210080f8101c505a0780241c0101080e50180070003040359051091064014200882c12151102c42c50f008050b95000e0510500b070400038652070b8151061340400203060040320103007a60500755160040307170980d80401380e800c500151a10 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 994546960 1250 994545710 994545731
    0x210906081e0711070e011806050109181a030f1006061107030807030201020f04120203060609161404090f1a06070507031212090609140d0c03142b 64
    0x28601c160485954001281c1c84151007124150031031090418244242840419800840c541043c021b080e178101440c50186100c03c2c0030151021940224140301901005110035a50f000301401c0b28819090b00007562440c402003030108004200c1840d4140c026440340601040c404185c004017140c000c2c100744078096aa54003120760b4884541d8031550750300811710a100281200004085080c083d100150905401c030b940514150301a9100300103001500c881031046040601455510070300c00c84403078880e4900321031101043d4031041c010000300804210101408081c000940c5d0241406000400c065074a62100d50000d0030407041940d4510b00880046507240f4000c4226001564003d02030246d5501c1c0d030f6108204044000401b209000c001035103800000c0031803181d5218240600c40100350025a802d11842550b00c91803459660341126900e902c000ea0049011040150315140c80c18500c0300b811040c09181c06081140f40e070112448403140c68081c2c00d230b07100c4d05400303111502c20440c1c007410 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 994548210 1250 994546960 994546981
    0x60603150614070311070b031602010b0603042001170a0204090608070b0a0f121802180402031b060d020c01150f0e070e03100c120605062521090608 65
    0x3418850600c00300704410380021784562600b0720300d504040202d41c10316890710002a01500b0458844640580b080885019582c0c24000d00302d59030350942d5158554200368032a403c041c000280c0d850101b4100c903044c2c4c00541d00c144400c071480891401c4005482c01c001440801035030251091482d0a4200080410710403030200e008012140858626440d154102d40240c40c541d00414810003032100c85280701000e603010b40143c42078643e9902a1401d0801144100b01608103581000d00c2c2d680324a404002c01038600145105485640600c4892404021000295144079440301002c2450001c5007210010a054002c0b106401c007002e010750195866182d603c2800c000b5201d8840c1080100003c191081c0c080c0d03c00c0e00308400064117442c491801e00010500b40e43c180056600044c0c90101ccc280f000012608c941e002810080354030502d0075411500c5c00110100f82001ca0754800358803403100c1d00704210310301811081004090111254180748a0142c401101c41c4500c80100c0e030388000040d0107814 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 994549460 1250 994548210 994548227
    0x2040b1818100209090711190524070e01030b030703140303042a050409020a051e010e0a060c021c0c03050601150e03060403111f050406060e0603060c070f02040606031506 75
    0x2006000c8100c5e80d41d4100302140c0441c1d4104025105000c0c00c07800184402240c10111a5240180300614110f0300584034400c10101c121888403030030307110743d0510501a030311086c0c0100140d424640414a0200d000004e8105400c90f40001c01c600141c40c5200041d41d000700256108034000d00300c22071b100c0c602001c9499650300c07002100744912101c02c0c0a100074036103176105c01420350019208085954403440860700314641250b441140502d0ba01900400b50b078004401c0358000004c2c0c81d040704192030301802030151004c48000038440d03031a02d2600401c140100840d54489070b00181c0f141c500b04da581c14510b460750000e01484072009060f008091b2010302a00ca2407a941d8400344c01001030f80d48030b480c110354001c40b400d410009400307810002c00031100e8a01d14079000c8a40014000380500f05850488100d814542c060202040020200465070340c0214003160f100c0c0c60201c0301c0fa0b80d800a89890b508420250400075842480c148001c108194140e020011464182150a10003170311903200783c4d404c06 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 994550710 1250 994549460 994549477
    0x110306010302090a0903140d05150f21011812030b01090506030f070e190f080a0309060f090b030c04060e041a13020405031207120f090302040b18181002 67
    0x5000c1004c07070110001a0f0152043e540645003d0018410401417000640d00040b90300841c551100248031050048407030308842c00000b22113a83c010200000414000c0c80820441001d43c1814440c0e8500380600b908130040004048a4200c50780c1150700d0300b00303d4801140c9080f00001e142040c07400362540503d400704144e442c01003045065541c0c030f86400075000700c000c1c05007003003018070362201503203888000c541882074002c0e8520b0340d0940d09003041c0c148540d070150300403080342e44000c0382c08012a40101c000c4042e00c009240c541483d0740d85590035141d000c42580030318907021002040080900c0c5080c050410754409540740301c840402c1804000c04c2e11020086400c5960b804011080c89161544d100460000c036504050b0406544e5030000781040c510310020f00b483d8034000f035900c3c00c111a01081b081254154104000501e864400c001d10003072450000a024507541c4200c900b07540da902000350740d4007049070b8496000c3d1034aa072102c0c60010ba00c10920001d441030100402442d00d407402541d0a0b40f = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 994551960 1250 994550710 994550719
    0x703020c0709151418091c020111090f0a0305030a0f030c050702010e040c091e0602150103110d03120216020406060e060304060506120f0312070806060d09030207080706020703110306010302 83
    0x190130004449119500d24458641c801c008000d64668504c1040716a4440c07400030019000c0c00d600784070100c41c84910200c110085900d003c0c0c3c0100044162001c0e20329184081d55003100c8440c400010400c000c0c41900054200e10010403494000707540a4082d8190641075581800307409260801a03d81d03000c0c2c1c1c0002804501481000040f505080d070001050218614000c1c0c04140e0314a0302c05801c01626001258140985c042071001750f804204404401d084c020021001c0e624580340e401e17503401e00e000391903c107a080032911340906201d040e03010380110408404565989036254440040365215004074091402c4c0b8000003100350203549004c11800300681aa481c40e038541c5d50f100300610004040e01d038080c0300989074944142d070810115090340f04a070300440d0b0f81c00d402c20804460030001402c02003001080410410261524420f680fa1908a0b03100440c524000d880c0c1603081480070340000d0558411031000054099000a07010b044034052244c101d0f2410b248070906455900034040a0b420 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 994553210 1250 994551960 994552001
    0x50d02010f212301050a0e070305040503090a06020c0310020307050a141902030403110d0206040e040f023114010513060e0a06030212060906060d11090703020c0709 72
    0x100d018908002c010034030b60115040084410707107448101c6001501032014a00d80200900090040316034140c003522045540a40711441d1400b4074109520083c010340c2015110f030301040030490100161011590010700c00c40c0103649a460003542c03560303d40800d500c2403055250f100c26850091003228050030301070fa90b4a10f04075050009030f0728013040303200360a40b1042c10441d4510484c0354503040385401015a01841c0d0701c074038500f4a1026101032030401482619181908001651207108a404854141c2c0a607500780e560360030054042181d05001a401103055006001000640350911048a29050810188001c00c0307603004100c904800b603e800a0700640c0060005283c03a48122307401d2800100d011820755250300d000384181c4010754600f06202c1d1125001e108600d00f151840542c0c00c0750707000401e00f07840d100750301c21707038486000d084a40a003030011490b0341130200c1c051030000300d0341001e029041d20b0305188000500952114117600c4450207045030109405034140100f40b952900050000d60 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 994554460 1250 994553210 994553237
    0x2b150e19051006140d0f0203070f030606080133020105010801180203121b10020426120d060503150a050f0403050a030c0318140f030403020105120a200310050d0201 72
    0xc41c40d44490744900e580d201400f4170040068503001380c00c0c1e140b205250168880c01c003400c1c00760855010b03511240034141000301c28442c056125200b02d0440f000e2424030480c0350180e00c81026600b8010007401e40a07c040503180d511990150052812205020000c01541101440e8400c20401d01c4400039859049401242d0a0209110281080d41014000d00034040c1032003407030701d14182500d030151580c55004141000400e58034140101041f4407009060071078442c040034180c035804076017016004508080b80d0511200c00b241d2042d806480c6c042c0031200103a500140640744000101c5840043c1820b24002542c4250303410001400350782e05854840c2002003c190603400741507400794000400d0782e9500880726045000348400c203c1c074014500e540480001041032414280c0842c86200f9541c810402040143d0b80041280ca202c0c044c2e4204050948070115914094a962145480b000c14181d01c0d0140041d84071004600429041001e0032034242e8442c02c0c082c07100c2c400a406404598250844003 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 994555710 1250 994554460 994554467
    0x8130902070b041b082d1009051501030b060108100b0a180b0901020613051c0804120311071104091703161d04022d0706112b150e19051006 61
    0x11102201e0030f0310044080306c100040b0316280c0c44022520040d601e80d00030304d05104083c08400703c401e1180c900c030f0000b0b60654803034020340300c0068101410403441760000b8400c1230a40b665040134010000d4000c2c2e5800d45090000c1070140d140100310b2920b89491400540c2c10f08081c2200c005a80680142110780c0c0e45e01d64040f00700d08003080c1900c950148a51001540d82611102c0140120984543c13a0b181041c0c104803e00c6010440d025044c945002110b404085e56070301561034450f0301810315001c50004c01c01090150940b48070081c101e45407480c0090100c0c0040004e980310f50358040d005a40c0e40b10706682142c1c90031426102c94040521982070300a81e003810b80003400e14070003001c540e2009072a02030061400c101520540c494180000c1003400c00c01078140582c270b136158960344c225070130104034000e0120b4028441c244404035200410380c1ca495101950449a0016030300b6090b0300003170b9620040300f0040101100c1c8040402d0440240c02400441c900c00d440c010440c0c0e120350030082d8205030341038 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 994556960 1250 994555710 994555753
    0x11030406110f0703031b080f040303050a08070c0c051003021209011e06030b040b0a090c09020c21030a051e0709151b140a06051006260408130902070b041b08 69
    0x2a03c00c04400c01070700d8081c40301c8c14010002184203545103560307220186401864124040d000301c2c10041e4542580020891402e102c0741994800c0b21040c011140e00c107401d400912884c03407800001071004080042089041d0301c004800300c9031240c10031058a40783d51103421680103010080044180d0f04c0400c1c0450f42c070740d80080d80060031030000110048540c07240e529001e090790150025540000f20283c9456040c8000380c42030800240c240d0404950b903081081c20701000b8580031030b0560303c5001645a040c4945d114901070b418180650716030501160060880c0c2050050b042007407955140000c0c03451041c1d4008044c3d4607259843e00074110942e07240903011900c824212010f1154003604004140d09100e03150040620702961041d039480c1840140122020b0012802040c0c0350390008800c07020059200740d0301c40e521800300c80e0384107921005401503150a8114000c3c00d407021490740100098549181e02840c0102c28221040090a840e128454601c0c09841e2503034012000300c60403000109540b = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 994558210 1250 994556960 994556963
    0x40b0d02030712020c060105010e0d050712030513080d03050c0a0f032a0503010f08061905060a0f0b0a12020f040b0708070b040b04030e010806010512060111030406110f0703031b 78
    0x48412114401100004c0e60040c0040700503030381020004200c0e41d030300049100c070340000c1074822591240c20b5448907522044144680d0b00d12041e090342000c1013500c01e0040b900300754146404d9030307140358480c40d03c01d68a100740386561010a2a0402150505003280309541400c4241c0d03503050b5101e8036881080700034024070740000c01002481e010650542c00032490040300149141da032130b80c0701d62404d05800c020b80517035401525160428814801100d2072861b494180d030424a1021543d0384580d404a40102140d0344002e5859081c841c000c18243c10103002010303811065503c4105540f54100701c5000c0344654101403590520401041050b4002c2d0009800719a02450400381804816241e90003000002c440850300b040b20842000101900004d605c0c2e2260300a00c1c080c01e2a260590010f080c41c443e030f0b03201001805902e000290268405c14810801c903890209a9456942c0c2e04c00103001d64188040c0c0306007030300803450042c1c0510b10010324401180d815076907880340300707500c2d03140e14005c080300c2c280 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 994559460 1250 994558210 994558217
    0x8070306051012060f12031e0e1908010903030f0f05010b0a12140408040f21020603091e030a020f19060203060d050d020c10030510050909160f030c0b040b0d020307 72
    0x40081d0703171400ca01030b034401841025000d001174036003460000d1403401200c640342c91400d82e0241d07403054036910203850401e4000544080720488507103400781c004a0203580c0280d2036507007000220000c140d4582c00c0302d001c0f07600e495402c1c0312000b4a060814190f40090103580f038004001d106000300b00b80315580c0c059052030070a800041c0446084c00301d0b01072600c02c480c02c2c2c0c1d19000c00503040000344011080580281103074008841c440c111ba410007000a50038500c080d114403000b001103440c010090042e4944403075101c841080c1d018107404c4040d225040b6180c120b0243c0140071a0003150034001c621800e41515010068034075800c240d5485d8020b402c003600030b68015220480400028008101c038060440303440d00144805044002003003000e9409074500e508140c206414001044035004c40d0300e0079038400315140c40030f036950300902da460509607441d59410152035a070001014151042e48409803070165006900650301c5e051041103e11851040c514146001c006100052a0682c040c41e00301c5010328 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 994560710 1250 994559460 994559471
    0x1305061e0123090c0d060b04240c060f0204120b010504050c1602120a021908070f0302011e03021312051e030301030b0601121d0606010905030a0201030b2e08070306051012 75
    0x810500840300c654000c0c0391f00600004052021000301e205040a1030200000c070901d01034005001072401e0414880200702580b11903107a820b02c3d03a03540654001d000400e116120303100c5581046071240d0300a00c80c81d4042c03032600c00819036144c801e40440308414074903200011450010341c00e00c01d4440807440601d07114041d1036240740040c0d403988001c0c40389406505607810360b5810140c0103410820305a200d84000d4400d1340c41080140d030407201c044d61010310b942400100c1c00c401e0030154064460f24140d207126401c4c1d01004152403c01c0502823104c50301407800c68500381351511100081050901446603558802c0c0300400c0060703c040c03640d0307911141c1850301c2003428803100c420b00c0c10f840c1c2400003e07510b80705400e15210145070070405141c3c420000d00c0c02c54242d600e1700d40030945840c900c0c40042d04050310303081200b400d5141c41e05856030900da600c040c00038201020b05c940d04485030b0348900c540094402804120300d603109004490175660000d10940c48284075460680d440301039a0520000d00c3e803940d = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 994561960 1250 994560710 994560727
    0xa150501050f060c0127051902132d0c090b2b0b030613031d2121030609070c0b070c0f0c0303020c0a08241305061e0123090c 55
    0x32951b07440007440e200f014a10801c030314000b0306091f400400c0307602c0141c004240e04056038465242a80e8018a090b000032810f1941480e20514614480b02100c01c000d8030f880c0c1c942002e080d60040b5014006507440160440e00d0b01c003514154172400c0041d51401c10029080c0c0e4400c4206c0d48045210405010001030000e0100c0109040200c01c5178250f0040c3c0008560a00745600442402c003824101d04c50350303285000c03500004002c60b046d1800c1c0103071403060180210089800b00103001708050400018400d11140600100460b0300c21101140600c402d0004141c00340d000c0d8500d0708519034000310500b099a034001048034668500303d41921203d03900020000031078202a40c19000e503001e80e010b000d40d45800418400d40c119035a000000651001d02400703a902d500302c00b10101e9256418401b481521114080c914a000307450000e4040d001d403409001c40004000181155034118411100260380c0c0d4800c00503504108401e20800000303402040802c2d4a0240355150b801000d112000b03040c141030 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 994563210 1250 994561960 994561991
    0xb0c07030f061a0103020a140c010e060408040f060c05030405090a0617070906051905120319030c030c0f020d0f180e04020f09060312070201090b0c0a150501050f060c01 74
    0xa00703801c0d2001940e0700d5411414a86150031100d14110a0900390703d07003007112078024514840000c075080b407442d0120f0721140f685002c2d000054486030040c2192120b0515040112045d449882600c401840300340c0300085160080081800d411b0b0454080c5003054a00814070000120081c012a001c03a0340d0b00000c2a1120903410608030088814018a01a030130801207400700c42441d081184198146803140f00e80952050800081d80c0b019582c1c10911410034409521750f0281c008495070302584144c0c0f440c800f641c950f1040d4020103465809000ea584d06000c261385141c0c8800b55000107821058080c08094040e8100340d04142d000e24020f0407038141000c0b40580400c10b43c02c100400c0d80d821041c8000e41c94035550720032800340215136900321402d022001940d944c01c41d00c400d548650003c60b8460a45e070041072100010b02199025941ea1a85410400d4641d41407050480351358613845500f841c1c0601600ca054140c1300e0252181d4031240fa15000c003e40f40e0040b00342c2d0a082d40d00c031860981da0038035 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 994564460 1250 994563210 994563233
    0x40e040f03020c03031804020d0b031e060f0105100e03101a042403020d0305070203070303170906010312030e030708040609170105090304030611281d0a0b0c0703 71
    0x21162080c48089a00d8001d041206680401344aa40180b00600008000d00c601345107400c0204c1d80140d0300c0c80c1d4107034500043d20804801e680e05004005a820160007654a01590003400d207090720110780d600312410072880000c1c01045d41100700b2050703900341a80908040783c5402030080c12600850401c603401c0d82594600c503141018181c00d84421201801c11707001e075a441340031444250b4050010b800c0e01c03031440e40d0180b101a12812200324511706040c0035404650490760050305540d0b0380c40d103c0c10701400d0030000c400b05c106200803500014104040208500e03041c0ca0744529000210304540710110f029040000c040c030460b0004000e444002901000100300400d055180c44001c54600071110212010203171801099034140410404284004401c803803d582d804140000d0382a2600804401e43c0141a51080c0420088004061103030400d08004054001580c6131504100300003580705558a0b050030442d0000d00103201800b00c044200080c11904024504480540d070342c0741c490450140 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 994565710 1250 994564460 994564463
    0x30a09020d14070f0b0403050d08041506080c1201020a0e04150503060103050c01230319020c100e06060102010605012a051603060b04140f18011e060509070203030f0408040e04 77
    0x3440203504001021107414990010200c81728074034201441c5480e4261502c028881c2182044800d0b0005001c000d203403580c072040d50721202410859181c0f40c400d0b2546d618081c80d00544511100c0c0307914404071005000f2140d00c1401542c410030303040050f0081c0000703440d005116202c0309001c02400302d0140c400b0441316000790f005030010040000364400240000000d4040c0d05407808521a003884078500810880e6040340000401c94078212480d80080d0083c0500840824640200c0140075625546500710755030301c4125100380c1d56030340c40d01001039003281c20b07621030540820021081c25260202c2c011081c00c44080183c1400000041d80d542c41e820300c08091254100312121a1040c020700ca0f2621a071940c0c6081524100300c80c030689002910308203401003a034200e00708500c00080f03043c2c0c500e201900042c182d9400a00074200001034280500381700e02200a403152501800150500d0030181d00e5001340e14640246240d074440000400502400a0003903a5a900070440040c0700042d881506200344d = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 994566960 1250 994565710 994565713
    0x1b05070510050f031504180305030a06050f0a0902091c050708101e0902030f010c0e04110702060301061409190e090106260708030d020c0d14030a09020d14 68
    0x4034145810040c0710402464071504101c8144100301e581c500d600e08803a0418115481d03100c0041c0b01400140c09841c03009540f01c4103d100d881f21008040c2c004c0007035070144811140c10300110307846606002c0881c0708051081d6114825450400000b4480c0c0c0c010004048081c081c04415060b80d40050810b010000c4121002e901c880c10400c050340c2c0500881c1e1407001c0d404010300c12070040c00d603521400f18807480041d85c85c0b942c51001da011980e08002408091000304000c0c010440034810241c10403041200c45401641085071b01249030103640122030b02554010212400e690a03d803045071541c003000c890801d80402040031605660b91003e0341e25918002d41404100e65003030008070044034030080e1980102d40e05200090040052903c08883d0702c4680306207080420b0640c0c9100c40c5400c030203038010b110703070701000030036030f10112850300203154141b0f0310030032280c0c250f031903403401c540728001110000d40e030720320600100c0c04409a03a0042c0c0750860004100310042c103115101e59040c2d695021094580307 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 994568210 1250 994566960 994566973
    0x30b0301021b0d080a1407030e0c0909060a0f090b01030f0309180515012d091d160503130816060f09140712060e190501020702031c1b031b05 62
    0x80c280c1c4030f90704c594400d002c10018400c0200803a040310380b1010107040720b410b00d1341b20305c9002010395041003c40007001c0001e094194038280500c015455041c00d40d034490308a4141b82071a500070310540100d19010754041343c0340f49103a185840300c683c072481000089081051403240001d280000d0803a410750011a00c000203924201648c201a40d010020b00b034505000d015404406842030384d0144504140c8401110742c07008a126070b044074100301030707000303100000d11202d040c01803c001050494030851148d200303000d00a01050007661180012601e40b030101c400d840480c80054081c4c0d02900000c220000c2c2e203601c01e0296512481603440304c0782180803460340c3d550703c101440985e4034001d00c0050320101410035030b414160b000c0d216075003c0401420180d1101c104881001301046404204d03d102d12400f46601294a0903a02075800710906034030134840c2d280c00f86040d8440d60440071024085e91200c00c82081d074410420310070303c8900e4065007441101200c5081a4011600d0b010046114038054141e = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 994569460 1250 994568210 994568233
    0x140d02030702061c11120a05280c181217032217030c120615072d1a0106020705090105010e03150a091707050c0118180207050607020f030a030b0301021b 67
    0x300d03072000f030020300049181c9e1907030302e203000f401c032042304a080140d04089a51840c00c4001c2c1c1d0803803281138984440e5071801c080002d4500f4400804c03001d441c0b180e0704440d222480c510109010380016500c00000354114a100c55070203c02003800140d50b07200301020254001e03804424902c0e60000c441c90111174200080740031580001d02030240c0e000504079a600b140750b9103111b114649000f480802040c00b4420104030034111040114800105c0301050315800403081440c0c149801c0d145001c0441d0120304000020840a0022450b441070b9400900001440da2900e00111403d0690006d038a406018550851046e4410402e8280c455a2840c50206001c01280f420600900394a294280c4403241403003108000f0740046007c2062010034a04105c580c4d45480d1084146101940000008040c1620b965a48040c580181009902520a81e1684d956041050342c40f0f50751a0a40c02070340d0420807400d1a0b11340281c0c001c28201030301400050828095a900288401604807000410b0b44401c2c0f0110 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 994570710 1250 994569460 994569481
    0x12030403021806010540083f04090603030918020c0c0d260301060e06120126010f05040201080a0b0307030201210204080f0606220b010516140d02030702061c1112 71
    0x501c0c00b01001d542301200e040e24009a402002c0510400e01e088051020f110071113003540607200a0440003c080020a64906d80601800414031034039410010b089100c085040f8144287d492046030840501603440d4080c013007140003180544222010900f0b1907018003410400303010140518071800c051a030325410058050003400e442140c240c0306000402400c0740301101c00b40940e044540d581c1c842e01081d510300000070300c2040300b40c98410a66107400140b02505045070040b6001e1030003a210f09015440e01414003044e1510800c0076505544852410401540f294010080e100c151205000b050982c404110003a0790040c0d0095205a21032524403450030001d20500c1d41105088500340c8401c1510407104c0d401505d80080e030f032a002d41e55000c1c00300300d034013a90449200900c8081a0700d2203003000e2414601c030554284003c2590701c00c1c42400e207401400001111382c8250002c1407641402e03040e004402810200e100000c00464417440c2d003040b44080c503405405000203d54840580d8a001d14505 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 994571960 1250 994570710 994570723
    0xd0f09031808120307050903060a060504110307021c1803030210050919030c020a03060507110c0306010b07060f0608060708010602010c051c05060d021203040302180601054008 77
    0x20380c40c800c41007604001003500094445035a028842d03103ea22640c2d460829611402207002c0240c2501958040180103a00340d404a0103407542207908100c0c1c1c60706d6851100003070208642c4800541d0103040c060868469040034800180001d1900000d001c50001c1e1440e5550408d03801240580d01c400c001d800c40c83e085006459100c00030700000c00d402c1001c1500340300855021030000d01842049100075040d5203d80447c80e0103160030110901540c01c280c0030082c05800c0c05800c000403809102c6e401d03407031440c0108440d412104a05800ca040200c1a00c0d8600101025600d01082c1655028000380c22001800b50a02c00d00c21520703444080d42c1f406001900b900d04111820042000c06c00c4200e10455241040b00c0c80d4a010b1170000500ba030b80c032008615001191800a0b501400c40c21036814107160000040007520310954140364070300c150002d0302c0c2d600401134890710301158084c08002c3e12440c034051165246842231501d400c240e651300040c0941d1800d02140c40524500c0c040040c811179808100341e = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 994573210 1250 994571960 994571987
    0x406050913060f3218040c030b010b0304150b030628180c060c0302071701022b060b0913050405070e0a05060a060813080904060504180b071b030e01050d0f0903 70
    0x6072141940ba2000040d040043c0801d004560070b141c45c00b1509001c1e049107400d0145d80c2c0b0418807441c40d6140c0c0c1c1101402d800445d4211101400d03800920300f031440c00e01800388030080103002040341c0d407142d2102c2091030200c03110341030240307017105403a4030221441d0003802494000548041045131072400c2c40c5030b110303000390890400c1c44581c04442c000a44d0010301c0c60100d03054900078a01d07070041d00166902912584800315000b10b00e51f41c1040184807114040c4822154148041200503500d090b1000c19004495109500c204044203c48000303400e504030340d90041c811070641e40d9641e01c0300ca8480c980b40090750820701c03d96503201005180d05003411110040e15940c1404222454140b100401401000710010085440810304601684842e0030030350241c00024024403082807200f54082502d1084002990640501400310f04128000d200081044001d0809001d41c1c50103500c0c1510142c0441c1c4c240350412004000c00c1001c04018450704801c01080100410142440c0c1002080040744814 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 994574460 1250 994573210 994573289
    0x39050405090c1518180402010e2e090906080615030a0b01030305031f050f120c0d140c040b0105040608070c0c08010b0a09050702030a0c02060405030102040f0e07050406050913060f 79
    0x2008058442d05807070107a81b090f0709103040b007040403071140400c1c0c0c0314501d102440502c0004201081c0e0b15002d0804001100b80345030794502c0c03141e90b125020783c19140203114080050700607401049012010002d6484118400303421242288030594a90340007142c00d900a034001030010003400b54010146080c2031111420b03624081c84503042c040019150f5450034202480345041b46101d090100040c840341d44c07000e200400e402507078040b50600f0129120100031080c41d034018920307204080d1515119420812006a540c5410f05042410550f100c6102414080520441e011200e0010380c0b031403070000250100c0300012030f06401440900c80325141c40e8121b1201c05090008101c3e005a0000589220740352518003042410300c1030000c21401d01c1140c101940550000501141400c00741c0c26071022a005481080e800360307100403040b0369a00840c069800080c0c01041005403030300d0040d107030342d068088142d070002e00c05135240b02035039200009034401c191000004c1180f0344104644001604089d12a18 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 994575710 1250 994574460 994574479
    0x80a1e0c030e210d0c0201020609010e0304050603070306050a030807051b22060806040f140f1c0338010809030d022539050405090c1518 60
    0x30360107426000018016800f800a5503010312020761103c400514550302c060a03100b400c081c250b4010510580344000380d02500c50300006c10450501442860710418545000e141054200307010803401d60300140401c82055190400840c02d59110b01e0180c00a51040c051541e64100c90301d802c0b030500034940541562040c03031072035a540a41f213040c151071050b00c40d01c04a941c54070320010755030014245504112014402c400c100010018040d0f04640303058084c904040c80900c00c404804d40d9111098900304868000544170600c09c03006504c0d07080302c486c0609011030348244000707071001000001c0d002c903048a0740d088540c0c004003094100200302d103142842d12607214503042e4851580c070b03c40e0b41146019182d00040490f00361505084280020000101a80e1075004d0b60030148840880f841e064140d108254a00d010408030446110341950b02d140e003006145490841008020103000301400050f0007141c00001c025600c1c645840126003110580d01c0d1075900c40c1030184500100c06c46400e0042030034a = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 994576960 1250 994575710 994575713
    0x519150506010917030c030301090b090903041d04020d02060703180b041d0408090d060203010635150a080f060a09030531091d0304121e080a1e0c 64
    0x891001c162011410003015404c0005107061642c82652140c42c154003000c00042410b111b5030300301c0d0f0100c400486d501a0350392140d503801c64a0303101d0b038403c1d1510030a00110b080b22a0f01ea1a0b945c5500070b00040c000c2d0001080c540100d407040e84008070850002e00d500008181441c1d182d03c5000141000c199101d0800d81800030039801440c5803542045a4003c140010707003003000740c2c0c04580e0be0040280900750041114502000a50428024140401c140301003c6a0503500502c0300008408050b281d04034808002d51200440c2102400240303031810342405098030b07612500c0700070b4000c214140003040d002ca244920703d07040c0407014015404807820300c140c05011039404015141a113289182c143d138005030407200c0c5200c03161550802d00320910040d000141a2400b54000802481104084d0303415003d001c0e01c6a4680c40703140220a40380040c4495040461119611882554482480c2c203a031852142c4440e007583d0021341e4114000f81c00006520404544606103881040d0b01d41040080f0040f40e = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 994578210 1250 994576960 994576967
    0xd110907020f150c0c070b0c010b031b0409050f0d12061e0614040f030b04060f0605030d0309021507050601030201122901031407080619030f06021303051915050601 72
    0x4404403503420341c00000321302c0c0d40301c9000c11a0706070401c480c1103841c050f548040c202042d40150180e56195460700803080c900e800c0c081885004983d80742e030565414422042004010501402c0030342e16840381031480313441740b0020018507013003043c1601c400301c040400c3c03540c0701c0590f2402e0b0800800d0148029681ca00500304040d0801500c00c54240541e101c40040b10800143c040e07544002d5000c200700400000303100c0184061402640a0304040c007500e082013100c0c50994829116107509035204403554402d052180d800380c4501d0340700508000505402e00c40f0074010383c00c42c890903216504001d004004643e080802e01c10b030044241e106004a6044004424144a040d82c83d45061080d0303051403000ca80c801d600081081080800ba6032050810040040012908075440b5000d85a01c9410845888003070b620b010480341d010701b50003c0000c09942e12000b0313410000310414144038000c1c010000034002d00615a140d00401d0204021401c00d0408481d581d0a800b041106c1c0b80c5480305010160340e0 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 994579460 1250 994578210 994578223
    0x6070602160b10180207020306061c300c12110703060222081f0b0f06031e0109020c0303010b0906190c03030b0103141807150306080c19180204050d110907020f 70
    0x2200d00100951143c00300e1000c1d945001001814510318041481c42580f4801b240d10001e6401180c111108480880075200c0c1b006114002c3e0140b40442d0100b6034ec54031032400f8491a060303420035295519a2a0f642d141660405010355440c68414215562080800601880180303011030082050340e0103160401d040c0f43d0301901c0130b40b1654a03207001560a840382c0722602d00c494009401113036203282034065060b40c428196201900813000c80300025852046000346d81c0b038031452502030340c80c40e40f82c0742a0340e9441e8801c0d040d05400c041c00740500700244502c11142ca8000030291901030310f03240c0c20301e402000c8455400d1000d0616103080142211654400e1080b5804240b1201e807080c00c841f1038100307900e0320036544d1001c0d80100c81503a0b20892540c1c160000740481e5564421520320405d0035041190381c0c40c50031000b4051101c0b1140401c038883c86000d11a0305032103d120010301c0c003603c44021039a51b14444c0070542c2c070302540070380d403118904000747d040c3da00c51040d1000c6c0880d103480c000016203440 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 994580710 1250 994579460 994579471
    0x20306060114271002101113170708031b071d04020d020d050124050a03030e060304030504090f020418050f0601050d02041e08060f010506070602160b10180207020306 73
    0x41e03403083c190f401c1d0000ea4501c4220004002c0407032034000d0080d80020742d02d50102003a800c8150900c20706c0280780d03c040003500d86400160700d00404050410b4000040400c500c1c1c60400107210355000084c01d08010310003403c07500801401100d0981c4103940941c1360060580c009070080c1c2414020000c1801070000041d00b090717044031909481041800020407103042c54401400c554038002e811141c000c1110300c00b040310307104540302c0b4004990700c0b020070503138a0007031001402207220350320014201d103807201c002c0d5440351107820700d1410300b0384440c0480100d51001a480004640c0000c081c4210030101000c1070b01c81c0e079440303c2132006161507946162040d0019110a051100104402c884041c66405a0700900b0a204c0d5481d21001070203040a0f840e0740c1c2d4810700702d45026440100d03d0140e00540d4482c161040981814641940c9a071250300a41c0240340341d00390160000341e40380c00520400c400d503000d06200807550502c81d0801d143d11080e64800f54040b500103104110404c01614040741569012 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 994581960 1250 994580710 994580737
    0x611210f07030e150409061d0f04021c080d060902090d02040203070e04090803151215270a12030902090a0e030702060406030c0915020309150f0a0c020306060114 71
    0x310030a1a080d9101c680f80003240b640504240705075107030680100b014100f10703601a001440b60547c0c44071800318044008442000601c550320024089942c840c0c4420b40140c4060085044601c100c904010b0200003000304483d03e400c00207001c1c10f0010507001391409481001411494050304d4400115003800d5008000e0003181c01200040002e4080c0300003e210101c00350090101c0c80b4117241402c01c1d680119000c80d5004001101030013035081241c0c208401150740d4008000840c1d1903500583c1d4100001c2680c1101010f109004c00341c4810380c41000d8004606e0707801466000c1c1d95203020007018401c20540070406103820340c1440565100d02041e1b410041c86207002625071501190341d400c40c41441d0003c0d4100350009400504544d06600061001c0071a9449240690311502e41c4901c00c0c200e0410700780168424013040c541ca2030301001240d100100f81c0d850358509040055407140036081011804c0200307019401d0401075040c144103180d4484000d10b0501c00000005983d140c07039000303040911544 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 994583210 1250 994581960 994581967
    0x160524061206040b0a02090d0c0924030807050a02060d0912030203090316080708030702060a0608010212010905090708010e032a0d0c0314030103240e06150a0308040611210f 76
    0x7400c2c0745e80d0440c0c41707160000c1d00d84003505001c1d042c50704903805144120211280ba000940e401e0164018403074001010024061080c28519154440135412450064810340030708110100140e855500400c00452000d202250241305070030180f241000000710300040c103004008200c0d441034080304403000c0014100c20010744d146282421507843c0519180101100c10001c14400f01e15000103035030f4461510a0000d01c8a20340b02c001c46030a0303000d2140701d400302c0c8a42600500c00c00703138190803140c1c0c0201d4120464010507a40c207021401d44506500c00079294100240000300906141d40302c0f5a044c2d080e06100f0210008111040c0d92079a240c1000420000c0502058041600c60451900c0d1004c88900080e16540c5034148280110002c01d11825031503c94090040800200d029540c005203190024188942c2c54800c8854110400e04050342d008078891008000562200b0240c800f414150380c80b0980e0041d140122458480500080c0d010040c4d0610034002c090350450442e02d603203d41400040c4c5 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 994584460 1250 994583210 994583221
    0x21c0b181501030503040e250503040f0605010b09030c010318020d05150702010c0f02060403020706050d0e01110304020a080f030405040c030b06070f0302161a160524061206040b 78
    0x500701c03000060002118801c0001051050020103002640c0d045486580d882d26001007940040d41e030b00800c10300ea01901035400044d81e005030701940d4858081c238511480140c85598090868009030402007902c1800f05043c41c1c541010480c104803007200703080070041c411224117010324060400708024401c522500204017006424088180c0032119640090b803281410b01000c0c2c003070025501c00f040020420040030008503c0010424012074047d0084c01d041404c0150881e25680210700c204001916010b01c02c0b04003400b481b0b0606d900c0b641c554816100e0420b031040014130925540140341941c080b50018403441d00100403141100e004580c0001c0701c0c408250164007801c1000400340c2c0c070040214001c010300c40ca0381111220701c2c3c400d03403c3d2494850000b00c144a440c0e0a80115001601a007a2080b12051140700810840d20fa0002b030388040c00c0155299403518000d068000b0340300e91080713411200b01842c002c015410940481d10312480c0080520000c0d0b0720b41c2700400c0540000842004541e = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 994585710 1250 994584460 994584463
    0x1205070503160f050a060b0907030c17060103152d0f1403150f09100c0504061206080a030c150203070e1905030f030c0c030303040f03121107060603021c0b18 69
    0x2c4903c0c0d03010041d03d8043c02c0e1030802030005d041c8684064054601c0340000b8852a200344a6041d0a03002c5440d501800521411803260004004110605056865000600c0d008003400000700500c0007084880b404040e0200a440c0d0132803a03201c000340600c8004003409640c01a402d02e0041d50b48044080180c0344080300043d00c0e01851803809840c0d000c03068280419500712800480c0325202081c2120000c05170781d081c1c08110f4010300c12b03203400100b080c041030040d03134456030402010740c00303074000404c099448864050400c0d600100490200e00400720000800242150550b41c0c124070340002c5086140a42000d80210440410544291403043e04441e0301000c4001c1e4101928003d82100d15200c5210542c641d07a6000000744d500310b2080f1202c180d800d25000007120311880d4041e00c001941f03039650703034140c841402c550701401c8015180e02d000303001c241014018210704c1c2c4c000c5401185051560061207003500e042c1d084c107440e0212050841020540180a09811940031900e0a59041e24400f519 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 994586960 1250 994585710 994585733
    0xb040b1503220804141e01050c030708040e1b030921070c080d0917070608070207240801120f080a020c09090d020708030a0206010605090406120f120507050316 70
    0x100b400c2c0e032048801401e1090300030203401034490200b280c284900024003007000c824003442c0340403150010b0203081090365210b00c0192447c1030900c1c0c100ea0400d903d5a42d4903249811542221110504050404c48019092120802003518000e611461341c01d02520b825110700801240d01801002608903802c07103400c11040b079426a40210710f03003070503544501441e91a4414040e80100041d01e0304400300e211308210103400c1340000540001c1c908240b074428252000400103001009500810b50000f0341000400708001100f00041c000d03500120142d40040c14070401038212980c00780c072401c0350600161114143c5200c0c541c102c58406c0e100c003d007002c12071070b10a81800c42c54011384018140541100300248148210000750243c41c016070b11aa1f40070340e203004480440c0010780c848801007008070b019100400000c00c015001260a82c3c0ba411000d0381e0f500c44440841d015040c80c80c8010900108518811000c4150300d400d40ca000700720313100c03035607a03011f0000b0030074120754050203000801c281c81940 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 994588210 1250 994586960 994587001
    0x613080a03360b010f0e0402100c1e030206010e091b1c080403020a0630060e041505150a0506030901140c07030201181e020117190b040b1503 62
    0x50949015a40c07101040201882600f00e842942950010a1000b450441501501c00c102c0059125980b10780030024462042254842030004850250f00854180050803003401e184146160040386185402880c00346c050703020040f8016084140320781c910001c508002d816001d822a8100e031510080081e03485c5064601c00d000d40354100d0316482c108114074018000300c9008171500408156100d00541e0009210142101e1414288051460491448100050f64403c0d61070028855840b020307a652842c10503901510001c0c1c2001010203110618042c0c2a481683c05810320401d41d4460081343d541c00042c090188200404000034038045800d610a01c8610007281000d940e5080c841404a00c66000001c103a0040d401c0140e8080d0080204d1342140c07840390300c000c0e003003080e41c0c08290b603440821200d01c08904000b1000b404420f211150450309005900510b001c041c0071042c0c90242c4100c49040307244c940641d05080240e1065600c010360750307903100c1c84c2c107405503583d0340c40c01124008144034858 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 994589460 1250 994588210 994588271
    0xd11070509010339061b02060a1101020403050a0803090f01090c0b180301240806100e0402030309120304050109050901050a2105010c360302062a010506030613080a03 73
    0x44000d25050502c00180171605103031104c1100b000742035001c01141c06008000303504030320104500c81c0300c203128081c0e0110700c025150005050036100d540303503801c0100420003510010f00101c01c0c40382440c0144044084610302500820182066540300d40443e8054458051592404945030059814807100c00f403105500800812003458542404100703600c4652400d24281884030002c510003a0002d1500d009041c1301c4600d01815141c1903400c460000000d03c2240c15005c18840e603499500c030100e50340d10b69032190001d107440702d04000005001e0f0101d540030070303c1824604010825030315140b520000b40d9800140103103540d500080407480303004104a0090441d0700e000c00078800303140d0007040e020312409150070148402d20009140c0500035100c0c4001c050f50000d0780810001490f140c0010240c243e943e4005c8142e00300c03a091045195200c00c140301b045a51180100085454213102d0298030040241991009800c507031140150390085c0c0e6901000d040e52000b00084140c1c40c1c144031240500100f1 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 994590710 1250 994589460 994589543
    0x906190806040323030619030f030e040c03092f0303131a0324011202160c0e07081803040509070512090f2113080d110705090103 57
    0x5030325641c0c20044400781d0000d02400620b4406089240304a01030501c00b120341c03419a1a0141009100380b85503000d107002403410f0074004009240410300d400c4450094880c00d103400c80b460180000e42c0c4030b00781c50340c08051030700c49910006030f00440c29501e4841c902091054400071040d07110070380c0c40c40c42055580f500c00800d040481321900000c02c03050f04c121542e140c108011035100036040c0e001c165000514091403800024070300e10070500e01031003400145070001c0d1000a522031a02281d0065000700307030304406001c2c0c4106220b00c01030716030001c01400c1c80c031410390f04d404c207001400c100003d000c00141a6014072400c9201d070f810004c1e00d001e000c0c010410b40701800c0403403000d0842d901c0f40004ea0540c2803464001003460401068500943c540d40b005059082414018080a5010100044400c0c1418000c281003001c0d04207110000e040003000400d6003150b030342030141c51103240ea10755021a5000ca1410b10154076011215411680d00503011500e00010030030008015402100c01d1b01c0030154038 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 994591960 1250 994590710 994590719
    0x9162d170a0312060605030403080405120c21040501052d1201030519020604060e04020c011805061b090f0102010b040c0e011101050108030313150e060402091602060105090619 77
    0x410241e141d9031180e100c1c0c1c440c080c9202032403c1601c100313218034070116809100042c0480e000c0c0d001103511503ca10706503954400c0c0e80c01d26840540010300e00304001c0d40540d0032000e090041c1100c03c00044a1a41c900b820a0700d8800001d10310721400c404800402c0f54141e541401981d0000c5040c0180c03a0508600c2d10343c0d219540760341811809200954180c480c412900480041c1002e18110701600981821f1500d8100361090720040a0010b070b00303030000d60821034030610a00a10502c2102642170002010340c40301418600e103019405000402010108034801458654420840c1c020f030700e0a40704880c0181c2c110300181d00400c81101919046418903e00d00140f0350300141695104070240c84480d4114101071072582241c1c4240a611010b60042002c20f0b4904000320380ca21000e03100f1901c0594442d05c0b50050002c0d200c00c0c940c86620366000301c090104518095204d56031080e0b02101c03a41c3c0031141303503030000d660b0601803048500400080c070100303115480d04120003074200c1c0010250b030050307960f4 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 994593210 1250 994591960 994591963
    0x210a05120a0b130516030b031e06040b1b04050d0f06092d030516020f0a0306060f0b070203061611150a050a02160318090e01020309162d17 61
    0xe0b003680784100054505025140d80900c912030092081d001000b85104540700e094000303025002a055040c0f090b88030450041c01610380c0001080a00c502500c0c03141003503c0c10402c14000549070081401c980c15143d9085c0300504282c034100e4100f25681903c01140d8140070280903040000074100300d00b8101d501f4180a41c00e8018940081d0050120114003005c1c14401c0a04014400080001e04204010003400c000348481076507a9000404211403005800009602d00d60954000c96800c0d8407500104400b61583c000e1a004001d442825840c0c8111a4002901d400e00242401c0ca14442c0c0710348031400d50302c00c60300b04035071346009021121800074000d081d0699010440310001e58904020001c0c40006481c002e03101c4003002c24031250040d0001c0e07a03040c0c401019038002091601118000040da20540d8020209860031817000180c1d039007814403815083c030240395160303020706040301020080f00080841680040e000070b0b820385002c110405400b41d080140d03601c024841912500040450b140 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 994594460 1250 994593210 994593221
    0x120c03020903070f050a180605031608010b1005040b0c120414130b06032d10140102011103070e060c030309010606110d0507021c170d0e210a05120a 65
    0x1c00c800700c07028559595030442c0700390322500a454000f4000c2ea0f040040f565400d2014214680091012030000c4c0c4441c0401d142000c0481401d2480325800b400b001044801c0c0700e44942c0c403105440403007081780c80e0000540244140d03ca1241c3c0f4440020ba52040a98180500c441c0c0340008100135550301d43d903507400c1d464804c4040030644180c400c120004a040300c2841800f940110180529095076260322a07514001c211444403101a003817005110156403074240e901d8404d881c1c00c10300d0a000d03820030003001c120904420245041d6071400751440c203101d08003010b40703a01000603c2e002400d10580d20101da242d0240501501881c480403081c400201e006422000c1035411640c1d0b0b4440c2c01c1c84442c2503d60711000700e00c030140490707400c01c628000743c206540d812402080040c00f02480000907030302c0001180c0d075092640400000407568180c90016030003809140d10300704c80201074911140d046201c2aa100c10061006010001070a550150183c03081e01d4850040c1902c580691a05451220103441c = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 994595710 1250 994594460 994594477
    0x2010510050406080709020a0909050a050f06030307050c0f0d020d06061406041202040f0204121424010506070c031403041409011409040c090e1e060408030c0a120c0302 74
    0xc0800000c500c5080c2840b8080c101c0c0c14070802491214074001031107000394401d042d28800c0048039000070441c15168001c2901560581c0e42c0007031145404c00d2901a8503502802003403094104110340c0e40400c00000d0391b00c020010444402c40340c0c5000308001102400d10300002904440100102014480b950380b1010880d00d4079040022003213800800c112940c41140610310480d405501d01344050308069029400034031404400605d495100c1405007003184860f20200c40b540402c10b0204040c4c9400c1c498131b10000004000400c5822102c0d106c441c41c0803050007001c2c05440f0214032441400090010f100045400001e2400f01d420414081901c950090148194440d80340b4407036542c0b41045400300703040b240052800802e030400f460030445200c0c0080c1040d50300291426000c41c071940b0612404c02d0941030f050081030003046c0c0c0e0f10b072851f020001c0181030289401c981c2c2000040762a41c0c0c1266400840081301c41c1d03071004170394010745006680540c2c21085514142c00040e070f041d0103034000c0660340d = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 994596960 1250 994595710 994595731
    0x80d0e011b230301050d06020d270302151e15060c1606020a0b011205010e0607090303080603060405070b1c0501060c050105090601080c1302160308010512030a0c020d1b06020105 78
    0x10310110b03000b0400740300030b21131a500003d440b0700c104080b03402a4003034401d900d051403011a0885085000c4544410101500070140e4540901c01e002c2603010440b140210107283c10f2010f0300d140500103034495100c04e801d1013254000f46000500d4000c442c00141c0c0b1401d0004103403075190340b061181e50f41d0382d03500c1045100030781380c0a01c0041051400000c919036140d900c443c01040d103038240001c0000c80700e481d0300c0459466494400610750000b044c85541d1003900700d0756070800e043e1700d1810001e2113864080c000703e0080e004002848040350001c111841501d01c64445150b0302e80c2014004d0360420480b0520412413403030f080022964aa019038071490090155000303006688801c000603440340400c1c41403000d141d200c0d544e00103042c28140810b4400892843e03005041030a104201920718041020031000a5408030050140d480c00d00120722003461104011800d0896030b0b203000e0600c0c10b1300314029100341c4040d100d0b44201302ca004482d40c06203070351008050302250b4522029020f05415210311580 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 994598210 1250 994596960 994597007
    0x30910020309031b2b090f0b0d0c050d05040305042607051909020f0714070308120c0d09230d14070303141807060804080d0e011b 57
    0x29455009407400707008418003035803070319060108510f40801c401d4100400c5002d041051441030f44500141078452401108400311425005c80c001d0010341700d6000040044c000001c140b040443c150300703850b4140700d0b441001642441c410015907aa01071310302e1300c1c61f001d810b000400c800c051703003c400b03041143c594040601d010060308900344e030f64210b40e0440d0702c400d90110764200000d1070000c6810284e50243c00b160040d403070f25600050140d074000e18a214410200154103400c00c2040448401e0120441c1c0242c182c20382503036038105541c4030300d01c09403119a00740c4020490301181207080b40d405101a40c41002000c403d403501d4071980d0269105602c008108910307d013400c2901081d07035251a4200c2d5200c0b60601e001e00c02d0000140c0102e0019010182e4454040303072005403150825000f224400380003d54008140c240710b150800d290840f80c1046048414000017420401c180c620103220081c01140085a51418900401560880350844404107110042140d0050b242026842942d4000c011 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 994599460 1250 994598210 994598233
    0x304260307080a0f17060603070806120a0b040b011d0a050c0d1b12050702070902070f0609050a0b0c0a0f030b010c0519050c0406030b0415060b040b1c0e1207020310050c0309 76
    0x145ca03401100e00c103420400420002c0e00b99031184054951120b0010441001c1107001c48010346003c5810104481c401050011b2006021070404540e005100c4040d400d1044801c40e0002c20b1120300240003103881c2c54490021468007944c0782c080d070b0048003d80344208003406a0000c01007182e8851411400402d071825500205580c842c0220752141039141c00410529282401940003980203c0d419252030900714036500004000303004101c000b50290f0700800c1105910700b0310b000580306c05801c1ca640690204087c5858032340100001a000003d4100081c044500c2e200590b030002c92001d000300a40100c07982100c24842c1800302034419405041280c2025000030140b0041783e0103400064002102440010300040c40407141600d80c803101803012411559410a0404030780041d04414440d032001f140c581100800c07191656941a0608400c1c01524500100c1942707810000905081c80d00000812409545082200315146104158200401d15040300c4821032900f05841d109442c1c010164280c0 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 994600710 1250 994599460 994599497
    0xd090e16050301060c02010c1202010b10054015090b040e0109020f040e0109050601120b0d06270c0503060f1b0703092112020304260307080a0f 63
    0x3140c41805498292640e42040d40c00d591403180344c14124100020b41c1070000c00219096010145a1120340020034110308085c100041790050500420030000148420800300000d102c00c1011414501c0420803a4401e40030207041c00c0d04007031213030280c0c0c400710000011403032682807442d140c0b40225034070018034a4645a4002e40d034071440c0700708070300743c0032000c01481301c90703030643c000d108081d82074031154980f540c0c81030b54443e0240700741d201d800a5988c170300c20001d242d40c01159588091b0310800d01046000c20360800100e05000134540034200a5a4051001c0c85400144804001681850700003020b07000e50701d001045400207010780f42c020702400d00030800c0060101440c1d0b0042d18054080c451a004c40b25000d20303280c009610540401c00214400034010301c40e5613100c000d90046c8980d09103000090f09003000c182000c5410314085600c2080200421002d502c00c3d80c803078042400c074081e2100e081e05806880e40c01140009400340e072000850681058001c0600c80700e228a98031041204ac03280d08814 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 994601960 1250 994600710 994600741
    0x81e1315141f0f06030b0913120c2303090a080706080406090609230106051002030a050310051f0305012c07171e0906090304170703050d090e 62
    0x41c0150060480440d00342040920000e40030101d070104144596561616011807082d990711100201c0eaa80a0141444c1404040799a12150000e580c0c00754013290369070420007550040c0c0b4101000b807081540803c120100340c5401e0356803903c880c0d40d041040c9a5441035140e034056099540303d0314003060006048403010803070508840300350b1140101983c03107440f49005001d1a1310100d900e280c2d03035042000000c4070300585080d01c0c49402865011100170345400c5003100c2d881c0c0c008500c01c8400d4161040398503800012280450071a2614079260303240c100610310b4109036904100e90007450b100010070b40f42c41406904044046c20b40d4180151390740d50489000d8005c135a0100414501c030018280e52076100111325941000749460520440d910104000c4141441035411081c480ca4140c80085465a046081c03900700102b8406009181030100d400c2c1d941e4805c0f0b101d41e80c00780d407007007403201c29011082c4480b00c011900304040d0395542c02080b40041440686010fa07120764000300303010030034070003540320903 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 994603210 1250 994601960 994601981
    0xf0d0b210613020f01080c19050301082a0607020d17030f070c050309060c0f0a031d221104031202031b240a150906050925081e1315 58
    0x8038990301000ca0044030181b03401040f8840a0700c0c100500842d034000c000031034400400a0346c81540f41c0d41800560703030030040c4001320400d000c00303410040340303a03121001004400d019045601c140d403004284040344400c0011030010302021442a14040d0541c3c00c200210320a2480582458480d0780d030384003d907030700070314140094581d900a2001c2c90450070b00100510a10031004201c40c105190b901425182098414088000079515040c0da03040c200014584505160201d44000c0840169000c0300030003403200c018140017580301c5840020142201c1c003290051900001c0c0e01d942200c8482000c0e699601c5035180c10303440840c06408841520001c1200001801c1200340d08032024080000c040c601100684106000c0d603580700189442058940d0b2000180b101c0000841c0851408081000d0444028140100d100340d1002000307100304000a4076040018504242d0550b460b400b21882000903840c240d0411283c24205100e96012201c9800042d94810107a60000d607001c04c0740c900554450005 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 994604316 1106 994603210 994603219
    0x1802031905060702030f07021e031e0c0d05030703080402150a02100c110a0f061d0618160501080603030f03040c0e09030f0f0d0b21061302 61
    0x1e0594000540c1c0017a50070700c4448144035200b849078000082c41080104140710705000c221034600342140026040b606030a48402c0413090700c1c035200c40c0e130196a1240325290346182c42c0c00c0104145c1c40303a200340a541408111f0b50181c0700a9800303001281e004103004002e009060841014009494480c1d0040a0052891400c0001c03907103203060398400c0100c2001d08100d00000020b402c03040b2035220403030036118005030a19400070f040b80e00180014038882002c00100d1980000d04600552807c03025000c0b0792082c1c0b4101e907840e541480b403241c8654101e201044558042c180c1c042c2d21001c080d055078074148010850305410390089030100c0303400744e0b008402e0103009000b0300c402e64800c0c0c42800a51504001c0710302c00700c40c0d00400c035150010180004404181d03141980180941803000380a441400b90301c54048211280c001008542c24400c0b403000944c00c104940e1072504c4140c000c1c2 = true := by decide +kernel

theorem cover : BRFrame.Cov 994424460 994604316 := by
  have h0 := BRFrame.cov_init 994424460
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994424460 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994424460 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994424460 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994424460 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994424460 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994424460 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994424460 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994424460 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994424460 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994424460 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994424460 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994424460 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994424460 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994424460 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994424460 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994424460 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994424460 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994424460 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994424460 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994424460 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994424460 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994424460 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994424460 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994424460 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994424460 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994424460 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994424460 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994424460 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994424460 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994424460 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994424460 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994424460 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994424460 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994424460 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994424460 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994424460 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994424460 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994424460 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994424460 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994424460 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994424460 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994424460 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994424460 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994424460 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994424460 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994424460 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994424460 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994424460 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994424460 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994424460 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994424460 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994424460 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994424460 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994424460 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994424460 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994424460 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994424460 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994424460 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994424460 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994424460 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994424460 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994424460 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994424460 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994424460 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994424460 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994424460 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994424460 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994424460 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994424460 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994424460 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994424460 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994424460 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994424460 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994424460 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994424460 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994424460 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994424460 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994424460 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994424460 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994424460 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994424460 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994424460 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994424460 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994424460 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994424460 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994424460 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994424460 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994424460 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994424460 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994424460 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994424460 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994424460 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994424460 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994424460 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994424460 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994424460 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994424460 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994424460 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994424460 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994424460 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994424460 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994424460 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994424460 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994424460 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994424460 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994424460 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994424460 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994424460 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994424460 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994424460 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994424460 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994424460 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994424460 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994424460 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994424460 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994424460 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994424460 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994424460 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994424460 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994424460 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994424460 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994424460 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994424460 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994424460 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994424460 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994424460 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994424460 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994424460 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994424460 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994424460 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994424460 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994424460 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994424460 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994424460 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994424460 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994424460 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994424460 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994424460 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994424460 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994424460 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994424460 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994424460 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994424460 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994424460 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 994424460 ≤ n) (h2 : n < 994604316) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
