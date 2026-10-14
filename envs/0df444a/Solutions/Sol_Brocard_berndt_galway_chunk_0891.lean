-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0891
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T23:30:31.565401+00:00
-- url     : https://prove2.me/submissions/7739c32f-345b-4ff0-a9bb-6d5eea33d239

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 160071942 ≤ n < 160251798 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 160073192 1250 160071942 160072007
    0x1501030b0a09020d050c0301030312090212150403110d020717011401080c011403130b07050405120708060a020408100b0a120305090f0a14091306020408030406090504060302090403 79
    0x18000b89100c180c00741c3c990700c1209a031000da4800401d000f000742d00c24001040404e9002c00206813a058079840024021403c0c000300b80101e280c00e800684620030101c0814211800c5050648100d001c0d0380c0340c09848070060b81b03003911542c519245d0340c010fa0201300180005a19044006210f000c0c0314000100e044c0000002109400300741d20402d82504103a0881c803565070003411400c0d60000f0135098626601c2d10702401714521840e44406018101e0803c0020310080c0108200c9000d450014180c40302080b500c4c034115a56100d0340590883d500420011801c0178515000381c0c0c0a5440d000050040a42c2c0300083c0d1005040044040394811220b81c0c0c0003400c154001841c20f0b8550096442a50710800c81051043c1c1c42218080e02c1d00035400c1160410551003074075450046030341c0031500e501d0706454610800f60085040417000e0441c0344002000104184008000c204a9140740c580c02950707036868040000710385452201030b4025440c00d0010f00004e04c15040c2140d08800000380030501021581074 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 160074442 1250 160073192 160073209
    0x18050a0615050a030501060302031b03130b130201030e0d080115030603060c08090d080f01090906020702100c020102060138070b010807060e0609060403230a050601090609020901081501030b 83
    0x403004075500141c003180f103d42c1340c003809000d407005080551550a0046141d0f100c80780907198035540000c084089584a20040e91134440c040c5c0002c080b044504189104031307411040d821089001c2403901d40110002e000c0440e42d80010100c6440c0d2954684c60500c4080c843d8210780204020550784a8002c4005003613446207059007691995940c0142c54280340c0700d881d1038802e40714036050040b50000c0144041340010450f0540e1115600400c4071101031411030003a02a038100258406000e10480581700e5003d5032001d86d044c000d03401c0714610390780d900b5a04116222040789940d014580c12180002e60a036200078680400b0410509107400166100c3c51070001080e0482c44513030b0400c603010040168007000c080a104d00c101c440d68035040b6140c00180c010310852100824040c985815100c4c030700090045860b01601440943d440041e0358540340b600d405003409800790342e503c3c020000c54164100d01c04d9440500042c0c5400b080d47d22040d40c0c5030b50b0325604104190416844041621481e21408003 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 160075692 1250 160074442 160074479
    0x504050a08091503091b01030b330c06040308060904031d0d0204021809010501050901020304290406090503160602150414150a14060a03080f04050406030b0411010918050a06 76
    0x340c1041c1d01c404003401e03241c6c0e003600d01190402d802e2a84002c1d00d981c0d00000c03400031031003c0a038016a01d40801c070b5a041000b00e501c038040181408180071071f2080c80030410604c1940309070f65490311591404e0410009450650300900010308140805402070f00024041a003148018005903000c940c50340060280d900402103000441049844d4021604240c91194054070f000d0802505080584d00001c0d0380e40500c0c440d6282100c481d00000501603490034803044940c10071018140d0303441c0c48800c0071701940c2903403103058042d1003681901804080d03503501040a40f10340380e01074500c803c03400c0b0071900c00603400382082e180092a0405110403840401450400000c202500b480ca0b18180c070074903040358043c0310001000c14503501003041e00e030740f8121003c06403a809446c0a4907003492003030200303c45c092504a10341103807078814040f051080101d5520700c80c80c440c9540300303604060100111099000381c855004e241c8031442803071170140e010b07030880c0342c0c85084818005003056490142c010707503800880c03 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 160076942 1250 160075692 160075711
    0x204230a0c140c0a0201020c03030a02030f030c0c010903170106050f070605040201020f06100302010905030a05072d06030609180206031b090d0c050901080319050c0c13050108100504050a08091503 86
    0x9900130308558050145811114044000d50304084113640003070b40301d200b4400c00041f0003000100007900415410140c4081401d1400200040c0340b40d4600940b80c400252440d00c4140156800011032510640c2150381030b41d15030365001d0400201d582c400b0080d00d4064001c03030560059152980c0ea407502080006e20500c014114003602c9841d41c00003500311360450304042e02030b41140170f801c0c3c0030603400222401120f048940b83d0031005240b118032140a0004110b203144c403080e10364002441907241d0022000d4030034040d0100400c000e0303101e080d80192072001000390004014070000f00e0400c0410b4070310740126640c1c41142c4c6041e824100080900c0340610080741c04404032181404581040e44689000d005d60f50011403400d5131441c60f108040614070071140420100041c403051585040c0038903e503007840940070100c6117038401d52000c041d090902071500e07680302c2c03400c666150001c1c2e401518002c0da0001c000e01070b2080a510362043c258442a801d239082005000c400445e1200320004610900750013 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 160078192 1250 160076942 160076953
    0x50f1e07090b0627041a0619090308040305060105040614100305061206010905041101090f2c070f1d0604090f0b0d08070501060e1509100503010903020a0204230a0c140c 74
    0x348104400c46c0c2d4503100f00d04c91340d10704408548245d01c500d41100c120100b6007540c00f40c0c80e40c0c0d481084402c1007240d00010002c1700085400001c02c6000504507040c1d940807a4184980354031502a510032580400034a503202401c10072901c070550082e4005c4e40c22450140004192001c1010180d20340f50080c0d001008155844040200380841810035800d100000d10302602ea1901c0e00a0700800a1078038090a4020750740910012942014a0248100304000d03a1000d911071070300b40d0020300503a40090102e00420321880242c00b22000807006072066010003010242010305001c60f18009041c1c262100d007003640d50782c2d00701010341d403440d11280a140c82007500b5079852409180942c25295254012888800030109000c101501c0202c149809403080d0781d0348102c0d40d1140d02565a0b2509540030fa81c241d4a07049000d000d06a0102e20016054000d680903c200d070313555081c6120317403440c402100d42c5054100e40844c0103a00d00303802118440100b850005108600ca42171101c1c958400c00d101603c9900c070 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 160079442 1250 160078192 160078267
    0x1f0c11100e071a030a2003040803090c1002150612030d0b03010e07080a14010606080105040903030617071d010506041e0504020d05011e05060f0a030612050f1e07090b06 74
    0x40c1d01900c6c0351600703890400800c902c141c0c92001d0b11400054402400010084001031500008114680018100806074012400444006501e4841c81d040c81c85c0c1205608000810504000000c140d2600c0d10a008505e81000e0383c07115401080300c0c101080c0c0c10754841c0b102c15203a680c200048800307002044003030101e0120707130311f440442d12081241c0100e44d81d040038070030008107030001f05050454400b5103020030728200515003240100920b42006909200e01200510003000005113013040c4c891901102e071b8202007848416608070303000d02c038017644032030104402d06c00030801d4034071110300300b84101c86624840d0726240010181c0e003203d4403e1030a29aa44010403144982100d110039442015401030300f072506100202d41284143d5205880300c5100040a1150507c01e07441100240110981c0c0122508186020354980601a40380d44c068860058a000741d044400985141558020020f00020307243c210441d003d0400e81c00d08580c8444140310702c500c52103103910403401113110140c2400d42c2450 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 160080692 1250 160079442 160079461
    0x50c01020607020c091501030212010f150302091c02191e090209030c0f0f0306010806070801472d070f060f0e1f0c11100e071a03 57
    0x1004103441c00f15881028200901c3d15000c40f1140c12001002443c00e01e8508400164040d10540c020300710f80e5000c00c000010300710305131810344003030364500707281c1e680e0714070503010102c9c00da004644429500810342c00c3c0c0e041e500142032403150380083c40a0485420305441c048521100d072800d501c002154a4483d50b4207070103850406c2508003820000400b1410070350b040011a50f6403480e0f034080d030b014010f640800000c81d41c4828000c0701e1540020103c411541c0c4071031003d5200c2200b980c0080c0031034091400400d1203003000e4101481041500468400c1c2c45c0082102c0300072074690000040c030003c1a25034111180c610000919244405507e00306403516940c0c5d0309a4903148a51511011101c01d024100001e081e82b400e0005403134210303202281011400104000400194002400e20711800c480660703507001949502c00c409a9240d4208a41c00321600143d50ba1018480f41400715042050030a8056125502441c42d0080c500700310350b903807521401d5100c130890540c10340919440b8088100000d100 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 160081942 1250 160080692 160080703
    0xa0510020c030d02060601120507120906020c03071b080a031b03091208070201021c050901111024061d0607060e0303100305100c02030405130f02030a0606020d0c0507060c03110109050c0102 83
    0x1742c8c3c800410035464901c4000308100351000260742c02644611100e001c0c010150140e90316a010401525035845051600081241d43c3e844110041300c0440000603104030003044890f1440c1c2c050300c1d0485800991440203141c06c0300000c0c2201440103e03680810340031810080703c9000d500c9100c64590381d81c401c2c0006480e1003580000d103000e014040c00c2240f2115448400d8420030070007030928500c00070304405543e040030000c001c8980c2c228035000a00402d156001070021124400740880d030b45030754803400201c8080d87d00c2406401030007070b200c1a803110b80c02c000340244030b26800b450000407421406684e0905582c03058440056141d0065020f005210707041c03041c10035002200504200a00b11408042e484e40141c5c450544100e00004c10300c0038403038058010710994200004219940d02d00003c03018014001401460014800c1c416a0460340b801450804000d607003080042c0001442c0850484044102da4021030401584c4030b1580b150b01024060190300c5403007900500b0382d0b600c19000085c60807 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 160083192 1250 160081942 160081967
    0xf030302031e040c270c0e190b250210050318070e0403081801050406020703090501030c080610090302060c0609060c0f030118090f11011d0a0510020c030d02060601 72
    0x120150b0600001a80200b10303403086454a0101182c0300c09555000c4000e1036221444001413401d10004111040d480002c84080c100100d815000d08070942c03088000c2c3c50054003c4400004007041020100c01e41c480000c0c1d0f0706103407802500c030b0050407075000c110700c20198540c56003c01c0740802400301c46200081040c460710941c0d4003c0c14510f144c554915402c0c4405000541400840c1c004078412414107440d84500d006802c0c003e0205082ca40b510b14003c0d07121450640002e401c014000c216507102e40030304500c02c00c0c20b9850300d0440e05c5030403c10115908400300201800900100040182c4883c0083e0000e2003914001d4206407515180315800c000d4000c0c0070051040b03003007010001480403507081c1c9044d9007284000441414082d4a80b40083c1000480581216070f42003241082020030183c1c82d260000a07a1480d82c0080110030181144044002540c0d0168071b00b00c0a100a041c003940d00c13103801c50760703104032904590910046402c20151080840050304500200f042c5542c0025102101 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 160084442 1250 160083192 160083241
    0x91024080108030f030c0904020c070f0305060f06090403030f0e150a0b010c030f0c110a030b0406060e0c0405090406020d140901050f04031d130515030105060406120b130f03030203 79
    0x380704d0702c001000e0007484010003c45104001062191440c1c07540d034103035000c03c580d034800c0780c00050f1501c00380e92944113144400c48151007000002007035003036100d07049030144a000d03103001095141ea9800f034018094100187c03941956502e442d40c07203c3e20400c81101980280b5128a403036091481181c03042d030b0144140310781030003d03011901001a0303004222450010140c9040d100d1a5035500c0d02003440140e101d5055406500307800c02100f8022242e015038000c5104150402c4980d98900003007030b807141c04440c16484900280803c00035814819041c40d40544143e000600d00000680e85c00f0489001801011a00300d410041101310030703003407107003e0308400d1100784040d1518007660010400940181400e009510034800e4255680361080035400c0c001c4201030a000303510744246254030041c100c4513a540b00e1360920000c1815030600d4407800040d0b03800b1390350380d404a400c29104d034001e032000a4018983d036a44041da007000701f40c400c045941014403079600542e42e41441c01c0e1044072070589007000c009 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 160085692 1250 160084442 160084447
    0x30b190615031d030703080405071206051504090b0604020f04050306091c02030f0906161403090a0b070203100c05040b07050337030e0f07081c02070b03010509102408010803 76
    0x91500c40041607660885d41468041f0095031030b071400506158290340f04a41130710b044601e003400c04c00c0c41d4100600c611101504060440141c1c410041940c8096901400f0002400301240135030810303030020201002442c1019281594440c0413a2400004131079051694000a00841240c10461110107035410700d13100440c10019211031410a0b840f581002e244a031200103402c0e8607980d038101100010710f070004501d00c00035550351007958590b400664028403c20501c0780c04100f007800c0384c056560450b00500201640f41c2900c800b1001070680464500c00c4c0030060200041c8014002e00400866100d64051500e40038480c4076104495401d00318000414903d201220b00d00a502481d00c0004182e89004140901901685400c040380e14400f982c5174016a013010a05000008444000c004401064012201d01050403a291007286c0914003111804000401c01c41c0303484071001e90400503032070b07002225035503502e071000702c4100c00e0380c400b0345416083c4148840d49400007085401085081e01451 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 160086942 1250 160085692 160085741
    0x40218010b0a18050301090b09010606110a020d1e05030a0f050a0c0303050a1805010203010e060f090f09030d05180607020c030c06131703030f06010c0c030b19061503 73
    0x2012401200b14403001c208900c006101d0b210a8002030800a0001900800910040f03040043c1c0c4204101d41c1f4010540c2003010005e0f04c98030400706007040042900241401001a80c20071140440580c015181c40401e1281c500f10715101041c0010708a1140000359a1129941d201625a141c6030110400740030050004120700c64004204102295152400090310b50394120100001d080c0c081c1951200d0b07070514801d0041240560081d810b07606400801d00281c0d40341004c11a04030242000745400041c2c40007c80c1e40e00703000726141604400c05c1026a400c11240d0011070044803011036206c038014901100c400b0307031010140442c0ba04083d1074409000c0c0041c91101181e078800140006074000e10000072910841402c2c40c104201800003481e0354071483d06038040e000d59030780050340d01c1541405003002083c020f601801c080301176141e000d000000414515144c50b6085840105034008441d4403007220714186030248601c2028111a42c0b08074800e8201200050072504401e80c0d00022030007480004 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 160088192 1250 160086942 160086959
    0x302011503020a0e07200d09050303130e1b0d020921030a120b030f0703020a14030d030509100c0f11060c04050609150705070914100e07020f0f0604021801 68
    0x30f0703064030300c039030318606490701c8001c0d003103505803603d510a040c401440c29162201140101d143e0990100540d68044140e480e001090307100e103c0e10031a00d90401c407800e41000b5655203145c2a075804000e05980088102e507010b080031031940110020f110080c0e00142c40e0040d450460400c1c2e5460350340614082d5103181240d050755403482180340e40c1e81030003e252040b2031a01000d03007190800c1764003e01030300c480004640649907640b68500003248920807102d80800e0010030440300ca001000000c0052600b482ea266080c1d00400b8081c00c250342500807a07400f0340c090709080c001c10041c0020340c0d07511034150b070f010440101544405180342040350041c9041c0170380500e242040d075081c0d64089408954038244040040d060b4004040100c046440104206c01130100100e409000c546a07000709116000141a075201180c0040307605081d020025002401803401182026a005000e401100c1802c070380042018900740032014015029800b200030041142080c107524070100d15210907564040d41443c42d038 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 160089442 1250 160088192 160088209
    0x80403230a02040b04061a04060908030304031409151903110906041a0903121c0207050616050421020f04020909190f0501080c0a050109080304180f1107030201150302 73
    0xb070302c40d644481281005a5484d4042c1c4000c2c41d80c0d007017510b800049410b000700a90010301ca40400f0450300000003d903818088200c920940d8140e0b10000b1144030443c281425070031080780c16822095410a003000389084a005062641c02d4480c5d40304802c0140700e00a040d9a1800c4041c1c5041800380f00c40b0120382c503070310240c4d81a07544008105280c90b01d40c45101d8401d008000c10b0726410b108540c0814a5420101d0090154a80012020b01050035260440059100f10380005210f50b208000007150344040c0c0009032240551458100d142c25907a4408085020b00c41e038200b49201900c04a0004600d007010000140c4c010540702582091880c3c00083c140030001800c800e01d200e49010080d5000700d0f50b60000102841e105820000c3c1c1d6114426150783c1c2204180203030062030750480214266000f00000411542c0d0080210f1034103017402d8416100b40441d1151006283e02c030010000d004a82d401202001810407401d1501e810031424024290764800c0822940110b00990a10260301c5d413000 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 160090692 1250 160089442 160089463
    0x1011160b15060f0d15050a03030806040f0e0d03060e100308160b040f0b09060108070b07020d1403121612020a12060609050a0f0b0406030c050c03030408040323 70
    0x2903482166640812000c0190560244690b00200016007120308800d403a0107050510b454150401c40040c0200c558541c000903801030540c41180d440c01000080d00c90b58015510440161012030040c001c41c0011003510920076014001d030700903200041c81c099040c480e090043c00c030110401034508103904140040d244501000d00b15000004541606d4a1201041d6000320341c00340000815140600b00113910500100049543d1400b00e00801d06008000403230350305886801d000741c480c2d2480c0010440140d803102ca8121b802141c01005100032030304585028500c1000140510360b102d0840100d0008850000d20070110558410038602c40547d01200f049410040030034016a0751811510640e81c3c5c4d01a031200e900d045041c0000840d886031f1000200048420075124108003545a03c00c01585055a028802a80d04140300420000d0b12a8204200c200e400b4100140350618041400e4115841254140e1300d042c4001820420061030741c070202120030701c0c0b02441000f00b283e8955a42c40d03183c03110 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 160091942 1250 160090692 160090703
    0x6030b011b0813030812070e190510020705060c01020a180b070204020f07081b060709061706040212070207080c0103020c0a1401180b04110405010b0a0807120e101116 73
    0x20b80d00e00c0d4018500400f402441e00442c815440720701242450708061400c4840c9400100c25108007901c6040404404074500c000d6044a4031700c90514043c000b0b00505d41c00160110321408800186549481b0020b011041e8101c002580e204100300c0058111401d442d62603900a0360010100b2268202c901915103040c1e04440240ea00c0804545a482e5030142d02c4024100310400104031464030b000855220b51250b89030103480c0c01d542c4171a800d48610710540706110101c1c500318401c24000a100318219030041c8000c0c00141402200f1000c0013482c0012201940075a1000d0418040b22008010301e228100d000d01e019031620000c031850302d4446d40c420314000d00740788814584d644590000c0d000090000e268000908580809040001a0b00002c0d9400e9840c3e05c1c0c5040c0040290600e07009d8a4103a914084100d0700e0109a03880031115480c0041c0020100311801c8500b019000941c000c4040c00c0d40ca40300180314140c9400724002c11207072042c3c0440240c01c000c1000b0304112144030545080141c104 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 160093192 1250 160091942 160091947
    0x307060c050712030e060a050105060a050f0c01021902161406130503060702030d0513020105220302030109030905181b0c01020c162c06100c02030703050706030b011b08 74
    0x181025100c0d4015042c00810701c1c24a0740d8100e20090303141d0b12010070404075104a61b0b558a51003c40310841c0c80131f00038150048010044844818000c02c000c11386134030000310240c03510301040e5009003284c002c00507900c00040810700d0801410340c10888500003805e0b5100b960032507403501201485031070364025040d000308000f052003401c88490101c204000d000107401e641c80303498182802900c3c0c0d44440e044040707030351501000c942e0080b2041218140140d06031035091409010030700c0d24995245080006040f803a01003408401a20300303000d41041c031842601c900c40f0f41405c2c80e04100c04004d50b442c840c048042c03081d04100c1103c14040a0f11703000300c4090b0856941e00e40a2103614007a22400c8030022480c80b51041003e41c102c3c0d10140d150455851030000c541507170000c40071418403c8014050440c1c1e04484011035240c0c680f40000124041850a00301d40c050344560129041245590003900d0680050300104141509401808c42c2c01e00d0900e002c0000704601440210004a010006058214003 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 160094442 1250 160093192 160093211
    0x30c090302011d090c030603071706042406060504090b0306070e060f07060614010905010203070b071805090a0b030d030b090a020f040b1305040b040605010503150402041d010e1602030706 82
    0x680740c0408001d001d014510755142003e9aa441644147e4059029208621000500d811303030400c0d041e45c034921200600490788603a2100041c800d14154005103544207681201c0d41c540e205e104800080c001910340e191a20701d004c3c1ca1074200d49402000c9800783c4c0080d010000710960200c1600100c1104448503034403600b040a480e5481e0040b9070005149914018002c14010084003050080303840903070302c2040759600e0b080120f840b4080d5144c000d00c407003114408141e503540038012140c609889003104102441d500e200094800790280c03031465000da0395000043c094101448100c12082d0541801e00400c03e018000c100b613924000c0103011084d9010403002c14a16030001102c00800070102050341b209070358801248114401e21a081c03003070346060010711f45400c1901804e01142c105860352800c540d41c1d04640110404024290350b0b000780d08100c00706002081e00d00c030324454445ca0500da0071560420006100c3c241000d0018002180c02c1d8181c4060140e00008407040e850f4000d01c0032a83c0c2e1107 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 160095692 1250 160094442 160094477
    0xf02210f040f0f050a03020d0245010518070323010e0a05010b04140f060d0e060910110a050a020a0c09140a020c030f13080a060f0b0d170702010203090d06050402010f030c09030201 79
    0x110100f2400401210000c0d40520030b80c01202c0d1040390080ae0040e5a50f66a210200481c910351724007101c400c0484400080c000c9400395100401d2030b02c0d4004544126040380c1846035801009801500007043c40c10700f80302c0e00d404a441828003404079188010300c0c1904103058400380305003030186a48104900340754140551507481c261864000921014041c019041d02c20540750803048410810324402c0c4460742080185038042c00328000b0300054041d00d000b1000d10304403850b501402c00300c0c0c01d602c55050104000742101c0c00490080c008010b002940001000a80c6624903018215105540c0148440c60f4004004801c0b902ca042160060319900e5444150400d22a102a07005452902941e0120303801c0c04102d07042000c40708042c180800140c07402d80200700500804400142c43d0b2007035108044d41030580c0000500d0314500500440781000494000076031000b10520702103610130b80702d03c14002107580009078100880c0301814103200203501960001c0c8103e60078400a410010380e00c407510700041 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 160096942 1250 160095692 160095739
    0xe0f1204090f060e010906080d0c020a05090405011e020d0b01030209090601030509160608070f0c0b0106050c01060506030a0b2403061509040f0501150f02210f040f0f050a03020d02 79
    0x4c45030004007503940f15a00c1c802000710341f15040040c080c014150316110310461802c0301c0700742d0060802003030364100f1090140b02c500043c4111500d650382d0045003409003004484d010240d480640140e034030240d0b442501c01b962a100f4181d814075006021103e41030b5200b043e0b1543c070840c03e10b4000360f03030b03602c41ca1180c6c0f4007102d102d0141039005a2200100314268010070f554811308064907042c90700b0504400484445824000c081c10441e001c8005000c181d101d440100090104a40013040c601c0c1c80e140040e0a5600940341d02da07185545d24007103d000d0415408040c1c0d850324203d0300702900c240c06d1140303031014800208454410040034510112032100c0320240c2c2c6e6141c0004d8820052002e0648240d0b000f04400e020b6030030f42c0c40402c102d0460861040006074080d0342242d000d072400707541c1c045542d11107410300b2101c0100038405101e14074020301900c01410091807072424941c4064a400243c05d5041e41035001680948845507090000da1103596003002ca0550584914459400070b640c2480c019 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 160098192 1250 160096942 160096949
    0x1b050c0607032606040b1e0904030207080d11070605090307120203010212040311100c050f1b0a12030b060f090d150e0109110d0c050108040c0e0a0e0f1204090f06 71
    0x103510400101151880d108a591013400103031010040c41c8040c60030003d4000c560301a1070b42c018203c819485150420540268100b80329004582140d40c81d0314840e420103060305403540005410aa4110b4120001c01c08a0014001c0381001490150200040703074540c030b20fa0044030740304002008484115103095044400941507141c030a84d0074101031800904080207403941040520840c0e400c2c500f646034a12814140d90101d4864078a4141049c0114415803c00000451803000d41e00954a8a80050004120751072042c1031040010301120b030042d044a00c200000c074020113051110300381145080040f1a0b8580c421140015060f0b5140707400003004031806010349c01d50b03051044a1640a205401018809208100e6a40980c400f0350520405c0100c100000d072020021120420203540100b900b43c0e080340c0117500210a10f9110800c4055519054801c00c0c000f070781d201281488605c06000c030303071565031050025000b042c215030507055150007540501c000e01552081d0b8040280ba00380c0c80030008 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 160099442 1250 160098192 160098227
    0xc0216050315070507120c03170f150d050304030b0f070201050601020a080c030c010c0207090e190609020a030b0f040b010e0405070627140f010503010b040603020904090f121b050c060703 82
    0x6c09441e510003c0c03403642100000c038003194000454200d440c040043d4607203d2544486d84002d00c0d651041c650341501d01200381e01d50881d140600e0400030807001c2c8020009140100740b00d07095400c0849003501040c130020490f0086900d05030501c0540c1c2e83c0032030b00da400150050b00d0780e600c4188e81f0011a0540c0300d060716002d219803070546d40d40c1178903401041c2c0104942c03201d41c00f0420319035588050303616000c6180010380c150000010000025480740e0100a10314000341895583c00c4c0c40303a40b0b491300b8a406075110f0700203500344c10411040251042045000d80248507070390701e403420140d60f0195520f500b4040c450510a004420110701821004c500360248000b040e6903200e90340e13440030a11401d480b401c0765400f440d09010620140d5009000304ca04035010a030300c0901d0300d460410300314002e4200982e880d500039141ca161102058404403e005601d019840304105480c1074803000d001c11f0300d104185141a140140c160000c03c034041250480a20b003910202d0740c40c2c2d501d1904403251441c0d540001103 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 160100692 1250 160099442 160099463
    0xe0105091e07021606030c0c0813030b010303090e01090b0d02011d030307030306150f09030b040201020307061103060907030c0c02010c1403030108060a0606090311040b0d02060d0c0216050315070507 87
    0xa607140d0000c0c000703042c0c404c1e0018025034580c540000f102514121458003010844071144400011703041070040041860251102c03001ca40c880e614110180303c01e0b40300303400090300441c090043e0303070001c01050300400301c01c03108002004218001c22000c030a54500a810702160b81030301507100b048083c00c030018078401419039a4849051401400601d80d50058280b02c08090410980b854024030036901000c0b01034448000c000e1035580e5651030018010403c07411800305124450004015028403050790480c0b00102c0e0716071900509004440600400310030815040804021445402008008ed04d44c1c085c64481c0750b1128504060031005034900b85481a848004000520985c011800e94003030b0100c1c01c01800350369642c801c21100c2020f5804040c2031100c00149081c4245010340c0803c2031040007600c168501c1000e0340004090760010550582c0c10384c0c445400903021503051020141001f500e90a42d881c203410000400c0d916410600c008a00c01614404074529034000d0b01541c0c5841c0d4410246003 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 160101942 1250 160100692 160100701
    0x110a090e0105090604110904030e06040b0424140703021908070302061609090c1b0b1506030c0723010906060509070305071205060d021e01180e0105091e 67
    0x900900110040c18829441c140215840210105040d8051900031020048010301141002180362000d0421028800400d103010419100c0c0380241c401800c94000707032511140f510382ca1030300e83c0c00b00d107410181114a103804021401d0700007144900d10200100d180351201c2135490309034581151001c0c20182484045038000811441100500d03030350303209600380c50183e108c0f0700003600400090024600841c4121005209840041e03000000c0383c42c1070b05e002810380d0000c03c041403603c0200c001c2652040c42403030400000240681102c003d103841900d8861441c83c0101190550740105000140051540c200e084040f40404005000e460980c0008100c80e0800d8501507005180300c0c03103094003d114010005a50358000d216681c45140c82e07464110156800c206014000c12000b005940e10404184e43c3c1001358070b0304d8480e1a00a500324200e00c07003900500002500080030a40e000c0c44a6a500c142030060141d5100c6050444906035400c1000341c545100c1040306011140192048410440420 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 160103192 1250 160101942 160101959
    0x4020301090902180103030f030c03060b1207020607090305120703020309120102040303030614010507020d020109080f06090106080d020d030b130e030702100914060f040b1b0f0303010e0109020304110a 88
    0x410180308484c4a54128030002481c0d030344c074a0910000c1c0c0813980f0202c41e50007042c0a81c0010702c034910b2502d000070b1400c2d1103c041108a0b00201c038640585100d000400c09200c1d010024150808140c0c202642098070356a030351036440c51030080580000c076000c45c4000815000300182c0c0c81a98000742400103002807901e40d14000e4200b81b1064000a0803d0000640000c2d094000d0b101c2881c10394805140c241e007038091140b81400914220304001030000001070031101400206981000c00c00a0029810100c1e0041d09450392a0032441150b04111013800040f600041c00002c2c443c80f50601250301010030000988440c5000b030350180480c20504001120203001c00140720b581c0c4201c4222482c1d0ba03a010080340c1c1b1042d00c0c0191840300a80c1c0e804400c40380f9101d000340809008400450f440c0c070743c440001100d660000300f4256078081200008400503001880704034500081d00004505540c50584483c40810042c8a00440654008081014011070281524807240c015000200c031b55500d0060 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 160104442 1250 160103192 160103201
    0xe0c09151e0c0c0d0f1b030204051e090c1f0507050a08091309022209050307030c170708090108071e0905040e3d18021018230402030109 60
    0x600c900f03004840582d00a840c02882c0741d214503400c00700070301c001e0712141d440001c6842040c855408010030004c0010059a03203006403442012000303c4000c580c51201075100851001416214075500800040b000d01e07180c00300300b61100c0410096010135020005800d0383e41e0b22445c080580140140c03190541070004000c0240605030301650754a680d039400e00042412245c0c002d40095028a0101242e0b62001114070700d03450b1400c58104c0010583c1c819a1218030310b03440302c20b0443c0400c00506c0c400080c002005100721550122070466450000b8980d1803084a01c100910281030012034808201ea140c8602078050f000303c032107401c0310118100400007900b18102031040034403d50a00d0745070419884c000c184101500c2d0304142c06d060381c4503000c00700c120000c1ca400d8456005010107840540c112070a000d43c10b101c0002d0941c2004d991003070300502c004000241c01c00c100340540a40030a001030504290801100d44007011000341c2c007001c0580d1541d003880a085103a001d40003000105144e00c0c2c80c1d00 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 160105692 1250 160104442 160104457
    0x103150b031e0a0216060509030f0409060302010e1e010c03050405030105041a07020309060d0b0609060406080105091003032001111218160e0901021b01020a0201060e0c09151e 77
    0x1010010b42d520240c090090b4429280c1c20001e1a0103a10380c2e00003d481a004190401020f1060301e04104440702c050000f0b422070303401400c1068407401d0410070342d60885402050a00d007521202070404000c80311110001c00e183c221810005e5806400c420305114400380c0c3d000d420020000e1055040c00d0034010804420440b1020400340010040b0700054000411582c1c1d800010b0308240c00d084d18440400000c0c111500381c41c0d089901089041050303039880c8010405002c054407640c2032541440c0500582000007007080820000850042c0003007504440d01850f900b441c5010155103a501c43c02590240441e100065444000482d00c621040401c17801244141164030300e02000c00c003050300203981c0d00100c00c0540c03c0c845242c1800e0002c5003119a107180c0c810310f110700240c602903c0728141030711b10340d00e2680311101ea50b0105400c14500e6080c01104010f10705001000400d0820781c0e010960381c03140120980c0700340b00d5480341c03014038a0680140c0300034040f04500c0540540400001e2034843c0d00039070 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 160106942 1250 160105692 160105741
    0x103110a02011d0d090b0f0403053306210a06060f0302030c0a24030605220f0501060801091d0114090601080316060f0e0d0e040606050403050604020103150b03 70
    0x80c40025104000554990801001d17619180110300c0c00301d0624190340304243c000d01241c410040400451801c0084003d250001840704191764010200040041d0608031200c0854804c40244001555080584041ca8a58005c1f0500c140d9032026002c0c9425044070000f080f542c00c084000910018086451046a0090301920311720041d12080000310340450203503400240c44500c3c0d2440c0300084c00310b640b06440c46810001002ca46076030005442118143c00b444804050071610468003250b07002d9401c403060f0a00b07080c0929410040e01414a80e0140500182c1c2641c5022070716500c029030f005040c250038254003c210581d0700348140941c08200301d580303920f613101340d80000524030000011607101c4000d200e461004900f05550302c002030401c44084103010341c0c60ba00d0b940415181442250320804d095220600703118040000c0c802902c500d54088003d11000340410004540c011601c2d951240c0e09280c002f031031098904900d8400312164001d80c90800010007042080c0d0324441d84d0094411340c00 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 160108192 1250 160106942 160106981
    0x4060311100201111207020a15050105100c03080118090b04080406020609070e0c0a051908010f06090605030606030a1b0201090c05040e030720040c02010f0f05040201050f090103110a0201 82
    0x400702030b801d8403c088031030010ba14080100003801400490036940203906032050322003c16482d110500c0390b10903503100301103560b0303200c0041210f0729000c03026910084640c104900440110389024005c00f80500c80c08100c00c458030107441c109241035102500c8151300c224000700c81e04150510740882d1f041801154050300c65540800c202150010345031080303c26000c2c000c94203a49101481a290700001440703014403500b44546d2441078031414880c815002c43c0d68030046998941119000d0b1244203a0040040c0a4074050620a1070780c0a41142da02c000180e98a82e56510b030807003848024858126403203607140c000d21008140030740c1134100c074509a0003008900905629030040100f112000300c3d054032607601c100400000140c0309540c11104a01c008418480e0203192000314064917844131041c00142d55400780c020b841c8034503218070710400350908000c0100b0b00e043d50000e4154401d611ba2030344d41900128440d009684290400344d005d03107841c80580e460f00f41c0504040d000c0c0c910780c00340c1440e40096 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 160109442 1250 160108192 160108219
    0x31c05040f0902070f060903020309120c24160f05031c0515090402010c14061005010306150509130f09030309020f01021c050703030b03120301030314070818040b04060311 75
    0x140261100b95400608602c40b043c5d40b41da80714002c105502d01101540400c2c0b0124606070365a02d802002d41d19800c0c040c01284c41d040c03081188402090104243c100e1401003c003074031681903003c1e00d03010b400804134140b50401c41d0901100282d000203004006200014503020384900604020175601141101403055484001020b03074994a00601541c1215103a030005002d907116000766420640600c240810009070002e000b81000c5040782c0851a2588542040005503131500c1918020203c451038180c0c03000104400408903c59060faa520482e1094041070714400305500c90309810800c1081001010318a00d000b5014154071401640b08203941c0c03168000359400490054000042c6403052042e07142c0d490001c2e41c05400c900300607010907a542c120359529407010404007a5040e100640c07682c49600d103240041020044100d00380d810002440b440000032540000c0d074003151460001d0201442c460070200340244507803003116900909044000091101300e0203d804d1000007500d221254141 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 160110692 1250 160109442 160109459
    0x10906020a200606010e0f15030714030933090601060f030203040b010603020c03040e0f060f18040b072706030c020d09050f0a0509070512180604060506031c05040f 72
    0x2c40314000b040c0d4222000041c0301d0342c418000b1030311900004011021450405001c610721068003160020840c0b400414480c00e103030072803d20012400100585440c41ca80f1000b107a0322014401a0044a9a0b0302d0700341407004083c07803c0380000c4541801c1000e1340b6141c22801039554078400c7c41504081440d01c00e030b07942c0052182c000c80344610b0300070340300c090642d18080048000354420019840303180010701c40444c2c9942c802c2030442c042c18400800803507906005040103c20100d04a802c0d10450044201c0c0c2c0a4524100415500c00d400c0706c5588465501c82c8400d64902c011440140c02ca840840920004c2c0310b0408a00010354619075820883c0355005103099944080d04852071022400900c41040705142c0f45545141c00000174001a05490b41e401c045145020240e5004000c14070203d020f442d06034920901c20f511003030040d00c2c00b00710980a4080743d2a01c0c400b5201602c07058442001981c1610104000140c0c08a0400c09840c40010000002c00d02c2d00103000e1210301540110300000c460f10b = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 160111942 1250 160110692 160110737
    0x110603040305030f040302031309062c160c2301050a050108100e010209180f060418020108090a0b01120b0105040c0509060307141204121707030902060c010906020a 72
    0xd074152035041c41c64031258401c0041160091040301140b00c00c1090090fa84030441810000700642c0902081940c00c101040b00300c44117840100724036200b0305106108020b4041840307504001e40200c1c5180c0082018000c03039050b80101e2000d0481040a40201d010410404001d28103a83c080300070411030300c414503860240c820131321603840c0903808095003401c1c000300c5600111404142c0d10005142104001c0896007504c1800403c41c0086604003c21240f4500c110205d68061000c0301c042080304140101c940c00c00342d40101c040c0c108901d4070009056038004201c070040c0c1641100c1034101c01d60390f4400c019590a8000c4045078901420f000005007420180204500702005481e12030804c071030744007440300513040140402d003009058203031000310700c0d181002000b51448041080c0500c0c505421b101c00b09094401010041214115000c40074681110086811510515005c1075400940c00000c0c1c040c0140111000c280d403038424144208041035000b015480380544880d084064030303041000101 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 160113192 1250 160111942 160111951
    0x50d0b0315150406030510051b040f030f060b0d050f07080f191a010914060303031003080a030f02030c070b090304030822170d03110405031e01021c09110603 69
    0x311110008100807515802c207201c10000058000503c07540c1d2903c07810314045032252840022030f542d8051159081107016030441901c00580324624003840d100032030030b080c0c2203440060500c00d40000c50b001000b515803c00d40e47d0310740040140310f0b06000d0b030602e2515098881244e8040d4440d80b10001480180820300e01012a404000b0b071007206200c46240184400c4200112141505141960b444202c1182094080c150382200041c12501312300481c000b082019040350b1003980144100401d9590607075000e4286d0b54440f69083d03c03550881402c8d0702030300c3d000020900c0700740084200080101c1002c060034019000380c03000d01d407a4aa03040020f41b248907a01000d05006000c02220f888600240091011401a08460b0424680d00c100444480d140d140e00b14142d900441202c03c40380b941409030401d00d16501d517205252924110000e55103807010700d40c840880c02c405050203481102136040d201d40095240c242440c2c070711001284070013041e401c0c40880d40c420510411003403a0a0403400d0700e118 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 160114442 1250 160113192 160113223
    0x50f0a0f0306020703090510170c0f0a0c03021204062304030305030a020313021f090501030605100c0f0f1505090c100e152d16030f1707050d0b03 64
    0x10314196212100694070488003036040c0720218a0002d156107821035160040100c81c3c0d200980890b170b08a50160301480a000700d00c040e03000b40043c0e92007200003001c0360b01c084150b0401030300b504214a0164101090316041494036180071030002840354020307280100d040b10707040d6180404410f03e0086040e40c01079000260004009000140000b41e80364000d5030018a0007101c1000011190300285000a040281d00c01200f61010240075003604205442c0141009007810301c802400c00b4081800d9041c101b01d24010010004a0f0a00340406c4903030b02303601e4580101c02c00450b10050305090510594500c0b80007502460600052a000c10100c0e4050f036803035000740040d274040c4250008a450708150890365501400b59041140e61040c030b84000c100d0700044034a80d00e50f074040400b1007400c0054911100002c0c807c104613040d4105140f542e01c05c4029418181a0380c40503d0318000c07030f50588110803556240740010103008441d90001d02400603a05c0288080c4400004072040c1070321000000a15080f = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 160115692 1250 160114442 160114469
    0xa02010e011103041a090a0c0b070212060402010f030c090504020a032307140c150a0b10020c03071a0409140109050c0712030f090f0f210f03050a0605030f010501050f0a 74
    0x385072040342071700c1d50403041c100101c42c02441e0685401030007110f1548008a983c600142c1c10b81141403c8164a1110392580003900845c6055000648425991500c4804043da2008035004e03441c00b502c1d688000c0c0c0405002113443e5580f50f40e02034000c19140f540052440860f844403801254080c82c928801e02d01036485822051543c02c000075190080031543c9854007074074050001e140c1c1c28502c000d2045590703503000314412220f00284420131042c1203d25045411170f401d03415190b20700003625011a640c08001d000f40c4030200c4032840290195421441c1034904020040d20011b01d2650158141e03041d03404101324588035046482030600ca5080c005110701a00000d10101501030351040794600e4050300040740786501655a0042100a45011560000c04441c254140300c0074903100705c0e180807400e03040e030031040d88160042c02d42e040b05a26107042588501c0020800c5401d0f41010b0010580a8101e40d0307008084c85400e400b0304009d00541d0b024000c2031419188900d4000701050031100c50002809 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 160116942 1250 160115692 160115723
    0x406031103011a181305010e0105040605060306090402030106080a060504060614100f200a05151e150604061707031b0e040207120c0b0603010504120f0908030a02010e01110304 77
    0x40e40c41d01300041010903519402c4145103d40c5980075262212140d1050025441d070520014410080701038010721b001d10f10b843d009000030f44804040300c0c0c001e00201ca90b061940e41d0707403000a0160065400c001424000c091040b4204503090b08174500941c03041e802031004540b24180388036415491031015510a0111b206c89903083d018804441b2002c80e50302c2c0c822030020240d80201c2800510101c4540c103580071000e510280f0805015005200f40416104001810111030002c80403402140400c1c0d1840401c1c00b05040c154098141c00c800c080160905031210313598070340901080094120041004000c40010b4141072080c4502e44045c1320300a421207400d4442541114500041e0b040d20360010350800410b000b00d0114000c90400120682d0b4841008031503180c00211030001518440c0284c0c1004103009c0090251242c0c04148940d601d41a40c103401d00590403103241c14103a02884480c0070010b244144143d040d04422902d069860091041c10719000d940851440200ca001d03015101c40401c1c00d = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 160118192 1250 160116942 160116989
    0x30311070b0c0a1502070c031403070f1101030c02210a0c15021903110d18020a0311181012140105090c01120905060402010e010c0f0503040603110301 66
    0x110085510011251410380324101d40c1200d41c00700345100d1050b44000818010030085101000154402007000c0d820044d15a40e03178100c40d06540001814000740d1600400c00310420025107034502e80103000c007040010f403800c00001076040944820300213410100400000c5000007030361503043d003031001c0b0320213020301d0f0820b02035560700000550b004000e803a80c82c030008141c0e0404007400503008010010390722100c0003003002da520007412003c014103003407294095100c1448010790b101c2c400c1d02c000c081990a4407400c100c2007900fa0901c000d602c0a4205000b2050062081010f241d078103054406a0a25080c401100d5041e502281d001ca400c420002e414441040040350341d81c1c0a520541403101c030390908030210340c207545013100c2c514202d5201072010072040da03114100401150450714200003400781901d40b0f5448440040002e810700c2102c003800b40c80c5034428142c01210b960480340b06255500a0700c0c01588a41c4184034074000a810040440c40002a0324103da049400c0c5151203ea0b1003089850b8 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 160119442 1250 160118192 160118207
    0xc01020d0e040b0d050601090c0903030f0c06091406090f01110702150c030703020105070f090e0708190c030227180406110309100c030209030703060f180f0302060601030b09010303 79
    0x205500a40c40f004103022a48904080180c03017486940544015810204131404803640c0888400c10010011400c0002c250405048110400d06150210001601d41001c031301900f50074100910981050381140d10750500454900e000300140c10580e00b041602903003950980f144003094060105042050400602d4011641d4020316030b1090a68180310f01d4a820302c0c11904203050540140c2d45903420400300590151180c1617200c004c2c202803031903e0820500001004004040000340804a40072600c50f020b50320a03043c0068100c84c0500c04001906401400780d080014416110004038014603103a444160302018510000ba2000c0804c001e8615000c03503400c40600142c8a00d95201807014100fa03440c0c00641c0700e1521407000307165010341440044112500c081450041600c1409900d00760b903804100101240d0300564003103001d40c1c04c00506002408a04503050002009100741001c218201c01c0c03088416009400743ca009a650900540c00d0300c0c200040d143c0d21110071001400041d000b4001d = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 160120692 1250 160119442 160119467
    0x906020120091206040807060501060203040b0d020c010605031905060a02160215070b0709081510060309111003230903040312020a0c03030806030d110705061606020301090f0605030c01020d 83
    0x3c03040000d16400710700360070600151000d82c5e084200050030001e00049018941c01445584002e40c0b402c2e140840c0d4261600507901a95400307900003c1908000340250000000f8120085c141d8000d4400c107003c00d5240000d54808907000e0003910001081c2d07040c14402d40d04444842650060030311400d90070407514400c2c01d51041100002441070b407010071440390300c05120782c00c281c9400e0991400d040d22986480d11002422442105480800c19404c0501028500b100e40600f03002c504144030f89011500c2c95249000c10382c01803046403c4000b42d992680024109503800c0282000c02203e056241201500444e03e810032035204110030000118240001581e20b0314500c140d9203021490760b90340000f00696442030300054001c5c0103000e070a24081c030500040c5405814001d110655070b01246807905600c1c0f1955110303900108121100000040c0b4086084d98032040455170303507031910400401000340b460b0b0640100e280c030101192500f0002a101c9921905800400101101c401c8c225000d0200b0130 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 160121942 1250 160120692 160120699
    0x60807031b09020f0301051206090c0f060c011103060906060a020d1803080d24050d0f05070e09060405100c05120a0e01020c0c18060105030c131a0703090602012009 72
    0x140454152000d044c1e0407000b01e00c041d0341d9500d80020040805065070301003403130703420003418403510040004080f0050f15041d600e849080007120f000800ca030040c4083d0b0343c155403c16036108400c1c1c4400004500c594030840e6144207580300c620500a031402101008005a40400c0c8948140d500600c8107840d0003608000040c003480d143d035904249904086075000301661a6060404c03148450203c6801040c0100c081501c7d10303203032600042ca0880c1c84540503049281c4440c1410074884103028510203804200800090760500180340c3da0307182c90856040e601402054500211407800307000c1d0001c18440b60740c800d4285102030040c082030003c0a40750b0401d2640c0d5407000308a2030028005010003820840c040c000a8181c0c01c140f00201382c4903415150788406c044204002a82c008080d0b94010058100d03081c0c07102d0701c0b10b00e9240d59141e560018860118103042d551042d40021004108e458469900c00c000703199600000c0c0c5c26074120401140c00c20590400350307562081000003038a20100e004 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 160123192 1250 160121942 160121993
    0x70e2802040f06031407110d0806040e010507080f060603041a15090901020a0815010f050a030f060f031406071b020a0905040305041d06010f110a0b16020f0106080703 73
    0x12648040b0054155024001198440f03c0c0100c035400342c404071590281e0241461001c01158510140d01d50200a181c24140705104001c0385441c1c4441e8484501428450300030480ca040421016100140460700b100d03104644400180c454244841a0b9000d0390f8851030490404104c40241c2d120504000e1110202001500f50b00d2499035940d08500e000382d008100041c0c2d039001090000f000280001c1443c440342000441019044c0d030300072221712000000d0302c3c2c0700342c40e840030101c210064090305409000d07003418070b5400700f0002914404201242c0c4a000e1401840d241144425103811040702e64202050300c18002e40312480040300d0882e06523100400250707100380c690309600308840d4162010f40005001207028041e881070611141030780d0490032030302401441d140300001d1002940e400c10404118005210301d548d0300c42040110321040d8490303078104043c83c00c0e21100a0780922403162900510071108806001071040c802c01e404d60f502034007e03091072400c4d5213030864081e02c0da005080d10813541 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 160124442 1250 160123192 160123199
    0x40224090d0809100f0e03011a040203040f0b090705010e04141605070503040e0109061e050d0f050a06050406060f1404020c0312070c050c0f0616060209060d060305070e280204 77
    0x10421000004c21040c0c84540780680300040c01880700610811240c0260314000054a030f1000048031420000c40458003d0382c0e0b541e81d4a442d819140c5502001064180c1c901b051040111300407806400b41d034000e0741c80502c0060100c040100703807800b82c050100c2002c41d402c00700b28080301d82c00c0f03035000c10001c3d07041080c0f512550743c0d10145036902a0b80120b00c04001d100050000c040ca038080e0b40c00800d024000e5103041a03070500e802c0103000310b03846020310400301104500304100f4400c16640e501a086170940c1c2907a181030070100041c0c0360843d021180ca034a002008034075880380100d040305139407400c000e2003480c2c9401014040254040c5100410350b102c00c0c0040507c0341503842302a445800c0340d9480c1516001c8500d052490004505200e51050410158088254641070103807403000403011a8070544a415090820003403190710700780798110200042124903031480342c0050007100c3c031420032550040c0d5100d480086600013035603103560001d4a90ba41ca178401030320040b1417101d00b022000052400341e4 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 160125692 1250 160124442 160124449
    0xa020d0504140103201b0709110a2604030e0f091611011407050408010c0516080d0906020a0e0a0b04030503090d03020c090112030305090f1c0302070f0506040224090d0809 75
    0x501b03c8401c80c113a01440815141c1c4081c400b01c001030884110078440ca240c1048010490702070b2008885c00c0003a48110715502590030102c42c0841503140342d4015039410300d8100104400c0048243c240070300300059002e0701314144914560b106600300e2409480c2122080421903564a145164a596640300d40c180c1460702840714059000d240d45407200703075803285440c3c0031500b50307035421a01e141408000e001003250000b501c0d041c26141d66209401725135031071208403501c0082c04845400341455101040d01da107000c1c0c010b0301c030100854040b15940c48070759444880d003569114501004210380c00030320120006080219280820354441d00554283d8650000828265442644000b400d0840d60031210141509131203095042141040503100e0407418091a0b0b030794000604a2a01e100b0482d02e80c2003845100b0b5058528140e40080c070040c403000a030410550f55001510207a01c0f034110240a040502c0050540c2c400209051410506180c4003404100c1103105012098900d0340703040003a42650756 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 160126942 1250 160125692 160125697
    0xf04060c02031b01020601060e1306090e010b03030705030403140f0a0305090a060807171b160b010b0304241803090806100b04030b060a1a0a020d050414010320 70
    0x214954400d45001401c0c01090701d08110b41c48064400b441900100d00c1d9a40d010550a0540c0c03c1401c0080d01c0c041d038000405d20302110150341c14011481c020020030041c03801d4015003951243c0c54005d1201c00c0c1c0a00400d600c038810704600074080c0e4020402040011556050130050503240e0081e10b498004103940542440c801940031000075a00190307990b090700d4000c008001400281c50880d50500d89020080c0802442500080d0040100340016000070302503c407a10101c60450300c1141c0305d946040c0b221403048900d05013228981c000c40300128139101ca450070359104a801c4004100c41403020040d02201e500e200f6400819603480d501400c405240381d02072890200d1181d507494041c0703031400016030f04110000d081c980301002c141c1303810001182050155400c4c1ea8010380040615110900011046a4a0b61250b662811162201404001030b840a0182d050b482e800743d650034103076040d044503180309501070081600c1010017250702d2940300b68420805050005401d4140c88c041407144103036034 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 160128192 1250 160126942 160126949
    0x31c0e0d050406090e0f0604051504230a110304080f040518100608011202040b0a05090c0a090e0103031b0201020a080c0304080f06040b0711071e1412100b04020f04 72
    0x28000140030405650700070100c1c130080c0090f03801e09a10f81401c9145081010014201c13034851511480840c0802d40c2644103808085002041001102c035100340d00e5200c000d120110146030902000019520041806580c900c415080300e082d2640d502d40d50b0709441508504054020300105100209250b12140c5104540c02851807040e00c481c07804000380d58421403242c001c401003000420042003401030405a129403154103e8011448110301c04c0440c180300840d40c085c41d80000707c0c10a20040c07008590041c4076900c1150b5928281d00d07281d075110140b9072028840100043c46130280c4800d100418983c41c0c0c0c0d95481441500c141e010640c0b84e01500350060382410145030800a810400c00108001d503520900007000601401d2410f0380354090400001880e000602500385440c08101d1018070180000d4480c03951155403c42890480071601000350050010300c1078880310301d0348903107400100062540b0848004140c00d0848048500242040c042c41d150040c2d028000f106c0c01c01c80309805003014 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 160129442 1250 160128192 160128197
    0x1e0c0e010f0504150303051c020f030406020901090602010b01090b030a0f0c0519180b03070504120507030b0c071203020c0703020a090b01091d040206090d02060a080603120c031c0e0d 80
    0x1440d0520b030801080721040c0c2e0002584002c4201c0400c0080d4020302a03c80800d403540540010804c514401c03000703445040c004001d610000810441045141d42c0034090b460b000ba41c840505a071607120a070b08031280843d81c80d000c42d030304150420078000b03900d0007142c2c03000f2143c401180c01e0b42c40c40c0c0d6610a0720503940c81000415408158400e00201c800000306003220a0325141502150212440b060135482d4010620001700000001d60300c00d009c5c1081350010b1556414108415406041194540c52240022150b0541903400305091702d5403202a5401c50750401714520f040c15001605a00a6204600340d840c64001e0400000159450540b5940100994400403e918031484001090090320781c0090100d003d684400049419a2030070650740a907058603c60b0f600d450203800200c40a210b51402940640002516945141d0103e109801440141e00716001c80c000041030b590301d802980c00001c0d441e40b050188501441d4650859144803210030b000050f1110b10b0a0554140094240f02d00007 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 160130692 1250 160129442 160129469
    0x20613090e0a1b051302130503030a21140f0a110d0905010501120302030703030e0709021b070602030a02101d01090804080f010b09070f09150c06050606071e0c0e01 72
    0xa00c0f0300100004032000b8150500400c040c2402c0005090030418041c04151039804204140c04200c0b140082c80502401801c4039202d8007820790081841803150500601c0c602da60b0000704d040c0107a80140c0da00100312018032602c0d95030340e800d00c1100100040440c0915625031006d84100c81d072820082048070052000421061501c1c14894259070044e40b0201a07042c1c64046900440d5000c01032341c50310360381440c02090780b0b01003605448c60010f154000c003080038800100d0407600402075520458501441017511083d55840201343d84070301078284c1c0d980240c0c0000080c0398a61382298003240b16048090581b5108108002c400303821180305000c1100c01207000101070001c1c420412404020790126002407080401c014085000854090203400601100303504c003108050199182c00080d100b5010ba21004c0616020000c00720300c00840c041d507100d0310300343c00710b0b807982840c004541c03800e0f41020304000b400074040301a000c1010310722070a40b2800e410b40e00104000002483c1e4030300901c002082e499 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 160131942 1250 160130692 160130713
    0xb0106030b0f09060d020622170f0111041206020705010c020304051207030201020a03050306040f090b07030605010c0f0215070c0f0e070804050c01080604020702060c01270807020613090e 82
    0x442c8402c40e5000903c03075101a001c01c0003540d1030b90000c42c81710b0307410358107261600184c8540c1104070076441d100782e05450b51020701041d88252624805900000d0b6402c0710320005141801c00d080f104650114a196282000107001c0105203540014005210307000052900300140c44441c21214150003400050700000b6042040b440d15010020358216003070040d04402d0302d150f0002c0d5482d2140071000b020701c580440012582d41e05c50b40300000c4117400c842c00707024441305c0f4070341490010b0040f50000302180ca0a88041270380d5204e5460043c229602000600c4410095000c00035950080c03e03080c502d00504100e08400100c50140c801e004007404084541202e017011f00e840f00e25100201410100b0039070f0340401020540004540724100003e00300001d903070b10340c01c001c10060701c901c01c40a500081c001400070943c032815445030303126141c0c240a0a440b400c0044004005141400d0046d21202c0248880809440c2c0300d0010001c008205d8074041040d0794030000c01054400070f0310076a405030440122103 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 160133192 1250 160131942 160131949
    0x180c04110405091b0702010c0c12050718090c030206030a0b1801080c0d0b1b190503090f0106061710090606020a0b06060301080a030c021503010b040602070e011203110a0b0106030b 79
    0x2c90304000c0200e90004c000035481041201802445d4000c0d04100300d15682100b400740908182c405085110300c0850682c00c1802d0030b42d41c6400c18030486816219561035810801e03820300c104c00c2910340c0220115881803a40c1c081020f1a00040c201400c0c0f1703a41d0b80c14500c4507a6509a9a842400c89030607003280d0b035031500c41d885080100030241a800b0700b88007072854000880400ca0107034130240e07151690b0212005402c400e5801d016030503400c03040c0c0e40c12160740c03903103103400c18040c510603da140c0c1118044410000410300762100d40c880c1c01c0209165100001000c4220144180d00c27005111071014a00c0d074410707110040e80c405612100150301320380705c4032060100c01c030f00b01603200a042e507007035156504d000d140e00d13500e819480c0050200101105800115510804000f030305d110340d01101916540c503581002c4250f481480303010094880e408000484104c2500c249040380c203541c0343c4000040c05501d0948070f5040803e40c000c0c9602581090500203800821468040c000b01d41e40019008200e0080c03 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 160134442 1250 160133192 160133209
    0xd03060e0f0c03071e0201090b16140c121b1902030c04020708071a0f070207081506010e1315080a15240b03100914180c04110405 57
    0x6001505050070081901c920050711030b009000920702aa990381c640d542142c00f1a0090340d1003606245a40038181c0865054225511690155800c10004c0e00c80d0091102c007141c00e0844403000c0b4100c0050019005640c00242050000345420303150340c030344c90000c010344a6112230761640408a0426041c41c0c0b094081202c2c44640098401650240d92560002540c035800c1403081c0c2e100d07940000f9110100b0a8840a5801d0560300091a03062107036615000f04940c40200c0e190781710401c01c0030003d244c03248000303011011100c0042c0601110b01c11030080e5600d0980c002c12050510013a9032440c459030307c2c1c10003c072400c10030700500000c0511000300c00700400300c52a40400810740c010f075840130100b0540701e42141c0950b40d2a000088080f032200c08400c120f007a01100c5449529807020029040c1c01c0311004500c203100243e801501d95071541c50190031070b20300b40c03642004402c180000030004a50751203880040d8030701c1001c032288280218005000d0f07031143e05003241c45402c0410100181e050010300c = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 160135692 1250 160134442 160134449
    0x170c1e0a0327050a0b060310020f03040501141e1b07030305010609150e1c08030705040302031603031e090b0408011e020307020a0f150204060c1b06020d03090501060e07020d0306 78
    0x10300c500511243d869140d035a03500d0300d00c042c08075003005001c146144c0c0c0c2003000440114054005544502c80361840b005a50022a010b55542d400d010000c9200100700c411035100c0d8400042d030b00c4c62041c80c4a56a0300c940c1d00106808038100008249a039014048800b50408601c43e41d40401caa6041c84001010004242d000e424810000c8500c40192a00500150385110003a50950400c5c200d080c1d000451000704070000d000b5510002c14868229031100040007560f00990072540341b40410460494049036610001d000078060881c1160380b240401d0000d61980184c1c50228006508d03105080031940c425070150000e6036584c2a6015480c0d6018050300b40c20070300301011401d514002c600a07484d00c60040000f45101d02c0709081e582000100f1683c005034038041d4400715115600c0e45006480b1151039001130f44e590119646800c0000141c1070340c4420b0b150039502074850b041c41c0740d02c15006840c1e5058210f0f469500c8400c0483c20b071310919502c6102d0300da1540180300d206101040907044851940 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 160136942 1250 160135692 160135751
    0x30e0303061003020d0b0402040807090b0a0e060f01020f07060201090212070b0a140d0504030c110307030503040915080a0c0608100e040f05030c0109150c170c1e0a03 73
    0x10800403259100c41c840c0c42c003180e480c02c0269035400803c103040c004281500d02d0300e0307202e132000c07401003000d41e000103c0000369180c141f400c00540c10102c0070450305151900c200f240900c1410300254036410b0190344c0365965281801151402003140c1c00d00c0741801f825411090040c1c1d07482d0305d86425450000c2e80980300c02ca14030098040182009190030461082c040400180804c10415a145803005800c07503140d404070140800140c1850b190040824030b61520a0300e041d12154071071080d51030045031103811240d010340110314052074600c5200151107944511808034602c2d14001507080428010071040a108a61b0b201181d400d0a402802007040034001f0350010003010300510402c21101d03140c64026801400030b4940da401454072074554450001c04e40c8595007040400740400a00e01070000d03031000080018880407007040c1080b034152100d0107441a032120b991021400005101005108090041c03144002d80c0d0440c0c4020102c40d4842c0034506c0001e595401c0e01e107103000c0100e4440c220a41c415 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 160138192 1250 160136942 160136947
    0x90d063b10050f06040e0a06090c050909031810050912010b04110301060c08030a09150606020d050702030a171e03070201060911070311100e070f1509030f0204021b0102030601030e03 80
    0xf0b038090100c5100040003203000e0359958100e181444410040403441c294000418030882e000c40c604100309841501c01d45016042318004140b0303414001c410340f82d4401e003120341480c0c0c1221003020800425035007140c85040c054104000246600c1c2d0154540c00c1c200740340004100c140044081c08112120242d00c00c0c00c07040b0500051220301c3e804400c034481c031900324a00a8581e00c80d0f0700000020b0000250061882030b4403500354000100580140c0200c49654003603943d19036a502d0151640c1c49560002581600160120800190600703034a0404035090346403242000c1150781182c00b415040c501d451340c644004402c0101c0c0d1507090103504040c10070210140608110b102c158901c902494100070113201c2501d5405251007820040211030b00c000b070f203041c071500d0001c0041c03540b40c100d18041c0310000200084007040b10300c0e11710342260302108141e0f61412121303e103459291b007003000400304982c85034017040407144581d44040e0000c2034a01c11000180d403400c25034000b40c00c07140f00f00003004140d0001d = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 160139442 1250 160138192 160138201
    0x22240f081b090403030509010b04060608060901080f030909190c1d030a03120f0f0614010201140108030406140d11030f10060f0f0e151b03090d063b1005 67
    0xc8654050f0001c0d4942400300c0c3e0342d10341246031409059080410b50700145440000100c250740700710751070300440342510003941990b01c4940164032043e0222446003d580304001d4003201d1b050292880e42d2022141101c04107115032521614160fa039003240e0200000c0000c00701c2111455001051141d0500c00c60050021004030b59024245500e000c0600800c01c1c1d40300203ea12042c95900302c40b062034200f40c820000c030b54031510451b851030040e0611034015844c0500710306030380c40c070b12002d541aa8623010045003083c1c030300344084400c8c45031aa1160100c1c5428809103107000b038240158107800400c4c0b2442e075220310b0f02c400d05c00e46030345c4000e041c0360f1480d00000c020000250080c0a00c0481d52091401d960b074094101401e0314000300c0c80307101d5034101701e41d50002104020100013400706280040381d407c180d0480340c1d01030780c2e980c010041480d50144043d219140094003d9001d1192424629082025420408141018108080c1c01280340d000c00440c10210a0b2052000c2d5600300070b010020002400d1 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 160140692 1250 160139442 160139449
    0x9050d060c09150905040c0309020a032004020414060708041a042c0403080606040807120605060a060806130b10021606170f0a021b010e0c22240f081b 66
    0x1144105d500580d40e4200b0021598807940010040760340103003505a600e907407403a2a80220102c640b1901c043d800704c0c0380407405d91034540210340494900801c0c0d00203440311401008003e9106660072181c410007044000b48013509104040740203038078144520707240c610303000781042d15903010301040791b00d098440003000e420710b01c0307103c40c50300180c05103000d01035030780c07942c000c24024882d940001400d480b41c0c040000f0542c0c1020000c04106201d0b40050001780c486505005900680e40141d00c0400d540d170340010f099040143c0021260714542c200460240c10800108442520320701c00d40c8010b801542086120641060a202c000e0081c2d00d0441d40703a0544607000740038800c0c050105121281c40c08045201c800154060b00e680c80d6503c42c220b01e8440e0450007440c0202450034000107180681070309070402c1c0c605803a000503200f100c0c04240508003146424440108102e00c000d246680e00c400903a144149407a01d1480a84103c400d40120981041081d074a040c00c004040b80c8010580542c8a42c10340b03 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 160141942 1250 160140692 160140707
    0xc12020109060504210201030b12071403010c09140f1806030d0809030409021e27030309010507030c05120c01060602010f02030c1c180c06030f0b030304060c0309050d060c0915 77
    0x100c42d184c41718569190b10040b00038041100b007955010540d0340a02030007010120f01c4004944030f0020a00701c80ba810024103081c1c5151070321040c0420301c1a02c0400c900c1000301241a00c25500511443e00c2d1254400011105c20641c9814200540341c5800c22a5909040094002942c418100030846107080c110490b91380c07095000341c40c21581c01141c848501c2d4080455031b02d40c480d100d40c1c070f1500c1c0c11464800300d2029011074000d2541c41c840b600c4020326420048116501d45078180c0d241031130000f20751016100500103031403c0724a03104452070501c00d90300c1360001d8076442410500100780c0d1841c1441c02401d5900c0282d448092920400c103111005013408103d0300001c0356002090514200020150018003070541c807401e0082d0418003440800842040f0710040d15001c1e01d0400c10403c000151204403070b81251415015030040000340070305e0707002e01e00a85010b446450005c159540f214045008a480308000710740300b9840b0341e0412601d80d0418031410281c100c0e401485243d5440f0100200303201c = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 160143192 1250 160141942 160141979
    0x52401060f020106030b090303040c0603020316030203180105070f0201141302100909091203060b07020f040518010906150803340f140c04020c0a020f010c0c12020109060504 76
    0x100740e000311071003003900039002100195017008070540c1e070349001a001e940b20390040303070111403440103a503020a04601070700c2030302d000e101e810581d41c0300480d14200541c021f600242c12104810071507d006150303240709004192117011217648250b1041c040f0000642500d0000303040307025500000080014032a1189109040350350116400c2044808030a01507522503900d4200740c0d121410490400144180115155a41002982c0030001241d1720080980540074400c8021b5018030620580c2d4601d20b40b680009030040c0c25103600801d480c0c0c01000c002d003141d5508030101d500a4803034aa9892440b0b101c0c0700d1900400700740c0050b44c0392485800081200061003441e851032040e00c000d01820602000070045e00ca2a03012029807141c0307210781002500b10b6148540c6044c0d80c807074404142d04605150007980c0342000164011300e041c500a60170011005044001581005044190040407401004d80d10300141805907a184803c1c05034000109099071380d800c05001c0c06070170441000001e04265144040 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 160144442 1250 160143192 160143197
    0x1051e0606040308120a020c07141008071209020402091c02030c09070c060c14040602150612070b0729010e0c09062205100f030b0406031106030a0207080301030b010305240106 77
    0xd682e06c00c480000280139803c0c00320254440d540d0040380442c481680c10286681c00c0300d09104080e59500200c60690003128003c3c0055801100c105507030380c450700700060311403000f000035090641d0003002ca81000b03130609070030390701848000036a070039814240075203001d442013550503000c64a0001d2003d040020f29560040c41d0941d039400c203014052151440e0722048207444030060303650355200d500075a980940c0d44441030400424001c50020f182c000350402d8050314240c0584405072800001100380e810048040da10a200146051a402c8410042c5044170700543c640c8440e40d41000d06505170b205000b0720103407040e0303020414810242d5508050b00c1e180300b440b40b0f820410ba940c02042e00e444810720b60080790030007016424000995000300c03080c80032071003540d010441c00c084d010400042d1242403001070b1a400045050061a0400d1801554051648100540b41401d1640d450f180d5920990059900d0502600144100300d0144000b040e4440100120080e482c80b03581c03820302510f01803155005 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 160145692 1250 160144442 160144477
    0x603021c0f0b010311180631051e0906040803060f040b100e0319170313050a050c04060b03160f110601240f0909110c01051e0606040308 60
    0xc010710300810780a91940100030003a1941d581c50310034501c0c0000c0764001d1141625520700f406140041e50041e01c5800020039070303042011402004081134445c1950464a81c034a01c00c04903458080f4000c582c099000c041040380a81c074422018602e007040940400c0c099000700c0240408918002c0a482d0401070890b5010050345045002034001d003240706040d0307041640d1041416146402c0f0005424801c015030a81d0b01849030309100b03500c00e480c01d10b401459281a0f030f580f41d20300c2c45024051907102e924081e000084020907100d60b450501428012203855000340044045420940503c0c0000c0035080c04880c21030a05140b01034142c3d000ca0424001c00c08440750f840c42c81340c410440e075034158034000c081d84c00079611030780b52030a100300c40c40c071100d85406000700010b00e182c426030040070004006c0d5100c00000342407000b0a409040d6101c4d904008401c207000800b400e403400c1c0310fa64011841e100e0381544980510702c0ca90124100117000c1c40c41284207010400200701200c084558160070401d0846 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 160146942 1250 160145692 160145749
    0xc031801050412060501050319380f010306061211040b04021c061d0601020303040b07020a08030f0f071103070605040c03080c030d0b0301090c0509070201201309060302 74
    0x1d44030b000b40c0e80305603050365603140e4980500032a94861030588030103a0a55500355000104480d41d89070500c0c0040c007081e503200011007a01103ca40005610507002040002910720360340a10502c0c40c00d407545610484c07110b004201300704d81e03842660001c00b0900210203c4d940952195080c41c100504881c1c0030729240c000c5a142c990342d50703044460802d41040c90480280c0001e80c1030700102102d000b00340c103000f164402c1a040928200b111480340c46c2c143d00461859032161354002200304050002001d43c4107400b459000208094080c510404529420000302c4c5010a0b101481c4940501a98140465a403c41000361400300403241c07841d07040040072036161500d01d0210040301b00d80d480600040004520301003013400100003451061b44a40c018400c020303000082500302c4010602c000c1c0300b03800c9440c0820881c28240c2c58190300c0b450500000480ca1a041445032000c1101c0c0d440c019103800001e406201d4a12000c090400740900b02010043d85045601280c2120490360a10400e90403001050 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 160148192 1250 160146942 160146947
    0x90905040c0b030106050d050f06061b0102090d030c031701151409060f0301031a0c070308040303020702030f061905191503060603060b0f040c08150a0302041103061002030c031801 79
    0x81c0200300000d22107a4940c1d44440080c1141c0240300b14040c070343c2c100000308104500c02d02c515802002c000309201d00d80015019041007044400300c0c403810a540a1000f0891503450444155415011341c42d04004603032940340051610701c1202c0c0003907400b4a40d03401401081308920407030340c10540500b00b402d2800300412800701e42c1c2c092100c1c0168801c9000598280c030341d001d00065170403a48148003017280d071280d140c45152005d1040381d054090020034403003580071a02c2031076041c1d04a4002c1c2401031030030380d0a802082c10001c05000b9142c1d99031080d02844a08410030680425050f009107042001d401c0c41503000c1407400820703150305221601e403c44103548070381c5000004011070b400007080045554900d8100e020b8012034441512800b45805180a039040c01c7c001d0080e00d031155560510580d84441c07264103100311365040305400c00000034011005881e1841040903a140ca252919283e00e044010451980d81406040003103400c244680104208000145d0b44003441d40c180c2c090052039200c004 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 160149442 1250 160148192 160148213
    0x903021c1403240d11010e040f15030201110307020d12090f0e01060f030606050702040c120914011d06190f0507050901030c0f050708070c0506040e0f0f060109090504 73
    0x208582000010700c10900c00788580b030704501030050045010314980ca02003103c0e100b56480050400381c85003205d07554642c420000f4030000d500c0200009004034101c074490080301d010003901d03012001c040f0001e2043d0b40e004031030118101c080304001c1d45060240c0e8042818018100c03001400c008050180d144981e000b9154440030f0101c60524100c210358400d01071801c02022320541d0007148404000b000c5071880f80c01806c0a03115191580d51414165500780001040044880d100b08002201d510408007082c0c010642118001c072a03c1d004050308004080c00c480410110340041c0341c2c884036002d191000403a403164084140d644241d0440c50145805c8040c11401c010a03100b645800c04105940d03410002509119500703a0302003082c0a00740c01d056400d14000310b4444041f980c180140350024080c0300c010f115162141c0001c88802d541c6001251f06608160094500c117240c000400529850516580780c0c030403211a507420580c01d0680000e40807080e0b80c004c02e058261900c0004060100c09031b603 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 160150692 1250 160149442 160149467
    0x70203030906120103031b0209040b190c03061404050f070c03020a0209101503060f0513090503030708190204030c0e09010e0a080903011104050901090207020111030d0203040c0602010903021c 84
    0x10203070f9502c81010200c440b040240001c0340070941140e03074010342807029003007621030aa0103404000a07803580e07145c2010b01c0c24010300e64100d941002c0c030750b02c0b800409c500860107030058688001c10701c541000d0506554802440700c09004038070f02402c100d00007403c0e00c0401d4102d031460070901000c48180c20101d003440c40c81391000c4d4104080e8014080319001c440d2070303038045070300c10701da1060b041d2806a0120141e501e94414072083c0d05440308244400d1802038100014160307900d070001000e9045030303180c3c2d040d03400c101d86100c0411002001c01151040d4201500d0082980801c11450503003161769842c40400f050290310303000005c040025649036001d52004024056004c2201e5204125103418175840c4e20140c0554040d5082941514a9504010684090b22802400b124451782000d4100b0003e400c540401d904005107008189541e0f5000d00c001c286c0141100b03400b507901e01d424100034a110b59194003001c1160724113040c041c08298003180d0074610840024a010400b80c51200c00c50306031460b0b60 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 160151942 1250 160150692 160150699
    0x61201030521070b0403030c02070e180601120c0603091403031602010b01020a031d0301091e0303200702120705040609020304060c090305030a081e0405010b040b0301021305060702030309 82
    0x10008024004001424a00c1c1d41e0b112034112100388110280e44490301501c0c034001c00c213141980120300020f010b500885c0c03155200388110b4040b60707038541d2490814078091341c0100400e2141008907100312010321826002d000c1c10b040c1c2480a1039650b494105112180c03282404240d40c42901004022894112000c10120f48003100c0e280c0c108038985070005040321102d0b20242d8a4100007a2681d4008942e800005805407a0000c890800d00800500c090421420b02c3c1c0c19583d5020340d00000b10401c0002c4007000300305500b40c072041c5240c0340c017500b02c0d10703086185180c00c02320300da0800c170900c00d00e0708840b04c065044d00d100205203004003085190004541045500c01e0800c240800c10112942c080c5200d43d0090405104004041c030045c2e449451500002d886c0c0d400810200050300e009034505078119080300350151124030003c23400401ca4405480450302d59440d04010f800c503113801d024014941400310021440e003d00b0300000c100c5180c0a1080b60f01504003c2186d405560302030080c0d450303400d0040e = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 160153192 1250 160151942 160151977
    0xb0d150510030213051504120f0605010e0f0f1611100203011401180503030306060f0730020c062b05040602090307060302030f06040b031f06180b100305040206 70
    0x40310090080c0d0007141d0000c40308680740780001901d00c6c0880400c04c5d10112038400901c5e00b030920842e5000038050920903903100c2e08001407200050070a200c0e090003040b407100540081c2c144004424145c11000d824058060344031801d01449030900f0103c00c031130b140c560402c40444240c0070072103130403c0d0301c0300340e45095940701000006510ba0b0740c0c40340d4103a040c0309980340c12610261242c403e0072481e0b18090290560310910010b541414440020030200e41d540e412541420195a40d081d0ba0070840001c0c1407509152900000603c85030780c000c12419607030783c00035000e48041d0901160150003080400007150709081000640d42c80400d4400f21401c030216001e1001e89414180384010394051781d0f807207002e07204000c1c0003c0d03528441d10a0300c0c000c410342039040070300e510340e4010880613200201105170b140c0030303020301d00e0100440703643c000401440401001c2401403501c1203107114802c2c440a0714126034206207180c21143d8403048940000079103424006a251194008680180a48802001c440c07480 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 160154442 1250 160153192 160153219
    0x501030602040515040815130807030c020103050601030b010c02010503130803011223030d111603030e0c0a0609050d11030607050d050c0421110d06020903070b040b0d1505 75
    0x2650000c00540f801514144a0101c00c1001c1c0482403080e0b104000c075541211546200018541403032a812a0b0312407080d88050109407160a1194403900003280456820341c414421543c050140d40d520107024201040740064034800600f64031301c4a240281080f000100054550088105051043e074014000e2501d070741e12001d10a402600c2c0d07010560303c640d15424195071760a40c620401002c861100c01950070000d040104001400c031021a008040d282800783c845851442c11042022502950b004103e15502660180c1030a000c01e440724010324084005018441d00301107107604540040d58107201c0d000341c0b030400c8074021894240e41649801104280301707071154043c001d4140100d82200410080e140c11048107604c1c4a10b204032440c24a001c0303400064041c004880c192024022050114416106400120844070110b411194036034040350380b01d0b0900341040200060f0440a4006290030305000f07030040c0c01c1c0100c0c1c0440d401c1d6519402e00682c0b0500b02c0000100070300740500120702c24180e = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 160155692 1250 160154442 160154453
    0x31c0e0d090f0b0301080d05070c0302120a0308150f091906030b092a100201110d1406060a0c1e0b04030c060513030e120a0c080604050717030d09110301050103 70
    0x107407240020002c00c164000c10320944102c116412161003400401200688070420f80b03440d0050702041d10880194140003003d0b0701c8280041915902400182101d25041d00e4041e0401e84060714681d020601c032880c408407070b12140c040d0480702200329105001540c488528042c000080d06e28011039605292000080200c1ca48603d80901142030070f480341100308403d01000901440c4802007200c0307203448640b0303c0d4100b0502d980c102d07004030b200114183d030030190100c1d02903003e03410080c1b4070780d610030801c094010804003094102108130f405a1502d05801cbc001807520782180030181a000078040200760980b1542c00030001c00d079200b81190351a10785420043c056803440d41d0140c4213681000005840e00002c4400a0706440d13068894400c84031004080c484020151152420b141c8148409407000c41d0320100543d00602c2d03d41c00810040c60145081810300c03280d070307020050815485c40802d0801002106803400c01d4010113001440c807160f4144080805280c0b00001d4042d4a86000807080c8030707 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 160156942 1250 160155692 160155707
    0x307180b0a1e0f020a082a0c030d02030903060a020f0c0607020a0210030c080f07110105011e0807030c030609020604030b1305060105060c100b0103020f0d050126031c0e0d 75
    0x1c0030190300320200800d000180c0303142000340c07507840040e007140800c0400070302021b0107840d07100e06405103400000c0d545030681c80c044144140380300142d40110341990941c0b40402c00024941c080344007031418a0003170408203a440da40500030038a2181c0200ea1000090554001c1e903061107803040484a0f40e040c52040a9260001100107034080c5020310316070617410b8040d0003400501d04465a504400c1c1d9142680b400388504003610003020002d0701d00308034640c030341c1c24007542e80a000608280700c00031046010649007002c139075010310002d400480040000c201308061800840f80c1110000c5014074191002900511840d00010700307030000182805101c590b51031455100700d10407005c84039107980303032010030600d4002e141030800243c0c030000e400b0858401030341140f056698103041c098203207044110305401c0b40d000000540602caa0fa2001004601c005149500318240c588220b031401c28000b2820715206d205501c4111001c15440c01000016441c0ea488240704040301c40c1501c2c0b0000020030006c0108 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 160158192 1250 160156942 160156967
    0xd02010c05102301080307030e130606050c06090d080c090301020d0603110901081b04020c070b0a17060a061205040215042702090306070c05070b0a0302121501050307180b0a 76
    0x140501460010740783d40035581d0300e0581d04040e00030f5040800a940403140c000e40d4200b034981048901120b0600c40b00c95002d104060b11481d2156501c4030081c4501500e03026008040b010140d100c610800c0115400140e03103078100ca140c1c43c113a5591001200402d02902c074010940305158504a400400d20801e00494090322000b114420703081c0c0d9079414625515180f10b851040c0080700f642c0c9070107617840c05600801d40e0702c4094050b101010783e284d8034480e240d0020141e0030003140b0307414607180b00021140103035a031102d8111500c4003010706044d80180040307190903d64500c81e41d54800302c0c080d541c601c40c40c200a40c04c0c01c1c100c0c41c3d446440715170b0b0349038888030380450740010011282542020b130080c0c025905c9010b4090010304480da6200d50480b140c0f0111241910180141c0e1008600c071125003004004000250b10003513601d04440d021400014402007440c00c100e0704528450806d80c0c1c2c002c04803a0045903070714140e1210151a403000c81091403940c041003441c40002507040744a9002103100c00107 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 160159442 1250 160158192 160158221
    0x903070803070c120804050309060c010b06030a020702090108010c02030f1b0d090f090915021605010c091505070203211c0e060c0c1c050f03040c050a091a0d02010c0510 74
    0x2001c100e4941585e04100c1910001c140d90414094101141807e9000c0d04004407000000b090030101000410240e5009944105000d500000d0100950030b00200c07642c0141b50030002046803500c6c00c07500a44034001c01c0c05e0f8031a8410700080d508090b202c501490114640300f0030036140d00303030403400000d03041402a00c0350182050724a08001a5000941300b00000d90345c10000d07400714070720042c907040000c0d405014000040c0c0b900341c2248000c0f501c00d20503006110546d403210f0400c0f03070400b003588011402c20744000d07041103000c018210040e1800f14a4291844548074407408031400000c00c880c10303008044516402c1d404104010060343e40503040300500201240560f40603440300869805688a251940702c0c00d41e01c8404030060b003061030b4444507500c01c081d01c1d0041c00d00003807100c01d045a0740162803d40b00d801031500e080c00145000c1110700001c3c02040e80400c610010007205961861564295031710a0075140410001d59005000b103000950703101c0169101d0354444d8100d04018154403040341c02 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 160160692 1250 160159442 160159463
    0xe0f01060f050306060f01090f170105240906041b051803030a0215090a020402161101050a0e12030c030c0318030a0f1b05100504090f02070f03080903070803070c 71
    0x34252080564034042c2e40b4043d02508580d540d410038010403014a8022a04121402d46c0008400807261041f102801050141c07004864080303003403900b958030161101c070354035030040d1801c2c4400311010307810b0000e0181920b51007482d030b4807140054010400d42d0640400c0801c7e51884107403980d03000c001005c003c50300ba0f2069401140d00300034141ea81c040c890030b0601580c00094800103060f40c41c042a540802ca110455a5042455000c101681c100128480a61403020b2080040159091100c5400d40007840c12505145554200500216100ea14140100400003405c103006e4424011920003d9051040301d0f6601c0d40310300c0c040d5695010300010760303101842050780c0106280205004050350382181000d042900d03181c64445206003d110b40130304888110b9000204c40d210501503015881854880c1600c9d41c0c41d1908a2050300c6031200d69041a0340b040000200081ca012410011950103203800c1c0196910452070528601c03d00202504c02d0300301204003ca1640c0c0318840c02d1610703220300d55905 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 160161942 1250 160160692 160160699
    0x4090b1501020f010908030615090618040c030515040e0c0316080d02060c030117100f0b010e0411040306020a110303010f050f030d080a0203070306050402070506040c0f03050d140903010e0f0106 85
    0x80c201c0d00c0c0c2817002080d0b200d0410100b012880d095800e0226190040f005a2915000c10001035182c0d0007040122141200c004a8081614103032040c06000812800d0900080c5003290000c440c032031300921034034031483e42c44c0b103003555081d020000e000602102504440d14400e4488107203a405460b44a0501107209440994551500c04038a07280100900355009055908000c1c040c000e45451590301d1243e0320800c500c408140b04140241c0c3c03901c14410f14001807a01e5030304001004103081050190145091a00d8038804c03909042c221011250855030050f210300e41403008680c80031011024030300703a200100000c14681244100034040f1601114005a611018001c2c15100d55040b11804041a4260b002a411170b03a03580085074040c002e8a070000b142900d90001400306d800c92102540c0981c0a07404200420071052400c3c00075144240d094480c0a01d550348240c1e596040948900421070882c14083c030041864090707038450800100207200b10501d040005035a985030240c110855801c00030b000 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 160163192 1250 160161942 160161973
    0xa0608030a080403080402010c08030a090501050604021602060c150a0b0f040e060a091b1805010b0702031207060603020d03030c1403100e060a08011b03060e060a090b04090b150102 79
    0x310190349094896070300590f200d44003913445001c01841030381445245500d680000700014021032281da4458000110701b039140c1011400c40b400100080c3c040c504c1000030002100d014464141c0440d411a0310541c0c031002d01c0100c60a01540705022a43c80b801c040510400c0006900300000095040d80c4c0d242580050030f00b08015510b4079440105180c10860108042201c541c000c5c01402d406119071080700345809680110441440d4480f0341032040740314210b000d1001c2401070341e0040180b049040e0400c80685c0000303890700c14425109001c500e0010b445010001990014802035400a007a450304410b6810058090400305807004005060800d82498030a00c81094a018100c130b40000c400c410300702080001c0041c40500358541c40030942d180082c3c03603002401200e58540c030541590100c0809100c0c040c040d610103802c00007028410f8010072406841d0a80c05000300c0302d54050102c2c54442000c08100100030b40c18000d0004046502003242088a1b082c00b0340b19160280d003150060b400c42503e6 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 160164442 1250 160163192 160163197
    0x60402030112080c07080d020304060206010b03040206120a0605040911090a06032613140a08010c080a0203250e011202030103050c06071b080d03050a0b09221a0a060803 74
    0x18000038110001c0d5400118406078050130402e0f052000311046aa1a11446442d00b00c0c00030030140164000502030002c2581031100a0051080102260960509500003160f90081d03408440122285030002441a070390b40d0042e130020b29004c0c03c10071000c030190805011013103040d54024040e0b0070f2440030a02801c2036114070300c1201d400c02001c40515000c40814202c1114150554182100a01c828143e6103010b0007400010413078060080d40180e4158180301900d02039510540c444d915043c01c280090390080344a9034001b5441d100140d40341e03030b0082d100307111090a8508401e01429691004129500300032030006488091701d4188417907042c44154001d07480b007400020003581125801311940d0900358050814035114981c8202c60400e11082002d120403603501001407584400a40c902050f01841007a401c610b44400078442d0840c82800300383c2111003c0c0c084038940242d11141042c01d1240540700107080e43c044140039a20310070503032422220702c050b151740d00c00310329010f03000030160b900004 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 160165692 1250 160164442 160164449
    0x306050d03090605031504020d020706060e0403050a0309031b030305060a091a040b011e0e040c0309120e06130605031b13090506040f0e1c030606090b0c01020909010314060604020301 80
    0x1610b59080d070070050704403140d0f000581140500450115884074540c1d8038005031042030a1040016201d9005003031113015aa401da2140c5201c3c2201700900000c01c1c1d00008079942c02e0b02070b003004540c4d0900c80c80c00b11602d0785050540c40b5880b08450440c0101a403580210b402100c0440715035000e44e4032646502c0880300b140a03030880d14074041604100500349500084690741c8141048104425005101a0590248030b203140c0040d41000140c010741c03420740700e40744e007004a9150801101c015a03071100700c07400d160300c2031006210300840300c006256180e1085a868220800340d104045640c0c2d40007070310360b030819103001e0300d441e10344520741540000031030640300b1000072800d182803014a84604040100f002034495a00303c1d8482445a640003201e0184103040c843e4000200101c0c1190130310540e05414030380000c4100741c1444410443c20b94000e0341c40040c2da03050116256911403c01e100e41c02441004006904a8205000003003409402c4651848003000901507540950701c45041004a01c824003 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 160166942 1250 160165692 160165697
    0x121b0c030d150b1303031b0b04061a030d0306030b0105191208270f1801090e0c180415020f071106070c03080309010c0806030c0d05070b0a030c0306050d03 68
    0xc0300c0041c0072401c0d048400ca411581c100580c209840d0050800d407540400b158004030780c03024004004066104200500c000c65211b0110520a90755071400c0600700094000b6180300d45074089041e10901d0000041280100102115120040014081d0150207148815603340f203641e030001410341050603910100030340d061811940d0b07505050109503008400c81d402d980c4c0c400180900400d01c09800318000036601c2c0000a10704c7e01185c4820003003000b032003e0842c0c0c01412401c5182c1e00084031480c1a6054540d440b0010400e43c9035100207918107840c0c860205d600056900d200582840d0710103820740600d01604c01d4201103500d62021500368411b840180201040400011011681c8084280b0340701c28001c0281c1e1a202182d12440a0401d280e00182d81c0c0719400000c0c400d403007409120300310007000f076070401c002d1b280380003000a9151500c0b0000b1500401c40791442c0c0c01040024020783c00174114004455031544100c031030040062101d2650344011034030f001004281b42c0781010444c05e070030b0b40c160b = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 160168192 1250 160166942 160166947
    0x207090504020a1a040b04060210050a0b010c06110d050a0b12030301030f0206031e150406050312070f0c030b0901050717090d0f09150203220b12060a0308121b0c03 72
    0x541804c400a03602d07211100294000d200200354903d071040240004d182990081446205181c021011600050a24000031b803a0100402d4243d8000187c0044680c0140d00096101d00b84850001c10b0321840c00701c0c1071550702c1d0a013041a440031070b5104211207031040c1c030700d1400103203401219580d03880280005000354011005030001441d001000f164001702404005a03449810050820700b008240c4440d44400c603150b81003516810705100e18401020704600928090500030000060b5108481018001c00c20341d85c07001043c0001c0d580c091008591080401000c0e2400402090003400d0a403268070000300b040c5904c8a110030840b40f59402900c1020180c841c01e017403a402542d801e0320300c144c000203001c2110400203102c0350030000181e5080458019560760311103075440941001104201851a0802000c24031010801c61b00b0341b4502d00200300100850313201c040015941e00d001d60300081c400c14000030380e0008000842d07005ca00800d8035016070281c1843d100c0d124842c034041c1c081034041c0d65105 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 160169442 1250 160168192 160168199
    0x8100902030403021006090c110d0e0f03010213030503030a05060d0309060c020a03020a080a03090b031303050f0903060103110301050709050f1c12020607110102040510050904150e070207090504020a 87
    0x8503801590414800e00450386010384c46902d050513940700354090003006a94141e0400c1954200303201800481c01c150141c01da44a03841005006403000300d0b1100d015043d0441c8a0215881c254122501d042c4a400c5910049540746031683c0e41e80c0c41225420f07a95030030f2501003069070401c490b860182903850307140d801d4418241001180e94812115060ba4010700900c4000090384a0710340c2130000d800c10354040c0c501b104207400e02801001310355100c004002e208100f044001042c481940014503030501d0420703903c0d0b60071b4801d0707083d42c00b0780d014259041c064000000700b0032040200c1040c22520580081c4001d07580c0c0c00094030f404080384141500038111389417000103450880444030320035800c801e40e0396410100740c0b100050005031004110250348820180a0740f01c1c1c02c050b0100b800350702403000354a81070030311010450f89a03429035a00140140400d050001d80d0f0307180c00c0014041c0c2059911803c06903a416820f01402054445c84054003410a01042c01d0741c0c10702034544242c2d0050704d030503011490f = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 160170692 1250 160169442 160169459
    0x191e0512070e0901030506011707050d0807020607060e07031101020102031e1305011404020123041a0d05090c040c020106050604170c030a05010609060e0402010206040b060303090303040f090506010810 88
    0x1002040c00c820403907122012440d681e60300580c0f6000c1d40c0188000c1c1402c0d030600301c6860880361a121620403030307030040c0c13410400c90313445503941c0c90003551000e031080d2136031024404907416000d000d8008003000d05040101c100030300000b40c0c00048901a1081030780500c03140e00168201c0c0f0080d82c4c503103461441000f200800c403820201007a0480704080102c4103000d4592507480c215030b42c151940d40300110081c184015580c1c0044641c01144048400b8207a5824401c180c0070039100310300c06c030304043c40f03000111518500c18000755081c80d140d9080612140c42c002c01002c0c1c4801400381c41501c114a401070103056503205224650580782c0243c010b524042c00c220304a050100c031404d00c1e144130f00c141c0c0841001901e050122000303051282001080712814401100f00381c44484e08009d20b580b5107030040002603a0f001a100c2c0d0403907000507008440c0d46407880403a042d8403c1030102c58061000040010f0340d41020030407542120004542001540c0743c0d03000445541c0c00c242c8405010044000040c0700035078 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 160171942 1250 160170692 160170727
    0xb0306060409110906150f0417060f0415090b01060e031b060406270b0415020105070516020136080105041106031504090b0121050d1b02030102191e05 66
    0x100410031b856121168060f0032a0f54444080d0005160000c10104820307020140d90440007480e070809040940740001080e5886c0800038005000b5500c40030142c040301035594410800c098001001049541c3c45600203400d02c91482d800300d00a2042948242545c00084145440400c00422a0385000c0c0b4041d01210b03120100102c2c1c0c0c5168090107190140f5900e800b17850070050508810b003d03100c9190615941404891200120075641081c0400450b543d0041c219612218007a141d00311100c0140012102e81c00100c034903078101e07246038050030a48503034805080c012107195001c11044540b00c150050036544280c4006211040c841c04040071480c010000e1640400d165070b0600001c161140002c06075015441c054400c1c86100005022800301d4001c6202c002140c80f01c500038001c090740d21a40d541d080c4052007000c0200305600c032815080c041200710302682d0000c1c02991110030030252080c8042007801d0034000309140d60f40d17154031b030341104410611007030682d25140d0a1441c0420350b1103500 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 160173192 1250 160171942 160171951
    0xa03021905010e03040e090f010c021f020d0903120e0718110c0a0f06051608060603090a150209010305010e0c04211b05011407020d15140a0b03060604091109 69
    0x75520f0360b4003e40058002c0001d800140190034041d0380c10f041015038113083c094040507000c126410030598400b03260f00000c090030200c18089070181000c2c148040000240a1400c0740603012303052880d42d03400d01d948110280303c68401d90504200b00900c1e4090300b9581c0c221885040c03003014442002c0341d0726400ba9840110a22801d400d01341c5880100e10001c1e04001001ea0308680c8000d200f8200300070711410b071243d039078444102c40745044410007145002d045c41e58000d000d01d20400300000069800c400521401908a901000350b05c103d02804050101940000f004039000a04c1c200001600d01d003451806406000583e400340d1910f402c0242005100a08521881c402000d6525000000c0c8014110204001c61483c24200d100e00340400140b12111030509038035004406d000c95400350b1f4a062101c54010750000c0ca080c0c8440040d443c04014050040588003400b0788581000315002c0b298201d950214000c60a0703a01942c0d901040004585d6452030144c074080b0b0195003e41541071042c03900d41c01 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 160174442 1250 160173192 160173203
    0x915030b010b0711190828060e070801020708040e0601030b06160317090d09050301020c0312040c030f050708070504051e04020a051009080c0301020c0d0503220b0906090a030219 78
    0x4143c13400c005c0b848074001031038034280542003444100120708051040c0f000c00a0300682040e2801c4042e600300040030703070030700d00581190782d104511300028408011800003081d802c00290b45a1040b402c28007074580041c803860355520502c40015105610038850f003001d44034010952800e14040c40651b030058036041204030700340004101940e1440984c3d00f00d00e4882e41c1d14800805501d1062076009111004070390050303001c3d078010f110200d88130f44044140c90b1219000103041142c0d0383da0781841002c0c1e610743e500203031440b100b21525005204010800c4410b6032076150440e203480c1c1d52001030004941d0101e40d001d40038108110012006411103007540d41242c001814030034810b8885d0b0010743d14180701070756040030a0406c40d00b040f2604e01032044141c548400c0303008600705003035100e110b0703215400c3c100c02e10108400000020a180c3d5000369000c038030801e01103040d585da8043d15002c8403402c000d031100200c030310504d800180ca00e14001140d16000b58075030301030540b41603081130f642c01c001148a0120394 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 160175692 1250 160174442 160174463
    0x318121101090c0b09031905061f09050a0608060f010e04021003020d0c03050615040b0304231212130210081504051e0606070503040e0604020d050703060915030b010b07 74
    0x10400c03200440c400b41c0303d14100345136942842c5c000c042ca0800542c06a6440b000b0040760701020490100e2050b500111054102c0511000340c500c00071000560340001e48064540300030f10006507560744c4290203071079181e02141c8850f1180a200e40411a00f4855100c001c1d0340e0710300240050500c860500c0040046080140c00d003422036040703100b030ba80104c3c40b020000780c1c0c501c100a050b00d00f00c0020b41d603480b01150020701c0c2608001a130a4140700007040130f0b240d40b6461b0701e2010800b80303210a1101e0040407a0a482100040354103010b15a8070a08075400140c2515001c11400c000400404070655801051024810903041043c1e909010003800c05d4940490100401d0464643d070062620a4440ba0b8014001820b42420b5104a00303000c0d20050046006121400000300d00108031070590380000b4001d90f140c0d640f43d002402038402c1d01d0f41d4011290410301804092a01600640c1c160f40c64104140501c26607161b020486103514400601705544840c01048201d00c84001461603e001e04403140 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 160176942 1250 160175692 160175711
    0x324090207032f1c1d010e0303040b0409050601090510121503060f0612030903140a060e010209031b06070b041103030c031b01060f0330030902010318121101 69
    0x60b4040300070084401c881039944034030741c00d0050a121510005010780c007050b110400030003003180d40c1d540c07468a2018200c0d000c886e0b0302844401c801e444005044035503803611051300e26030582013480361141480c10840400c40b190700038a02c0d2030176a5000b4040c3c1207541803140c0119202505080e040904959900f10350300c5110102c54203501030350003050042010b840d00c0c140b8038100e540603406601e1400d9010941d0002a601010f003c00312600413880a030300190020007103003060210400140baa41c0b030400301d0f0031610010b401030130044e1421000d449528040c6e5591507070401f40036400d241c0c4842d00f0450318001031f000700c80060704140112000c0301202801c10109185520400d0501c0f401d030f1003c100040801030071800c101888100c5002849554948150400460b4483c040100003090b8285414105410010404d03100f015960202060405a0402900030607200704141e00190901c40242007030004411400281544407030140c0a40400803012520342580c1983e61055540310007400 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 160178192 1250 160176942 160176977
    0x2060d11131e03021c14162303031c11040803190908120c010207050d031a010816030e12070b060108090f060a0c05090901080d032409020703 62
    0x805a8880d80d030711042410b0b0418540786030341c2c0442114840c00b00b465050520068881d80c4803100e5411a212030b2601a1070f16140901e880e0301c030030160007140d02c42c6203103030540751801c0800c0000f150501c01c1d400002034080680e5110080000f81e40c2909035000700005e5084410041d031285400e5050b035030020341410740c40c0114000380c2c403030342c0a581c9039480806c03c8601100650030084c0d15640e1410841101490b01d0040c2e0349494a22148a024210200d40700c000c02d1400c0d01141c420f15404401d481c16000380c100c000c0c00401c4054103044003100c281e5100741c115400f81005a026032001d00407400307080000a030440c054014a8013600443c05271613401300404150750050305a1510400404000d49003030000100301200c007e0000340a64001c0340d030074511a502142954200c00c49401c0030900b0902c944058545108589120340c024044000001d5100000b050b001c00e52080c5940034041c52012040702110382c47c4252400f101002422002c104d5951136500810000e4880c0c1800a140c40b090b8664 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 160179442 1250 160178192 160178197
    0xc0f06090a0b070c11040f0b12010504060509010c09140a0f0b030f132012100504060506010c210201060f0611070b0a09060503040c03020d0302030705010f1802060d11 73
    0x60840c69400307103040030200308450b144540d00c9a403500d8a442d154269854100c10f01e1280d680c035900941d40c03000051408009a040350700d503040060301450401d03200021a034001d0004071010b4403a14944070119080e04818002d1000550303195407a1002d607800e04003041d0511013048003007640684004030002e4000608120b043c000e01c410b510303464a078903118205110b680d600401c2034101c030303944200709130000f1042140d05614004542407140c116290a002ca05814401750700d40019105407190b0a18610090304002e2189100b03100038170540c0c4a520040d0740720b1508030001440d070300d1907600d1040c01000b00301c031151881c2007520000c9407285d6503540c503803041c005c0360f00400c00041d4103010503a40d4400030007030240140880c41e05585001380b41d0100924000300d83c01208201325001011a0501c60708000c021302445c0c000748801b1096840b440c2c040d40c0c9611111007120603500b0116800d001103191701c10000fa83c4103400748802d58168641c06c10100c0c0c3d010308804545d895442043e0050760728030901 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 160180692 1250 160179442 160179451
    0x120c0306040f0b060a05060a08060a0320181b0703020c0d0b010510020723120303090d11030304030e010804150603050c01110c100f0c0f0c150201021207050c0f06 71
    0x500003010400d03030800850f8624000e200e18041d02a40004020725190302044940040f40c51900e40d40a485000008031070905990010300b031600144540890190080281c0450034422504ac94a40311350b20002c0c040010104e41d07114840f088000052082c40b82c0e0b80046c8a04e900c28810703105103580340e0380010005801500d0550b0054840d0006000508061246014001541c0020b00d42245400b0500e00400f040343c803c040c00c0302041611180540f0f03241044004103102c0303000d8a4076841c0900b80036540740e00c150f0311100000c0c900202c643c101d40011003241e00a54241c0c1d62044027504000054a0504010b00101c1c1c3e0083c100c8021031120040e442800007452250003d030421400c03a00c0010301e4955082c004180681045924202c142d45001c003a5200006505011824021840c0c1c1035880c9440307668081c0c141c080c0040c26104100000b154070056402c01009045280e120500417801c1380aa81202a110480c02002c80c01c00c034000c002818000d824501100c080140f01e180d46414100c0540303 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 160181942 1250 160180692 160180703
    0x100207080a0f0513090b06090402040e070e060705070e07110a030c02010e010905030616090305030301081609020408030a030b030f070605070605010614040e0c0d02070f0c0608100302120c030604 85
    0x1079035901c055000c582c841100d60315140c082d003440b1040b009141044014818500c105549401079405078a4030303415500b01003c0100704541325580c928406c0c0c40d1034000c13102c04000900c034113103d00740352800b070742600e0001d5048401040c0280c10140c0520441002405d0041402400c40000194041c200b040003c5030784a80d843d0558000c492001414200200001078103003c1c40e04414041174500048659001c41d040040441000030004181c44221a41c3c2024249010000c008203c95100023290051407200c19410f0f224540d031006040c00301d000302c1c011400035030000c20000c40102d1007500f0200032000006d00382c4101140d4001a6850700c0120750003000400d80c04600c40082c003070284a5a40100714901308041c900316540c07148000741c8198040d40c44075441000102d4a00c02c4560217589002800c0070045545054a0515012003030060004030780c0010900000700d58203108981590054030781c50101d95510b421039081003210f00000b1549102032241041f0314005603002c100b8070307004038000c1 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 160183192 1250 160181942 160181947
    0x20d020412020f01030e0a08030c0903070e01150216091505130f1802010c030809010204030b0403050304050d0f0801150c080706240b09061812010c03062907020310020708 75
    0x14414010b1040d0510f50490515183c9512410410400301e400c00c5640d03404030b6401c0c1d50703642e408402c4011780104402a601031040c82030105032000303a600f055050701c0c40703800c907403001140301541240d0305c030800101a00c8a00340c4d02d000300446c11b402d4000d40c1003502e0f05111341c1096500c0d5808104c0700d090410344c0200c0a91a8a01201e1064451003081c0f00b5002915605c020044070750000b800504c80340000404100080d400140c1802083d41038401555202c12861a18241824020420307001520290780b94040c810f00444018054010f41b00d001e1403580ba420b000d41c1c600b0401f48510340744544080d042c85034076640f40001072201c0005044140c070445000440a4400803907a003a42d100440230191031140d000248010030582d0b094030f0091400301c0d089a42c039240001d9003140740003114400360308150070504d0f0301411101904000750105469408021066550800b001840388607a0103610703c0c1207002c403407505680024024a0318a001804440a408041068000302d1380518002c0d100031300301 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 160184442 1250 160183192 160183229
    0x5071b050615060415080709030804060203090f013905060901090c050316050405060d081602130b01050d050a0e0f0312011409180f030a03060311030d21020d0204 71
    0x40b8680840201c0700703407580c9091a0401c444100080702c000d424505005078940042c03400c0c0c0c41107003113402440d4801d8156454540d80c3d0406540c9411000c001440741a465511110f04d5101c0c032400150412588500d60001e0038182c40e65540f908421451161040f2808010001c100d00300207050149000034000541c084031410029410b56040c2c00c00c1d84030f078000340106040480c0044680303060b80c90840e4001059210300b00043c2d20800c80c0b01009207200b101241c40100400880201c1c0344290003515020854030115085000302c550040300140403a8040c803c0c181200724a501c01e41e8000000c190002e803020901e0310300e0b840e100055204501c541d000080003404642521320081c018141200c880301b28010071030028588420081102c680c64140e40c0304948803100c200244000b01800c042030381c0d0384106d032a1009024206600060314240101c0030f4290190400040c1c000d107404d523554402818a4644480584000c00c11014100740c540a000001402105d071000304010980b00071000949903a = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 160185692 1250 160184442 160184461
    0x604020d0623011a040e010b0d0b0409060525051204020f0301050c1b011103070f0311130311030a05060601081506030a020307030e010c0509060706020d02030117060c09100305071b0506 81
    0x1c4c104644986001404208075840000301c20906542e0b008074202d44962501912000a06440c1d000c1c5a110b400c1440004c00e014096000720f000c1d50550005a1085220f00c43c5046103044200e0001d001070010003903221a454403000d15500248014840c0d040c000100d00080e0130f5a009840700f1004000c00039202c01d4500e04005020351380da8541c40240300e00f1564003000006404014188000e000700d03d040210001e10139800982d4252449211035194440e510002900c0040c50100f210401c01036000c3d04a240340004500c60110380c40b80040081d680c904004503245030016005006850801d58114050350300c44001d035200340b450820042e268580f4550050a070f5803202d0304141035234500070310038291550000449164220541c1d50070b90b610175a00c0c00e00c3c0284540080005000d2000c40040b8404103c0c045e542c5034040d41504444241c4c450540c100c6a138804c1449103940601502601c0c1c2d0841d0007034101d107502c805203040c040c81b1200c0c00c1c007907840d0085082004030303001e80082080090140 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 160186942 1250 160185692 160185719
    0x507021e030f0a031d010c202806030213080601030501091a0402010917030d050405071505040e01051012050f04020109140a03061805030705060f07030b030604020d062301 75
    0x280400020300f1442c15645014100d9000c007406600e5a4000000d11702080c1d000c0c0d05070520722540000240500e54404901d150060881041c00307101361400344d0f584840b40e0f0740c80300520b0135a401c600741054161510106030000e51107281c04a03004012503000003100081070254500840c00f940001c28a000c2a24049054101c0c0d941c034100403040b80018400076076402002d80f01504c00c0c01c101c04c1c1c2074040c2d15020701c0c954041c820003180b095091a08000c100040820901c04a6945000c11030070071420100540310760165001e03400115403100010040c86c90400c3c0008040e5101d41030410510b4181d4441d84c041c0c64040341e10410302d4074580300380000c40d6440031014004002040c940707011200158009a02c45500d07120281046440b81c00001d100c403ca00317502e0b11203d0b1b011003260b42d40d4060340f428036180d42c01102e00d04103c0d00745000103a001400382c09002e07084140107010300259600ca40c200403410450460580d46140d8401003142c0104015150400c0425082c902d04e5496141048113200407 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 160188192 1250 160186942 160186963
    0x9010c021504330c050f0a03020a060e010e03030403031113141e0607060207060e060f04030305010e040206040b0c070b13051c0f0212160605040618060905010507030507021e03 77
    0x40f141c00c649003d400f2002c441c1d100c0030440e441d00003c82901824142c0c80c114454203e8141401410600810180c00081c0c0340401c6d4400e05051109203d840b0455088501680302c1450a4104200080001c0e02c26481000303e007420b08036035404c01d0314034980e0300011080c3d40c200c064401840e0088601c1032500400b501ca0000701d5890b4003041d0a101800704500d4006d500000302110b40116070141000055000414141801c1049641c80d1401c1c1c4400002c0120035103003940424517080011500300c6490448034811500500b000d490030340b82c054030901d0b07035002d11000900c1780141c4002191004060004102c240400218401c0090911040142e840000382c0580c07151500c11024000003400a4011880075404582c01c1d400010300310b0415041030341e800d2034004126002e0501080702900040604182c032001d603200344c484d1030000c181c803008500e240030701310200d0340321001000786620030f800030074106104e840c3c00e6041088681c0803580e00c90211210102e20b0031841504c0740207040c20800c00014 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 160189442 1250 160188192 160188239
    0xb0c0c04060305120c0312090c1e03060103120e0a06020d26040204020313120513270f09050a150b061c050a181a060402040b0f09010c021504 62
    0x80780b550f500d590380c030300c180b43c4100c1d039554000c0b030700c1a02000180241c0e50519444018890b840c540305407030326220080180c42c03e115440c180e1015a0004890001002e40e06028000b4552a4256258040a841c50004030350401c1201c0d03459100d2515003c0c3c0c100010030303d0307400500d00c020612002030f01001520344801081d082d07240c0c60784000444110309580007601500c006950741c544051810f030103810107002500380c803603000a501d0090b5119006014800413081d0003e03055444011000103204003458500c0d2450ba0207159081c0d843c0203a004884100d005c40001507100420340d01e40c2d04111542c41c083c1c5030101c42c6440a01090414020300032080c80c2203c0301071400b85003000d6040144500c815000c485540c420024204a496034800d492145440c410420311141d80d240c0904032503840743e80034000707203c03031008241d19041c1030081d40c0955012101290a100c2e6000318061181c224480039410010403048440c05600d420b400c814049041c900c565540d10b04140b20401c0c42038a0b020001031 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 160190692 1250 160189442 160189451
    0x10305010e0d091202010201090f1a06090628150903140613060903020a0b040f02040b1912020a030c060207090605010f0e0f011e1d0906030d1b0602040b0c0c04 70
    0x201c00d030f10940c0b2205450010f420306072a0051400102d004000c4007800a014001e1460240140214190028420101c1c9c6101141340d45d01c9100344007102501351801030700681c2410880105c2c0e03500010300c8445c01503000205003484c0d9204011201805500c00c0c0502160a8600c00c1c020b0200050b40c001c1000c680c03100506c0941403140300e600c901c0c040f030a8007030071199a803e500400c140c42408543c2c40c84d170704104601c1e000c1c04c250404a0003000c1d100400c07841580741441200c1242400d41c081241e01424076554500d00c4d24200c154044258410307012644039201100100003d8509600c007400f0f011642c1c004d0601030700f485141030442c6c80d180c002c0360510a26040038800c0a5120030380c0380340d030301c0d081e2000500c2c3c4000b1360050b640e6511040c00a440c54005103c0014420b80c800c0501c0da0004861801256501019040c4105241e0542d8010b81503004450049160707409000312501c50103079690f0020652140f5265042240c009812120580c0c1000807424011750040140191b40c42040300e0400 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 160191942 1250 160190692 160190713
    0x501090b0109120f0f03051e0d050601080105090a1d06090309030f0a0b0c0a051c0e0106090b0d080304020616031806030e07140d08030f0a061a1c021908010305010e 72
    0x206502d600071001004001d2291448041612400580e423001071035000c075860444034240b0403c0142c2008c0400e5580f1407030600015031562140406c0f03812141d0142164040c0c0d02c0d80703562400a04020207500c2c040020b044480c9080ca0f00822410f441042000080c3d81c4841d247c4003050700f400d659800048940e440301c032055000c00d52469107207030020300d540101039507007001841c16200741c0504003c541c0c040b5800c16406410f4400e40d00030059419051000f044140d0310360740c42d01b04546004003500d820103400c03044000001c0d40a401107412500003002ca50820b8003030022184945110441180041e10040000c0200700780c402010000d04082d050034896412400d2200d40e94800340e204080780d140010b5601c0380140c40d4403a010540356004101d0543c0c07403408212400110b541554070080a6207011000660001c0082843c1c1c410184900d1b05890500031400303030000e4a1041c00301500c030319070070002038a488043c3e5842c3d000045054442d0b851944c03441c28110b007125031100411202c0e40005d103a40e03 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 160193192 1250 160191942 160191953
    0x10f0806090f0c01051e0d060905011208041401090e041115030c0a0810080f010218030a08030a0207083c25080d11040305190f0b04020301090203010501090b010912 72
    0x8903100d030005c2c030701152a0a025407601003030302d00d441380341c54819100060b854621240c41d00704c032066410700741007448540d070b84036518162a081c012016180110031300c0240680c00750102e140414100500d80120441d0f2a0288024094400c2d90704031810b09066100040c1410104046002894440d20043c1945401500300c103c42c400c0341d05030810890700704e00240c0c1814144a0f05400340041c00300b15150b80305400c0c003080c001e40c8151140c145d024030180e03c2c00c601d03182c0081c4502003c2d030302440141c11034a51780c03040c001a401103041140c1040702031081086140c0310205200350079038031402c840c131001c0000442114010150300035080002c03003040102c4ca2014281015445500243d80045a500301c9043c41c040600655007800c15060a041d1144507120748440a841500e02410035115601764001e9280c1c80c000c14603200900e410700510014000c40c00c4200f54951040c0082c4c00403540c014550300090849000340c00907002c45568280610305941d1080e484400343c622200400b401c1710640d02c46 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 160194442 1250 160193192 160193203
    0x7030504030807140f0a020301060b03010510050307030b03010c08060103050a15060c020102010e0102040e040302100603031d0d02040f1d06090a022b0b04150c0c080a17010f0806090f 80
    0x42c009881c002001d00c204411200040340301c801040a440ba105c0c00518900d444a0380c1d588164800c0d0301300304021035136132a10748c2281d0480c2d90090402d80e03c000600c00544290b00010b0090007450366891010078075890038042c08031034a50550303507410103241020014045a00203424002c610b4541420364500780380d10b00050f0142c42440c1002040c0e1040d91004034094450040c05a0665001140c0011550301008103180030754401d40942c0c0725174009001841c11104144009030008944043c02d02d00081403407424808408094030080300c61401c1d030089026903400144d40040c1580d2781130b542e42c83c0d02500490044204010001d010181030001c03510340d460a0045002c0c2c403070004d480303500e060700311b80030100750000040762410314803070700c1c94203040603d1441107805a070003d000740c030786100e413070754501c41d10103c590180c462242c01900c03629404c1131600040792080c24403c200980c140c400b0040b082c03241c020544401e913840d034681483d6040341802c0c80640004199032013900180410540480c0 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 160195692 1250 160194442 160194449
    0x60c080621010204030c03050c0a0501020619090c0302180106090f060806040515090f09100203090d0f0201060801180c0504050c120622050609220201270605040807080307030504 78
    0x7052141c05407440c41d02070091085500040440310b40103c00410000c000c10000c5903680e048030b40c00c054503551070069841d01c400304c03002c211010701082d801407009013035480304c9003180c01400307103503030036a06e035404a240e00c816030203009281c0041c80010070040382d100805102403d140c0c09104512890200040c10104014000d03c4c0315644420004214049260a0441000c4010030703030b041e1820940100c4103550420f5070845024020342100441011281c02180d00030441d0b10000c0841c00c900c0101118021701041194046540764480040c9049090240c000709401f40c24540e403182203145040d07002001d8a40c0044d0044d4204410410003450360760682d81896405501d5250341d039502400502029200644121100581110135010020942c011032080005550000080c0c688038400e50348610140040c1e05001c00c0d050081005511860f00040c0c580b40d881c020b0140d0014520040c0c80411981d04880c002443c082820040c15104100c10801442c1f030a015507c2c105d041e840041c580c0c840d500 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 160196942 1250 160195692 160195729
    0x509010210021b0a0c061d0a0b0c0f060108011a270c161a15090105010c03020118050604120503070804080f1e0c010b0609030c010f0219080304060c0806 67
    0x65440407a184600f48400f1810014103442900101c3d10300080700c80c1a901910000805c281c10f910891540c990581020100050440c40304034a0b01159802c00c0e40b0888007440c2c41d004005600c41d00101c05c000c8240a0600c040c00490340c0341060310301d05020b9040582c118480c00702c0320000180242080a0341c051603c1001e0324403000d5072442d07924607a9110382070103441071107100c80f6200d00703002d4450743c0c4608006070108a40346940350044041442c442040c01e003640018000c0040280d58028074281c5241d82c444d000100e000c40c0d040a12491804a10b43e050782c0c0c07a04620104020000c00c00e900701e44085490a04a0a40c10030389001000850014401040950009107a104c0c5104131416140d003902c4484492406001103c1e502c4025042480348069030740c2080303802e80842c078040c1c054641244d40540104404a00c500044584140340e03910901940980c10079010f102d0700d01c14800702034038010b481c0b070b650341d003801c0c03038900100c032000e5022104000400c010702c040382e958003991214548048 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 160198192 1250 160196942 160196947
    0x110f041502120d0b010f03020a020d0503061305010b040302041d15070507050d12060f030312020304020604080307030c0308060114031303050c0706020f0f1207080721170106050901021002 82
    0x448181e2402620181d0741c60030150118942d40700d10f0540d00011080c400a0341c4100d90b1041043c8160140c0c000c4501040140c2c01c9144541d4840e481500a0369100740001c02c40011040740c07070006000c690b401e0300300b004900c3e00024288207500b894082d100c4125100200c11584113031140103180c0b545903001c08810740c3c07d01e56020810b110711400a840096402109680710151a40030140452030959400640e080c01d040000444c0050040c01d2400c40b50180c0b00c0d40310301c0c201d110410009500051080381d0203103040c040400d602c1001c03c080c2407254481d88526540c0348032810060300106005103c1070402184003c070250040880c41581d40010340b103280381440c1c1100345015101805001424040f0348100400011510b0380060003014808600c030668802074401d0b0b2040c0c1e10385014041249152004101840000b48040000c03c181800340d407800c0400d2045100717900d201f0310640c0302680040c08a40000710b641400d86049030041c04c580c20030901d00121a0f001039100d0025540385408950302 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 160199442 1250 160198192 160198229
    0x1804240e0712020301060f110105091203040213050420031603020d0f02090718080c01050703120e0303040b0103020f2b020409021005041a041a03040206160606060201110f04 76
    0x4042e0004028050942991650f1311140c0c000d0400002845410000340310f1510001600d106105482c082c84031036000d032640240803c0c4c50a0960300182c000c982283c5420b1a1103e000c0380c0303110300c0380507502c00c1c041d03030381074401c00007491654140d0445424425007041c0c0b61601c0d014001d503003001c11a54152040c0b541c015aa040001e0112484070000e504900c8210410401c0b81d4450b01000d100e010046858104a0711200f0b1703103684805107004a804504100301800200307000780d910034100440c0410100f2500100d04006085400c1540d0845141d101c0f54014021407505840104001ca4250f502083c0a2000c5007425510202c241c500404607030040c0500056440700d4004400b213580190007482100c00542c402081c0781c0c49480b035082d541710944c05040500715220221401c0b0307528816400b2482024410001c040e0788042d0089074028070401840d0214180382030350036146401020001001031a2020186c2911106081483d000408011a110180080c001d0b00e09846a108245d4401200c = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 160200692 1250 160199442 160199447
    0x7021903030b1914030d05040302103005190b010f0302090f040908210c040501031a191a072f0904050c01090506040503030304170f1804240e07 63
    0x4983c4200000511008000c5610890094401c84001c020350841ea40080401c2d001c844600580c000250301241810903902542d21031201e03100d421684140c000101c0002c88080a10b001c0e5807030050101c6d039144d108200039031901d0040e0704502c0c4262003060001c2135200340000c0c0104205004c00c0241607000c16801d117182c5402055440030040608200040905420440c14640100700c0c0e1100b01543d07110001c0c083d030402c030412070043d040260301c51f08007803c02d80150041c2021442080c0060810001d000c819503071050198810080301400c2100c2c24141020088c009446054083e4280300170001500080e9400c0030b54410201c8a60306800407081c2c0d000942c03c81e2016a015a500201e240d080c48184440414101c49040382601e810401541c0c0c0e40920006026601c910790341034000b40300190118012524400c0d500c0c0b0030302aa2850507614010071800da822030f86140405004c1e00658240505041c4030380185595561244030030200411440300c01c3c040030f4028070100d81c0c2c0c0035010416450 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 160201942 1250 160200692 160200709
    0x108060f09120703020c04050604020a0c06020d0207170a021b0109090e070509010b13050d02101b0803010906080c030712082d0703030c0f0503060f0112060e06010807021903030b 78
    0x100880c10b4165280c00a080c002d581d004e000003410b1156243c003002c192a40f60504c2222a80142034440103481c1030f06482c0d0340000c0d000311307641036400d1340c0802030b000c001900742c0c120188144542c2c18041e10b8041c0740c00004c1c94005200d030350b41407400084c10b07000320a0f85c21815070800c0b5041002d01141040a00c400301d4241a61a84000c2d00705103101c002003505811080607000c04815040210702142e607407000c12828405210001c0c1d0001814103070158501c5c4180302c9910544101032a051510b406595103410aa2090344807080c071a40d1441c050010000600489051131821402040c100e820494079400c41d8020080007130080c900001d03202070718116000e044d4513191000307681040a80d5a4985500320341d111000441c000703071a14000c100d0903401344851b52000c015550b211400d60340caa5090129140844c40f8180c14030108400c03850f401000350240300007409001d000d240c0d0a041c00d10016002c0e00d00584010150340100c48101e00c003030b0407041a6a1020340510380442c060400101082199 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 160203192 1250 160201942 160201963
    0x140708040e01060507030f08010e01180e06180c030105060f120708100b01080702030a0e1002210d05061215150d06051b0405030606130b060c0114010e0108060f09 71
    0x110300c1e8600025920342c21030050900c00c2d0180e124101e10361070100c1c0450702808e01340190000d1200e0100103006826a124040204846a000004041118840340c0e03240003012036070080420070100d10050001c9003400030040249040d4000c0c409802e041000410310318020102078040c000079410a22580401c1000c1c0b0014800e2070700746c800c8000c05e43e030404060422808101d000c902050042034075284000102c440307217101641d800324030405100c00c0084a01d0408015011485001d07000f1a03500d4103683c0000111600844051f130700d40030300003c0800e80e1700080c41c40e4425031800031400b00c400008192030903d1900c40c440700100f5680c580124071900060b107007903a00501c0303580c802002c20807940c1c0114050303110100c002d01e8062034840749890612076402055010703004800030403800d080065a8154540e140d003000f0481d0100c10f40407940c160041c0e44010070316911400d81f82c24440c4c52440160141c00503068212896040004082c0e40d014090030b5443c0020711030000505058041c03003640240d = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 160204442 1250 160203192 160203209
    0x4050c040e040503211303030b0316060914010504060c0834140705060702041808070503040311011e0c03110f150109021305062d03070201050f0714070804 68
    0x42c1001d0404036500e40042d0310a11044900c00f0038258803d14a0f048284264003600c0c0c120800d4a55942c1100502008043c054051040c042c80f542c114001120440160031183e85030103c0514003101c44103010208240d06051050800c02484a26402801c00b180660411103659461000f809520b820110709840c1c1800c04000d04078524600b01c42642c1e0f85820380c01254131000c1c165210b030a1548a203031900c1600c0e4003500801648005003059001450356014a00d0801c02507280c544480c0308551002008031255040040d003403040212800c0400013080080c40e03c000028054000e00001003003d400751814091145032000030988250754110300090003005070742100c8401030105640e40301c00d075101c6581130480e20010403880d801e4402e0741c40c500b801450000b0143e00e030000f4840a940880711051044c8514142040496040d401c661405421041525902e10705450000c6c00c5800c0501181d244948900178401c4080d803080c0c40e1001c000c12052070710f6070380601e03140900903440355501c20000c = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 160205692 1250 160204442 160204469
    0x70308040b0d0f1506030906020c03210c070305040e0411100905040605030a0c06050c0712050604020103050c0c06040b220b010518010303080a050709030204021c181104050c04 77
    0x1008184070015241004020000340b128098010a0b00180c0b00c403000e1394808a11102810020380344641c00903541140541e200500d4051614103060642c3d01160507060150541031040328014115841d0700e9000c260320107000d0811105540c0102140300350301c141001105010086800e1000122440c2c0d0359460040c2081c4c00084d001c000031b09040547c0c4102c038412480e05c2d6000070745040100c2c3e09040180e0180039003807800e0400c54181d6007500280038404103840354460115400c00008039030714025008070011720591401d4030005069581c01030503c2030401007488041080c403400525650800d50144071110303075640c1d8045480718101000240e000942d5040d500d9401c0c00780200b0024180d44007076400703103035400c803c0700b280700200001e210050002e00e4100c0050a42c40c03441e4003103030f0004c455107400041c04d90f59400007820303a0042c140341c0c00303105041043e42e12000e607544113581042c8070151019210f0501c540342d2451214201c0200d5010790b4841c0c00003a20110210126400380c05501c130340300d0 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 160206942 1250 160205692 160205699
    0x5040308090709060b091905030609010e0d030b011b03050f1210060206040b040609020a0906030809040f0612030c1110080f0c03040b01050f0420091c1109040507030804 74
    0x4102020644150401e4010490085000b0760341e40541026a04240300310b40c46c050314070b400d001506005070341c1031034510840500428203590500400d40188038210000c68020707844940b01781400310391803040301414901030b52000c0d00d03600101e090104035200e41c1d002c0a1030f40b1381c0c202600c0c07a200b02a545090420000360a42418001600540c0075540030b48040070540c2d1078880681e5030382801e4401402c00500d040000d0000382c071581100001910143c0040c174200d1307440a40a058a0281d04121780c01c40c3c010810780d40605040c4199601001580c2061221502c0d010907030595a19071000542003101c11180a8240049410003206560300941842e140c0ca2a014000301b000c2030644030200b40b65116170200700011420030660b800799411031003000191340b0300000c01c008500700341355898125440d00d462403441c03080214845681e4000960071a96004114100000780d000c0a03440c0d4403603611032071030001042c4107201002c00c040b03083d60480807580391800d00a00c2d140703650740000c1c80c2da003000a011 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 160208192 1250 160206942 160206947
    0x60f180801061d0a23092d0c030c22020f04030f0308010b040305060a020c0a0b07080106020709050412030b01120e1605040c02060403120902120309030609060c03070c0c09050403 78
    0x501c0e00140300365451425466014214040d6245c1a401400b01225000418102455041141c5e0001808000c4170500d8541e880c200c0a8107092220f001c500e45005005d0501071a418007840c00c902a08070b01920510000700002050f8140c11030200c000180e000c82410711190702c0707904403a80d01c8114100c15403501c1e0f0380d02c1e12401d1a24074050460008961800014000c14004251016207501001800c0c9558030a03000c0c9000390400c82c0400960f00c41d0f42c0458000c0303403003010168041c4101e036545003225814850301038601180d40d0b111190780c0b0324050030880480c0010a2010711208245008150311118000481c0c00c144940c88a4089626100009002e4000010102c40d206034144603001d0030ba40d80c10412044980e0003039058007580040002038002031041d00140d619240a0300e0004400d851034010622050105d9090666984002030031001443c04000e00303540600d8600c000c103421304c1c0a10a508107800064103903011b20849641160403c0f14000482001c1d280440f030800c81c5282c5420300 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 160209442 1250 160208192 160208219
    0x1715090f131505010815040507090c0c1b0e06181b12070e0a060e090609040602040902070b040209090c100c030201140a0c09080f0d0e03030915070b0907060f18080106 73
    0x446111b842010034005100c00c4004071503100326000005401502e180c502590090720010707000702e01b04150908150000341080c80e0740000c0f02060000d800601d42807100b05a4401c5001d4103161045e8207000c207400e2075800315640c43d548075582e005001409041100190000d01900d00ca44072801d404804015500f40d09c804060024001110b91040440e61401c09494a02c0080d8110750031800040c0050914182641181e4200303210718001490f184d0b03191000b40413078000c140e0440310704084500748000c0d40b8008080a42100c080382c0644221010000040e80c41c0c0c280c4c15800017400311881402007494000e40c03004001c80e5020300043c0140c501142c0850040502500d548081000003c1c0030440d1100010307a540040c0d03002008041c00d81e1303e0281992224224000e4560500c010808041e42c0e0b254a01d0340540d24940004032601d40c82d4600e8180c80c000c02c010a007620170f41c00050200000c5903c02400e03034050b103940c185840345c405c1002e007051915440390014040c940c00c11500144050001c040c = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 160210692 1250 160209442 160209449
    0x715060f1811030727030b070e0d140d02160b04150c0b010603050601020f0105011505071509050303040213050c0706021b0a0809100918020c0703050d1715090f13150501 74
    0x212203a540196440d01c2c5d074200340500001d4008040c106c002200940510703400c0e4140e110042c019000c6c0221a6036400c0481c04032400650306810204400404030b404201c41e122000c120344039500e100d410003070f0003115400381d4480d11110120341d081c6044840d0245844020040d0000e104030b2456031a0382028001d000d0a48449005218018062008400602c0303120f042c1c8070109100c0b82c001c000c3c40e10407034094210704001c0e101d8040607028070f140c0d46464495070b2040c502c5030000d56141d141500412508510b003e40380f44865040038100460880d89004841013594000c3c0e00503202d0142d0511204240070310092041a84a009040d006008940c00900071411048500050691012400300e07840d02140c4540c00e19407100e03103050710010090b50090450783c00c03217400f141c00039a030b070303482d9280380c05021100c07030b404504030000004181580d182c80aa0001c00c10325402c4413079802c10003061100c600184007400d0070b40030303001090094141c640511001a00051089451802c0210302001400c0030710 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 160211942 1250 160210692 160210727
    0x50d210e0c0a0b0304020a03111c060501090605010f020706031802120f0c0a0e010e090102120705090a0f03050a021315091406010201090302070e0c040909030201020715060f18110307 80
    0xd0b0002441402c3c1000c80c2d101e15801b409090b1540d01d540e9500313150311380e9034034007585c0050040d1075090b9800d01d05032a100d006004500104003540f510038240101c0d4840e4102394108242f4500c200900e0381c000544104807407070383c5000642ea0391086c0328030a0200c00104003c2d4801401054082e0820340010300d41602040309095500b10111a010489a8007042c4154298140c03d02e00403c250004407400a50220f0003200252038480b00050310868014104c48030b002041e00826101054108010410003828241c0c004981660454840d2951031040d00e000034401c540f0031690f0314407040b007900700550382c007121204030500e00e45440b8902e0250004400c8401c181c45800001170007580305001e80d508503a0150003900302c0074100300d038051003020300804080c00307107208201c0081c06500c3d41c810400414001d03800182c03108030034600000c085000c00c5c0240d07500c5081032018040d10940b29031041c11960500b50404541c1c200304441d802602110900c1694800c1c04004c0140180e00030381220518840c52 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 160213192 1250 160211942 160211959
    0x801020d050a0b0f010c0602090301090308070e03060f0a0b0f03030a05071403090a1703070209040f150e0304060507020a0509010e041509081204060e0a030906090e04050d210e0c 78
    0xc40914122103007546942e500080325043c131030855000d0081070300001e0180380c000d840c22103840c0200f429644160800c8001907441020043c040350f00041e20706010b10f044028003164103011600d4114180c001d40039030942c0d6030300d50407802c0b40d0380c440d10484080300d000380c10349407542d030200c034080c0c825003040d03e052f00c880411007060421011702100303c0790800e000400c2003007402e05141da01e10a15200b491040d080d4402040000e000d6075400c42220310540c0f20318130000c0171021610b44180e0101607030000301002d80c140112000940008000d943c107450051502c181c44407031600005101c0d03400caa100c107421103160400400c80c0c018103141e051295000e07001424021503e00d030030381d086074409000504444418801c1203000c2410b102c070182c001340243c00101d504844943c1c2d840c1001c0135881d0032404a80c00d66401c20419410050a100400e00204002142d00d4203854164550403c2c403000c0c0b080205034101e4929000240c00e10300402d01c507040080100d0f455070058035a4456480c0203803803098004 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 160214442 1250 160213192 160213201
    0x60a05010906060c0209040f0c030b010e011a0a09170a060e160e040b0c0f040e090c0f0a03030915030608030418061517041511070c0e04080a14040f0801020d05 70
    0x9403113004825034013038009002a60341e170b141c07060292400d000841c0e44540960000001c038071b1000410740609400c07003440c0c01c1945810b6030000380c0c0c0f00d66243c0c2e84204030240081c05045410172140d030122680100710b1841d050488800350f0400242440003845035113052070100c280000040c2c11105c003100b003840c0c100c00c282c40d0f03c10800300e400c00f140c000700311a0031980000c6118440d000278041281210a42a0403d62203482031750400004696006a6900140e160592868941020700c01c18000790b406c034642c0360a54400038401540c42c09400e81070394203002d0510b080b0303109520420003412141c007501e803201d464140e04519a0661200075003180e092140c00b24000085a01907001072100b601c51000b01d0800c2e06a02e01c000800500c280e03540d645034000090141c1143c090048501d024002c0c05945064601d0304c051800c8050b00204030a2000c0c20270803002501003c00c80b490503607541001100005844951003c500c03076034201c0d1b410100c00141c001006481500602020103609500740b00d903695 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 160215692 1250 160214442 160214447
    0xc01020c210705120f1603030f05150d031107030501060b0408060a0501060c0615031211011b0f050304060b0a03080c010c110c0402130306020c0a0b070e01080f07020f060a0501090606 80
    0x591002401d10b41050301402d014484c0d10b002048500422200f00782442018112070551646401c402d03400310340c0b12500034103400c0e568482e0680c481500003544810094010105018000951005040c03244070000200b01c00010402c0000443d445070084c0b005ca07480e04040d404540107807040750100d00c00d50011424580c1c40740201e0341650881e80e942e03244041d8a07150300d00030340f034102c421008440c04400040301013809072030000b182003204d44aa1a4180f0001c2081d800c43d1803503284e02d000024080310030b8100c00d42c07201301c0103801c51091600c16120740321030901c0d400510f0041c0d001513000700300000000401200401170104c1c0e003071420007001301c08480d010903265202c4042985806401006000030b0a02e0b00d42c3c003800b4480503520441d500c0d55126900d0f0720899000e88100343e4164002035400d002c0210301350310b150f40031201e13180c0128500506400a81101c5010f040c1003103941a22000980a0344204100701141291204403141070810b1080b03140280402e00420641d6410110085945030 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 160216942 1250 160215692 160215697
    0x4060809030909040f02060d050106180b030411090903160b24030c10020c090a150602150c030a090206070b01030b0c130e100807140a0e01050609090a020c01020c21 72
    0x103043e12000396103c0e513443ea0712481404040303038854014080081e41c445207226445c082c00c1c2544400e24a8030040100c80c440c490203601c20a8510800c008000c0001c44000c9607400ad401d0580b4055429103869600c0ca003503010b904605100c00b140210071209000301006548c0c00b510500c110f6940c2403078218580002c40c40301e0050a0340660080856035102e0904011412000040c1d1051710044141c1e94002441410241c0703c040e100b0b41c40b20854400c0103e0500c02c0401001d00380010240c5c4005040380384980700008040c4041c5100203c00100012000d030000c00c08184d0090070701d5510a40b503c0d0641a0389020700040e10700c1841d81d000503110404440807a46551004240400c0ea985015507010300c0001c002c1030554081d5039544000740441c810404800541b61011010b205c001c4038000b400802803180c2d001420344035200004200c2e9480d4003085501d511825124011141d13200021a8068031610202e1410b13503200141d030184074007000c0340480032400e0b088140d02d107146480c12408140e0 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 160218192 1250 160216942 160216957
    0x51c0606020d080603011d10050c0901021b01050d110c0609030a0212031f06020f010c03091509111917060c0301060804030912080d0b030706050d020d110f0406080903 73
    0x60b801414070141030350156030950f80c0300d02d00500214034007191007110194007405215407a055802243c482030034984600034254400c04140649050a0102e40000d6441c034401908043d0401e003110000b0060741300e50304503100c500703440f00d0501003c14007840004896010030781110180c0204400310f5501140401101d600904d80d6005103c280d868900c070901e41c0c0d0029010411036103a01c03120364004148001000c00130111f0382c02801103221070309006829191f048420804142c500001400024030198031140d400c10aa04e00082c404018174081902c9403012100d00d0b03200303001c98208141407411182c9101030b01d25208522052180c1c80c0e40341b658030034064804045d003041c1480140406449261010b501070300903d0820401d941c1e94101400f80c2c42c0b51002038840b02030000e02018126802e000d080c1e510402900140042c07403404400400d54000c0652416245c4d0300003030b80403005003081e00203500764445804c10682c1c1d00c4203016003681c154018800c01001c204580d002601001c0044140c4454 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 160219442 1250 160218192 160218197
    0x31f030503090609040b03060a020c06010e0105090403030e010f0f1e060f14010207030f0506060f1909050907080708060601140f0403020607150509010c0207080a11060d1b051c0606 79
    0x3886100000c010080e0000343c000e40c5c02603507903064500b450b6000c200281c0a0a00f081d00103950709007410a290400c030058004244444c41000100925100d1210540d8025018940064504054102d150140030395441d0302a01d03278141300c0d9a0b844e424035944106040707140e407070fa443c40c1c944101d08041c05698442c0308921070918100c400b00300b4045a55880e091920307052044e5902d440d280d607201c0300d10060319141aa4640d01003410010b00b810003208030726020104a6107021300c015800280e82d48120341c0d01603108a541ca400c00b03e02c820380e04000c18000b45c401181960500e507120b40c0751940d80c0e401100c240d80000d0384101e85814000814040380c5000c180b02040b10301d400d08603028426594401c0314111032081c0c1d044010442c6102502c9003c1c06490000004284500b80900003450f1490b50b4100040c2d43c0c10000e46040000c3c1a03800303040040006407680d5031030311a01d010b0200101081d00c011608010140303242d00c407aa078004000c19111036074411035040310148009074070884080303000783c002 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 160220692 1250 160219442 160219447
    0xf0503061504050a14041d0c0f030f072d0b0d09030c06020309010b03060a0e21090d210f08040b040212070807052b02010c051203010605031f030503 65
    0x1803400e040e48065075505074511510302d407503920001304d40e10900a500c100c9034078000c003203110043d113041c4c0a100b41c6211100075014110540141154580c000e00481c94401c5018000000c2c5a450a10950107041e48110944600f10740e15030500e40306111010700344006407091000302284030000821107042e50400c0e01c0b20707401d00d0361350070180000b0075010308141c007404180252180054018001944a080c001c800490082c00c1ca80a044c5040b070094030162580e401c0c62440401c2e003800217180c0c40c03d006500640024110f074a14001c049104142485030000b4405c02c1100600c103000c120030f07130140701842c51101c0c00c1503005030840d00003003a080d0750740c00109240701141c0400c032260003035a002030004040348016112058042c0c07408400b40d20030203c581041c0d100308068505002c82c40c0400d4003506911110207040070f2040050481000001d0501c503c5a4154090020401082003400500c4001c03d54070b5841d050081c000d5001202d020602c1c0744030400300200107002c4584c560403280e10000960 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 160221942 1250 160220692 160220701
    0x70f030f0c0e09071206030f050c0f0f0d0c08030c06061008090604030509060910030b010f03090b010e040516090b090108030c06060f1c08041a0f09190509070f0306060f0503 76
    0x201c20b510181c0070300100039450603414817943c558494078000314440e0441c0c0c840c1091a14000703041140400d1071a01c10012130810300842d4851150341d811480044031407409008540c5001d20800348180c125222510020411180700c01000401500514040b2080599544d802c03100301c0b010a800c50390303015070703402141c00301e00068000c101501090400924081c01c03e00d1501c0401c0344888181038401c0025260300c100403165030846100264110b451030309014000803038441143c43ca6041c42110514080d00c0c1c005014040c0c1031045803150304500100411580d55288150090002c0300200c91240c12103c000280b03071a0000100d4030003502e00e0b0081e00190b81c03100c041020340c2d1444071140d900700564541b09025003070542081c50032140b148100944403410b052030107402c400c2c04111681008030401038156402c0860302540c20029042702c82d80e4101e0703518130103100059620350149402241d0b02003404011500085c03011110b4910b99410004c442d6540407c80c0c5003841e604844000c03e100f040401c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 160223192 1250 160221942 160221949
    0x504021c080a030b0d08030a060f12081b0111040801020306040c0503190e120c061801090308010902070602130e0f07020601120308090307140a05010e0102090a090509070905070f030f0c0e 82
    0x1000c0c0b6130340040100d2010a0b1680b0303141c1d00380d0304c1114011103070390740c40d00305000c0f0b840f000499201a045000f6602c2c0a01c0807551880c0961040030380980c01c3d04200041880480001d40052210f5811500f140d525141c0e11040c560203900b0656400e4401c60819030507902c01c03031152040d40e11405103101003d400d51051f8107804000c10458964284600420300c03079606522807071000f4103105041070020a0280761030032618054072070050503404564141203108003c00d5000c00d415054800021006a8690b018a4580d000384120342d0030300403ca5442e000050f4841315001441c1c403448540c80912040e590f079110498807800c0900540c038500c410102074002007131080060b03070307400f20b00c5004492904210783c0740c1540c0b4442c145241c6419502c2160310004000c4217000d507641c0800158001d60420600200080d03031a4458042c10700f8841e522000514804801c204010042c0030b071400c108114280326134002c0c14180309140000110f03003400040d448070032491041c254416083c1c1c0d942e0100f0301c2c911003007 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 160224442 1250 160223192 160223201
    0x209010512040c17030a0305010b03130b07180b090913020a090e0f010509160f0b03010e06031c0302030109060506131a12010f0302010908031318020c100504021c080a03 74
    0x10342e552030f030024001c181105903284d000f00c0c041c0c3e80d2004603190040084000c0998105030080407c0c07080c14018020b60b411440c4030440c0a40d8007821910307842d40c0d580302c2200c4440a46800c0b0295501c07a03400002d40c2d00346a0020181280213a0328050702c2d59403a0900d40199405680007900110f032070600b0442046a0361281781001e0b0441c007658485003c1800050a640040e1402070840d00001c41880702e60200c054140010400d852403014510314007103102300280814403500c50b54072800c0300011b1041e90f003403040c250303a2203210052046400c001400100290000d000d002d804c2e903d0b10034040341520300320068458420b58140516072013420800a0840c4281110008140850920805883c480c051b240b09000e03218148051300c0161071030000405494031070344050800e800401003041c07070200d040b01c180c0c1942c90034020a8001145121000c00a12900c0415007007400f038071660f51000700240d0440e0b405075000312401e01d034100c00c0c0c400130441c0140340705004100300410811150f00a0080c1c22 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 160225692 1250 160224442 160224451
    0x1e0308060130020708070507091b0f080606040909030908060106090509130c0803030a0b0f060313170c030c0303101505030f100b040e0402010f23030a0b060f0a0f030209010512 77
    0x240c04c00c0e48030b07038403480f06800c0000c0480700c5400100c41804101010b2003205e018218242d1620000c002100024201039104c802e21401c009480c400140070340c0b5204202c1c1e00a004c031038420030a4840a00740100200c105015154441c00303240000141d1500c500c1d60704050718401441114036485a40117a9524400c2c0e5404585541080748000351490741400514842c5141c00000b0801801c507504028046074284541ca10610081c81803115190341c114501c000d540d8010b0043c11000400341080145d4059070a200c0c0d05480f0020f03010b0440c00c008400b55000340200500004c0700368581d4090110701c03882c4034000000500500015544150112000360020b0a00c103e540c4159120032152009038000c0e0094070003041310a061104650f0711084c2d1105d00205807804c0303c0751541211507001000ea0624a403d002040400400e42010b02940550480030006103007035a507200c0071400c800e0b0340e00b001c101c180100d42c5c08840540600d00074001c0700c08514050355050b1a040144584080c40c0701c0140 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 160226942 1250 160225692 160225787
    0x301081509010e0321011208070602090102010b061941040506121f0501080112030210051503070e06090403050d09020316050a06050c06070302161e03080601 69
    0x74440343c0d403280c140000c0448003150065000162041603400b1241281a4006005004d50441300e00c0840c030504203690b002c5a000c3c10140e602d42007480100e01401444040e59880240081c007001041501580d6041c41080c0392070b40500050000e0380c401030191000103110801d0001400c0c10649400c480d6590543c00b032039242103080ca42c40340003003200f03034116038100312a285491080c44425000a020281501e16007544191800d0404000031b10020062040c4110081c20010f46c008040c02484480044088030004120340d15040d824884200e00781d0001c14043d004100300410805120701001d4440e1502030002e50240c0c441c0d5900f01d699030311600c50800c407150381d260100010781d018003541c10350152460603028454100020040c41c1c4a944c1c0c8100140b11003003010f14003042f40800d41c690300c038119080040e1a040e04c0100002201c402c81030042a0508200d10290103802111004152034000d0340c2c4c010060381c42e0001958203180a08442c540140024010744850103032810300c082c181c4008 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 160228192 1250 160226942 160226951
    0x803040b040c08062a07030905060d0605030f0d031811090a2405040606030c02071a0408030a0f09090911240d090209063106030b09030901030c05030108150901 70
    0xf03801a50070181c0940c0c4a491101c1402d003042d410056610320307203155540c2c01888525054180d60050003401241c41424042c160118140074201c005a00c903100501c0d01134161001c001150002c21b80b1104d09604e800c01291914061902505285000c40717055684032ba03a0020100c102c2e000c21a5890000780a5642252039005588220f98100684085640c0401b20f400515003014100802d07540103801c007800b05403408400122880d40007071003c040b100f007820100403060701c0103102980ca201d143c1095000d44000564008120350082c4558400c880340e544040d2416100d0078401d080d603503445800351001c0248080302d0490b00c0c0c10a0302c60802c40e5480110019200030344882c90040d0841c060001506503607501c04415424203203561584140110382c0422120000e038a4150740044d22007120202c4120690124582c0303407964418405980c1185014001e460b0400da01c981c5ca50204e0390f00c6000904200400084c24041d401350b134182e510040141190340d2500c45c0c1034610002c0105130340b00b19900d8 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 160229442 1250 160228192 160228199
    0x6030309130504020102211602060706060b1216090b090109080607021608010510061206050319060c0306031e1703090609070b0f0a0503070315090b01030b04090803040b040c 76
    0xc05140c240850754071640402e052805000190400f4416844071035074543c409111511041c100048402c0352640103001d030001070343e6002040b5680214400184442c3c138020001c43c4901070300300948640314445100d03507115502e648003021400f5112151402040a8dd00e040c0801000d18028044060041c90302804180e9982d108610b031050030b840d190f0250300141e411300000b508124880d000340c00040c0080c011401c1c28615140045024400d031410440c160015000300d0456070004c0004040081c2210641d45100b0001a03880c800c005085440c0c41c07400c20040c5c01a406400742c4800c40343c000b10881a03a08448240b100c030f40c410000c040b20440c031061903401c80c58803284051401400854001c1c441442d1203401d03203282c04040d400c010490b010500201d514803001604680400c4003a00d0155240d403507503101034018103608800f00c503001d18100c030045203080d190b40c0890340ca01c40c00d980610050010310180812148a110060081c500030800500801c1d0312103138060300b25106580d800343c4c050381e = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 160230692 1250 160229442 160229449
    0x3080606091003060504140f070c020a081617190b1305010204090504061d0307080a03110304050c03010b0a0f090e0a050607020303070206060603130605061306030516090501030b04080306030309 85
    0x81d446180c40c08a9074a904c188006e06180c81900c42d0224980c55190f002c0c1800d4018201e9040020908010803c600141904548076882c09000910f0080c044400511039640d8403044111240600c3c08080c090101110400c0b00000b202c00306001c450058410714041a00c0f4030180301d6000341030707a18040c03c02c06050000740703003440240014501c0140000300ca0030b042c0b4020007a00d01c0540100c46021941441c481060400700c00c443c000c07980b01003155914010484181c026160f051090115140d020013080f080c03250120b000001070740e0071002081500c40c09420400418845c0c003842005111a0805020070990342d0b03c086680030302c000413106008150340e2414a017a00071582c0c0030042c1c1020090115040c0c0411a00d6003001049031018150b103055818001c6a111359076001e07011540300d102054607070702c030401917610900290f1801e004240e22030030700342c2d960803c1d80e0310221041078141c4000b9040c40540b240605881d030212145400751180d4460016681001c2c0c88180d2500003040040002e64 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 160231942 1250 160230692 160230709
    0x60319030f0806150a0c021306050306190902090f0709080607140c0a050a0c0305070e01050f040b01030b03030c0102070b0109050c0a0c060605130905060f0403051e0c03070804080607090b04030308060609 89
    0xd03541e06c401140e0840c1c4140103141203045009050780e07050800a104a43d00400c40c181d00c1110a070f04450007800350700251009c3c01540101075005043e96040c0304064503000c0295124080984901180b00d83e1504455034403002140d00500141d600e921800c0a524a103000b042405410001c907160b54015458890903c460058126a5405110b02c200200542801824028150350100f4403180d850f10003c54411101c1540c80351286a03151001c2c1c00c168040d03444112101805000c0725280e034591704030f41c0c0c002d6114400a851205449000181608642c040d00384201132404000c0d04201d12902c003a241c2045900048451649820004c503141c2c9400c00800c08401242c880407601c00b059061503070400390050700c407408460402041102190b0000c0c01c03a202d03924081440100c0003058a54503910b0f018031076403a0f215000004110341030200b081e002d0003d07a920442030344d0581e150b820040d02d07035101c24420185241801d0108002090017100307940c1e404075000c0c015030305d040d610500144041 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 160233192 1250 160231942 160231957
    0x210510020c03071401050c0d2307080603010e0c0f15041809060e0d090b0c1e030406110718050601050d0c031b0509090103060b0111030c06060319030f080615 69
    0xa600200f030640c140011400c0040390250601d00802c0707a42001c0607000b60602c55210b060508a4449000e229440c60300c502c9004121005078940713142e818800c82c000d18884003a00c0700c034804d40c20010180c00d40840030640c0b91100380020300b00d401c06070498082c030604000c122004480c0e10001c1c000001c50103036880c2ca00481507440840000d10040c18905031084401c808450281540710001c4025407035001081c09051344d00b100307003a640300d14414a40f81e00d0032407562000324044085d00f205082010000010700181c9842d6194040308002040d04140e461000e4414441520b81c0d400107880d145100307520454000c1c1042c03400c145000e104070503020640f04005600c00c0001c1d80c800b06444000861045010b503102149400c0b840d06501600244080d141030001074040d5658801012281e80581191005050080107481c0c48402d26030003d52540b2007100c01c940203004010300b041031004851948524141e15848000d010401800110b4002800500b202d0304280d07041c2c0b44802c0c0d000290040c140b034 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 160234442 1250 160233192 160233217
    0x20d03020304030f0c23030d030905070902040b09030d0e100e0324090106090b03070e100f0f031101050901090e100f151b0c030f08070f140f0721051002 67
    0x31850503404144034003c10106e03413824160340d0b05400241e903011034440d008450515020030502c2d082e041050a0ac41950b000301c2c0700d40e100141c00070b148114540501042c44044054070203010001c80d05544183d80c010285600c60361950090305550300540107000001809401c607000343c3d0103c0da42001124070600c505411f240400100503940400b40160b101a241c0f24005004540c12030740800e54568060203091f0f014961a40003924295002c4a054010700c040b805103c0c3c2150340704c10303131009058240010b03605c40401c4030f44500765500440840320304c610180e48001036649440134810041c03d01400c291104440c504000a4651009054401424003410040030009404801810f0050740d4050740502885041048011401800c0813004580d0820721030001c080b00780c80c00011900c6813400003003050390141c9208040c0003101c1c1c5012105150f2000b15041e04d50b196a040c0d5880c005842240c2e4480d00300c0c08054000e0395008400041e40d031284c401c1380c040440c0c060a5200742d030000040c1201 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 160235692 1250 160234442 160234463
    0x3020d06090f03200a02010219140d0f1403040f0b0a0219030204080c03061b1c0e1507031407110c060c01090c06050a052713061707050d020d03020304030f 68
    0x13100c2d070008100421400c00c40c0040030400d07030703c1d40083e455142032141803181c02580c0c00c6d02e00c10b100802c00380d0701c1c1101000d0146ca016001c40070010b131446900e910401e00140484079a0141a00d80200300c134016070708003010b60100007880d074441c01c14031b00041c01190456024000309001d03001820948007a4000368038007584440c03c1101d00d502d8180041d049503c6940501e0500620740400e20503070401c0b80008503c1a5203200e8103071080901030362840c0351404586060820100f51383c01156001d4402c0b0318104903080354444100803400d803081c1c0d042c0d9071208465840822510350284030740000d07500300d03d000e807482c1054400018182c1c0d00b00c1c54032400c281e5103401000c0104940160310001034141c1d41003c600384104008018140d015110000c20142201002c0d402d400380d0048003840a2000142002ca5012183c000340014101a10a8221210740761244c483c0c4001d012820900b07075070003c1d02084078901ca5070200f160301030350b40b841030702540400c05c00480402c050399662100039000d1f511120 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 160236942 1250 160235692 160235717
    0xa0b0603010f18060b150403031725030c23030a0b010212180d060c020c030705060406050901030506120102030f180106060903080318071206060b030405030403020d06090f03 76
    0x142516101210608040c3c03900d0328803c03800b1070100030007012a401150016070f00d4100741c00b10303009900710446407580034000710f4008201a032100f51005d803074581c409540b0701911501c02d034000e000e00754900404c0e80c142e0001d07410011031080d400440721040c94904071003441c3e48075100b01d2006221900c1c4500440000040114440341ca001c1d240c1c3c4045c081c0b0040c9104c1d12440b0020149005002c86e81c0250010310071780710807c0d80c425000315000e43c1c0102d0100440c200303512000c0e69030440031009034082e000d40f03680001c1c00d02e400d0056400710f980549a980c0380582c1c100c011001440c0040805070301a0004c40d00781c4003900244041e41c894140c0800390035440c141156030f0701004401c401c1426030342e0b04141e002e100701a4005c40240880354040d1207180c403a12801e68420441c846594252203d2050b0400041d40307003c440c019070f031f50301c1c001c0108009098542d20440054801140c0c0030f44658406c100410050809081507036419002c1c0c2000281404550368016256030b81681c1900000c51006811 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 160238192 1250 160236942 160236949
    0x303030b03060708040222140609070e03100b0105040b04060c050717100f021c0506011205090d0e0105070b10030201030506040203100e06010207080106030804030308010e0f160509030a0b06 83
    0x30302008104400501c1c1928101000400004005100034041d103a092a0007828441c441d0510780c404034218001c0c0182c0e078482102d5400d42004070340d0a44511040c2001c40d00a50103041c290600b640094050507480c07005044d59000f0b094104c100504102d8100400247d0581c2c8070f028202421150f40c40c40000c03502c90070200c1c640383d415000300c2c1041c0c006140d84004100000344180321740c950582c0102d200e190450004009015401e12418a08584030b02010004410b41c051480741000340c03282c894a482c407003200c00840e00c040300c0841d115404a01046045800381c06200418001450700c40d00e08545591001c4881405a6583e003200e40040c106000719a014047d0580c81a0291002c41c114a0003c00d0b11071070030740c41d105203800c40c564000070a031264400d01042c00900018002803040550700e01d480c044607401740c402075000407100340010400300ca4548138180104211820b50741e00341c403030303035610504e1030580c400320b1007030000030040c0f0400740e2000d00510f44064080c0200d00c00524102091 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 160239442 1250 160238192 160238201
    0x100e0a050703060603060c080c04030b06062122030512091914010b10021b010504120c031104060503120c07170d11070503100f0603020a0b07120c0f02041e02030709030303 75
    0x3901480203410400855927044800d44007100c5c0c12282000303054560303c000c10040d100300044070b80309494a031124204038062002150103111300f580c2c10740d00744944403071800716201c0c4100c00400085e42002140214240340645641006002050f03a0503407614901041d0814100b032812038002800d80f0200000d14421300c1401c074006025141d080c0c00541000c002034070740041c48884482d180180b15650b07440d034810000c0e100035000500005450031140e0518486000c541d00c01225000b03000300c42400c80381498020b070f204451002d801480c807940001102c90140d0041c2441551520032110000303060031003c0b0950151022175000707080d205200c4400140311604444c0c2c00000d50f0300072842003040d03490004050b48082c1a030400065045180f0000724058400c4d47e0001e54409038a0b0408200c1c0000c1a0003492003920603022112080b4400c00c06076204070341c031003001d8460070010080c400075013090b411a5a048030700e001114100d003ca0b0000100300d810688101001881080d410f0040503018170a = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 160240692 1250 160239442 160239461
    0x313060c051318090213020705122a0c100305040308240d02010908010c020105270312060d12021c110c010e120102040e1017100e0a05070306060306 65
    0xa0240c0307000d403081c002c80d2280c00d4510a4003051100e101c0490518003265100300a403a600500b480c0280e201140402c0194118010070b50b80360040d4050710030b1070716400c070880c3d2140c0c1030342d83d000540b04a000c880011190020100c00341c940a407070304204855503600c07559894444951800603007401c0508005024a00082c44c034485840841000200c64420003040742d0a040103d5404020324482c5c0b00483c0c1049542c0c0c8800e10b650b08294584001a4040d0401885617005903040c40c90052108001009818146400c1c07140e0f400800407040780d41a4525000c0d40244060705c0800340401983d100c080e50b07480600d082e801030b0007503449801c0000059200c88a540d85034940820080480003040351200b84402d1028140205850746081c8e03070b2180a6a4100340203900021500c46035a000007a410382401c541801c1d005640c00d00200b4280201504241300781c103540000c10280b80f586803600c000300201c1410381c80fa8440d51140500081040102c1d1019510811000c54503070311314a0100203607800040c = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 160241942 1250 160240692 160240697
    0xc23072301020604060c1101020c0d180303050d050c071202010b010f09030b06091e010f030201140307020d0305060a2c15090c07030e0603042004020a09050402090f04020313060c 78
    0x8680c03142030781d000035441c1d08940c0200c0002241007010406480e480d85e410031600d00740d40007280d142110000800c4050070240a519071400090901c0f01d0020504600e00006011174418800c40b6540540d42c1d0245600036040940c840c40d20301c458407005143c0600110b5240140e45660505580b542c1c00f00d0040141401030600b034541900b1742d51014540000102810b024041c84000140300f03810700018072007050316103d00358a1550f102e095044542c0620b00050740840c10200c0c01d03c400ca003042b400ca074841d0f400d0780d001e0b140c44000c40c4001c0b40600b1000d82020340c003601d0004082042d0b9244c2000080480210801d56098901c0e03100c2d00d04c81034001414061f510b00410265412916814203007544080052296075442d0907500e02691a054100e04181d04810013201700010800e04914180c48900c0000308103050200341c104000692050700303942800507079032900400c4103040c6500502840703000107144406041c1710802180498104840030ba4642ea5070305e56000510002c4d2003503164100052 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 160243192 1250 160241942 160241999
    0x60f09110919020729010305160e07080709150203091f02033103030f030f0c1d0f060703030204030c0b0a020606060a0e030a0b1005090112030c2307 65
    0x80b038202122500141c19840030b82d00060504c00704030340b03050403441e1803080c20080d034049140401000e0340d420090008594901c18041d0840704513598500352000c0700c00401c40784c21140ea0350a411103401c1006010982403002854011a0740030040b8400c40341e0f445583d0003180c40c0e02e003030b4041101c030b8008403c82c2844074401e00902038035180e01004540f08100c03c0561014250032021809107c54484200304500c0708280002004041e44281c191488031003a5400344100b0038032103001d604070ba4400805001003111070501e0800030149a00441b0b0b4903070000d001c3c0c8014100360ac0494196031040c00c003180082d90000381881000b10303220213000138003001b101203810440c542030b01954504010380f43c0c904c00c1c40b000c105900505c1c45500854003001018007a5081110a0b00d07102240c42025901e0000d06811000302040764106078400c10b040311020900c000d48461641c401350744100c200202520028250601c41341a616030400154a820b0007000030006140f515940744000c1003594a01d054482c40c9 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 160244442 1250 160243192 160243201
    0x20309280611030f0702130501080109030e0102030307081506131715070e09040f0503070f1118010e0c090306070f030f1107020910051302090306090307080a030e0109060f091109 78
    0x360b90701c503416042d20321760720700141c0005844444075a5507185c1480c148000418007180641144403681e11940300c10906590140c0103a8585c00105c68100024a428000819000e29007000b1110060090310712481e194504118110075002c0e500040c0d10100e02d40c3d13511150715010000c101c40c1d8031541c00040d0081c1020b040081002a03c604024450301c5560045424024907071400c0c01c02552000840365039001d01d1a22940e0080707080e00c207864411040401e05164104400c085920000b2004480c074107a0038110b400710038180242001c1c5a204051100c4000d58400b00030040c02401c80b41c80385049407002c2c1000038141c5074000c004450860030704440180e148180429035000d10390445640010f83e58502d54200500d0b01540002e9021340481c100c4140d00b0fa07254000c00c1c000c1400e800707440240c1c0d510010310741c1e207115410b00182200c03002c2040c8c0036020702c203038045440d000504001040e040c00a4a803a01517460383c40307822400c5070303a070340002d820400500010341d0420020354041d00540350 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 160245692 1250 160244442 160244477
    0x6010f02120c071805060a05030105090a0201030f0f0c2007050d03031a040c03020403060e071a0c01060e0103300f050d09020a030b0403090b03060609100203092806 72
    0x9200140d04840350020400e482c041c003003407016102406100d48002064684c400540340030f0301d4203a8142d405a0443c0d0300c04a52401c2c10f00480b4400c1014a000304003188032580118010103820040b002441d6554180316103d24441c060000c500c00c203580d070013669103034090111a103910040c6000700f00b40e11140e02001030381c94104036980f0094160400041c0142007007a1a8654440e103070300d66910501d1f214014500c04e03015409041540d0161008010700344505122642d51b02e03140c0a410364800c000110042d0b410000801031000481b902c001161250b5100228084801e00f80c00c1220807116000c050002d0802382e61350708031110740068903010078098400015018604038903040003000360018402c0e4000c015a00660012a8090300c20420b2503a43c0c1000c050710034090b00d04400080e0482400102a0713030103c1520f0040d03030018021032800300b038442006120036201c0a80c1c415400300703101040450740d441c6217409031f5800e800d21640d81d01e890030818050007200d41e08184140305040c440a500c1a0 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 160246942 1250 160245692 160245703
    0x7080a12090b07050f070b0a051005030a0809061606050702060a053403110d0f0c0206040b010e040f02120105041103030c03040b090d080a09050a05040501030209070c03050f070b04020906010f02 85
    0x141e513070400d95658600d21a441c0c030507204255018000030480002c0c41240030b41c45e0300c01485030f01054074080b40302d0f0310340c0304040c1c5078a400c8402814100050203860418940040104111500e00000150300c01e01035a62030244c4404465180240e00100c4c10004c40007481e018080d40510140c0304485081c6840c14070400048811070001c030a11000440d010b4030901a92008000100c400d461030b0305c40255048280140c52703d440c6401126091580e52515180009081d03401035034010107407056a82403210500b21048010402e60301400010080005626246e80c0a123510200c07400102c2c861134a42010540e0300c0d00b00c81e004c8d00940c0708001c1083c0c43c0c04080250342c140d0b900c5051007955100c0c140700140081c80d008201414418000507c0543c0315089013000040752000d6a80648081c4d0b90410081103c109120107034001c1c1803000040c8040307115040d201400d61003828401e003440c04c94a415440390300050011036054200c0c400b40800e40c03401c1202940d001100746000c160070f18116400030f4540c1c = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 160248192 1250 160246942 160246951
    0xa0807030e25050a0806010b16080f0d0b0f09061c05330f010f0504050406090c180509011112070c05010f020306011e050f0f040b07080a12090b 63
    0xd80d0350301d4445203031102406030b14070448004100e20701e080d800201c40c1c00e070340180340324143c4640001100058041d0010542904a55007190064103290400c4103079110700040c1d00c0101c4400404101ca4416981e11102a00021444280014a61115106100c09250500c0046105e00b08180c100305441d03440041503901c0018400030f40000100030720340f0603e811554408490855003803500c1e000954515000071440944034440c0c910300e92258040381c4241c803001e000d64181e05803042802d008505003078000c2c40d0460301c0350000084e071405c607450b10700c10040700381c21541c8000748003140d0720b1001400740105604484a40000c11074010709140d05c404910494030183c1c10810b1860000c0c1600f4010406a441150000c000f40580c01c8140c40354402544112000c0340070504410f0380c4080c0030b803003000c4403615640940310301c1d142c040e181e036030301103a60009076025262080070080403801b40b13080d0026001203441002429101d0a08100240101555040c208041d80c030702000e5001040300701c0c1c02d99810 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 160249442 1250 160248192 160248197
    0x3150e01090e010b060712020610060c06050408120405070501030e06010b0717040b0d050a06080307020d061e02070c03030f050f0301050405040201110313080609070623070f0b1b0a0807 81
    0x2038406042c0302901400c0b600c002e090b4007010102d241e40c00d01443d01541724002aa9909039041c6556100407036546080b18007030440040c0384000d200c4d0000d0440d511098015004515850809003120507040000b803046400300d940d44c001c000c0070019035806001d00f030400792440d030103868590306003a40c02880e40034640003e070051141000410001c0c00c1d01044030301030006140d48139600c503194640744010303160070b56001c034500d480c0440000b4980c8011007503881d11a8001c01d40c04403480580c8949014003007000c0da211010b0081600502003840c68030081c0221403250b181030003080c1c611f04001d0301103000b01c0071f00e005115081000c0e0841081d00411241903d070f044a0005080d211800100c0e03e11000080000345844001500f510702c00890015100b1100d07007804549a035a98044541d44401961240e0700129007100b0003851408102100412420a211081c90410107203441c0c82180b051880029110380740f040e01840070441c0c4568000c10760f140c459980c180b6014030080700800003400100711508 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 160250692 1250 160249442 160249451
    0x1c020906041e030b06010f050723030a1d0a03020109030312090605090f0c010f020a0609020d020409080a03110405060403021903050706020c090a060509060603100308040605040603150e0109 83
    0x1050364403801900d001d851100c24000911200b4100c80c581044680020340b4001010000550558407505400504d005540e0b580c0e41404490703510079000100d920382e0b03d0307181300c250910b007810b0003401c00240c04045903079a14588201360120b025154000b082070b08a0261390303450010b00250f60428625002c80b5854500b0342e06404442000038000e1900b05c1005044606210030b006462400090701c42945405505a5400071425001918202c3c6041c2c050740258018040c1880031500c01e0f071010203401d00182003010300074100d90001c3d0481d0a16401240c0710600802d010119640c544181c01701242990000303031403d0b04107400130380d0501491000900c81e1284a1310f680003a001011814003e40d4440101c0f41702d81d4481101945410b0b030300800501071100d15000903103008413070044404944001d07200c85c0d95a00c5913820300400d03600007030025030300000141e00040010390820003000100380c156102c030784681c1002d00c004c040d030322050b00c018001d6034030354001e0001c407481c04003a40c1147d028410008 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 160251798 1106 160250692 160250707
    0x6080d020c0108010927030302030f0907050a030b091606030501140108150f120624041b110717010506010e09010305070509060a050306090f0f031c02 66
    0x10b00151004004201c5441d159020f070558071101411140810b100112203030200c2c000c854102c0c0041d50000401c030000320801c5080303400513046000303000f9003440c1a0026105000c1408041c1c0341800c48030200700c60705403c2080011a640c05402200c00320b07514000513000300001d100d18006034180e02000d460a40c425030856101d400e40300c005803c1c4480c001d05020440c0c01400f00c198100110350729400307580104001c11880340d004d500e0301040d18900e60408800500c6d0000c1c07140d025070305150400c0401181d4004080c4445030381e02c2c0c49048400d414a4207490130029601283c180304070a01800c00e842010341005100f42c4003a00e50042401d900410701488030003d01c4041d145402c100c106102c0f5150903079890380c000c207000340004500da0302d0300006401c01c14143d90280c0c265000307561180348a0820320415006404a001a43c01c0011801c110310b0780f40b0110764040c4a880d400250b25 = true := by decide +kernel

theorem cover : BRFrame.Cov 160071942 160251798 := by
  have h0 := BRFrame.cov_init 160071942
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160071942 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160071942 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160071942 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160071942 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160071942 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160071942 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160071942 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160071942 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160071942 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160071942 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160071942 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160071942 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160071942 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160071942 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160071942 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160071942 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160071942 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160071942 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160071942 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160071942 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160071942 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160071942 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160071942 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160071942 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160071942 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160071942 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160071942 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160071942 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160071942 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160071942 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160071942 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160071942 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160071942 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160071942 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160071942 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160071942 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160071942 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160071942 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160071942 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160071942 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160071942 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160071942 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160071942 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160071942 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160071942 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160071942 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160071942 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160071942 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160071942 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160071942 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160071942 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160071942 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160071942 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160071942 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160071942 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160071942 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160071942 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160071942 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160071942 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160071942 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160071942 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160071942 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160071942 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160071942 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160071942 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160071942 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160071942 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160071942 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160071942 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160071942 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160071942 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160071942 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160071942 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160071942 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160071942 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160071942 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160071942 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160071942 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160071942 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160071942 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160071942 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160071942 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160071942 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160071942 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160071942 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160071942 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160071942 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160071942 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160071942 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160071942 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160071942 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160071942 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160071942 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160071942 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160071942 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160071942 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160071942 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160071942 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160071942 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160071942 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160071942 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160071942 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160071942 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160071942 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160071942 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160071942 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160071942 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160071942 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160071942 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160071942 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160071942 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160071942 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160071942 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160071942 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160071942 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160071942 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160071942 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160071942 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160071942 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160071942 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160071942 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160071942 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160071942 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160071942 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160071942 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160071942 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160071942 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160071942 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160071942 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160071942 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160071942 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160071942 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160071942 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160071942 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160071942 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160071942 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160071942 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160071942 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160071942 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160071942 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160071942 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160071942 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160071942 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160071942 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 160071942 ≤ n) (h2 : n < 160251798) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
