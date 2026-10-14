-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0870
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T23:18:42.645647+00:00
-- url     : https://prove2.me/submissions/1d216874-b7ac-4d9f-a72a-f14d43604b70

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 156294964 ≤ n < 156474820 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 156296214 1250 156294964 156294967
    0x10c090614120a0b060a031d210307020106080d0315151d0102010219020304031703010b03011a1303120905031b01030911040c05071109040b01092c0304090e01020405010203 76
    0x8280c0b640c035442a40e4071410302000403401104007030200c1e000780c10249801012944070141e4540840d42c400f10302c001c04010800904003003030840d00d051400342040d00c4c0c0b9a146880040440c21030740c402e401840250082400303c480241d000c24000b4001d0101c601080d1641ea001c50340461f4103a90407241d03170b9a03001c1d20f83d5440c5201000070001509010300d22899419594200070840c1400c04910f00c1c6201c4001980145443d1072079428056200d00c81800d003040030200800c018000d030383c80c1006480c15140020351042582800524243c19803007020400e0880d00901900041084035081d03040c000303410b19540303032921140e5981c14155102e01f420920000107140c0d452003601548039a001c4014035028000d00b8841840c8407000c20304850300d410030180080c0c00024200144218540001661202528040e2061405e5221964901d03070600850060701e440c1c2441110401c0b425548003008915540051072000421182030781e654424030900071a90b0400c800c40c8604141071090b602101d0040e0043c6 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 156297464 1250 156296214 156296227
    0x60f0103051e090d08220f0309030c0e04110103050609071107050a0608070807050a0906080432010e0708070b1b0313091a0112020c0a020d05010c090614 67
    0x54001e8a00200280400010700403070142c0103000041441c0220380c0d000c060004500d00100040a0000040800312512035880840020350105050032061581111036544245400d14080b94500c0c603d40c400f80800c0004d55000c01d014025902c0203001e1481090700012170064500150700b950320407601a50f010700014009904103019105001c0001c42c0002501e08860b11180007804034907c60304664001100c200411100a4000c121541c01c441681403d030b04220b45110010050300d0343c0c1c000d4008000700400820101b00c032601c11629092030210842d61800310420030300c44003031000005042c49608114814200a0300801c03110140c07a100c1002d011000d0515102d00c4681c0d001070040712942c18401039901003600d051000d4800c0c081044050043d0509e40642c5800b50350445142d041a00b007240ca040782030f603820040c1450207500001d80942c54000b04500507003414820940039411580c047c41303207001c000066015406002e4030307858150215032207002c122581d8400c5803040f548500c0c1003100 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 156298714 1250 156297464 156297467
    0x5040f06021602060309031b0307050703030e0a09020c0f0c0409020906060304021207092307080a090305040f0308040e0109090201020a03120912020a120f02030d090204090203010c080103140105060f01 88
    0x90101d00707802c1090b11040310881e4042801c036801110400ca0940011465800c3d03507035044640492084448021410440c0c1e0340c58094561104d4400102400780c02e1850620f90707142d00d00068010020103500b1500e072150000816100c00304603100c828180101074052440f40303001d10840c2d00c05900038201070200c0e5160350900c5026480500142c3c2c1c48020861a8283ca0004101d25409001008804501c2925006104a41c003041008064100c03840c40100800c00d0741c010000780d40603084a90204202d0f0481c1020b40f07142c46980c11082444488000100520240700000c00c115003002d404602c69a90790042c02085680d03104009005070403c20043c0007191081400c01884401c0c42000036071124640e8990b122081e01210345000360f00085440c50501c045451800066561800d007450610740c43d420083d284d105030110030a003607603183c40050540d100c079444150300c20750280c02000114000c88000d03080c00030034803040f504e40b4103580101c1c01003c418016180038500c0034140d0039001261500 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 156299964 1250 156298714 156298717
    0x510050d0e070b2101121a070c05061006080c0c07151e080609070206060102060117010219080414150411131a040b04051302190e090309040c020105040f0602 69
    0x80c0707840911403810042001002c43e00140b4500340d442503404c95906513014802c02c44007050740240400c0707645a01c2080444d40a00e0b84001403004007200300c501e6602d50b80d041c0e42d083d1040b000544240300300300410400100d07103080001640c029440740d42c0e43c0d589095440c22036105100b41100345410011082207003c1d0100e1214405055604003072110802d0f500a84900880d500749550001d812182030050b1810810302c140d801c004c1380d10103040309180c07410000c2d60310030041c86006100c0001c00020003941500b0b40c1a6054040d11a4a03200c1340295584010504d003000d48040d40c2007c0203511484480c9400920702550f00403a00301000199650307150032000c12246441941c1080090380002e4819559104030130854060a0314a03180806c0c417010710044030b2602c0080c81c000c07442d0000340321010b0824030754170300301ca9411284d01c046840c80609023460300700c0c1a88000c0b60708100d078041c8502840c6c0400030f40421f12003940d003005054071070201242030325010f1342e000e040740b41402c40720000f01d1347e60b40 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 156301214 1250 156299964 156299981
    0xb120601091706010302010e041407050a05070804080c0f090f16050f030a060f12020a090c03090b0108060106021501060804030c020105041a0403050c030c13020c19030302070501060510050d 83
    0x1848880ca942c0c0d80060903203107004802949150b04224014021980c003e01c41ca000174a094500708034028200e05c0082d00c17180b000d0482c105210003c1150000c1c1840349045400599005100640b5541d6907002a5924a0901c2c2d44511900c54000c0042050030200701080c85040000c038800d80a8403070914040d1442c0707100600400300035082090200c41d001900c01540100303161203001603501d2421800398103901103508020201c1c9a0060044050307071700c04003100e06851b40c0900003c1ea10360030303100640081401c81002407240345228000100080c022401d2412240e154003515210f0061400c03549510000740560f0020400c0b8101044c0440d21603030498400c80d10604180307203026281c25101100e0000840c0321001600d00003820b00030880244080450000150000e000c030124100000300c1d0031603c00344070340b00c2c15404902480c0403d420415040c0000b00744007011a00000ca0030000c000e58030480003a1425801c0080000b0079051003002e134410303018140e544905160003046101d000c0d20401 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 156302464 1250 156301214 156301217
    0x70b10060314161206080309030105060a06020c01050310030c06020a030e030304030308010605090a09060902071a01030503030402010c150c03020705061e06040c0203120709050a0806041e050f100e07080303010b120601 95
    0x81000300070a50f0510424001e13280031001141c239507262800301420344800a10b02409210008020051503400281007503462409003003081e2a5a07814441c520141143e80c4083c1a07101144000601585c0109400c01407070301a5079a03904045010052580d02d22035440001d0008000000410045200f1005094034002c000c02c0e0000b1140d60705130507001ea0b01c8a41100100316400641072080142e10595403400881601c4410307081d62460710340c0b90702d0313020050000c6e041c003820204410800449454400c0f454080840030003003d01440001002504800c50444103441450040f50710b0fa104510141e0403550b110f00c1d1110079659440911000e0488105000709502c82442505541054460308520644a40e510784500c81e02d80002c112203005158000450b81d0000b006200c04100d11110446080c00900311402e001c0d4240d1400c2c07031401420b8840e40702c80e401a400400c227401015040700e44042c0d200412240e10799295001c490303d1f03120030b01c07480c52682410403034500142c215503c42c0780d008005 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 156303714 1250 156302464 156302477
    0x60b010507050d180501080f16051b061009090b150a08070e060102120421020609030a030e030721120e03030c01090507091b140f070b1006031416 64
    0x41d03581ca42c0f07810b01d0711443d600032451003007264088040310449000200001d10346908142403a42400028000183c202c51407070010780e00c2c41d00d24601074000c4546a8000c40407d51036048850000c41e100c000c180d504400884020341c1c0002e24124600070808515005621040341c1d4480c0141c000d114551005050b030407030b41014001403005000e01c4a0310052940603607079000fa20b051400241001c0d41c00c1000100c4074020710041c00301c051894134041c0c0504410f111000e5980807400045c1140c0101c84585515104242c3d92800b010307400740103d0314103c402ea00f251490b0b610313012412641f001c50401042c4a0b0003401d003900c04240c441c5a102068440c60818500074147c17035010a0440c0d002c0e81c00501d943e0344078100403003004020030151006010052040190034030b103d41503030510003503000000c10000140003c194441010007196428148501c1031039540c8007516142c1d4010700110369101c0201e03207903c00090f03510700070f0080462418030503000705059136584400940010321402000b082164 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 156304964 1250 156303714 156303727
    0x80d020120090f041e0f15060206041101050714010f0f0b060904050a02090307080a0302060603010b061b0705130f11030402061605120f030124090612090203010903080f0a110403060b0105 82
    0x51007122403460008000001c01c0e446c1030040c00c1e1050303c1c00417440d03684080d03041508100196000c181e40d41c005d41e000c000d220241882500488060060380d8003e031101c0076844540c660000154400d04010341c010780240017111074000744008898000341d03040d802c000c04100ca030400e0b2a155115543c441d020b0600103040a402c180403030314110040c0c100c0b614960100b038500c020b042c0c04108640d4424070441c000d1003420102c00200d1a40e00400940d0403008068140e501100c0d1000e08c0440060000038110403061003135654420040c1034024050007881d03103445800381c1724060b40400c482c46140c0141030507160001406010300c3c000c3c02d420080d01c02e80142031200014140200040c091640707034a41c40f82d200d5040c039404210483c401d0110f03004211014210002258011011302c040300e0680c07c20100210308100114064584400000d5240d4a00700d01e00c0300b0544c0007140ea50040500c440c0e039880780d81e00d0020b80c0c0e0840d540c002c04102c60b20000c0c070003003000506903003107011007200c1803501c142440d0 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 156306214 1250 156304964 156304991
    0xf0a080405210d020a0b01080304030309120218040305091908030901050906040e010311121c1b08030a020301030b340306031a01081002091e01020304030507080d020120090f04 77
    0x102500c88680160814184001489104846d080c090070020000d103183c286590f030050701d0680240f15440040e42c10005000c2550750344000c1030366000c0d10b08183d86e103d03c0e041c5401411a84407082181c400d41200341c40506a00e41c2c040d9400c2501e0b5a1001189458403100042d1b400d9000200d080f80d2020b003c00c00826641c0c40c00820f83d009500c03070843c4100b410080401c10081515040d01d4000a512100e014174590504485214406116040410900d030a40b09440c072500104040907000b210004248010b8030b090790300a504882c0145c904010f283c941c00705015842c2c44c011040600d0100034468019510443c8a101144030100d09001500b1981ea554140c40c10841c00e09030070318994000010001d5910038003a416100c0940c030011403400200500042301a072031300805150424200119900c10f9000300100e901460300001100d10300381e51043c41581d0b442001c441d420042d401c01744210030319603146000c001c100d09180152800c0600b00c4091001240c4046c50495015494142c10302c03c01c7c = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 156307464 1250 156306214 156306223
    0x302161106071403040501030c05190e130c0c0203060f010b0304030807091224050c07110a0504051024050d0f0f0c020d0314060d0b0c0d1a030f0a08040521 68
    0xc0c3c80d5000c0c64490b46001c1c005400c90b80501000c60a01000300f151041c42c130700800c10060a441079080100780e41c50001d02040260602c0241440100e181c1000081c0e0b13541c1000741680ca140c07084080b203d2a50341d141c00304610540a105400c10741c50f00780003080009024030107642d80300703503545843d0341c48960b01c08c0340c181c12031a521802d0321071072a00150186014111001446143c0992500b40058280700c0d044050a2042c0d12010f0b2607040e03040e40c1800c055456a4903000207102c0200b0500250138808641161500d4903c202007052131900c405061441c00208681364400d015210f140c148400e1240317241c040e1003500642400b00d5503a000340d81b035601c02442121002c000030303070090551103891000038049031141e070300343d5100555034800c0014582d6400b00d0f064016512506640342c94580c8138003403d0a000d00140c403011103080010b12002d0b4000750070b2600c03100400f05c08448281500c2032086840b50300d41d610161140c84104400e00090925070220000c020700c5a0005580807c2605e2032801c0 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 156308714 1250 156307464 156307493
    0x120206030702010212361f0b030a14160b0306040c0e0a030b091501050303160503160f0c0509090604020907090302090a050f180607030902120328030216110607 70
    0x5002240040d8204d1030566041c9001c80f0900807500704684810086ca565824640ca20148000d480500d401803180241e041415203441c0502201d401004500e02072402c0581040100c44038420750b00344d0464061190a114200c43d22400340d0713441c544800e42800f001e000403e00c800140552002010b03880e803541c6001f00010341c026881d001c0b080c00c04071030460422060101c050001014000148501c0c4d40100880304c3d51604034802d04040d044920b80701d4218001d90340ca20610b521400ca0b80000e10444001c446e4107540310b8030782004050744800401c101c54030180e1303103090681c1c450000a001414505250341c0c0080e010305098064941d254000360140004131031420804e5124418400c04042c0c0c21540303900070a500c041110a1907000742031a0f82c0d040001d181000309a2250364110654903038000c00b482011450f0b0941c1d54038100c5400b08100c840ca651225000061a2080075015510034400e4507903809a490804059018544030380411105190002d0b0340000d0800202c000221070f001003c00 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 156309964 1250 156308714 156308731
    0x31d0a050610120209010905091c03020403030e0402120a0c120c0306050f0603040206070323070f050c0f0d020108091203100e01090515010c05070b0310050415120206030702010212 79
    0x49a107812491607104640301d42c82219a18242d5803603e00580e40c080605041d1514130000148641d1241e507546d1810255a01900205e07040803003e181c140d40c5500203105a9029031900a07800654a0900c03007240700740b00d82408500a01c5001c40c01c0941c0715004004000d43c4c0d1301d0107002c10301056100380111015104000c01181d5180c10402003030902208000a41c803003283c102e0309518141d00415154401d8907402410451050b02c0700c1079410000181611010b1075080b90b030f4860303c0c10324100c0c0765000c03042001d40b441c2c801c0d144200401c3c0303003103c582580340320081d246000d04030180c0e005589445c0040c0014082d80242000074940c042c2c050041c1d4800c102490070090614508000d10220410681103500348a082c24104500b0300c0380c4070444000c0b194286402c040301c0d08581403860030300255801c4810741000c0081840304201e0720812102c261074003158200541c00c2c8101d4690100b8095118000000d0101c1c01c21a0151610710051607000070940009864414843c0001555450840300c000 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 156311214 1250 156309964 156309973
    0x3010e0709020c0609121911060408040602150103120f050405060d020a09090b1e19080127110603180102122211100908010e01020d0c020a0309030201031d0a05 70
    0x500410f01000a0360704134601e41c018245505140040e0042c82c403403002c000d00e4982524848403040d42c030800f2111590640b40058581505252030094802d500c144143e800500c03032014a42c2d1214055510306040301c1d032014022074184042002601c1c00c10482c0d1010b81406014000001c83d5140c0344001d05a481c000d0000581e122001e01020f0300b10f80d0903805c800e03881881c11808400948601c160301c0d80081118980e40800210040002c5048030260b44000d0114003410001840d144150800d0048a1101c0c60030b656001c0344e800c0c940c0c05520a5a00980164104295080c46e070410000468028446444901d102c009400c000c1c0d0036a44880600d03021240382004205c950070510b14880640480d80d460301d940c0d14003544481c0b40700201c41555030b101c0c4005d041d2003005039010740c043c5801070545000134400a900101c40d83e000b074002e064111495420450400403951001c03545007123140c3d00d521404038260035034004500a00840c2c822825014849083d9000c00703104116441d4614030640090 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 156312464 1250 156311214 156311227
    0x1e140318060f0103080904150803071208010602030a0504170708070b0307020c011d10030b040c0804020f01050705030a0c050a0f08090a05090910020705070306060305030d0c0906090308070203010e070902 89
    0x2031070140001c05000b00204120014400140a24110b400101d011980410707200e04c40b5503090080c3c42150301621880c48002849400c201c601810181d140e000c1c0d031034180486e80e07601c400760307280c1c80383d07141910000d1030070032042c825501106142c03088180c5810403540499200e40101d80780c036440c1d8009806050f008410007000541c10421200300f0542860b01c080c91881ca90002c25440d02c1c1c8040551095000c1e10110302103500c20381c000441000010001d1100354041400507080040681c0e00303900a9038104540b000c035501800480d40255440720085180c20744da803030110781031007a003201100c403809154020300200b80f400710040d1140cae008500140d525010305d0204104800141e2101c2c0c01041e1290400107400c00101d031080c212440f042026a43d0322452500c10708040c0f55400040009182c11400f009202d0004007410b10124500800c10562102c071905449114181c031501e0005a40749001f0b000080c0514003a0483d80d10103400842e48503c0510081e041100075009201403a03400701c0c01 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 156313714 1250 156312464 156312511
    0x4140a0f1101020a020a05090604090204050a0b0109091103071803020d030305071128020609130b03060a092003011d010218041802091008010501080610151e1403 71
    0x14030240704240010407400460b40d0205560f800c3c0d030b100f014400c00340c1030005015511140c00c4800c071150700400410141c900603560340c0040c01d4000c1c8160010740e503000c011903109203d100d90b0403921081d9411a0441d601c9002c121420b01c0411600d13400360380010800001a120b003141d02075041c0c0310b6200480c6505c1c00741e0b001096001c80010b9880e46901c00003d0017800d004510f0f280960007640c03520039101c240d1030f00100c1d4140c404c0012240e081a407007607801d24a1241a40700c01e4190300218151500c54641100c91800d48201400180441c074506400b800c40c4c601400d090021414050004208800c2c0c4031100c100420346800300f16466500040c28148a4100700740c004450041190b04104103010210032150004032401c009000300d00182c0490980d00855514600400d4031000070302c03181d070b1240705079034499206440d0030464103111030011a40b4094101c2040c041501c1d030744e90004103d009194004e82000d0368405000b0310540091100010005000541c030803008619502c1905003d96207 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 156314964 1250 156313714 156313733
    0x20010903050a06090303050c12070509031f02030405070e0411010c2108090d0201060e06040905070803160201031b2f070608040c06020105070c060b01030b1314060a06050a0804140a0f 80
    0x310300e110b00b80070007502074025276207403031580c20818a14000e80c46180c01c2003c2840c0c4018006074902151200300401403c01c1150015803080384600281c8240560b90a1604a400310590f40101046000303904075015510914410030420301034007540130548040030b964000004030001c61400582d18401b00040c01404000074660085140f008000f00ca18010314404814009041031380310351b454004010030f00c401081300c40301609285050760368503c00c4048280c18100b500703200300c0c00f0900300500903060346144000c41508141e0382d00d44c5d1440704402101e1740d500e24a0240c09019110140794460701100b01046600701400441d00d581e2864203090610801c0c540d074540c442411a81400200b100d0a98040d00c2c122406500c00f02c08509a015180140c000d05000c0c021150803003444076a0006200c1507800110340c2c00402e01070301c11182c84036024484a0380c0b40b4042c501c041042003200000c07861081c04016403050081c000c0d00e888654040100e4208110301d5000e48806981e0326a0100740254480d = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 156316214 1250 156314964 156314971
    0x23010c0f0f180306020a2a1b080601080f070603060b030402090711030c0d0206101a1303051c0e0102071415070204020c010b0a12020108060d11030d050a1202040320010903050a0609030305 82
    0x100c08401c81c5504010440080c0e207c01c500400c42095000d0641003008a0b0390281c011b081c0210596101e076841c1c40f016a030728810318131050360905c200b20b00094424040c2c419103043e203448281d21071035aa2641c0901685c0e0710050180310402c00c02d466000301c00d40302072028020f0002e1060261408264480c0b000b440c002000e40201c8902083e45d2041181c20070b60800000c6543c84070507500d40b268040e25041c29440b025900c060f10310300520503009106c2d60f8810101c40800741c1501c3d41090006040d004a94400d401d009012001d201041318601a140110080500b030020b0b00280340351070050342c0407a00360307000b00f001840203039100d1007085001c0c80c00c81c02100140101700da0410664040740c000030708805004c1c0c951402582001204014002d0500805001c1d44002d13040300c400c8018818010681c0d03225800c00c1000a60508034115042114001c480480741c005901e501c01c5a5440d00d00400c5021916400d410b000301f030000000090414003080507403c1c001c0c1e800240002c0036003406015228001d = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 156317464 1250 156316214 156316247
    0x309151f1503111306080c0c0f01140c1c0e010213090203061c170f041706010f0611070302120a0f08030103060c050705030a030e01060f0323010c0f0f180306020a 71
    0xd0181d0034032100d12036848003c846440c40e220901e031f111000c0c00e030340300c0c4074440035001d55024106840001a005400c0b00d4a90640c8450740102035a0b070348c403154094018141008050340320300c84d0071217032800c032a04001d4002845600051a103640101c9004c14001e19911404400750044108030244c03070310781d2441c50f00e084822070501c43c40c09280d0320b405441400903030104090002003420040300100106031000303000040101c0c3d00107d40140110f03620102481981800c455069010943c6032003120030840341c6030038100425801c1c0c1180d081024150300d0000d51011442103070141c40100c0e8040f404912100c0c050b50070300341e0325410b500b04542070390500340503042032003010010980000d170000200c4600f465175180000d2416104001d050241c01c0940c03001c4041c01d404800070040c070100c410031080914003415154a002110105503013603c00e8180d84d4030104280490069059007d01c8a03e08441504d01c0d244204949040c1c1d0544010035580041d62229400b241c40d945041d00060003c0b00080030 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 156318714 1250 156317464 156317467
    0xc020c03070f14030f0a0f110915151305060d090501110a02100209060406030e0a12030209040b030a08040501050703020c040501060302180406050901141206041103060106050309151f150311 83
    0x2486446607841100e1003005041f050204401014003804054142c0c5801000b41010b100e420049140c0313000c02e20758030300c1c544240703907100c0540e040c18000c81c11101001e503d0725647c2040e9140c803040104a400c04551310010301e03260301910300003580c02c0c0708041c64043e03074076241e40e140d21400e0390003490a000c0208800c440c0e0301c104088291555014140c1d4111012131a020400380c00d070015007420710701c28000090040201540d01101d01e071b05500a0181d0540aa90400c5049440420140d4461130008040d01d610030401c42072005500c03910050103650300900481e000041180e01080868000b6400000021340c081030900d50640511494480402c0403581880103e09040008402c1131040c480da141040088843c0c002e113480307682d8881e810314411026200149001d040c8064048007000107103109000700000031481c580117200360f07801040000018401026075003140804240080c150100c41c0321401e00c000c00a00d0070504802c080c00005007041e500900032034018054880c0f405d401d030100d290 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 156319964 1250 156318714 156318733
    0x105070f050a051b010f0f0614150a0302070c030b0108330105060904060302190e090d270302030d2d020a0f0c1703090f04050402010f030c020c03070f1403 68
    0x18403005842520071104e03150a0340680118006006218880058140c1801c2009002002880b54403030b40031203c81da40070400c0ea803081820805071416070003080210748820301031407000a111f580a040d0a40c030850906000075100d0725400c0014a0903030213609981e009211032110108802c000810110040c0004840c03403001e680070840ea036005000b076a000c0c18003c541500c090b45c0ea5003210b00107507000742c02048070b40308a4003500301109080c00380c43c03001c8040a002c00c0800f40005000f20603c0342559640c0c0303040b00b0424480c503c90a4444103400d00840608010002d41c0d130234880700248108607101c404040d04814500140003043c612035500c1c0022000348004e80907004120403c210754004507440000500d0315242e01d2455454118102e105140044400080400001003180d0501203075400071010070801000160340080b10024006031010407030000d001d0217038100c1800e00c4068010b0352420320700503001c6490040258070504c00c40e528520100188140949862aa18000d9000e010341b02c5 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 156321214 1250 156319964 156319967
    0x204031b030515060f090405210702100e180c0f030c030402040b0108070e060c0f0322090504080d020a030b030115031707030807140405032b090807060c02040b0a06020105070f050a 79
    0x804403017000307000d0300024001400300403050110828092001c1c1001d69542e041c43d84044031608115801c07402001e480c2460340800780190480b88000303c5c0246660042502507542e0f84400901805840406905200070030002c1079020140d40700b025600c4240d9220324081c01084141e58510040130f044c451300300c0a11003859400300560b603c00500380ca80950301c0304901c4441d85015018190303002039010104424a9420403800d09056076101a060100f505440c2c440c01001c490068170010140e01082000c0030720303400d040c2c014051444507401c0002da00f101c41004a42503451640d15034202d802c400340b003402006503241031a0130308266100071504140380c5d940c0c05044220094480300a100c036900100c1044150501101c019050103070aa03414049038014486059203d00c40c0704031403000c0183c40310394003031140580b1011500c2c144010031600d440d18000350380e1100413a206907041603e84c1c0000c03420f070300c560750f200c0d0007800194000112803401410003403400a8060003c402c00004209501109 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 156322464 1250 156321214 156321229
    0x50a1e050d0c12140612011a0d14060c1306030501030b06041503120201021c150509090a0219080f1c1b0506090d0311040e0115030204031b03051506 65
    0xc2280820029548003401401d03601c105070780c03034400c041a080ca01110310380c0804c01c0d03010f405010180d0308102c2c00090079502e10309813030440d480c104021900341c6881c20345107480301c001d85125000384125560705000c0364042d8201a0f003203520006106d07000401744c8940041c030f150180181180d15041010b541580c0d40c010307011401410f542d124548030900c0c0f2404010858094000355404014111700e10f0003a5000f0303000c3d403c0190300c200d912541142e03408080e0858007135070541824450304c42102604200402c400c402e009880842240300d01c1d495080180c80d840c060807148060040d42c1075007145000041450400c440c0700b0b02440d9001a207001032841c0b64010741108041c1141040e20000305009941d100d4040d500c04050100d1003880e0500c1010f11010410b03030600c8406130340030b216000c12001c0241041c8240d1284142e0000845d004100301546c07428449203240c1a0b1a0140ca045e40d80d46882c07014840030100003c1e000c0310001d04004000301081645d001e50101403100e4411b1404000003a030305d = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 156323714 1250 156322464 156322477
    0x21030603051b010c0809061204050a0b07030b0108040b1b0406020309090a0902150307020c04050403080a06061b1106130f0617040c060507060e030a170a02070b010b07060b03070303050a1e05 83
    0x91700c030301049400c49540d4400903240280129110459140741034102566900411041550414518030214036214881d0081d284400b0f0181c541203125203c0e984e6080b04018010020244401255900da125500d5100148000c045960045484010100404c130f40d1000241212001c14a030900190060715400c00f40c0108484c0300c5c804686030358800a081c2e04012078105042d0b8001d00c0e0004010406411030303120760144c10040c804000081e128803065448400c0452050060801c04480600040001d9070a0310300c3c1c91702416842c18005442c180402c00400f80d046442c815004a038240140c551040c07002c0451881d0710403036070f9141810b440b614843ea2450050008026000840d5010701205400c0510740440d00c8049940d00c101c0984010015541c0810a400024007040450380e0206107009807030700306400926501d200d9280c000c0c48001035100320001c40340c090719410041c1d0b0f42c0c1d80070710032440218002d40b16140d468080350740090900b440c10790400074800e8219207500090b0303400015100c1 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 156324964 1250 156323714 156323723
    0x501170112031107050616050c0907050306060903120d0905060714091e09040c1d060a06030b0d0501020304081209030a0c030819020403050a020f0306010608040f21030603051b010c 79
    0x70381400b090f2800f4200889604081d821010024102821500d81c91040318400e0040090328007262850080014500060380c8080003d0003d202180e21480c10304010032009100034111030300000052001061500310804030b050030b0350340e10f244034103004c802c1c8070319030f409020b600c1e010b2010542c45505051502800c4910782c029403d14039203200c003100b20440781c00e09a0000345004807601e082c0c070341103076000030394020800d20f49903a42c41c0c0d10307120250119090088030020410b01415003048421002446003502940c0d0211108e01e250010400c284011402240901c20030388d524080002810f2020101038480003072940200000c20010380d1054100088070b82c189406421900c40082600c400e0710404480031480d480040c0c000204900050030041d0b40c0d1007590248006085401091b07280c0100741301c0d94010801100000300000c03220140b81c50401d1156814103000018490001d030400d520b400c0d848082031341c40304c040c000c1c4602080f01c1212035600d03280d84252145606c000802941e44000002d0 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 156326214 1250 156324964 156324977
    0x109180c0504170a02040f020901080105040507020a021c02030706050901080f151302040905070503010b0d0906090b09150604020309031b070b1207080a0203010f0b070203010e0d09050117011203 85
    0x4030950710540c1100d0040c11607040d40da5010b0712a40d1420b031074a0f5807480803442680740080003213420010b80203469144005842e44e00f210707031031303c000e02005d040d008044004500031508243c005a1781e1140c807112a050002401c10410305a206240c60000e0f04d40002c000c3c0300f01440150006e81c6c1c070081c0c03150311a00035681c203052074407003072801c400c08850011482e50015002c940742c48000d02c664080c2085848509051100341c1321000c1c2500c4903c0b0a000b803400504040002e000c95544d42d400542d1154400c2000140d02c5410f0f4456900b030f0303002580c03440c1440e04001300300140756094100090b0009011601185181440b10344199a4800c0075001c0c040d03482c201803066641807040c010440201128603096640f0342000c0c40102c40801c1c200c803400080b40c01d000210301d400406100b070300d041c3d440c42207001d041c3c0b0b0f0038040c14130010f0f040a001203a140d900d604941c094070500b030050540543c21501c5902e02641800005030000c14880d810390416110030004005100348050940711103500350034081c = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 156327464 1250 156326214 156326231
    0x1d01090b07110a15030c141914070213060e0a0e0d030c12020403060204050a090b010804020409230105010503011d06010302010813080406080703060803180f030a0f050f010506010918 80
    0xd800c901040c0e01c142c0c101c02103154608842d82c1c154020f0515600349907200c2882a00c0044401101d00603011014480e0f920104030490450242701603188165000301251f040144640c0014420070304421480100754481c40e0401000018440240e0000080d00d07052040686040c80c042d80c1da00311b4500c0300c0803d603c8012141d4002e000b4002400d0f04041c00b42e0540d07445849007400400f0358414403c4c0c50040c2c84a200004403404079209000f5400816541c84c1f1564032103400b00300c094429108107440c0c1c0461100c001e8515189480440310100b202d0700003240a40c9410105401c68110102c4c5040d02114011480056900400c45505499090922a00715100d41c0c0c174007080c20000020040c00140c2c0040c0210721690400010340c86406035543c1405981e896049180d200d000d00c2200d403c0d040c4418000250038075160f000d2181810000e000c03514224043e4940f05482c2200000c10765540e0880341110084040a01030241d11140a00b4054089807400c03410075040200c1c0d00d80341c03591680d40c00a9 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 156328714 1250 156327464 156327469
    0xe03270d02090c0c0c100c06020901090b07060c3c030902030604140c0a082e06030c140a0510030b0f040c12061401050703111c1d01090b0711 62
    0x4921a50707401415034201850031140501c85030388510704103c50380c42410030324002e03450040900ca0300850940d84020706d202082c1d84000207034004040e05d80c10311103815000b0481190070805804c6542c000c0d14045408041980080c000c00520791418100d0b040311007070440a035441c07148803546400d8088255240c0c00c0444001c900811503500020751601030301c401d01c41800b00049014510070b1510040c0d441403c201810030100a201c1d1090079140e811140311104d9004c040c410b0382054a03a512080c08107290400740c183c0c00c4075502d4004558100c0d01003414001d0302402c0505001040007907594032501810000042d0144100041d000101501d1701d010455036112010b40e03100b000c0024200748622a90314402400082001060240c618903145000418082005200100d500c068413402c1c41e002d41920101c498020380042c00a091280c405440f00c0740c0aa01c3c2549180d100d903545a140b0758417180000310b8402003078400e03e410007044400c06c0c454029060110758a4942c440300104101045002 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 156329964 1250 156328714 156328729
    0x50a03050702012927040c08060601090504091430090102030405090c07050625030b010e0d0503041a0403120201050c091e0909030a030605150703030905151501030e0327 74
    0x1c501c95a820300c03607400e50031103405c1c141d40158440c0848280064441c0d10042c2d440c1000c6880c0c80c00251081e104000c0c41c281544039401c414007034030420040010000710310b403800ca603403840201c03e14a40e00458580c08007404601203034064908000e8a00100800002e540303004070301805204141c00f07004124662000000c451501d075200c1d0aa0382245810110a148200e1500101000354809142020154400e21501c01320741e10503160071000ea60b001c41808210107403600111031600c01000b010403000b65101c430024480e000c41c21802d5450b4154907210000001045140055a05090901c04c2c0d8410100075102c1c0001c05840c000e1484400d2148464034500a00c0f0b2076800c0b07001e100600c85c1c01c0310080024110440301740c0301441007503511400d12945801241002141d00c01c248412070001e0f11980020b50b5042c011005c513201c03c001600340c4105642d0683e658913455504810107403003940c060081c50105900d2030301a41c2440b11401150540340502c0740200818201c00360b1020b45980c4004 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 156331214 1250 156329964 156329989
    0xa02130b0a031704050a051f08070c02030106150e0303070804050112021605100501080a02150d020415080f01090605030d030e0102040b1204050105161706010c0210050a030507020129 80
    0x195003401c2c0c140020b083c1685070b01c20b015490081041c00804641130a1401c145810221803c015030003c41c0094800c4404103400384c4a0410045030800d100c015079824000c0c0340241c64195441352a00801c3c5401818040003540b41900a0b0001e04c280300118104109440850f9402e08003150402d000100c060000d114050703804802400d840c154006208001a01504241d6509401c01c2581d0b00d803001c2703554070314003c00000d50140303824002030000000d14001d008a80e0051101600305a01c4612101c1c520a0980350b0714000381d41d00c82005000200342c15058011300c07034101c1c10403e65043c000804e480c0d0003a81c0c2c840b8149511030141003207181096044800400904240301d86039130713021100040ca0318069406554960800021a0520a41c8000f009d0780640b25100c51986200880622140d11001405141480745d42c020381d0f40075840d00700102002003043c0d600c4d2a40c54112030405000c071080504080e04585c5000109240f403031048480081e1304001d5039400d040302c000040001d0f00d500089 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 156332464 1250 156331214 156331223
    0x304030b09060613060f030620030106021b0108101202031e0109020a08060708070c0c05150307021507021207140307030203040f2907020f031c020f0a02130b0a03 71
    0x164100086018046452402035008807503040783d02900024030750030381c3c90031b000b50f00140c500254100002140751340304d181242207107914032140d24180006411143c00990042000d03800081c0c032400500c0300d600c8041031104c3e00342002400790070010f24544034251140075404a5408400310700007550b40400003400041d03840010110b80c446601e0242c1c4c060921000f040340181101031011544e0781c40442c035148140d1603076803031080c02e94071000c040302ca00b030301d529085e540c00f01102c0c0c2c0840c403900c6800507000c0b01c0d150480850b50720305180c00c0c000c1c40d1068100510f2841070010052040d40c542c0814100100354a0040702c58681d02c1c542021207031045d10701c4030305240e8400010301c7c100b0140c0100180c4121030f00d44070ba108013140c0e1650001d84466007c04403082890340048408201d20348200500102070014010005c0c00314a0380210f0b1810754240400c58a404901900700700842e4108200c4411035140409828440301c40d0b4003261621842d80804004251510720161841c2c950240c880700440e0803 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 156333714 1250 156332464 156332483
    0x10207020310060602070f360507020c12010c08010302060307090f030b040201020d0809120d0f1503120201060509040b060411070b07120203010b07030f030f020f0c0c101709030403 79
    0xb41e00103400248050311030b413009801103041c009044181c84044a08a60290708091b010310110303200180301091862852250401a0254401a6007180304291058203da001051042c100c1070412410850a12070104c8680c148090580e00d9a0700c01440c0d81140d41c1911840e40b00c3c2ca17501c109480100450300440d00c04604200e0010910003503c0a240c000c6000b0707002c1d1882d40201500450746110125814001c2da84180c0300c800740080003800030320700081d500301c00060000c3d8194401040c1c442008440c0f5003038040003010300c10304c0300c08007009800744a50300080014501e40030102c2c003c010001d0002e4000c501031720000d09940c0750303504a80380302e00c602403403030381c1c1c0f0305d00c034940030b1601c05064507480005858100c141d0f92020481c402c403410788031003031401810a4020340c0c007241c0c40040000024101138071049501c42c0c00a01c0c0c0090001c040428a1194031404410342c441c0c64880700d8403040303100d5110704c02d180d035100b44c11100c8644403401d50350010246982da150702a00e03521883d40020400d00c43d = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 156334964 1250 156333714 156333733
    0x2060c01020a0c02040b0301151502120a05030603010b01020f0c0d0c05040903020a0605070306050f0402031b040f0305061308040b0c01140412020607080610030b032103090706080c09120102070203 86
    0x144612031202e814404c82d0308006c0c001c044424182214140fa580924010b04108180702c168a283d0450310702e19000d10484040741c226810148040d00940341a5011460100c28050940340a0043c03400004085c40104014601c81a250340d42d1082500c45c4c50080e00380c0078104051041404640024040240083c0a852606e1030001d55a404540303095603103516001c0840c0a8038441d00904007200e4000b400501c3c0141d4000c1004000d500140090007040170003c0a13282030340c80100900001c02c0800c0c0301e44000340c41c5d800c2c45810030400a0402055007524145040040c940070199010384600c00d0010740c4410070900014014078002d00c8071200c10000c14100410055461045142c0002c2d42d800d503030f11902d03022400e8440e5402607c020b0b502c0414408044c180b00d02c00d5011001d45480141298898026001403540c600d201d020a0241c59000004100d098142005454014000c501e0442c50030324140c1c1000c1c03418014003c0043c411700d0103c6501285035001d40607200b901d0340080c1518800035 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 156336214 1250 156334964 156334967
    0x303011809170a0908060108070302040b060d051f060201021303060b01140d020711060306030607080a1d0d030e030304030e06030703020d020d0b040501050d0201120522060605042d050402060c01020a 87
    0x401020340f200004594100c040703001280420703400d0413a80075000603e01e150442c0e00b000003600f642a4501e401c100184180c0c03460038900d0007010b010725440c80d044c84111543c0301c5000401e803031036000303403055a00400c0101e440c40c0c100d50720801160380046000480d030070800c0040300c0801104592a00b651004512a800c1c04910750041416a11031981081d0380000903041c000780e808100c0754150306030407c20004030742900031901c1d02da0020030310500088030481081481628280c6141c0750840341d01905160103000e800d4852028a010b1060056055103007075a1b0086c0704119074240140118000300110b491940640c040d00c1462103070300c0080d901d07401c107412b44800030050640c881c1d00c0703541047c0000513942403192400c41c5041c0c060350750519070740c900034000700505030240c0110880c08407290001c080d240010b80c05a80903216101c04148036141004200c00d4441014a101c2c42c141e003a0740b20180036805429040c4139000103100800c06d5030700c3e400060b03168064101d42e40300c0303940001240386600313 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 156337464 1250 156336214 156336217
    0x150409020d14090d0804170d0506040e060603030301033012050703181e060507020a03090605030c040e070201090203010c0203070b13111212040306090320030301180917 74
    0x1160003250401400401e0b108038a200182a1401d1105400c104c00042c038461081c01d2895005002e00745011a421008840e444640e11240c52803c80c43c2e030b0355051100614007402101080b810140040005007080400207480b4441032100400c041101070720050050071480940b01c01c00c40744103282c4040143d040c0302134003080b03000044500003481c080000f811540244580141c400c0340340c0841e400e030581c6580c0c12400010a9241101c4152510360500021300c10340540c9118520590251a209409240c0a810300300c007a0071140038401c090040005921490080e10100c031950a0b0154842d1111310007039005000428012b501542052803040d480c0303400000a001503403082c0314808440e5603190344d81c100c2213030006004103401d042401090141c9801e00300070150140c41e209459802d44040b1040361560302c16030089903880c1e100c0355080141608030081056000c58075000c01c0245140f103000c05d4a030704c814003c000f50380108031841740001e9003035030040c80036562040c40011040811100742405 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 156338714 1250 156337464 156337477
    0x604080c062401030903051e0403051002030112080d0b13020307020f010204031a04050312090c13020909011a070213051006020f0a0206031e040f0510180b0615040902 73
    0x86109400120b680c03409030181c1d8000d024201002c590480c0040801100600340000b019407c0100500040940111200d4a4800007024040e440e950700c3c5503113070076803c0c0029841c0100f2441d00c10f00041010401000c00700391a10380c8031300d02071b50700c1a1103141080105800b000c165001800031100800504e8164025070003030076107800b150754941e9404001400d0b88a213000007406c420260884c0e04990000c15021604188a42c05581c2032482100d00c404014404841c0c0a025a0220381c840d4080d0500700082849003107142400c1d0329003844000496030000c0103201e01680802d000542040e031000410a8456482d402404520a05a018901000703080d0580d4400c1c0a00701c8414005032031030002607510005500c180282034402496000c00c012904020321400c040c0c0c007010540c042056001d00158492403103940201c404480e5810300c54908100300c9845014141303007501c440c081d0704200130300000003940084c1c00311080e51090041004c001d842607400008490204010640303e5454014000 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 156339964 1250 156338714 156338737
    0x60207050d110d0c12090509071e030b010503060909030d0c02030301030c0f030b391c18080c030c0604030804050f01110d0b010c020a090b09090105011a1b060408 71
    0x81901c0d0b20321001d9207414081c0c001c1804560303c90074110001d040c400318805600528149648140e035500042580100704842c1e4100084145010242d09403003210b01386901e095600c3c08111220074500040c080d440b0180425115020100004052040c00c204403400411840e40a101c5201070001c080c3d501e800a010461f010080030302c0c04a0510002a20441140d401110303402c116251041d00d44403180e0080640d0802d80e075096403901030080c2c0500300c1c0d90540801c070300455a845021004840300340203600001d2100307040c00f4205145841a0b2000349580703400c50117990342c901c80c0c544210314500c180140b040107400f4603000c00c0103154215021921440c0150f082c2c1c0c0101d010001ca09007220341c21074582500c040c0901405e82800010b07880a9042541030502c854001407540018801e091140c2c0170203007003034803050140c4e12410311210843e001740c0400c0007400294182415000c41940d880036002800c8030228801103603004039623444803000346840036545642032504028030154002e40341b046 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 156341214 1250 156339964 156339977
    0x106021c120912052d0a080a0b0a060504080c01080108100b0a03020d0614071e0e010c0507032301060f090c0504030605090604031407050d050310091508070f15030f0603060207050d 79
    0x6810b0288035581035800d0381031701c481503d0260030540648a491000c1c25040285568000d0183c250700c0701d04c52200900a0703038072015213031860640128940b204040e40c0504210752500100003103040000c0c2c1d00d1656002c0d08021a03240345907004075030503041c1e951010b540446620418070a10020b0760189407c101c03500c04252656541503801c0c0d83c49110340c11094042c0e441e03001d81d060424441d81d01411680014508800c41c11100d4980070f1070803510360025214441115003060348981d140b4055101c1c404040000e1100c01c2c50010048129001403196002d03803500ca4140004082c822000c031b0b800b56602c0340c02000a418402c04469071000221400c034045422030110181140310030003590035466000005200c80368a86000b00c425404c007902d0740c0c1c80a40c0810740410000704070f01405094110f1000c0d0003400918040e04a468564160711140461000306400d004070780051035410070400301d604010a82d01c00e1003480c10000c02e80c40d40060003151020841800300040441c0001001403290303100e1 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 156342464 1250 156341214 156341257
    0x90c08030703090302060901030f1b0e180c091215090705090105061e1614071502060109020f040e090a140115060804061410030b0106021c12091205 65
    0x6659100d41c50014003ca4040b9200f00014074203100189008a010300d800f0891a10160511096800c00f104c4c000100040c07035104031b9403079070003071040b901440114ae880b8031020200c600c00c2103042c005402c1400c0320b50002403041c0207441d100070383c45000d2204822903141c0400801e0b20a4004401da80c15006805000d800142c02e1403c814424141c0c0d0009100d02c2c580000840200002001d4203804d20080c80d05000e410300700303156204204400d40c010100700f030108450716002410459203400c1544c103200d800015000c00f584c00140c95054410051006a91740041c01d05440140911344c090088080a0300c00c0100c225000700d944002d807481070b1010744000c03050014850036075441e40402841c0c0c2240010402905114803101a08207016010009841c042a08600c2501d9000c1381c0480c2d81c1c121816023042044241580e20f40140340510160110340c1c079513518080c0c42002c4181540402c5034504a81c603403000380d07501000c1c42d00e42c0008048416138840304050003a030440c2c00c00f81160810030168 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 156343714 1250 156342464 156342479
    0x180504170a05031f1d04150510141009051903051218010201060303020d0f030b06031e0a0504050a080c100507030b2817030c0d030b0a0501020f0a030f0311030406090c 73
    0x10b0b001070b07882440d50005078140781c60011103049001007080d00c2d070703d00702d040c0c4c085d0087e1a84a0310380510b801c03180300c48040e403c000c1c16140d41c0319400d01647c090b41103c6104a005a80521000d080c1d032030845082c54000d500100b100ca00414a0b00b01600a014070381c022200050300030024a190005034001484c03443d01038006908071481e6110103005a04601d010045451040303c03042c06141c1e040c1800102040c1c401c0214996400444601122003425101d400c281d603d8080240c0d80904852002d2000e40352943d203042c1ca8203142d8800030000300011038252000c490920180990f880020340130003039841d1854004001d000310404060246905103a01c410110f45001c1442d580c00102c0c0c1c12100d180e2600352080103031112140301034400d02041c0040c40340e003641404245018101035401198183c001c1d003c20140404640c8994155400074400d510f2508001c146030a03070707507014140201c208411440030343c06080c986007800c0f0000030010811041202950201c0c100e01c1c0200d0400d041940c40310031 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 156344964 1250 156343714 156343771
    0x30504060b1c03050a02190809030601050909070515070b09160b071109090307020303040602070504051e040f020103180f12140304120903060c120b0109180504170a0503 74
    0x180e04400600103542c80010034000c8000f488000400d2040b01c00e000c0080703070f284040420702801103820003000130703501032a86420000079024207000c0b603007482d060811555840c0d64038000c1c13140a000721020f80e070803c09941d14600b50342a47c0e402c025840100d180c880482511a04070981484e00a141c01d1404203028603003000b550001076202c0110403408030403074100b004008004103025144d1008214800c0141c074244094002400d0a400820290f8104410041034030002041c5428806610080d15044280700400d942c0142d00150510208200c9000403005444a02da42c40c401c110b9540e104803c208012401b040028028a40300c132481406000458100d0588004030000f20070503c04a004078480f0b1410f8502500d0034148408015540c9d039a01003502c94032020f040100f070f15840c000048125500034000340c042e0034038021180f107080040c5080c02034007806030115099036400010b0104880e41030303000d203500d07804949a42c4480038000c0c0140340380c1c011545803103400d0120118980b40001a01c = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 156346214 1250 156344964 156344989
    0x60c080a1523030106030311070504020a1707031b02030405120c010e013605030c030106030b281a01110a08070f0318090c110a0c12020a15030504060b 66
    0x10410307400310315144841050440002c00e820307040b03100031221081c41c0c1e82445103000462080e01d640c4610886000e100e401d10100340c0c0228001c60041000001040d8000c083c0710b05400d061404051645903a0021401000000509417400f884030000e02103054001000d0b20072290200c84142203215040c10703480e220000b088402d40820074810000080d0f60040041c1c2c00c642488074007101244020714580000c011000040b0107440510a00500483c1018400d9020600c81500240081032541d91030001d440401480108183d901c0a18150000d4852620354804481c9000030f01070407100c83c801c0c107801105c510106000c1403220942c0040003801085c0031608940000c031581c10807119448411000e4071a00c0d0842c00c1210068803040845000305a000107000b44510025042d01c11501c040c100204000d000750495000400000000722050354441c15a00d070b600d0700002610051010030391440c1e09802c6407410041c08018800a035906074445c52141c1d018240c14020306108105120300b510b91034 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 156347464 1250 156346214 156346241
    0xa03090f032a1e03050c0d0806010e09040302150a020d0f06052404090b010c02031c0815060715110a0e09060d02030a0308060a0f0303020304030c14010c0b0c0f0403060c080a 76
    0xf442582048a4985059420540242000382c5010400048a81009000d138906000b29001105105055a100c41100c2801c801610390b0800c1d4185500c001c3d40d1820710350079502c0c164401c6000124021225010b40e50b2a2203003401c00c0c0b00050b041c0d203008000e040c0900a25001c1c1c45000344034100c071010303090807060340b116a94400d0724107820400c3c40c40207064004403040c180042d150307001c401030310204580d0f0390340d0b9080380c4845401d0030322680003000181e02510f0320a940054041240c90366031290101d0715007079841070000e074030b0314000b600400103044803400036940307a40081110002075030400c040c00e20702c942c21106004181d4487c800c000e4210350404000e07404d540a9000309000038016000241c2010000f0854001d880e52068a82d40b00344c00b46e001100141c01c00300c1c007002000020101000601800f05507811807100d947d00091184110540c040c01142d00e980105102007443c0d000c4a601c0300300200d40c582c0d40d544a04285000d0244100f540c00040c10300340c002051500144104c21803010030 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 156348714 1250 156347464 156347483
    0x3020c12240406060b04080f120a020c061c0e06010618030c09020912070b0c1506030a08030a0609020301061e03061a0a031b02010509150405070b0a03090f032a 70
    0x21040e840501ea94000d008071126540e03290045640303501000544000c204075802000d007600d012500c18100750b020181010f15001c240410a0640d40202d110300d20202d080c0d48aa480d100040d00f40c1c0303500407402c2d07040c660262030203002510300d8801161090581d01640c0312403400c051105030b100701c00d0109100180018810000030300052440d5001002800c1005091001c0b10f1001401d40b400c05550b0b50115410b06d01c0001e10104211052003031880d0300f124549103540e60b02e0100e021917200c0c07403010b80c010111a40000011800d4000740e0007603003d0903000e0011922980c43d24000f41001e8101c011401d4131200c48441c0c4c0c15541d20078043d140c10f86d00c034100e16405103010043d6003490b80d0040c40303800c018941c03100c0920559510b26011625548945c0d40040f903203040400015041000b00f0904810801030701d020400440d0000a03031400319441c1c001d440b6030390510184210020000100e001b402d401d814103c42c005e01d58851082241e055409a000c41d502c8040310039144038400714507000b80001003 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 156349964 1250 156348714 156348763
    0x90326010605031303031409160803031902091305070e01030f0b0a17010b0306040606090c0203040303140d180f11040204030c0b07030c080c0f010c0809100509071203020c12 76
    0x1101300e040b20068880d00707000c03800d41ca180c09400034044080310342c203100d540480f00c030f485071844100c0501c0052001a02079440c50600010a10b04070f5a12960405102d400190510040d02c544075a281c2442c0c80c02d00801c12810000303401071180021168460000341840c00e04000d0890a110b00b0803003010050000600910b8445685c0004c900420390780c40c155640e0341840c5150328140417240c42184503040c001404d608221082084481d2003055000319070041c0000e0000a40040185048484221905450f0113800307800002800c191a010b4401403156102c080801591606c21600c991003103000072611b00c101c4c0284001c0340501c2c400900080c0b042641004440b030a500146581c0740286042100300c01580c8440c0c1d610340c000b02c0401e40c9640201440c9407005028843c10a21807181d1402500d2820031013400c9075684c400c40007110255561b0b201040c0c0741d0204000e142c0041c4103c8455000e002d942d07003006074585001c100a18090001c02000d0100042c02151945e00c004001010142540 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 156351214 1250 156349964 156349981
    0xd05030708130c09061806060e090117120a020d02011407050913110705030d1b080606090a0305061009060806070903030f0203070816050c010e0915040f09032601060503 74
    0x2c460260a66002588940c00709050708180100b00180881e00070200d5200c00e01c00c039040480740e40341e10140801c21022a0b1308020341d40c20000360304403004020040e981c22041c202a50401200c1074140b41e80325400551070201c2a004900c03004101e007690001c00030064640c40130440103008a6920300040d43c100003030403113071900b49130a40100250140002d41e15101000b14642030b406120207a076130b070344046034500100307201d4012071150720000303c0800215490110041c3c002000580780038030400002c200c5030019110070848000841c2c0003c102e40b00b0303081981c8490b884103414011234507818200b41c0040788607500040d03064046d003802e5560707690040c9580c400b2130721440001d0255046000030000d520125601c0300240c44001c10480c1e440c03541100500d006031510b00e00e0031500d810300c00311456540c40c0d59038900545912540c0c4081c155901c3c03e0b440c0000e40101000c0504c0ca01d01c91130080208140f5600541d510300e40101e6110000c03281c40c2040e050041c40d03109114500010341700f080060f4010 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 156352464 1250 156351214 156351241
    0x13090b0a06050a1803050d08190605010801030303020f090a03031d06070203061f030b0a06151b0303050a0b120102090306060607120f1202120a1b0203031609050604080102030601020d05030708 84
    0x1032418130003003c0c080e84a42d565414002841c1098001820142c18045000c03da0110305000c044401010000603203484000703070102505100190500d513010541c04c05194200c01140e0b62010002c1c1562611a142d1030003900380c1040f0004845c01e500807502442c502d040c0340d02251060ba4005006002c0c940d51822808801081111720110030955010004005014004494052001c104005c03400d507081c4403410040340f5210000740200001c0c0f8a400234503c0304401c03503024103a05450046200d80e16010410060840e02102c181c004040da141030108401c19070117024818003c8040d10001c1e2102d504201c0c041c05942d0001d0b0042c040c00d14004c3d0001d014240c020747c0850581401c0c812020000308200c1240c00ca5541c040340714603010100640744d40d45109124445906204203514034082e400025503e01004100907903401041691690160199030503000905000304065170311616200c241d4040d4006540a034054807411681d0548103000303000b0b40784554040d5076420069590103829504c1c4 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 156353714 1250 156352464 156352487
    0xd0903020d0b0c040e0c0a081b070605040302030903100902090105040c17090a08030c0a0305011a0f0d0219050a0e0f0d020402160204050702160504150e04050708010213090b0a06050a 80
    0x60f40070440000c207800f03c110310314401c0c5903409403d91180c3d80150090240c1c0001000031315885500103c100c00f42c802802a40e00341604402c00103503590b504c2c0303400ea1941c407400940720b900d44140c13404d08040c1c405503088450054420740e40b04146903602c41c1400155005446250007044074840050b80c400085410306d0b0380083c08500f158410f02481e118a11554010340e4541e4505c03d001400d49d101c6a09805001d0051900a92440c80134107610068495030042040100e91018001810100702506806403030005030311345501d001d80210403402509647c4180c007585c0101e01803160480c928600002c00696940014018a41c1030180c0c1d401c000095104030940900014001c2144002d078640b842854818030b5103400501010310301080e9803840701d070b0a0380103e00c280d0900c21400080002e40741d40004491880d103003c692070720b607403a1450074190035070028510303036101281d042013241133010045d0827124903581c10444c649011050003460314450182001296040021440302481790486105 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 156354964 1250 156353714 156353731
    0x120c0a1b0b03131a0601080c130503030a020307050712020307090f180c06020118050d0f02030403150c090b090906060d1508030714160303080a060305030d0c020d0903020d0b 76
    0x4069448501c41d141903042030b121610300c41c80807a0208200103a0b503401d00c03650584c088800e00646400000202001402420590490b10200740c2c94480a01e40350640b01038003008064039126a4082c40c029507070341050760700703a9203441441d000045442070820340888043d005009814128101600a4054071040c000c1e00d142030340d51143c8065038040d42ca8131141c110f2081c86150402450008002e0a540040c220101d80c00c0c0c2d80c0d003030100011030000b07907030204940750b041415085a551105901314041e503800a821002900c44100300310070540c1c4284040a11911150215034403402000114040c0d0180306402c03d0120001c50403900d061800351542001c000030100381c01601c81071152600f81c0320703400b0080550002c1142c0e010400700e4145030142c02c0400d801000d0a00b080807a00b01032004520014050040d0200800c1310049035810500c0a940c2240c221717503503401c9007105107009100c4c1f18a0300006004410318007030901e10802450080380c0d0010880c4410b0034441c0c4808500020191030b220 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 156356214 1250 156354964 156355013
    0x90103091113060306050606040f0504181e021e03060f0a0605100806090a1112060301020d020a02160509010b090906040612030207090b040b090c090102071a0c120c0a 73
    0x1c403595030021030b9090b001d501c18020402920b90b1070480305036a03000d050648219010b1006100420101241008455084401181c4072641012800350440503c0000d080852088060302084c1042078101d80c07800c0c800d403030340956618080d80c001c032041c0c1c040c500d090f85070f084600810200003046d0400f60b0007207620382000500e940e507240000c40c184018503070305011070100c10070080c9918010400641c4a41c200c0c0c4244402e030440048060380f440b40c9070a41104090074008036501d61000d5043d9107000441140841d90b9006010029544910783c0b208000540804980800c840c14011040c604880d10384480d0350030a0f500d001000301440005004030382040c2e680100144250b00d070300209080c18000c0d0003400312203043c00001402d8030314000030a4040e03030401c07100306c045440750941d03190311a29419649481d504a03800403800d0800c1640080812800f00441c0125942c03100000d1680f030700300204850b0003a030000844800c40c007405000c0c860f036800c00c0c0f90b2800825802100d07010703551003202d1900b = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 156357464 1250 156356214 156356243
    0x2010e120d02160504050c071b030c0311090a0e0d030c0c120306080607020a0b06010c2f030c03010912050306060c011107020f030303090a030e030c1c06050f0c09010309 74
    0x192904a4982000d401a4040f440300c104500760340c4299005402d050b44c0a000602c0d00c484082042d20070000d0040030b03444005000c000b400d407078079520006036501401c800320080e0342e402c00c1e1706031500449405106440d20030100c1e503014601c0c030a088a02031200040c0450540c030718001e44c000c014241c1c3c4102401030340860080001d000d05011010784c22551000074400c1c0c01c5c0342285251078401850b45d8299440f803010707803003c10210311503a40d0118003460610801b1007246041c005c5103c2040d1b1402c2020034910a800031a030b08002c0c210840c0c9000c1d0100e031403285001040509a45c004003000e4080035000324803d4032580b06070021584480302528a529003d0203001103800c40e03100400104c8401004240e0004500e0304840700034045908400541c103500346511855128481400d005050021520130142c2d107440600c880140c06600400c1d0308a13041d00c44c0380046c0030515022088411a1130800086d03110030702202c007130340945010307a5028180300320f00f070041d07000740704e101001d8502444031030341d0 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 156358714 1250 156357464 156357499
    0x39040503120406031b080408030a0626060a1103040602160506040b04020a0b04030305030a0e010e0a1109060901030308040303050a14150a21080f1e071502031302010e 73
    0x201c4a00c0307800642490740d960701d0607600900b102d0880100b0150900c021761340e220130b19170021200b80c1003904020b440d9030700e49031102d0b120300809131980400520444a079803802104004600301460b08001401d030303a4290703101e0494008075100c03550126110903003440070802140d8164050305030f0104131800340106103651b446070362030b0410482c0e0885000018804000840c00e08001c40320040c0010184141040c1c1103941c050058003000300400c69817940d40d120310b08504025000305403407030615030548001c54103906140051492010a06015050040120312a810400e10480c122030309a510f00300710340c0b04da5804401821018000014403a02ca40303202d90b19907082080d141c091003041400500c20740070301042c000030604590250140c1c080000660120380440441c0d02d00565000f0400c0b07954100c1c8400700784090040c918000000c03901c002081c07085070000c900030602a0f000d02660714280c00410040c0d01644011220004100c00c111500700040d4091044110740941c024803401540340f00146 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 156359964 1250 156358714 156358723
    0x60d06020309011d1e0d0e040b030705061b0606100912080705061501030c030510050d02060f0c01022703120f120f0618160f020709090305070b39040503 67
    0x1a420454000c0081900083d00e038481c95005c0100d440083c02410006041c0a49110b04410099000c0c0b41c440001e035000351307400e12001014180c010701c0542c031182c00003c0304100d10703040c4501d181d240c4580004510a460071540c0d1244518542c0c0d81c407002c4508040390056004141c15085424003814056480000d90501105204265100703d85010700a50b500050540d80788655082c00d00d031a09050194081d01040d41005480090720501c0c1c4080540c404180144224895849104130108401c0014036042d002821580c9400e00c011501c1104503401340250702e11001010b5141e40300380c2402c40402c850034050300d4200e500e900a9070400a0f48501c40141c0482191440c55240202040056520b065a080c045625039001c0000c200d18050300d0340b0f0380310311001242d0814040100d64940e0040c3c8200180c1010308058001441420000c0c40c01406580000e44104c0b20861101c00041c83e9582c4089414090302002c1d42002c409040105182281215a07424002007401000003056a443c20003 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 156361214 1250 156359964 156360011
    0x11e0312120507050306030d03051902031003050c120309010c0f060504060902190b040e06030a1a010305060c09100f0912030c051603031e170106020303040c060206060d0602030901 79
    0x200d8954901c89491081001c4403401001c2009005040c400d2007010384000400101501c11402c002070145c50305030000095004032080381d03a9042c0000104182400c10400350780403603109104a0700022110004c0144101c07041c605000c8560043c4512036041d03216915035181d85028840c494151450b0340c0700c40066603411101664002d44940c1c40b841141400c100003036401c4440d40d10f0524144c2400c504500b18400c0c3e204404c0302c0380d003040c045400e65400748148401254401040d00d0b00d00004c40170044205803d1000342c138940601d00004940900e010102d07060040003c10b28202d4800c4524203642c1d18190b00d803d1800c000c450080030038203a0042d000341030018021780310717484103601078a8001d06e0150040e24000c100d1070070301d20401c0083c0c0c01101c040c0b9851544020380c0340d540300c0070804540100e0704814401d061541800000350081d00400190f000c3c5001e03c41d0750f450701343c440358182da03211416030b5066000b031300401400c4042446907010355040aa4400046030140b0840409403c01d400c09 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 156362464 1250 156361214 156361217
    0x402010c110f060c1f060f03020f06040503011b140a09270c12062c0a020702100807020d020a0201050405041505060307022a1c03050705150601030c020304030b011e0312 74
    0x14080c4172031895084800540d45240206205890802c14003a50394003907488001d01501d0350103501810f680d10307801038134090800500200911703445d0201c6042043c0c0303846611030100381407a1103455049410002c44241c3c560316290700e0801d82c82d080150300c407071034044402040c40c4805410200e076074040b40a804084042917035084040d100031034005040b030300305030312000785004100e03503921031283c201440b081e20540c0e5801d861078030303600d20550f5006071081400003035200704d54020440c0342e950005a428011800d0ba421030b001440c010905907915001c8680c0030740070460034803080201d49410f4108035400c0b072089090312552641c45021400a8006448000142e0030050b800e269400000700d030124180d01c1c2c221880d00e005281d0020916603c0b40d403040d0b02804a08041c1e68042c913005904031212241d0000466080c50031faa41f942c56110780544805002034104902e45100e01c0c80003003900d00b0340790840b1100c84140d207082c0e401c40821146010014106020960000c04201000503007468074485 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 156363714 1250 156362464 156362473
    0x903100f0c02120c060f04020102030c060112060b0f0901030602090604030501060e16050406090b070c0302270709050306130c050a0611071a071202011509020c060702060402010c110f060c 82
    0x500000ba04103e00b0040031581c200d000d1012819581c3c0000707455401c091066130b03d80041d140c0f07000407800d40c801d040078101e0921a49000003100115150780551041c0950000c1048445c584204a0804031440c480b56114510300d00600100b54258010604103100a0034945450b40c0c0c3d65500b0b003074903c250b01c185441d160050810086040c1400321400046141c540649800d090410103400708099001c0c1c3e6840603000318640c001c00c580c00c845500550340081102075044c04800c04960520592030207011403080c52000b0400d014010741c110800d451000700035101c162354001c0104202420f0b07c40548026180d6400003071035458441c20000545070b80c0c0e80b0b801714404402610303403800c2c08a510091103203035906240c0203d0740b01070040e6800254851608405440b01810480c09441d0f02c0b28104840d00f0055070008000e40c503075000300200706501040c1d0b1007903640d9140030b83e2182030848019001c03804c15042a0f001981e480007141c0d1810b40117000300380c0034640d03801080f0950070090121a8a030f00 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 156364964 1250 156363714 156363731
    0xd0b06040f0905041b0501020a03110106170f0709060b16060609020721021c030e0f1605030c2403090304030f03080103052104180b100806010914060f0903100f 70
    0x100907414017066042500c40c41000b407502000030f5583e010254080c00304001c0800720841c0d41400c0d001000100700403140c100c29240c0c5e00c0441a103c048240485980d4807070240002286026400f54a00b2200d641803c0d40c00d24050011031410749154400480c2c0340d507035030301c400324200c041c51010b000c0c0d083c05550528003461000509880500652a0010540d17115070031a010030302004903118031040a0b8030300440c901c00030104503441d0002000358140b2034000c100c3c0d40414001208186801c58108608503000d81c079000042c01103401c507043c140d03160850500c9848a20711010801035410140303550490b0300e030035503030703264002d004503256411000120104010024414104003c0204141500031007450300c0d0385c0e07007403003804c0e03c518440d100b140c0e006040400d04411240e8404000101c0c09850301d0307000c0d034002400400d6084101c8505010580151010950407440f44030707500840d10180c052481c0440030084102d080e080b8441c599450312500081031407d101134001c84001340c0c45400c0c0454983d1 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 156366214 1250 156364964 156364973
    0x3020c19140f03030106140d050f0a27020d02120304091b020f06070806030c0d06020d0c09060203121308180a0b0a0210270b01060306050d0203030d0b06040f090504 72
    0x4114105800e59544240301a610040d800310441c5d0454000e810844898608400904860301035141903005240c60502080f070042c80d1007071050b101c1e44401c00200a103c9244010030700400b90804010710740306104580d0001800c0c0b43e440104a180028540040c51941424152071035001d4ac00c0000415210180512a111300b00140601c01d5198006040940c84800070250f1b03602c0018041c2013001410000b10b90030362020301803000e0000010708545221413441c10208060750044103050344440c5400004500244640902010740e00241e0186103800c008002c60304114a001e800305151342c3c2d070000d0041c0000c00ba0710060116140620750750107900c08950030400b108001d0303441f548503070000700b286007040d0398042070340034101103080340000d034500c2407641d500e03e0314483c0c850030500e50a03c4e52208051142080c101412601e280cce2301401825210740506c074901c0031101c03000350944e00901a500c0c04401a8011100c0d030900035021609055807501b42c00e42d900c11503440200560340d0750b8280420300 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 156367464 1250 156366214 156366233
    0xf0a09060207060e061206060f0408160807030c0603020d0b0406090c1101051308070f020d0b0f060303120a0e160f0302010201050a050c0304021e0405040b0702060711031903020c19 79
    0x105103904160240c40c0c441008907005d0b201b810308072080410200c00040b803d94408080d103066402d200420750304c90b911030055079905c884104005080202c0c0040005940c000050900309580d8880f54401206103002c800f6006908031070003001409d6141e4170b0190854540d4402e08000307000914011840100e0208050400c042d0340340c800e40564140810840c2841258101c2c80050341c0c002030499031040f090900700035045c92f60300029440035404140700140240c04440074020707250311107280d4468881d0000c240e6244140b50181c2401010000011603140709680030006581c1580c0a994103901e0030000d0400300400303a044844051550755050041d960b091166990107550b07c00100076508096140380840e01000740300a00c241c40c562000d00c40c510303100300d45140b079900283c000e200301e0520b4603028800100c11104000180300e01400180f83c140710743c0c884008000d00c04099840c100032121110340301c1001907400c1040c15002c000b440c0242d0030420400250f680c448141e103071201424500b00d02c80d13 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 156368714 1250 156367464 156367469
    0x5070914061009140d060b03010204090b091501020d030f09121e0203070816020616060501170307021809030424090510050301090203071103070501061a12010302090c0f0a09060207 79
    0x1003018212003072050740c0f030701d04130303c0700b00c04049842d03a4120801e07240c04400303441501c00319a00741d400428005455411900301050f80d003021a106200f80e90703000d07110104061070030440e42c0183c0c880184516104d0086d8840b07180700815103000b01e10036160f5212500e1821290f007800001500c3c82ca0300340c5021110405800c0c900d561440950700d4003510340c503101494003c1206003500000c41050b0101150f03201c034116107820780800c02070480f4010905080c0001d040034842c004403200400e10b030390b15a560100031105d0b2550300600424448a1100481800c00d0000700041d80c984010440401c04805403144842c0050403248035480610303602c000282034130100d52240703011b040700041440b40182c00078242c0e410b55036110801a241da581010403101741d4401c050440c00345c0800140c1009004064101400b6220b91041040402004400c3c1800c24801d2101420090110700014401031900b00304081d081654000c08505045190b488100c0b5644402d03502c201080070114100034443e014000c0300c00 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 156369964 1250 156368714 156368717
    0x9050c090a1103012d030c030b0708010308070b06060c0102180301060f030309030b070216080c011d030304120501391403060f0a0b0a02010603021822050709140610 72
    0x14100c000e00442c075a400107005480074840c5044014110504000c1582c40e06201c1c0354400c03280940d2824880080320b0140001e6501b01d845100041440e4040d0080794120ba610442c0a0701d8030420b40c440200d407110140c0701a0780240304001c00982c0c140240007600440240440710100141c0803030400d42100d1584d4040c041c80350701c0b01c0d000c0021070f802402c0741e01200d8211034045855035548074224144400c0c2540070f0980d000c062004241d0850005092007010350a8a0b03107080c4031490b1810060410b5400c0e1050b6040e407042100388001c3c0d032195505a8014130850001c148260010304050a0207000403907030302c2e841c903000b052142e507102d0722070220030014660400404080c0168109000d500c4000c180c14014884076110b2991074036042c03030a00c001c0400108198170b81d145107000a000e00034611080e0304c29500b2a00d060040d080c5069003a000701d6a01c6503060140c40001020b0100b019800020340c1c15020701c140004d402c4000307024026450882400c0d2941c503103081c00400407004c61180c1d0a50 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 156371214 1250 156369964 156369971
    0x9090c150e0f122a090f0106030b01080103390b03071407150b0616030203030a0f14040b130c03080301090c05071115041e03050c0d0506071b0609050c090a 68
    0x7103d900824110031300803200b440040f45507011507003210381900440300b160300b01e200c04081050095640d407603513050f10704c0c0eaa000e00c6004001001140d1907202808007500500001c404050100c0c0070014102002c0c03058420900b40c9000b24450003084051a409910000400820010791a6000003071100890750100b4440c100a0319481c0c03429030002070128401081da540b15510459503840c410b81e20b11044031480e814825105190080d202c1d0070a89102c0c0d4802d0400d4040350300031005014041d0506a0410343e007004d0790311500da00c07a00403030180c040c200b216100c0307290038041031100d0f83c02000340d40901072065880d45069a6001151081d840300c008000301805648002181d1412803483c2000407142c2071441d44a461161030700344216032003928089444400400c001c184081000c044a00aa041c1ea070701040745001e10198520720a4024181d801c5880081d440760b0041c0f404814a18040481c00300081042d030700d803421104400e0301514164884241c80c42c0c145400f00350036a02810110060 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 156372464 1250 156371214 156371239
    0x60409020915132603130e060a080604060f0222060e0d050a030c03051b010515041b0318080a0305060a090605060702040b0d060603030507050609061009090c150e0f 72
    0x205051411805104034000c0700c00f0503004c1a8452080703408244800c001075030b55460350481c0b03c4001d48428400c2e5082c10702080005800e624290841c2c00c2141d201c0c00190403a070b6944e0f500d503401405080d14501842d50f00b48040700d00812800030340c050942200006261040c14400c0250403213802801c564410128042d4210005070081112682240e05041a082c07008e05440c0c1a107503805141c3c0c182c20200c248160700900032005410150042001c00d14101440d6020014041034800384160190b40da100c021100c036016200b5408038801d07150094402c510380d0700c26582c030011a8400b540c0200000d4680e01401541e00c3c0210000006052117041041007618100128078a03000c1d091003e480780744d40c2d003450150b940f601a042100c0d00d9111808010030307510f924024046070001201a02c00f8451a000645031400c00170300b030703401181d00f4100080b8661820106001400c06101c04a440302d640c03550000b0300080019602040c14410745910156090060074403455040d01c0b14154402d007180c9914 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 156373714 1250 156372464 156372487
    0xc03171501050306040603021c0611160314160303020901111b041104030b010902030f0f0405150406090506090105160905060a11120408010b0a05041424060409020915 73
    0xa00c20345000070709180d6200d0b528100024010012a4401fa40004c0d9860001c0391900d984150501c04a1042000300292408503100c1f4040c0d009081401502484244a0101290141d4810310b400302060a40c0d61614079000001440c40c941400c1c00c40c0820b4004c80c1246156801c1445c4140d010b490f1001000c00c800d401084400b546c80c0d45404500036641c504030001031a0b40c2c0d0007118051a04410145681d5070740d00030640080d401121001c0c1d4101e0035101041c8041c00c25a805409140c01800a0060b0220502e240403869030242003180d41c5030b0343d010307004000388085c05a140710f04991800050f0528003000c84c102d1044c05992118208002158240074a40c1d03001b040c1c500f410818946101ca9405030401d080c80e201c41c3d43ca00c101c030f800000c2000584802c05400801c1d20000586007440d14550b5813050006481c49452882001c9000e1030010b10702c85681c0030310058072002d01808240201c54000403442030fa10a4100c41910b980000c1c1900c0a81018074200300301c01c0c00000c0307582c1b80035605c825 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 156374964 1250 156373714 156373741
    0x7150c080f150102030f1306081e0105310b01080105010f05040e10050a0803070218041e020f1203090405010b0a120903032c06060109061710030b070c0317 68
    0x1200800d0150380c00d0b002441c0d200b0403c0d11103480c4c65000141e9074400b9001c11140324900391080c400080d104100081442c55924882690010502001003107a401c107410080b1030414072040e020114070040b0009461795043c00407280070392203603400080e1403101000050512005810250500080480c0d001c1c01e83d40c04011103007100c5540b08001d40c40d4840151400064185601c51030b8804011540424514000700080688502c02c844d10360b0030b0071036141d1002803002c0844010f070814120301c1400150000510010307103418801051030244801210016003003500000151420b0f5001086142150800d4800c55026200c0c504402c0d080c10b8a80c1c0c40204104400c4011000c00c5456140d04010940207403c441890f512418100610300840e905139031904510341000c402034820031010500c0340d4001c4041c0c0701526840d584451100300602088001243e02600b5100d08541c141e200101080d00c00148074000d484564601d040d18042e81002440c2206840000070704640910520502826401 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 156376214 1250 156374964 156374971
    0x31a06060f180d050a080315100f18210629061c0f020702011808060601050c1c0f02060f01060e10030b03330609010e0c0c010207150c080f 61
    0x20141542072012500007048000010418810305d4481010000c021000d9172150b010a20b42c00c2102005004102030b60070305244001c04101008500c8101612070350b041d01c44c042c403450300c1c107004558ae012060588a01000e00503100d00545001204002d80380c019500e980c280d0342c3c4106226501d944500303100301c0814054a1041c80001505624826460050300c0e07220284081007140c0f02d1240f0207030020b0740c842102280022655840d02e41c0e40201c00e030595054545280043c4201d43d25034006607126440300410700380520801030b030016003c2c0841044220f8071b2081c0d8404204500e00341c00039203040c9001c5d100806a41c1900018441e00358088444000018101c0d07450f520655144815030050214200454041c01038031200404803405400c5044400214800c1810403000729412582903181510000c0d0311000b51302c0100040745803070580a0f00183c030300450618041540407401d007241d0000c01c080700c0e034001d1a240c048c91400c2074855070111300d090b81031850040ca007240c540c580c1e130040107 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 156377464 1250 156376214 156376237
    0x10b0301090b01120603050d0e0108090705120102091306030204181a0a0204150809061026011518050c0a020c0907182402010606020d0f1206031a06060f 67
    0x41c4200040c2c0e80c42450b0040c00c0081c0c5010810a440d200d0500380d441314070480074100802d400e811000c0055205401e0741d07110307150200142c00c80f0381c108000c10000040c609040c008664003030100104a03503070700f0b1070414824495600050614510300c140300076140344600c40e1840881d60040c24000c500d400c607000c1242e000501402c0c00c00d50f55041e080000780a5504149003180002c0e82c0e0076170039500440104d0003040c150003110165510120b000d511800980100c01507003071b1140ea13241200360074901010071921154004200d00844071400060103546a00c56250716101010701c03104140d51344190b0703800c04402c21a02d032429079000c1019654a010010241c0140c40315800512054844c1c0701082e03a4000040703400134081d80d511004507103000c282c0510012503001c003d0320348495005214940480310a500642165511004162020900160340300103103c018003298005121034441c6801561062401d5001000e01c450004902c1000500c80c41c0100020006414407101d107000ba2070002104 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 156378714 1250 156377464 156377471
    0x51b010b060706021e030c0d0f05060d0b0a09050f0d1d010c0b040203070b030a020c06090f070605070312050403030e0d0e01120b0102010902030607080f090703081b0a0f0c150503010b030109 83
    0x103100c1e0084005d0880104184c0c041804800d0184d0b800078100100700d0080305010074070154142c101d188040b150165038003a400b160b4500044006040c6060b001c1e400030110000080a0b03100c0d403602ea040c0070510380d59081542204112040356034003d4024460703044601e58070a5005c10724400a050407440085c0a4a0b40203000c000804540d410041440030342000001e0540303904201410350041c1d000b10707070201e6070f0b401100002982c81708006000c2e072655450f00e0080418514081041e40e8607800341c04c0c207400300003440003040444512402211b0240d88256400070b186c1901001290428a11050f0072040000d03200000040d682d00039428010203412007000a0315501a0700141e004007400e03540250180180410488411b8004000307a108003814020610250358030134502e0740b210914000145403403010700c030141196010f114801c02c0100454201c4041c00016210300a951320030403005c07140200380440c24015207074480368800f80e0742c2c0d01d81050340c1594100705100345240014004c80f00d00130764 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 156379964 1250 156378714 156378727
    0x9080c090a0b03100203100e0903180a0e04030801031a070f050c210706060f08060f04030c05030d06090b010c0c030809012f060114010f080405030d020a051b010b06070602 75
    0xa03500001208070020221030f5880c407004061300c0a9001251621101e81503480000340700b1700071040551107880c0c004041c5248c440341541c9a11a081401c04040d000321469002195000301a40250300841c003e0320f600310b90358594901391601c2d0403002c54042100314003100307020f00c1c075421203540c6a500d0300038101a5240c1d00c4441130701d45003190640c001040c00040800b44205448100c0c01030148a02420080c002c6a480d01c0240030350f034076039204d03012469000313500040d1006501101e49800c14401e140003404101a40c035124910f40090341c106221554a1004011889140c440c8058040007070170200319010082e11254014201440003410403140003407102c00756072144510518510a0201a048080e0b20760b40048005100a00d4200750707108080004c0340c06140e4034440400008140d44500d04001a180202c1d5141c402400443c5d1030b100600c0a43d0618580c2d00107495202c60b01d6940a48039000300a802000d880300c100d03110a16490030546a0007030f25090110307048150043c0000d0b0f43e0f6007 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 156381214 1250 156379964 156379981
    0x909060904061b050c010c050309060a02030c040314030a08071b060218270604060f03080a020f3918150301150914010522112809080c09 60
    0x10003400e0b00e80c4040303501d543c0070598036088805800700c490303101c000f04a07110040b80e080ea40d510040c3c80c07490f00d552082d8002240b0100d41d80066604c000c2c0780284034217085e560f9407028a070701e86101078a0960f400105c1d11102c0203900041040c0d01c44420301d0070140360054450083c3c4040c1c0c1d45080a82180e030005400344102c40d40740b01d4026080d502a082c416000442441c0e110500360030000c407a1403180351004100e1624150107164103a41c640700600ca80d19103150b0301d05003181e0002d400442580101410050301c084240803440400d80c0d4183c24100410099601d02c4071142080d01d10021092421f417102100d403200317240310200c401c0c011b07000c0c0c0355900d61000d0b80d000d600d21916065410340c02c050748464001d0724010010204d510b821410b109214120040380b404910901031160480b001c809025070704500900d521842040c054000111a0188446d200e625449008921401040c100d141440c50725600c40d030f10b00044082c070301980300714100282c1c152255140342c0d00c0c500c01c0b40c89102040007032 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 156382464 1250 156381214 156381221
    0x20405030a030804030909112a0601090617030f0315030f1903030c03020313110f041517121e0d020714060108030412060513020604030303020717090906090406 70
    0x100401001c40741086414600284020411241140040ca0a031000a0401c09501442c0c0302d040345001814288400b4080c4249019011014104c241a40240d104804a014000d060103801c072042c0220349036040a100b00500c02207071002140a5008101d0a50001480f1058030781020040001101003452000041d10300300e0203550381c42650050300401610080f4094a000b101d5100b0b032002d101c004000e22090307080380000c0f02c440815243e5265210700046041020314420207004203801d00004140000c50103e4000480038402d5510b844028401d001591000105440c1090000c0c0300001618000520074080c40c070300300c0c40c041c00d070084100d00180a54280c2d02d0600b0103120454891120b400c1204084003554210000c9000f01800403400f128040308840036038440c03840c001ca0441041d40c580008160003000541840c8a400e68200140e45603402400111b011fa600941c940c1103034184403a120b00d07899140d007013981041000702e1003600c0e08000c413076000404a80040641c0c1e12810b00d0000b4 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 156383714 1250 156382464 156382469
    0x203010e03030a05060a060305070e012703081e0310030807081620090603121606060e0405010507210b011404091508011401051e03030406090e090604080a0c060204 72
    0x9404044100721012840340d01131807080004507807140419544003801d400300c80c026141c1d4000100d01881580180d400340d00200b21590b40f81440101241c0312801641c043c071025042102c0702c80f80080c041c00c0000d0280c0d4045c0705111040505440c5042c80e0500d02017140701c911000340032903c003142d22000e101c04241900c00d2042504082082c003030140c60081110768200315281491038044201d1b0001c0e0400f0004140f1a22020740100b4454200c64282c2d00d032500011641d511181141d189203001901074044c0000401c8400544c5406007400e10f801070965a000340854100f200301c0b03030031a11880d1400c4456440401c1000e0026200c1c40c04c10040700d02818420781c03c0e0380003070009000078908840d540203146100e054854010b6454603111a00d00380c3c1c519010780e0181e0781c0c00b403006201500c2c014021602f6030b03024035010006110154040303400e68200794481c0c80400c90b890010800fa401c0041d210740e0003540c820143c981460709075610120750007207190890403c001044000100716032503048401 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 156384964 1250 156383714 156383741
    0x30f050708040f082103070e030a0c030308010806010b07030c0b0702031b03031e060d02091905070905010f020c01021b060c0604060504110d0309050f0a0e09010f110c0604020409020301 81
    0x9030ba68403091041504030303a6105072016803080d0204040004c98010030034a51340c80400c5150300d16201c002080300c0000940844076494080e4290b00340004080710381c82c00c021842511050455072408680d01d0410005a1103c440d06e001017080c2800a94005d40e0f610403581d200358080c1003511001012482c5011f00010f802503c10460b00c1ca00c4080c0c00040550310641508204405407240c54440d42c0001c0d03010fa4000f50007200d01d07181c400042c90400301080d40030000502c4d074001e4002c004a114141d5400750b40220105007881e03014000c0756801300c100c0c0c0010540d8002080d8038099100000c0d030300c01640d0700707000407030030030307910181e0309a85800854200780140e9040b10705506050810a00500e016641141d4140b181d0741494114140002c0070ba180c10b806803500151541b03080140149603c158183c2a40200164008200b8001d40c01e80c440c05002a803000089142124211800b141d2203030400c00c2d1244018050740d5200d1000041c0c140c0d2041d4182c502144002161000c24050310710b4104145 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 156386214 1250 156384964 156384967
    0xa1d070c24060f0807030309090b01020309030d11150610030f0b0a06090509060411030c030c160f0b09010203100909050c0a15030f0506010e04022a0d2a030f050708 72
    0x300d9000c410340202c01500c1c6862050310360f82c0c0d500c44003941d5499441c800240880e000200401000c0303c55404000c0c0540d060050340d141104042c0003a007010001c10a21011070442c03d54180071800030408031080c0100032506810a0030544001054081130756119030030142c582c000101040c3e00760704846544c001c080c00300d4142c9900d0b9000503001429a0080ca40610840c2d40028098174083c011074060103290711340b0f10303d90f8980030b000780881d03070000344141c00c11030701000f00c0264031100c548e0a0500c0780c029a03411601c00c510f0328140e0301c11880906030500aa00500134450005682c0201004544112100040300c45051034518100b000b0300130510341c03000c15048001181c0d64803810181c01c9141c81d6604208059040700f000701104d80c02c0d00c020340024541080003400e81410750081603118070305000240054100d440d03000c802034000c40410001d4001030200e02c00c1c95004111034034045a1211600d502000c80e201208016500c1c8030f024042203012110700e00614051000c95920350b421181c0c00303 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 156387464 1250 156386214 156386273
    0x30507201501080304030b0606090a030b0406060308070614250f090e01090b03071502070b1803010501031211030306090c1b0607080103030f0509030d0305060f03060f060a1d070c 78
    0x813904c9800074802030b10b020400c07500080c000d04c0c106040301c10411000b0a02d98080e03055842c0c56000d0343d80204201c9500da40e5680c00320201d640f42002e0b02c1c44510851010481004211040c0e241004c040c01c0c059011000084034210092188440c00c5012070700d140074895040c403464100d0762441e9540c082c10540300110004140516240c207c05d04040b015801c58102070303500d03c0392000c0c2c034607000540ea0040c3c122290501610201c0c0b8000c24600030340f030b05a5940804000002802c45500307034401c9aa07200b000c4103401001d81c000d04004211604034024600b9442d080000c00c002500080c164031000380001a15009990208640c0b07020f00b00010444078145400e1001401b455000c3c0400c2d00440d05142c90001ca05200c2c108540c64194050060301e0415501e0300305502030f103800b078680c6501101540b5164481d0318208522403050b00754030184110340c101517091200406080e0400b0f000c902810040900c81040d401c08980c02502c3e515051401031014180312405020082e141c0320300c040a40080d = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 156388714 1250 156387464 156387479
    0xc140c09040c060e03070e040305030601030e030d0b09010b070807021309080706090213020f1e0408010f050a0515060328111b010b030a0212010e120c0706030507201501 74
    0x100b00540c0c0310b64540c0000c0071481c504041c3c0e038841502c90b000c412401d2000081c002481a0040d6070040b00c10704000ca032440000b00035034210782100d403800c240c10350744001c040310303d140015000303006201c60305110f85404015121120740d8880d005020b03000b14501011001c0c1d14100d40e025042443e081464180c5501c01c51030503d001d403140d000140c1c414440d806041c03030301d08210710881d4240d0300c0003200301d4a001020140102209861004200041400d000000d480c841c03e02400d2a504038045000645250443d401c804481014100d40c0c445c00340340544601e65210a811250804001003203100010b40900c2810032510494254012960801d5101180300078000c000d441514490841c0354020a001040d007402c0b941c0500b0410f900d503001c0d08104025040c07424071507035402c03060740012070301c5500c0e2846e0302d1800b0202d000c40002e81500081e02408010280005005450300d40b406000904103250024421760085608414a08401010070444102000b0880c0741c9407070002d2040035907075560388 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 156389964 1250 156388714 156388733
    0x40b011d03030405150304030f02030310051909020433020d14040b07060606020c040911120a0803010f031b08151e090c0a0509090d0c050f030f040609090c0c140c0904 73
    0x20208c1c00714802c038074009907880c00801a00d22402d007155201031118504401c010008194945000004e25490400b10715884240020000741500400e031100c0149044410225080c60080d5800d001c004005601c2c42c10740d002c1584040d05000c1d2410826100c01c090740a0654401c2d5404400b01680000b480720030420b468112408a500c0ca8082d01c2e240d503142028041524a40746006000c0000e501000d019460508039400e401c100c084203d880d5648a540c4080f0076500030b80200030711400003202042001555610003c1c110844400f98842915084160390348084449480012010010020b01314400060361803119025030304451040d8101484c066445010b200b90807401484410f501041c107003414400b0500030080380005011200d4448011655001c07a90340882c0c0d01e0203840300101580600700081e00210058203074083e0740c1d5140c4040504030100e42e503c0082ca0b1800d0011060301590003100200e5415008003202101070060000c0b0783c1400ca5203034a0f50781c04601a0b082c801400584d40 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 156391214 1250 156389964 156389971
    0x7060e01081e01030b0c0702090f040203070506040303050a1d0d110405130302030403020f040e061e1b09041d010606080406111c0e0c091303030b040b011d030304051503 74
    0x3203030404152203903400004030481e140711050804044100404c0010401d02030650b000c080142c406040c81c240b540014040d08060b280409040c001209010070351038240208001410100e41c8203191a00d507650281150103050340700805c1c481488211200f0300c00c0050b001044103002084600419101e07d82a06610503d600c0140201d14110010328540c00c1c0780003034038042d60560003c508091440e42042523003108010305a40140c2c81d017001040c460800c00c07005000f03220400740e0b1740c51400c0700c0d07005c1d10a0300d038000c000c60724161186102c000851484022101c062070161404a5010f500345800b07c0c94041207504c40c1501c0d841e1510006000c0e41c0241d040d40954070034842801901214140b02c10180945003e2034011845080144181e12540d80414000c0709000150354603031000a000900c0044112240419070f4066081130082540c10300c101003d40310100c2d000c00045591000007003890380b40008009450304002241d01541e60200265401498018210000f41000031025015a0801d4 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 156392464 1250 156391214 156391217
    0xe04081b010c050d1e020a200c0901060c0204110a020708011103010b040608100909060b031c140a09090c02071d040b040206071a04050303070905011106010b0c0f07060e01 75
    0x103414880106006001c1c801d4a00d07960141840280d2001e40c000300503090300b403101d2090101c465162000d60340081d10301c0e21000e44901488030b05c1310402880c640110780c41e0850b6a040f21584100559840d29000c0c1034400e50315181c4450703050b61000c500240480343c00100c9801c80450903403181d6900140305015915080003d1020400c00e0762003402601080c00341080031b0905200c00d01c172092103102455070240e0380d46840c0203015912070500086414000b41a03a01c030761143d00c00043c1c0d05080059a0400120400201c511010328a0040075040b001070511880c0c6030009929100b0b0703104607903142c090300380c5c281c00704911a00020041d5541c6018451104d03400e844851082c41c003034812b11070900c5240c02c03110500003a642c907401c00101c0c0d440300c2c00445884401a2540060f4403215501d10300c2248280000c564900f000c000140031650301354819070400ca018981c0400d40c070408205281120030b0b10300019100e174803a00c2040e090403036440d070b105810710031441c0c0040d100b54040340300107455400b07 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 156393714 1250 156392464 156392497
    0xf06011701020c0c0105130b0708070b090d0c020f03010902040513170301080607260a06031704030f0b04030c080d022706070f030e0a030501090204050a0c090608060a0e0408 76
    0x18400c050300b81c1c0203c0d181414503030811500b01400f940075400500f42d000c0c030807801d10b40564503669201c1143c1c12543c0300340c0b440720001c00c81804010070110036a800209140040401080f4078500502c080f0070400d00034055a040d00810540351400d41148680036030091007032241781b41086903c00002252141501c200d00c00304c940b1890305035540207d0341a280003001034010396550302815102c0c07103001107110b03071a1040021180041001480c00e180220a0005c0106411b895030810703e403031080043c4c8051851000704400c100144250f00780c41303500d6510884490b5a42e56a040503101c003001142c0151030071900080845c50b102d5a0790003012040f02c01240301c402101c10340049481c492041e2900f03600003008200c0240492580011015128864900f40070358101c1007021378a004019442128940e4490b4521421840c107401510744c040c6451108101019000400903d440c90b41c0c81007005000520012034101e8561480100245c03c5010160751142010302c0c002c070890f400341c100310200518 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 156394964 1250 156393714 156393749
    0xa030504200306180a0c0e1005220906020d06030b100618050108041704080304240801030206070501090b0408030604050702070b0d0c090801090b240a0b0d0b030f0601 73
    0x45001c00500212000c1c00810303e564136010000000c01d0b048a03000b0341e0703104449045000411001840e4050910f081484440d801d0050400c40001000d4001d148201c1001080300d440c1100725035182d407214641d050100d41041075003441c070b00034030400700130b20025403c080021050190042580b801440740d1a019034545945000842c0c0c21948001000c8585c034074100108050340c41140f4681d0170a004040c003800001599501d407407071f03a0059110b40b0090700041003c01198100c103e00e08402074031a081e0840148500340010511041400000c2c4600f0000c0340c03030401e0240035405008502e500006d26120b07402c26080260707940c0c1048409920450402c80041c15251000c11040116078031201e04030709010102014901401d281400a002c20800501c0010b40302d03c00d0042c007991500811014190742450102e012007200503843c3c0c03500369110700da5501e010391600100360044440499a0036198000306107140c0240480e03200d4554103125200056124a0010401d05d04a94540f865030440c0c00 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 156396214 1250 156394964 156395003
    0xa110108090f07060f0e0901030b07110f07050607050f0d0305100503030a080a02031e040b0108060609070905010f121b0206094902060f13050604031805060a030504 72
    0x20b00d08075000c4880e070000902001000c1c0505a07694821800382446d04035003030500302045c4041d100340e006481501065040c002095007041c0c0208450215101514a80741c0c50400705a80d1406071003000d0007083d00041d11020300906202e10040c03081d00d102921a1000c0b2100e008024280903aa4007142022a0708001141c0c5400411614110308546800d50507035120540300c4000d4000401034000f01c0000160344e4100c2850001940c8503500c100c500d1080341d4144440301d4580b00d00208014065070300001404191a04170001404581d02480c0c0003411a65821040f41c1607001004070040039404c02103070351907003d210303151550f45909a500320b0b0388550b500000c0c1c60b0307207012040d80c445100e20009103d06c4114040c4405040030103140b00b91203080b104112038400e910b1129640350340160400c0080c0b241c2d4001c1ea40403250001015400c01000346142e45400391911006803000307051001903507528800300ca4904a120080500411041d20b0342c1e04247d0240151400b120100e814280c804000b9080a = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 156397464 1250 156396214 156396223
    0x5010906020618010f0e1005060d0203030f0f0f18040b09011a0c030c0607050d180b0f102301090e010b121305060a0605100801150e04020c0a11010809 66
    0x11a030503802004140c541c4907902c603c3d80701228821105540340d850407655040703036014413440f54406030020031410642c10114801c4500280034184504154590680569000410303030785500203c4036001c0e520340a41040c403585218013940203400c4031001c14400000c0941e0800152030103c2603030b0a0012944020400c840814240513100304140001103842c2402c40d02805000300d100305a040b06d291082036941c0340e02d0b054049403480d0005800144104d41100c06020b402114881c0c90b211181d10010f643d2001c0c0e071024010119011001c0450014052600d1528818000c0c90302c2c042036000b00744150711002c98080303c0d20382d10b0701241c1a104002403002c14001c3e0305040342e202410050802d4403003042c080c1c14490245c080907030400b01d00d101d14007040007844103074003e0318031000003d407040c0360006011860036651107010603c011a00104078100f92441d403242800321614100b03051640d1200000c0c0207001d546885000c512a64040b83c00308111081d00507030f5010242c880600640d500281c0b140e03603 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 156398714 1250 156397464 156397469
    0x1503150702060a0b1306030b041e031403070c1401020a2309060702060d0e010f0b0402090f0111031b0c0411190e010e090708060f120606060f070b07020a0309050109 72
    0x10791008000a0903081c440e8414404c0c01c2c0c2c000e150007440300d80d0202c0c820035103580790019151440d001c000e100412000e64000700450f01c0c45200313410240754a072000b6000036a041420b20501d0070010000344050700c2101c1084085522243ca40d8006803e120228000e40201d02e680001c00c0000c0d5042c0d8003500c129501c2602c4045080c6100d03e04107441040c0101504840000c98001e40d040c0500c1c1440b4940d4000e5550203080d50000244580c1e9180c101c405407081e01015500036403040190305016180c1c00140034a8107800c0c203000300001d195008007444c500c00c900400141d842d140750300d10349043c0003150030045000c1c03c5806000d14170070b0b0040c00c2c6161003090246800700746801801005d1724040d0440b00990801414071141840f051380c042200300004552080000d1542002c0040d18503001c00c12240c01e020039120409503004c0b685c040756955002404192065001158144481038200301302c0d040c0d2540081d060985040c2144082d5484411400403070100b000e85502207070552040090504 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 156399964 1250 156398714 156398717
    0x10c030509300408030c0a020a14090a09021f0507050c01110a120332010b040f090902030a060c0908070803031506030405012a0e04050403200a02030615031507 70
    0x110080c40b00d15002241c1e4145101e00800300c10310001541580500181030441c1140d400f902c5021280d00c10040c02c812990000c0a9a105500d40d40c41e880d15441c442da54031244141e800a01c9403c0e078000503c4000070300380d541892002809a507401581d20001400801e8465070407100400035660054850082164051215511035000000402c0c241200c2c2c90b01e22406050000742d188003519200300b05506443c01100340c10a05d13400d1150180e85a40c01801041c0744140ca42c1028180407030100b003880a40700f90000f03ea115207224040d554280050400d542d84003400b002070241121000c0c001d0015841503180310300a800700080c280030084100c0b4481c44042c52a0b20071703641c90504100864001400546040d03507036207c0c1d100d08185040b00300c15501000c640d094684c00c1425002000003400c020900c0c0580e003010240000640c1001078455462142d5640d1039914540e8040d00e85000d0591001030b60610a84042c0501f8003205502580e542e07409805445000c4103454619400001c02d484000 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 156401214 1250 156399964 156400003
    0x90905120a030605060313050c030105090c01210e0c01121e0e0a020901080309040e0a0503071218120b06010305071e0c14010f140405070e0402041d010c030509 70
    0x600c00d444840100003544280c00c00080a9881d03001081e00f54004a070522040101c404d40340302400401c001900c000002240240080d16110403003a49690303d484507035060050038900015107264012100200108078241045091140c00342140c0d45c116040c592808603200c0d102d580041000c40c065100741c030201d00790021103c400f040a80d0010824100081c4090240e61030420041e034410515500a045200040d13888070b0302e14007000100d0b4201c200454a551003001c85a00140d00442501e442c240c100d0180480071101220940d0100310590030900101661000800d0703900c0103101e00780c0b0300d40c019400c00c825039544a0040d01128815a03100000c50b04000742e0411203001c103424a81549110700c1c00311802485a0b030b440018000c07280d00351040c0d9440701e100c400d00d4503081c03003580750044200380155014102600c4881d2529501d0103450304100111000609549a603008280c2d814448411850f0460124003401d00a010b4408080002424030010034641c40000407002c22910046c1c0068 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 156402464 1250 156401214 156401233
    0x11b08070c08010f05091b090a0513020a0803040f06090e15210105041104050c0a0c030c02060d2901050f0d0905010c090e01090501060c020d060e0111070606090905 72
    0x4502941024200300c4a59100c10008101d181c800c4c00b074420542540040032a6034140301c500c540c00c00301c10415444840c0c2c515608040c0c150f80f204075054201c0f4052000041c680c0b2503040708110f601b10100060b42003007040341c00103002000080108201d0300250382c5044015100ca0084845130322620644040c44100e202250508001e800002c0d68100028441604046a86668803140c0725040c224005a5550307004c11003408810030700048400c0b012602000342c0d1400110500d618040c400c00c52080040c8100740404240c040c03108441d4080d0010243e54568004001c800702074101c0080b00c88664055090b00110190202400245807505031600c80c01d01201c08551803d0350414010b9151b0385444642140109400703101d00c6940e016541d444108040c10841007218205040e8801c980c1945004010030070f01c2e85c0300c0d00c0c0c0d04c8030a6044038024545000c900340080a402802c094000c0c03540782c4011020511012070080c01c1d820300c282c4c801d02c14160382e280780d00121000b0b507002a2039500207907002c = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 156403714 1250 156402464 156402473
    0xf0406050a20030702010909020906030103031115040b06040b0409080306040b040209040f050105031603050c012106090b03010b03030915091302040303030b090108060601090504021b0319030b011b 86
    0x707000001950b192194001c60036403101014000c0500b0510840d410001304001503591041c0340001810783c00310150301d8414003201040c06880144005010061300c2801c600e030340c1d081409040e03e80c1d41410034003e81800d15040c40840d125064904600c00c03441c10110b001f0300c1c28540030301400300b6000000e01c0e00310fa45020901002e02058078009600c1942000100560f9907184945c00c01c5034506240081c2660428043c1480c0500b4545602f4404500c00780800004400158001c0d0620080c80c04214050131018a40145082c02c401d888a00342410382c0464104526400001085c40460003030145034514014135490748140f00000d40c2007524403c40244051112000304403c04000d05903c0b180007035000144c0032a00250400c400103a26036122040c0c5160107103030347d40075042d00c4001e41034504182c400640281901d00c210707406683c011958031001b03000310502035110901c0030705807039444564181074120340036160300403808039150085003080f075441104203c2044a2003081514001e02c1900c5 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 156404964 1250 156403714 156403717
    0x1b0106211208090f010f02090f0a0b0d0c050d0e0c0109090608060c0c0c0303030403020303100906060e0108220525080304030609020402040302101e0e061b1509060109060b0f040605 79
    0xc0c3c2902d0b072280f400c0c4c039404c040091050710006000c035000181c540388514208071808045400d11841000040c030180171a51840c012100610050200050090b40d03036042034800380034229000d541c1502c0c1c002410044070003c80d08000c03c48007681c070042c1803500d80c100710040320081c2c0107108540c2c0c0f03d200000d04000b9200000d04d1104180c0040340c0d888a8540002450350340101d40807401a0000720610040d25400c0c0c40343c002801c01203406100b80d9041c0640207042407603420269041141500c08281160f0303e11081415480002900e144555554101551340701301e03100c264200d0004155004200d9089514a0025203608102441c500340c59903c0342e20103042c0c2c490060740d001da0308100000042c0d496503074100401c2050740343c14451a100444610304501101d000c40140107070b181d1010203583d074141c00c60b01c02000140911014030407011003c0d1800041038000c4000c00801018060216000200030f07040b26031301c2c10144282511036044070803030b0242a50080b604541400140700d014010b90 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 156406214 1250 156404964 156404971
    0x50108011a0405090f0a05030c010f060b0904022215110303010f0303080406060905070305041e0b07050c070801020703020a021003140402090405010e0723010302130312051b0106211208 81
    0x45030501d203680b4901609000d610030b01107c2075480010720440c007c07030a0140703480c20702c0c00007010003030320340b5010140c1880c1c419021210300c11790b4001129038903100c51541320141200c44084959400e038450411050386800b40840002103000308503600030108002085034142d881101e0002002c0b491544c0503200214054011501991250700128580312188942d500c1800540e5021400741064149003030281c044c44041c1d00c8450400781c1c903901003000b000f8100e0b048526864529511003a01801d6424010980c1000c8008e50002400505040e4005804d1056074000c685060284002c01c000354120b40060f01540350b4240001d000030301500d030155146620074011000840ca503200b07048518181103aa421150803090480c0041068400024420b9035410013800c0441c50004941c1e4401d11400030ba100c01082c98a00480001110344510300f0340c3c240a48407486910014a04240c1c24068002e9016644406030324948c0300454100b00910b05811035003081d44140c40703a80d0f00d0000c840c43e01004 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 156407464 1250 156406214 156406231
    0x91e030c0504181a190510050f0303091201021206060c12160f0c0e0703020a05030a09050c100908010b04020304110f15120f0105010509100302090d02060d020d050108011a0405 77
    0x2034264041680c2c08a50540c0c0d80b020b00e04c095051030f00281c1c60402e0341c0b041c1000107041e0b103010704000e00e50892005140559030115503050b9010b074a0f0002030300d988110f8100035000b0483c1e400d6050802c405401030300390703020b130f00c0210461070307403144140301850040c00e824820680c002c0c4500c000c2985c045005003031803440305003c131080c000143c0300d07400e101c5061401220319100c2c1c0750003082024081245160000154a070640c0f034040281c0004065000c0030b04081c4070301d9942c501c8171042103010080150103540103003440f400c3c0442c1001c068807092061007800429400d101c024a1145000d1003203d1060f580040950360401041c41030000703207440c49640d9600980045100c1001d255100007400110415401380d804070300d400880d1801e2060b041e0b106d81d06002003480800d90658a20345045000708280c540141c032014100300055041240703000107504642e0000e00000b00744800c0d00200759568047d10180811f03640d80e14013a080b40c052682258031500c40035485200c51405401c19600100325 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 156408714 1250 156407464 156407501
    0x11b0f030c0b0403050c06070801150e0d1703100602070303120b04090507090c0e03010615051e040b07030206090d0516060f051006090614040311120d091e030c0504 72
    0x340d9a8440d100340243e03000e402052011404440140081140707503031018a03031038190704030752501c480f05a81c18984d502c903005224520f041142c0c1c0752550544150383d41e40162480b40940c0c1014039080d4a5032060b80e50041200d100d0700c02041032400000e5080132a5415666200e42c682114104001070078041110355129844043c07030720118030300308050790141c013100e40e0000b0a6841c000000e88902080d0311068060f90402c4802c0121066031307295164800700c00e08000e55140501c400b160640c1e40d07201072910211001040c049401255440a0032078103100740c080311559140c120f8419611482c90030b6107000658200405a210401043c149264910541f4082120f140c030050f18403d54000711800e10b03404459400811506074040300c00002400350741001c915605107150114010b20035404058100c03e08000c0140546e180c0200502c0b513003c1d0081070f80c944840c800d000520b0181c50b44100061146440790010001c02d401c50700e40e040300c1d400807040c00c80503c1c000501002d44046044040d44c41803 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 156409964 1250 156408714 156408737
    0x2030415080613050c0307030b091006050309030c01090f0b0703021e0c0c041109040b010f0503040605060d020d12091a070620030f0403200a11121509060105011b0f03 73
    0x183d80c01444d002d00840840181c6074500198010111004800d078103111340814401d21461000c231800c402c09664181c5801e5a40384e449046c4039203144603095807101ca0350f10b040041400e011f5540d4280405900c604200b16007500d4500044040e070040e61443c24072044400b61040c452409200244540485041a9403099280d0350000b0111061800240c074103520004111040303140038880c00051070b40c00d08001d03040d503a280100505501005000600050f52100800c07501d0f130700d040800142d2540104000b44030500d41c606204029240d0304070344017041141d0008160001000403d150150100082c80c0c24080c894803210080d1003040880e8409005030031500d8809965080211f2040000c6c8803540c400781402d150080001a0203215001400410b511440100501040c07140d0301d680c0003010480c00c8070140303001610301c80c0084146036051007085440f903112180c08011034465800315040e955a0780e87c9100560304100c10613640302d81e044181c110350740011075035100c0062250007490704005884 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 156411214 1250 156409964 156409999
    0x1e030402130606020c0d331803020d08040213090f03020c0f06070f0c0504110406020606090c0301030f05070b0c010b01110d080c0d0b040f06050424060f1101090b0115020304150806 79
    0xc21a800d80c000000300c502d071056503101e000e550704140502d112301ca0781391201c0d01d00030342703550445a0f65030401c1000c0c00444d013956140200240e09602502082015168900e08010034060382c01d004c81c054018103005069910705140e6402c441c00015000914024466403a030284041c3c0480403603183c503501c83c01190640f01c2d886840d82a10f04800c04039580d40c14042c01030324085006110074880c6d110ba00410140311405004d6030b0442e50300c8907410742c0a10070342c946541015040e400a090f0060302068070000500150801e00c09403a0a803618a945007100c180d881c3c55140c4d100107035011a00c0c3c4408104240007200041c265a10312120000d0008000300014041c2c03000c82080b000184d480b28014089803030300784607a040480707040e4020751205802c0c0410041c220171500c41c45040c040e84010300d1200d9801030203410742681c1d020008121007409490490000b80080c0160800c4202c1e0f60f0318825128000800ca50a07146500c810450024012008458800303000b00712a070000c541a11486200 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 156412464 1250 156411214 156411263
    0x9010507020418080301030215090d02040209120105071223060603091f200a090b03060103110c0d0f02060709150c0506100503010516051e1e030402130606020c0d 71
    0x103100d613060a40d42c2d45540104051802c080d883c40000c035504001560322a5038440d0140c8c0e059074151009a00d51501d00001032941c00e4030044624154246410007519a600004034503403114821000c008400c40403508100e0101c0c1030034001d603900ca40341c0229505141c100c015592001c00c2800b1075142c0040d0b40040c2c41901321500103544c0094448540341c1c90501007000f851003441c500030303001f810a010010002c10001003442624084c80000001c00c8050744660002d1002000c1e904034103690f0000c6182c2e441c0d441460714145c40c00a0070500c0c04120207840030071010f000300a50b980d03009025003481070010042c418056164148114040001c001034030501600d0322826402c0c0f00749426910301001c0c1401e642d4000c0440320004c0074150902c00f000e4001c010f440078900b10a00e00741116820300c14045191143c00b4112020900c4c101035024000c01d40350045224a01c25a45000c444410b03441d0f050541d070050090001603080900048590b00b88595010078450245401c0300d15440050140e1421 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 156413714 1250 156412464 156412511
    0x15071e03050c06151309060b061c0b061c0b03010b120a0303060e01080d110304080a080705010b04090b2e09060501091d1909060f020301060e15090105070204 69
    0x10840114016140e19020f004540e44074a00f01e0350444821940c0d000104171601310004a20401d45e1801058103000c0b455100ba14481e4024200b1991078030310300c1e1124001780048080c040d20b43d0030000020002e05080080d182c014280c0b4080f520320889a0801c600034020f0310340310707541666071552603041aa54510042c119440720307078081d0000b10101c1c00c1c000c0a48803160000d190300c001940c01005000b0340000d040318688500d00c2e1003207950b103003c285582140310384d40c0601094424076103000248041600204200ba200740002c20900603400b081c4000d0f0344c103418010f440e507001c1500107a0b001c40180c1c0c18000c4803804806490b0000391000c803101c07061004d40c1060041c1a81d4001c01d100950304086a480a0180e60140100c281d07072004a0845901d00107100d580c0c002481c070240b0b010410b89400902030103501c10424402500041800e100940091007101d0000d1341c03140d060481400e0554044001c0e45503010304600c0d0100c203400540740360b40130440c202d0700a035685041d04056224950903920 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 156414964 1250 156413714 156413717
    0xc2d010612060e0606010f0c020d050303090601080609070302011d03100510050109080f0a11060c06011415130b031803070c090b1206070806010309150f0f020915071e03 74
    0x580601410100300b00c42140c00f00b0a840d50042d000e001c00c5a0304508140b182660614008518166610206041c95501d0400410612011060009000000c50350318180e030218812174400c1c0d83d0b4640655030740c03901c510002e8041416006001250850129440c0428030b01900f260404440040c0040448508480081c00740503111014009903920070074400c000d012800040c54002c00c0d4804041d1203d50380d100007003074809083c08900e00c40c1c40c1c500035218507003100780a0303030100e681d9000400c088040d0000d189100f00c01051000e240c1035450016582741031300e030801803240103041040d070b40346582c00030b001d0001c0501d5160044030146e10800c0201280d03845000141803240c17422102e001a26650424148212000e03201c178864150002100c0d54032071403920b095000390700c030500160020158003030050f02581d8841c08020105003681c201c10960981164100310b804605c268601c128085c4090641c0d002c82c0095005a04030103590107482c01c24080d10380300a031400780105240e200010b0800840 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 156416214 1250 156414964 156414989
    0x80d05181c181d04030c0f050604050c060f0d0507030b04020a050408010c0302210402040912032c1506060f0304030917010b0105030604020a0e03010606230c2d0106 72
    0x156481080740d01d80c481030780428036400342004281143c801d00d81001607120f0b03000c000000c0a15109510145159410820408400c07a0b40d0900548508084800351014171807600c1c0000d1a081030001c641065801004c054200220307074144002803c4090101800c1645034481d40722250745501c010044800c00ba01c5180d03072185001140741c29100038a01c02018184103018a4504407100c07540c00c02e0746480d008214809a03074501c0010020300c48042c0241900002501c013004090301030344500c03201c00c4498800d446e64009561601009104107540001d1a041582035079120102c0707800031504442c1c0100486c0c103103504c80710340c0b00071900106c1e0281d0010301c80c03800c1003040c580c15058040c00c80443c48001c3c070007100c0910029044d0b21001d811580540c0e0300140001c0914440c0180000710b0400400a20906960f018001d10440b02d0307a00c0400c003a04003c03100268030780c110b000c0b5400d00c83c24030007900341d0604a54401054032074482c40001d0214000c0150b28044d1820320498000d062000b0451 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 156417464 1250 156416214 156416263
    0x150307030212090f150702010f0204090209040b0904030207090908091203120c04050604030206031911030a0e0106121202030714011b0305040b061516150c0903080d0518 74
    0x840101030301a01c001c14541080c0d4a400140c1313030128800701180980190f96060fa21640c0049004059081c543d464a9201240202e0982e04c0e81e0011300060074219001d01c850130442c4104051000150703030081c00350740420700800200c2050303041502014002c940b41030405040c0c40c00300f41145085884a045a000010044a150706003500719401c81c0c11450000d007004d0610005c501644501e010203481100003000140840001d82444444040069400d02c680d0109807840c9610f80c10946260304c10034203100d007040d01c03a081442848110b64000c0c25450940302e02e40ca40102c0810145284c1c030460004004c00d10204004444004421f800740000185442640d101c05071010b03042110718041500301400c1c40081901044101d03044003003203402400c0c00e4210f89080b1064459001c0c0c44803102c0344100308001703000718600040900c5140d10f400f0700482d690120100c4504c12a070000520f00c407400d1010100c9a00360750f1103e940440301100756101c00401440b4980780010210101c001d145074100803 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 156418714 1250 156417464 156417487
    0x4050304060801080a0f03121d010902090a0b09042613031e03050a0e010509040f02030609150a060503040201020c041a0a060807050a0c020d0c030c031109040803040305091503070302 80
    0x45900600014020b00024171444da55200c101a0f2004040c0400100d0400404850b00305c0d0701c820350760300b07898840380341030380f1080c02560203800812010b0f4407802c1d034000000c98109072400354003188040100a1030041d5195500c100c0504429143c080381e00e135030707100c49040b0107550740014150682c1c1510a40b44c07140c0307185030504e01c5d0380110504070700305640311140c000000d4000040d168000000c0c100b24990300003500040302da6000d02c28201e42d00a00b0052010703082034055009502841d02552600c18036903030440b0071081340c2481c0c4865508103040000801040c2d2080d40035680151051040d01d41454400e8002003c1d5415400440c902940a07440c0340080d14090401e103004014a0818070800d1408401c064414040c00b8940418030015030320290855803200404015650f110413a02c00b09038030303402c2c82400b10000e40000c0b25180c800d41000446032600d0b1000364842c030b501103081483c5549540d005c48044c1c0140c08146d030000c501c03a20b850039420740d100195108014170b50740181c49401c4400c0c0c = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 156419964 1250 156418714 156418727
    0x2030c0403060c020c010e0f01020f03031501180501090302091009020f180a0f050613080106170f01020c0c130e0a05031305040501031a0709090501140a08031c0c0504030b0405030406 80
    0x78608150b5028185c1152242d81010802140c48022525807442082d42c10060b401c002404042408a000000811003d07895000d10700703890280a136511403d0034140c89140f0010001400b9180c08140040313020401864850f40156210440c1c036103a81c46e00d83e81d400381f80207a0300880b085d0300040c08049408102454812003d8000c010112803c1c8007a1f450003905909500090145500400d0000b401d50125940701551800510368075000700400e5680d4401810340240c13400c041b14040c0a0701c0d51410001d0070500076100030f0310182001d000e40807107000801c1100400104088001703500c076260700c14110f400340021a000390203100510740e1400d5031582a6202d40d40e540000344030340c0c5807000610104040c80000f219a1740c5085540c0400c2d11500815582c0c8117540d400608160704100000c00c20039540d004c0d14012060980340e4040c100d132a4200641c69000301003540007070900c1070290440307c1400307070802e0382c1c1a291400c10501e0983c581d01c8840d1406800c88003074070254400142000180d51205 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 156421214 1250 156419964 156419981
    0x121e150b01080a02090f1302071e020909030c120702040e0d0309021c0302120c03070c0f0806010f061b11030304030f0b06010206010303050a05300f1510050706060902030c040306 78
    0x3c03021481e08130150001440640d0f00d403889806804040001d0410300482e80c101e407031490f049100805c2d4608880c4c0840d58860801108900800e140e802050b5925000010b03100c4054009000d000700e03100c0703041c8540f100e402c552000d0340d0150310350721f400b1100d65040c006c1404585040d900400e851030540144041507103840040781c205510402a14042640451190042c04482205541c0c2d2840d0700551881d600400c1000b40210000c10000210040f0701c2c8841000c0701d024405031580c03680d039000148042f8800d40f00c0c2d000480d40c072030f02924240301080c2d640c1031120f200316032081c2e1907071008000c6440c40e0401d0304210340c410460408003090008521103541c1c800002d10003884158151394008095010301d030740400038420007055940b500d07035038012291100011740810301d2421415021260501d07005482c0e0322070034440000403a1004604440c11001c85902a120640702c401154048815502031403081e80d84070303a211030124940b0b00c1400118058541c80c42410307103d500310700f040310031540600f = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 156422464 1250 156421214 156421231
    0x16030f0e06210c07020405090f0607020d0804030507051005090106060306052b150c0302030a180b0115050c0a050d110102040f090b03101506140301121e150b0108 71
    0x52000c003282c004a00d52030b503001c855030701024806480340024880c0074010003100940c400e052108101d810600020840c40000d0704408031500e07a01d480714142c0e2104102001140000c0c007076800180403e000e00024001d0300d03c00c01c00c44030b60001e44240f171022690183c2e01e05003140d4555104001042d0b150107101c0240c10300f03c0b840040c00208804450303442d0b24241084040640d1040f07110700f480200c95809884030151a0280008402c01600600075031040300c80b054450b00d800981c0c0903181d058200007c189602000e5040c141e400c01d1048030303c2c1460700480d80d0400c40100006140c0c0745e0184100c481e080c1c03241b802008041201d41014200da0510180401e0030380c17060004010001840c401c0c441141c2003103030001032900071000400d00381807011801c3d1054a0410303007603040c41600b036a5000e04840441d40d80018030b00c1031410f440e18620080c80b42d510010300c040b201801207508042c0240c10127203a052081d8144040d0740d500c0c0d8203880260390304100c190340c84004a446581100074aa8010081d = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 156423714 1250 156422464 156422467
    0x70305090c060f04090e070312020309090a020a080105130906110a0f0f0c060b01050405100801050406050d0f080901091d0a050a180b04051002042c060105180616030f0e06 75
    0x801c41289500441c4a84c492168035000c0c01b00c0301400034407404001d1504401c0e0f00c0e10202400038041e5913a4440040c40c1d001c1e03194200041c00000a0b4030a50780008000d948500669103400300300188011074860840c5c0c05030b41c1d05507000014031284904404094051403150711025030100113842003507114140020301c008034442e20455503000e42049e080c0c1c0e42c44100043c0b56103003100121254016500056001780d074515000d820b407600701c0c0406041b2001202c2c14000d45843c3c400b0b0001e48210801c008003140409840c0c20001404000a0403281c0300c10300d0400200c1e65950b80070603040315041041e21408100c982441034060050003007903404070142d9411300c4a0185c4568140300004844000740500b1080c101003400c01005126104444070460015520b554942080988100b4504140264110b0701c07014440010310180c0c0c403c1c85250140c5402d410084a8540401c00c106020f0000c0e6011900300117980d103008245040010f800e029580d00b8120324254400602601c041c114810302c141c00 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 156424964 1250 156423714 156423727
    0x40c020102090904170f0c0604050d031107060e03120c03040c0e10031b08010203010602150112020120031c050618010302061b0c0301020c15010e011503020a020a0506070305090c06 79
    0x60b424000c3e60001d1380415a0403503404989406081c60107a000312050300d4800041030391107600700007900d42c003503401502a44e03200074071894298200c071280540301081013014020003010804660281344000d00303c00a4034038096501c0308000d5a00000c039000035400b00040240818081d50001c008090409440d2012403410201c2007030041e01c48a200091441300b0411400340f2615446019a0082a090000303540b6540c580c07401a44944548420360001f2250700c000003542206080c038400065010303100c031800800b00c1c9034140e21103d910001e040b06c1d844104903410154003d4060b0702142e8071110310009080c01c020342000f2141d0a0803c201d82800b20000051015a5440c0111500c80d10000f040080c200c10140910381803445120000b82d03d548042441a94240046802e44402c40d081e11140b101c1d80e01d505100381c10b80c00a0040b00010303e210600c240d0654001d50003809021118011181c2e030010694401d89004030441d820340000c1e4513401888076041c0200314440d140d0700111000b609114 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 156426214 1250 156424964 156424969
    0x1a09010902090a022208061b18040c11060403081005060306210c1c1a1515070b130b010602030a120b1c050309010801090204030b0f041103100b040c02010209 69
    0xc00360036203c1d00b640c0090310030b4a41800005044899102e103200360310160f90ba290072502c03580b0403140d40c1ca034181c0c1c41400344254803100d400c4800c14224980004001d02e040c00501000f05103440c461818002d0448049618141c104410b0b40310b80d200c0d90300d40c0c2e420302d030004410f80b500741c1c90b0348503502581d824401c1c0700e02c40c1c0e50010003101007502d40c0d800f00e070b801c01081d000c945440480c09505401c400c01072040ca01c0c1c02440455040854003c196940300002d2901a480070104102d960341808400c81c05451401d20307200a640c0e24985075003950314100f5231140c40f030840c40710041e82e1019003041840c3c01e04042014020384117004100a00140d410310030041d00181514070b40c0702c0212402c0e07a5550080100756200000d005c80c0041110005581e0b1790300b407610302e5480d400884100d003c6101d1500008442d42c042c002c9030b090702d40c040302820040c2c545001410f085600034200321a140c90b5200403070320382e887c100301a8403006aa0003001c203410900d40107200880d65031120032800c43e40100428a0641c = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 156427464 1250 156426214 156426229
    0x9080307020405190908071a07020613051e0f010e0309010e12120a0504080f07050a031b09020d0204090f0902060403021003020c070e06100807021207020d0b01031a09010902 76
    0x507070701070342c0106503a9a600d4000652030b085082190105180c403150b41e003408400030180821301c0c818022a850340208056000044204039000b100607070040c1e001901c8440020396034030245101e2011102c812070045d40c5905450400e40c00070000e0790040720004050a0240190071200a5000185292036030302800240480c0c400c6000901071229813201b200d02e0203040000d08155220010300300d84170200044014280c0d8040c2c811502c0910940401910f2043e01088420484000070441e0103102c0c5165504900d55082c9990400107140105000416000394002031141c03001207940140e4440c00c00c034030001110500200c0000c1a4a0443d1010058a40300101d8003542d0301102d04a0078401c20080880184c49840003180a502541000065945400081034042c040440305561881c1820504a0b480c0100310380410050f4015184403400c90003200060501c903001401c041d540c00c1d09902c0d00d1203407000030303030003101e4101840c1c60542c0c803e0f0807240c84c550004000c00003403003080707c40e80004400 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 156428714 1250 156427464 156427477
    0x4230a050609310606030c0b031e04140a0302060907080102070c1e2301030e01150e0910051e01150e0609010302120403020c01110c1509010903051506030706090803 72
    0x16010f0f000e50041c0d04125243c2e1540c2c55040844001c0041c1c4010b10706000a0300880c44220703103991820901007448140001a43c2c421000613202102888a0340c02c070251810001c0c0c810394078008010340c040c101c0c0070709100d9143c20031300a80040c002c9041c6485c03614a80a942d900102050340b043c048000003401c0030b40080115890415140c0b90468049520903082e08281d1001104030401120415420120a1f44504140c1c090701d0030040e910b6076419a5098581c0c1d902c1c4801160b030380210900401400e4408660040c0858080700c403034802000002d4110342d419241062058246103600c5a141c0e11b5000381809040307608410514000c0815014107403059609500b40300d40300204d02c0c2461648683e042d141901100300780319206081c84c1c11302948403182e2100c01400a800c0c0c081026641000003101c0d442400301902200404207400e100e0540c94100204030303410403001400c00004200b08106079441c2010b0082441d10f01d0800c101014940a02c0e90b100c84280f10b5604010890078a021041d941c0 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 156429964 1250 156428714 156428731
    0xe0d0f090605120702070f090e060f0705070213200702240406050d020f0a0e030607141c0e0a0506010f0614030601050a032004090b030f03031b04030204230a050609 72
    0x100c44d10b40070426403d00c0510380060180500c1440c00061441d40b982000140c0076088042d205941c44600301c1543c43c40701215a0808103108001d403034018201014400c107074402a01c0b00041c10b644501e400c0482000c00c400480c1c40ca40d0100da020254608800001d81c1d04100041025100184d1900740909016612510080c450046607050005200d5012035100c41043d1a5066a0f40714083c00507001e0780c0d01340445030180c46400005840c690052441020325050000064200400221400d642d0150f800019a10549031308014441103070410600401600c0340f4040c04807076041010315441a2041c2e80040c3c03c008038564814240c0aa00341240d410060a280c55607441c6c0451106801501e00600c007821010451555001c000c000300005d001525480c00091203142d100c1c2d0101340d44c540800b07241d50400c3d0001c002080b00501400010420405410991400c099032034000504480e0281040e40d906ca0300244c00001001a1030241544401808010801403d0102c0814141070740180b002c603 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 156431214 1250 156429964 156429997
    0x9010509160c0804090204170106030c050f060403061104081b060d09022d01020f0f03090103021c0f0902090a0e070605030a15080a0215040305030f07020a090e0d0f090605 75
    0x1803040c03082c04280301554010040ba561240e482d11043e0081d07000c0d2090700302e03014121080300312444c01801076004032908109a083e02e242024100580c0c0300c184403c00781c1c01501004004001007160249824814002e600b154407603103070880a40c2011611803d80700d880044011112060b03440c2e40580d004100c0f141ca00142a4a040c8040b680b803004421410a40038510041c0750040301800d20074091088085c0d00341c0300e4055541000c0c961b01d403030700c84004c44250424451040c02d54480c0e4003401c0c001000382d00d5031280400e2050039108036098509100612900d90319040b0540c2840011140c0140007444100b164500004480d900c801d15130280c042008030002c00325203035045030380202c1c00e900341d113040c8030744140d41e0303020007950302c0c0c44202040340201703008881d41d401500c00034240c40489402a000d18940148074820003280c3c0e120120072a80b11081c280041007000c007502c80c091803030103104014040003696010292030140002c0c001c10400106035421b0105075130104c10354021104025007030 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 156432464 1250 156431214 156431251
    0x70e010e040c03050307060b040c230c0c1011010b060c0d0c110310060e0106051306030c0302130303050a0311030105030c0111150f1b04061d04090501150305010b09010509 75
    0x40701c2d035980740c1c40a0308900c80400c0329402d0150b107a1000500020403541001100e0480805582c14101c0202071400310040030742140c18401d8480080043d02001c005945002c1860343c0040c4081c0070440521001580c81c4107407182c8150240f1440c80340c0b200031160300b400e00c4003403000107648426800c016130070000410702500170800004070f400300141c001025074140450580c0e8141c0104020300c41c41d00d81340748032400010101e000e6421104104441ca040c0e15440341801802c0e005054249090b00416a00708000c02d22400c2501a00d405548644d589586e6540d04240003000e8695050030700003808010401081642c1e000100e55650120038240311006605e441c50180c04c2400c2002403c1115101c0b404201520300c0660417103120b60803032440100d45101d980c68400070303070095009950101d0444842c000f0008407907240c01c0c54240c401003000c610500d1340d9803030300c0c256030382d920700219400180d92040c0100f00003806000820f0109941c800303415031500d400078a22130409010340002e0744141020 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 156433714 1250 156432464 156432473
    0x602071505090f060c0304080403140a0606140108180c10030f020406020d0f030209032d0f031902010902030307020405090a08030c03060103140f0402102a0c08070e010e04 75
    0x298240034900c40c20800c51070a005a162154440800200c0e01e000f854005400601000240c80c0103a4010780114103050440ea1003040f58150469607000e10f102d001802e000280403400b80034060003014183c560110f2000d0005000340c1d4008d08140030340c100d80c0c1721142c030510f400282c814000c10f0880d80c0001c10708145c00b0075001011030380615080d003800007901182154001482074003012040d9a40d800450803102c08800302e0181102880d0f25401401ca10f580340c407002d0f44445c2e0000d06c2d5034110340d8171449280e0b0083c42c220450001803665000070944424100d01c1c401c0401720540140000c2c441c02c682540000d460740b007008402845a0394583c0411000b2004004503c110759012001c9070340c9003000040040a5003048444500003402d092008820881d00031409004420080169806841d00d07420022000b003030030400010000c1c11550420017600700c00c0341c540d40e1981a601480404102e0404000407105500241481d9215417010004103c18075015411280c1600704113845460307600e003 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 156434964 1250 156433714 156433733
    0x12150a0f02160b060901120c03060507120c0e010909090506060d050718060e060402091e1c0305030117010216031b1a09060901060b16060603020a0602030d1a0a03060207 74
    0x4146640740ca02d100590810141c030003140d00a2100b00c131801ca00b40c0c1c0e50381d40e074407030452144002024001401c40402c0081d03190740007240c20010074181050a01c1ca00048081140c4151f0200c200140c4004503031125560010741d0040a8085400240f202c0c6010351a02d036a00e90307005d00164010b0580c00040c0050103414030424016142d030382290301042c911958090003030083c03401411091107034407000c1005464a03100311400060050000c00c0d000000c004200000f1031000d405a4002d08002c4503501401c0c010b269640c2c0c00343c842d0f2241500ca5052001e000d040d10308084004041e40e01c104230307000d50341d4210b09104207100d500d864002503041c42441840544002c0082c020803080511070042404100e2140c0c061054144000311003060fa00d004540342651014800d028541804000d20004503c2c0c603a0013551250041c40003040541e030300e0b4040340342110035078010b00040c0c00100f030030b0030414180d006a00c1100c0c4d00c02c06440c1255046000074080301d080b44001440d46074002901c10810441c0c44 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 156436214 1250 156434964 156434977
    0xc150903030e0f06130e0603030a1704140d0207030506060603040b06060c0304260c01091a090f03030a0e090106080903030106030f14070e0f01021f09031b0c0512150a0f02 75
    0x2400107417900044d000440050400780160071742c60300180c0000c0c41504000090302e00d549425074804212000164900e82295030203801500d041c0709811343c02030180b40c10000c1c0150000d00764014904036185040c818100840900300911401040007440041458401040e820401c100e504c2503403070000351031103447d40c07056520a40240c0c4001d01813290280c0302c0600000c07850216802d0b11244041c0790011503c2c1c104c24091001022404091010141260340181411000192500d030f08a40c02d64002840d64010b065a4400510300e51601902800c10100040c014900f40c00d01c5940c0b410504245c544034041401450101940c42446003207004180d00681406030f007105080610b41031484000340b0200a400e600d500070300c95910420f2083d4800603403004020000c3c042c9015003802c01400c08d01614510400342d04004001e41955081501c800d94481c61604c070384d0b0107040d01c920307000500c4807080c03450301640f8590308500b181815112011003c40c5d440040035100003200040310f40200024040d01 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 156437464 1250 156436214 156436219
    0x9151e26150906090f160c080403060b01030e03040b0901080a091a07020708031201031b050307090603151a010c032003040e01080703030c0803040c050607050303040c150903030e0f 79
    0x190500c0051100e075140000308090a9818904540e607100901c40085025181002c0b07281d1210001410901c40301550011051170340b524505401d4035850b50341c04d0382c000e500b09882c4d555441101c80000c2d0307098811015014441c030f000d10f00b0240340107080c2c01c042c0601a0044c0c180b02110f07002075070601041e8046084280e009600c0200071446030815011024111a814050300c550b4a02003000c01000060303480517502d01c0003c1640da802e5540f410b02060345540200d190000071131020481c2d036014840140600300c0944005041851802d0000c007198020210300141860021610f0b04c1c1d80f100000402803407400e09111410f1030326450110359030840c0c800c0305018620340e0500c14000d000040000d100b104c0030203801c0c445698076928882d03164281c40c44024003107041c0c0c80100e40050212000713181d1041c028503031166410364460102c1c0640e4822881291283c1001003007004100d9588040c01c0940b0304d03528250344920425a005d051000180070142c2448001500d030b4071b82e40c0c2d9600c0c3d0384002d33507000f = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 156438714 1250 156437464 156437537
    0x1120c0912080304061514060d020f0f0a170408030609041103120c0105010806100512100f02190c0201230403120507050d0f0c120c0c0609151e 63
    0x1a030510b90555007056134201c8615080c95440110716800325100000d44400d00a061580800d80081000360343c89030400c05d20064003405603a50380c2c001400070b4180c1c11000c070042076603210090f4006104c8a00c000b0780c1e0902c1c1001d0300030307c0b0219003540c00756640301c481954a00c02c00c0d2031342c0c04c040128240420f142540740c4200e10000061310000d101a00b840d00c060300092180c0e9883d02d00707158aa4604460202c0b4a03407110908102c24505500840a005e41078401e031503075900d5030340c2c0d99400c0c0c6520b0220340c0c0d4082d4000405454a50803440f03d0303020728800c0e1505c0040c607046a8002824004d45802c100d020342d111884480c084205001128000c6a2000e9074400d01e100d02403000d070213078111083c10f4501b40907660010107224001c003400c03640040d00d0703130300c00000074200c0d038405c1100c03402c0c0e0380507401f00000354640c4400207250081c60701c040d2a09498079808245829204854400b0003040401000240b0254011104046050300c4008030682418401010448011030200e40300c024907041c250f04 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 156439964 1250 156438714 156438749
    0xf04060326190507020d140d0908030306090a0e1009060b0a0e0103080f0706090f05150601030605010c0602070201180f050f0409110f0102070b131503060501120c09 72
    0x21048006541e4800001410034000080100301401c0c000c00d20000203800ca1101184031181c4030b480107101c85440200001144c0510344c5403441c4000501e014240d055008200400c0c805800034101d80081a403030004510710703c0c02c1004290000c07000b4004040d059254003005025240c144a480724022046104000ca92114200701d0054501002d140d4052254031101103100c40842483c1e80c11b03640c1000d034061070100302040f00d07a00ca9000c5141515000c1e51410b800000688418040203110301407001059810110b0545103202427015200c08c0c14981760080812050b600202002e0f452900090010386440907030005031b4031001056801d22030240a403c0c080384042c408a030844c03d80704291180703140f90380c1900078001110740e8203001901440205c4019030261a044101070203800041c4140c410560740c030703030b00514244c10210007120070010100040c0466140003007003080200349443d0038880360380780000180c20040755468828400e5218107200342074501600d04180207202000b17080ea0f5885 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 156441214 1250 156439964 156439973
    0x60c030a180806070912050312040312060e01140402030411040509101a0904020906010c12030c0320032e0e01031a1b0c1006060f0f020607020d08060f040603 69
    0x7250740d8680c1c041201032000100c0e2000780000c80c0c0340b040f0529290a81aa4244000017100e141c40c80c204481d644010002c041e01c400c5054040c5003e5031090319595440d5501c0c07141c06007640d0309900100c440130841001001248400c030b41f51500400203403001a66030321142440d001d1440311802c01c5402500740710901058850000d40c0c003200700718059080000d02144428a01080c1e0440f40207a40310b52482c0220b0007520f0060b031402d0300014141044a41d00411b0b40d00d120b42214401403440c003080e940d80c0003641168250160404051110900c10003180020340c581c02d02d8040580445040d600340320581c15144080911140008500703150300780815520b008208021209000854440360080e118810481062030400d01070080304c100031031040706c2c0c9030384089aa0894110f21485211300c00c41c0d9821240ca500c60140949000e9980740d5205105c107c1c06050300404103031490442d4040000c01c01d40d80c0e0302182c2c500d050105860400510f131514070015500924107298260b02c146414030000401 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 156442464 1250 156441214 156441227
    0x50d0c080d18090203090a061a03060705040812070b0403050903160b042111010806010207033203030c0a0804030e030d09060e0604080303060f0406030b0a0f15080a0b06060c030a 78
    0xd803040c1d0701d0003004a03143d100100036800251081e5104e58003615403500001d130b440c1c004030481600512005c8a940c10400024a0300d8001c1d681d0b440070510024044c44107100600250128080e40298103162290543d2030389862000140050204100400d907250356a4041c040c44105c0a40311070140d51550719280f200d400d41c0e00c10303c10404281e20244c0200c40524900c2140704056804c4103100041150b0000103640448004107814118000d844002c000101000c2c40d0301ea100300340c480f03203a1200303002d03850000042405503e019015403041c001c04c41c002c20484102d40c04600549000f00c0343c1d4035130b45410780d81010b94006a0f5454042c40c80b000407010307448a959002c0714915a0f5000350318100c141800042e1245001e1462107400c10000a010f500b00340081d0001014003502c0084d110f0303034076212100b80d40015a0074000c980e8036901a141d00b4842405103402c0c3d01c1c01c0d0117104440501d0604543e540c0d00d0710b2280101007080010014400e942c4450503503070b1520002d801c0e213589001c0c042000f840d0 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 156443714 1250 156442464 156442487
    0x6020c03070318050108250306120c0306050a140c0c070e070206090615010207230d0c08060105041509090201030e03160302070f0e07110712060b090609090304050d0c080d 75
    0x4000300100300062540c0b00c1c00c42039000347c590840c58401c0c41080541c00302191201e0b40f9000500d030b2074050005d044207001200b8203101d4020950b03590300f103003540f4015055400161505440c94144080500b03603645110700d09401440240041395100a002002c508080341944404a804c05000400401c15008540948215500015100c0503a100000c5000c030b88211404035006900c8480103001c0004011230f44062554800c05100180e0017000c0042e140c02c00005003103404c803503a10000c0016113010032070b960140070100c4050096020602040e040a00d183c8607a0003601d80b07440da4035040d039000b6489620170007141c500340c0f41d640c40c00480d07651412088020480052064610015200000e582030500380d824807000030b40b46441d90001242c113810360b0420350081e80286940014aa800d07144a00c0f403c1c1c1c4905000300340c0c07411440401640b400b00a00b010b010710b84480400c8660840030007110141d0700304a5900740200c15900b40030310101003a400040c130b02d208042d001c00720b40b45c110f4207800c2c4 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 156444964 1250 156443714 156443747
    0x91009242306071103161503020a03062d0e0903070f11040e010e0d0512180f0f010605120f0d0f090b04030f02040b011b121106070801090b0a031a0406020c030703 71
    0x814282011006c40e49414416880c00b020f281d0100b88440d0701c01e40040005410500c3e000c1225038544410320b207071107490540d10b605d481e0b61160388410010748404400003030802c0c0e0800c410502e0024045a220f10643c007000704031440410b000c00030480c114004c02d20040002c2c0c02001710545082c9a1030003007460748000180f62140c5000d0340c48062041702210140f0850a5440d00641c1707034094103000148080701000c3c0701d07000e10146034030303142010090101d0610070076001003941440c01040c40310181c400716400c80d00e500300004441e4103041c0080c0710740d4910740c01d20f090300658505030380c02c885c2c01545401401c8200800200082800b0501410303100c894000c82c0c0421010340c0c401c00540398200a00d07218000c0000005414000c0303219502c0358101c80d4400d003030100d02601d0b0307245040d0416a0072618038000c94140401804501d101d403040e0000c3c2c6100341d4144503541c1c150f840d60b034206072400960400341a02940054208807068054444007030903041103030b444a500c2e103405000c444c540c81441c81d = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 156446214 1250 156444964 156444973
    0xb0c0d030e0a030507080c030427050115051e13080604021c020d030c02130606170610090b0306060d060b220e1303020a02091009242306071103 63
    0x1c45000c12628051545074440301e10308a9190790300382d01e0f504900c1034124140406d000024144042c07a5813091604802000300d900340c0b420300300c110b04540c0b040e000340c0d042c40b0391170b010800d6140d084021211041a0078611600220440709101c4191068409074840c8040b0020002034941000034082d0007540700300e8010700c1c9205c1c10120080480ca0400002c1d51104085c200080464016504451070702d00240115001180701d0000b1002d4813a00d5200c8030000d03109104071314000000c01c981641041c03003100c561500c41d6038407030001c1195603030b4000c2d1107241c80b0020200c1d4060b43ca142c11982402074100c8244103072a80e81010780625000080c407203c401d4082884a0800c0301440030700c0c402d0303443d10025240e254441c18213074240c4225080d0100c065101d9860b00102503070f50300c003c03a480385842c1220703400f5182c185084081079603100711820f10349804441c01800e030340c1c010b12514419030b82155004080340b89621007040d4090340d4031101319044000018900184240c40c044042990742c203038100d9 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 156447464 1250 156446214 156446231
    0x31006060e2e1202031e0a0e031902030c01090b06090106030212130f02131d03070c060c030504150201050403030b1e130209060c030c06090f03030103060f060b0c0d03 73
    0x81902d8021040c2c40a9100d01c440c041d54851103045002d10030b00189140401c0740c40c0d051210344040340c0c8103849010030507101d0f207440c2c04403c032038641196002010301c40c00d118019010586641e03074000c10680035100800203612203807540c400c01c2038880c0007403028000d00449485081160b01e240c826200780d0f00540c168800450441c1c001e0003101e050303910790400d1280954070100e03011b00d0061944021500915400b00610241c0c4d01c074204505141a0345100043d201100c3c2460504d04502e2a251002a041448120301248880c1e1a0004513403281c14141150307222894120313414072440c0c0054002d040f02d03070f0050160380d50560200e441548251000c0251003842c0703040103a520801680b005001030003c40040700b5007805c0803000701e0040c500d14003500b40f020401c0007810300c2d00070309032440071548041003000484d00708028254100040a015080c401d00c040d1501d40c0b00e100500024040903154003408100e200907034490001006c0181c501c0c4e456560811032140c50715601c60082d00001d0034040f04 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 156448714 1250 156447464 156447469
    0x20c010c08160e043c2003090a05062511030d0c0302090301020a0201091a070c1e060507080a0501080d020304050f0d020402030132010c020915031006060e 68
    0x1000d00402030224001c20700b201295040703d0800903586407075003042d00c515055003415136a0b00340a042c54400b40e003034240c070580d10310904160013841c449008414148942e10000180d890125084035030002c2c4001d41d41d5941000151400c0c02e144c000401510500d4104003020340402102c407188000c0d10804c5000c109503800c04c6518000815018455403c20400d00001c0310320b42c9d210030300024560030050b0030480358100190882e00a0010030b00980d44840c0031008101000c58164001c015180d6003081508040b28010a0103000080c01088091000d101c458800b0452090204403940324009010620341200000c1c010300083d140c02c00b0682c18940045101040842d20f41204025540110b05181c81e10003000001d00c90100c4158106070b9044002d405a02c40340000c40c041c0111900c0e5803804050482c4000c545a242010001c0c481c482e5141908a680d1245d01d0325000c1381c0442d00820561581017200c2910700e03c1002c001d030b1610802d014080d0300900e542001003200d140791520026811440d00307 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 156449964 1250 156448714 156448727
    0xb0a03080a022b0806010903050f1506030d050715020403020607030f080604050105150d060f08030702010207081b13020c0a0b070905030c15070804080703060f06060203120a0b03150a020c010c 84
    0xf03107115152000c00300314030f03010311079138806074401c01c1407600c8440c95640762125070500325a0301c160881e64100300b1548140d907040394192038100f002600200302c105140d000041483c01803c000400b4201400d000b14048007440d015100690b4000f40080c0d5680c0c114a8064099944e03041c500c00460b004030000ba450346010320415040303420281c00d02440c10038000f206400c6a0202c04440961a51998045107025203079903924041d040034401580d81c0c503e180006132a11a06a10070b080700d500c20112079070820b4010340781c588818800e8407040601c04140c1e01e81d002a000b80c1c0c141410714410014403a040c010040e00342e500135021030b110000c1071920342c028580c4580300c000010303410251101740301400000d0707a0001d1030100d020b180c105041a0711650340e2828143c495109840468841c2ca40d04680d049030710940004181c0e40c0000d41c0390916140c901d010a0000400000c070281c3d9a804e11211070300c0510680c0c0044488900c141304d2850180d0882c0c000f508910f100c200d0365860004202c0e203160040c070 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 156451214 1250 156449964 156450013
    0x4050a0207020a030605270105100f080c090c040e0709060323240904050c090a06060f1107050303131401030b01020307120e13020d0e0105011202090a0b0a03080a02 72
    0x1030111100130709540f58040500b5024180c0d03d00200d045180001c011400360f0342c1116420301030004555810203650040c00151113400c00400030003288004c0180e17031000104801000c80c2525296280d0f699010062014040d60307115074a20160b075801c1011307555016003139400b607410a403002c100d135809040280c0c4443c0c00c0d80840f080300300300c520f000c14103c13141110b2885441000401d1084206914400b040e5006810b85080711264040c0614060070b14243da4225481000c026080154a203405001442807400c4c0030107070140300301206006004102441490090580a021a995030b0011642705503041124407034000124070b50541b040ca25803103400388031100b00c416401507050152f26240c820b03140f2410928403091084141c80307040962500f88820848804080700180c49032000051141603850f240652000c60345014014004251281c455414640d0180e80c1e1681aa0f95101c808005200030800303503601c03100a082c00400c0124540c02803c01c00e555600303465a600690b52508000e5036001d = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 156452464 1250 156451214 156451219
    0x1b0614070809010608151f0308030108010e0109030914030a0803070c021c02090712020c120c0c0d020102070605070c0801051003052401050d061803030b010f05040b0708091906080604050a020702 85
    0x41018004000ea1b10050308901714031040d81808407034010105503030083e07a2040f54071101c0440100402a030a200c1c03c02c444210f507009012a004507a001424418280900d0000060104603200503440c100041811164000111079603420b0551014080000030754089200c6c1c004040c40600825089288101e4107a0141420540d900e07041020b071010b41c1c5c11140300c0907940d030074007800c20031500c10000844c607004000d03119580e4202e07208000e41403c400e000410f01070074030404884010b0344e00081c5001203802d40d14189441d00c4032031a180300c000000d43c2c803640c281d6080000344240885102880400c90b84198100c0b050b0306c80c140c0c01c0000340780c0d145406008444000b801041030b81016030f441c8a01d5845410009100910781810100e403e100d0001030f0006656012114035650300500a400c809806041281c00c2c1860560035010511662500401002c03000c24109203c1d101c2c070800003c0b001d801c20340000d0346500c40f6401022201c08489a91103142800d002c103491040700e10803100300b640c01 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 156453714 1250 156452464 156452473
    0x3190203090d060b100903110906010c0605010603020a1202210604090c0f05090f0f0403030f02070503030f01090501060e060d0207030e0d031e0e10141b0c040609110304031b0614070809010608 84
    0x238208125402e5002050349040c4000b1100d00800a0018420140a0500b5442c0181c4816102c10b009001d10700c4481e8040c500b80c0304105401011041c58004010070803100080c64180d524000440c0240c803c0000c01440c51030000404201c0e4041800d25005a480660780c03d86c0c61350f24020380d0307940c00105546200080200c1030110340424407a0300001088501000301520302001c542c0e4480c0b5682c0308813140b00c182c04040700140104506401140d00508243c500980d49401000c0050356502c00d02c00c10040340c540c009070180806004a03c070142070200140000c0d00c0c0c800d6801c000d4130305850b5100f6140041800c20381d60905600512401c003003000060726000c4000c003030708029907280c5107401d0440842c641c14040307000d002e21a031743d44103003002c4c8002c094a8103a90640510007554040d4105800e40740c01c0241c81082e1070761a0080d01d40c0035400d40f500e21415a034030f0350b18008012002c3d43c0a0304440c1002111301c20034180100301c90241015513152640d5a4034240c9050889800d401000f400d50817 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 156454964 1250 156453714 156453743
    0xf010f0b0306030724090e060102190c03020303040605070318030c2c01060903051203131509050312180604030207090c0e03010e1c030e03190203090d060b100903 71
    0x6080e4060341e44903201500315000ca0381c075444840103003403941025001c10741c1c071501c5100820b540301541500412840802e80b100d424100300207500c505d112070011480c0742840319034605002c19540000019600641030b01c0ea11a101c2c5401051035001c070b44281c5c04992a03002d1100b1341706044190b501140e401c02d04011541d401d007035400d00503041d840e11016588261008022120088036031542c001c000a40761402c0c0c641c6180390480c1000c441c6010203518050600410428800320781c45454040c3d807001c0403d03042e228110000c03005202c12070028110348008500130303051030000710346036024156044502c12030101607020703140e890340c040700c0050043e0040340c4200f20074402034020380c2d143c00c00360400306401d2400201007401c441e041c042418090340f228555204a440046003403030485414030b01400b0302c120613a080341c0d8a1007000c41d641026090103034400030a0380300b8000c2d02c030711a000915242c0c2c402c030300d401d204020b0310001158610628125814044040c014104a03088907481202c02d0344446 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 156456214 1250 156454964 156454979
    0x12060103030f05030601020307140715080f060607030c050106030305210405120c01090209043c080901170a0c0207091401050f060c0d051c020a1b0204020f1305090f010f 74
    0x4c002070545c90540c171081c040040007800d014039110011401e40d0040840c02d141032042c10244c02316000010900c83d6000a0200c04054041740c0c6511140a44003e9903070207131490215034900c40101c0250055203061404800c240c3d014000340200f24000b41800d85406030311114140b0100140c0300140268801c070081c1d18181140b00242292520000000600d004034bc5c002c83d40c0e18108239400c5a142e40d29035140030f0410030080d503010303c0007040490b4130f44860421400c2c01e0a07034900c80c0d011741300b0140441c0e440400c0c3c0c8940007010610034041541030b59800c0503004040036020300300030b00000d80140d0001240c140b50743d20407100304828090b04442144d180006104e907003001148100d0b0000307001c010f41c400f588820004c1041c50b44450707a8240d60760301c018002c12040720110a14144030344c01044242d0310366501000c0c000c0501000f02c0c019841c0d01c200e01c0040c00910400100f4030603c2c4d400300342c1600d59425096040d003110025604034a15039140086440341ca5000d02400d51031001001c410312403403 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 156457464 1250 156456214 156456217
    0x30a030905010b060a030b09070212041a2502090a0507050d020c0312040b0412020c0d06020c0f0d0f0924050a05090a0e0114090907050d08070803010305030912060103030f05 76
    0xd03030246000080e40150600401c0c16030380320380c000c400800e4568200682c1400d00d100314a50114039440503103840d0310070600c0208940f0580c450303906c0200c40340c80c0c41004200303511300305d0703103018400501080e0012104d00b00011054820f14264403030300c2408001800b040b143c0c007c07076100f0041561003a10700804425400d000303402260b4036403090700c0300f0f0107821445042041e8031401a4000c0c07250342071500d094948820800380c010301d80c5085402c140380e050810f46030024032420003a0700400158686422402d05460000780f2103484030944140103034914803a070800446030104a2a94501c4002e5444591010407461458109540c41c441e00208400b218841c40140200c89070b42c2c80c215140c580a032001521040701d5410001d00d1042c00401003240c504140b501180001c0300b503609030200c0c0f60181c43c1d0740d207800d80c501c115400744c810902c110042000542c202d4041980c005400c41e1a035840341040d590f00e4006607034090003400702da40d070050940740001f0018100c0758140c2c0d0f1140040d00c094000c6030305 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 156458714 1250 156457464 156457481
    0x703030903410c0a030615120506070507111f02010b010c170915030108010510091e0c090902071a06030f10090c030f20040c08040807170c010504030e01030e030a03 72
    0x2d50169801001003691020a000001c501500300032610040742c01000c000c07030189501103403503040d04001d140d000030300104585600c00510305060791214a981008000d11808461540c0d011003101b00c2c0041c6252500c1400a20000582c020003508499000540c0e01c00c038080c001420403440307951034806050f4400010b1041440141c88100c21580e0003402d40030300e0b00f01381c0003004565100e0041006104603a40080d0003080914814800e400300c24550f01e2000100a00d8448003a07201c200100480d030041e407000e0020301d00c0c810304559800c441d041c5402c24600302030425900c6030a9201007001480c000820385045401d800250242c1905902d2881c02072100d89021188005080000008100d89200340840035003d40d01c150f06200000700c8140c1e1661100d441180701c0c0c3e250080701e803540360784034405660055207d194195038170f0407810004003405981408442e08900003400586044040d04268001e43c42601e400d03400040110040d01910f140c801040d0843e441800040d0341e091183d0022620b = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 156459964 1250 156458714 156458843
    0xc030c1606020d0b0609010503041506170105010302180f010b09010c02040c020102090102060c2502061b0d0e0d08030f13060f0b0a05030105100e0c04080703030903 72
    0x5010995000350030110032002003552850750200301154008454003410316500d03011a021031401000800181035030002800161500070f40c0c07184180c40001310b41c0400e014081108007012181c4a0010b2240038141c02d01040703020709080c072844c40f810345011543d18042e20240d440001c0a81c00c0080341c08458000f0302003107040103224070b038540250700d40d44140010f1400319400540d6648a400c00a4a4103c0241100c900f1041c1000407009901c0b003101c1817982c07a03284480c411090442c50000544c0741c0542c08488184074100040d00116080c00200f1a2101403561205082d0001020400c0500b003000301d03002d4142e58042000802c14031412014a40c040c423070342c0e0300b80c00504a5854a104032810300802c131010b603542d86048042450480900f030001d0500302c0083c03142c2d1800d101c019010b84802d1003052000d038080e601280d04c0040c02c0090320701a2000600316000560380c0e040c0100003c80d64441601c0ca000012104000b0305007850a110300d00d43e4004894000700803024400c040490f05000703204 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 156461214 1250 156459964 156459967
    0x3021c02100c052812020a05030412051e0a050601060c1101030b0627030c041b08062b0b06091b0a020a060501180605060301060e010e060f0d0e0d0906080c030c 70
    0x4000c0f0311114801d502010510850003050b4051a00c85e841d80080c00c000030030741d0b01014a1200066000084406882003441018014a40c6e072400a28100c4801c0e02c2e910650300083c1e02c903c0000c0001000075105000c1c4088030801d0760384483c08d940e003841e2f025020740174140d540b840e00c100d54003d4000184002c4054500c500d0444c0101c2c10780f01c2c6250030710700e002004e6402d02e2010620f150400034440350f41c0f8111000c12280b90518041c10900e140041520140329400b00014042d40c0d03440c2d40303541c60b01c0e803442074070803480001c0d0071494080c442014100c92181160000c00e0443c102000f09a2140001c0d052008004015014aaa144d0070400c0c3d160114800ea8403160000b90244c00303090f00030400794008041d20100c40040c14250364894211030f0181d00c003400100120380e809502605410005c3c00c00001b1034074600e022445500c254102e181240800080301c01c00e024441c3e00100e10f243d055010b680703044011a0b0220307862100e5204210004240101203402c03081090700941c0c0000098000a = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 156462464 1250 156461214 156461233
    0x2070c050301150503010506100207090f060302100203030603060106030501030f0b09011112090d0c0804090203060409020d030c11041a060d060806011d0903030f0a0f0e030d0603021c02100c05 84
    0x70303094406003407280441055401c410812400e00340126a0807810840f1503140500c0c2418001355101400d00c035694500b80c4400c40070115402030b07405900616000351420380e0103000180f010307580c3e900030707034003140244038000001825611074400c15058a60220000c0700b411030036240c1d40b050360700181050429568905400b00c0e09a50300e0000c108885d0a00c2c0e1020b0503141c014905130811840c40e1664003400603024041000489400c1160140c6803255001078032600c42d203011400400004000a400a040209180925802c009040855403084090943c46038545003400103680e40a10f02c0400c403160348000c0105403804401408954903413100005400e136455540c2c91802c2405e07400b80481140003100c10003441500da8542c3c1c0c2c4240f02a00845c6141810090900407000007001155000d03a1841150b50a00064022a03000440601140c0c0c0b1110036200c40e100405440c44100d20441c20710481c0701c40c2490119021000c960010003680c147d01c800b09054800005500d030450b414014103021 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 156463714 1250 156462464 156462469
    0x40302011409032503050123010608041104091a10030312021606060609050102150405120c031b010f0b010201060f0e06060f041203080108011b110717030a090e040305070602070c05 79
    0x1a842c0c03811503215044156851800d05908540b084d490a0540c1241d00341c3d023841d01203207100c2e91f42c1151300b9072414100c25901c03410038074039654600056a500605040020040c09010010704030300c001d049101d0001915441c4842007802c040b8800103001c50412281441c502e0100e40c0075121140518501c1404180715907980d400729209504080d0208030f0040013803100b075904000011100c3e8104c00c8411040c00c080d04e9251396840e04032241440d1500006040c3c6200300280103503004e81c03140c50703420032300c2413a04803010740a041d05081402801745000002d090030340c8140203143c00c8981e616006405541052080520541e008248030380064040000901c0101c481c4010300060141c000c4140754400b4a00c0c0c000c3c0341f40c2042e0300c0101103a0401c0682110302010300902411000395080060106140c00502d500300882079005250700d441855201d04441c1012005003541c03d40356a9a401b91912800c014050002c16a00600020300a0018000044455004000d046c0c000d040b5443e0315035540e0300 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 156464964 1250 156463714 156463753
    0x303020d0204030212160e01080c10050d051806070306030803060904030201020415030c03050c040e15010908010c0e030709060f0b090402070f06090b060312090418020307151404030201140903 84
    0x145c4150661085255403005415103102901500c80c4810700241c9502d01000300b659001095103051040500404e1840040e00071000c49a80c0c4096240a001e941343c0202c0251003540441500e00050181d20001554903200b40b081d003065950040c803050542d181e10091120f03024000700102d096660821000c2a1a55540105000710507680c0d404102c0300098800102662009000e2509000c0107200904c8911100d0f90034a80c40608070000c18400c0751207400490368405030390302c080700f65480c1000408010b54441c01246010400f5400c841d502c603559980c510445e0301510505803c0104a0814008501c680c4000c110880c1d0080005d828115107403100c004405005904440080d81ca0f4035030010440c01da524070f81c0c001c0040b0054041800d1071485003078184150311000340708640d15088160f1081c0c4207c20403c20580240403208610b4a80352030000780a10900c0020205000309002c1d030301c119003c011141078030350603510100e10240500b02c1004c5500200c1340664103005110200c90800d03034284 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 156466214 1250 156464964 156464989
    0x21c032003090d110114010b0d0f0609020c16030b07050d0207060c05030603010c08010506160c030b012d0f0b0304060b0306040318050103060e060904080d090507150f0c0303020d02040302 82
    0x340000091066001d85451003e032074013455641800707a485200c80a14010a0440321903a400c2a03640036210b046900410401050301c8600d442d2160100c4c49008680c050450968020101c1d4126400d04911070000c040d5071100801c041e6201d000240074a00c910050b04010207515000b50134803849a440720103481030345218000180c0040108061413809000d0100313581418280b0040c0ca5040c070000c2010381c4140103441240380b00300c0e21040200010409071100030f41c2c00044049480d48c58008100f501c2184141c100c0001c8010006c00c8900461680b042d411075556000c6040403501e01610040300c0d0704000d000340c0309683e03a0040e49066841c00e009052041c0c0c42aa154514400f61102641e15003030f26400c180d04152400505204083d9540710305504a042206c4480c0a41d5451070000c0300c0d482900600580340b0b01700700c2c0c003d08200002440c203064500045c81c0b60009100303070400312000c060640c0e01c41d001441074280f500c0400d010380d0040c05011010310303026241c03e40781d401041d0f4140142 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 156467464 1250 156466214 156466231
    0x90c0f0d0510140601050a0e0f0109090204030f0303061d060925091a1c1815140609070c03030b1207080604050f0304030203100b0a0f08100507021c032003 68
    0x442125a50741c000f41035040d4820824209141414080749005046a40082410380640391020612000b6030080d003402d8002c1c00d0740403095545d5616441c02020000790300c14100d002c6414007901048503410410b2011781e88008129807459546c4000420001040c0540b05e40403410721420591260341410810400c540b501d0b07100d2120261030510f04e2080c05150304400300f083c00c0140f000120010042c2810020501d03610400b2580d01c2c942c0568501c0b10356480801403002c103072254400c1c8810581e03000300d00b0030304808144440301d58442c0d00344240c0c1d9030f00703c400c0400940880303022000a4007a034481c261448025102e0344540d510b00d03481c0da281c010103801c2135906502040070041045401c00480c0c03507540086002e5810103280d40d01083c0c6d240210b46540b601a5107540d003107025616031100d031000903c61030901c628060b5450411a4490106540c0c0300300b12400d250000341102d00001b401c00c0250a02c4240c014048200d202c101e0042c8510240c0301c032a45220b2080015000d503ca018501a040300c = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 156468714 1250 156467464 156467471
    0x60a0315090218010f020616050f040914041403120711070803030108032205031f1812030c0c0206030c090103060902070c080f060601050a030b06070213050a06050405090c0f0d0510 79
    0xd00e4009803900c17101400c0c50046500c198100300408190400900d4103c3d002d050031501e0b1544151040d20034040c64000c90b40c541c0ca040c010070b10007800215031600480c000c0041810f03114812034620348074442c00c4041000060b4075008a03000034401c0d00114200060030b0280c5051035218030707405003154800e9020f80740542c0003040c6221420102d5810340c0c1c0d0440031034001c80750645824086602e41074001c2e0101c1e0340c00040b058031000d91110f508461000c101080f1207800d2130300c41340340405d002d1300e020b982c04000901d011000c00e0440e009074a00360038a0b800500b45800c5603108450060940e1000c0800c50415071104800038080300d107030000d070100903c95642c0d03a030f446092204403840d25960a40b031003581d6000c5801d008807660400f007201d001c619685004074034001404042500ca101d41f0200940041300e1640c412090030142c3e1001307000d986001030070300110341c1d51000c02090307400680e548244d81d04501c2082145290a009065204001600c0a03000c03070401d17154142010649410b58200c6601d = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 156469964 1250 156468714 156468757
    0x1e070b1009062c09030c060702031314091f080105130b0c030c0d090221010e19020a0509041a040b100608070e09180f030d0606030b060a03150902 64
    0x5450049038068540e41d500001c111040300c250a041c80440d1180b4807103503400f140881d511080034011210030303015038400ca44440c140014002c2da2a0320400d81c161011141c8030f008107120440c80341100c80a00000c043c0d0340d068a6004a50645403440d814100703500010040c00100c600e401e0060a100d01000b640200b104025800c00d020046002009015150010820030442c8000075058404544041d20000f0f43d4104074400705091104280050700350701058120030900007015042801105000025038020301d000034405100c2000b1305e80300942c0180303084400d00c034500b00380c072005034014091250341c0d640040c2d42580c808602ca0548054440ca80c50004100768044805204402080c043c030300800c0e54070300500000c0008412030f0300c0714404d0b0048008038101c04401081d015071840d4110a82e4114885d80e400944c4d07030343c840904101240c0c14800001340d0980a80b0603400c405001070b00040c900030680b87d080b0010581c43d1103510000b904e000303000c515000c10f880502a4407450203603403601c054 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 156471214 1250 156469964 156469979
    0x1d040507090905031209010204180e01150f060c08090d08040602060106051e071103030c010c030b0303042702040801140f060409151802030a03170703050c1e070b10 72
    0x1803680040e5140ca061801160005074000b0498004101048000200741c8882c107001d1b02910a13940240325024495008140c84030540c0d2046010295a00c000c0100041340408181a86901d11481019152a42c02000300a00030244080158462000c09182031521400a4140301516000f035858180214091180341d404111aa014013024184941411058100100540404903a207000160045071030000c224800c2c082d0410700400806480c1c0b111143d041c07903402440b004068900080c10030507a50104d05010003103e0a941034841012014480f040d2106401c15142407807056540d420400012040001e01c103042d164040080c0301002c500780080c501c100000d000e40301c05d200d540350540340c8001400744078070b581c031500101d80085020b000541c0528112015207901a4042c0294050141090b91184006501d40c1781c4820f084003d86503907508a04903034040b42c08010043c010000d000c041380c8040b00350b404402480b4003580c60301718140e544d5103800c9815203070124a0314a1840c1805503d = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 156472464 1250 156471214 156471223
    0x15080402101403010605071b140f01050301080331030606030b0f090705040e010209130c030e0a050c0d020a031209060306080102090a030b1314070e0c03090d181d0405 73
    0x10007561500c4400c881ea45001c2038903d03c0113105038424400009242e408215859051a908040c3c25001011032a603039500801c0074072200d01082e00c5030611a4030940f503503000f50142c90607078403000025410150032075090106004031104c0054080411410343c11107003401800f01e40603600c600d0000c00c500349585421107000300e010344802a1f0b030315080300b00100000c0006071031080754012100412954400b141701402441040311042e00603101403400c008107105030304903040d4450141d42c20050403849054540d243da0a180009003a50003d060302c148501c0e141e04243d01c500e00041001d00d02e15600e0355480b0000042e08440c0010640192003001050340610510008000490003517103000d80c4200054043c0565000040011600001150f00c0440b8030501041d1594490308010030441000c42ca9581d400030340c4030305400414000009548501003c0c10b5a0050303608a00a10780e8070416a800e03100702940d0301d000303400001c240b980000c12102c0c0010603036111480408102c41410941006da040 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 156473714 1250 156472464 156472489
    0xc0906010309031b0602160812160c060e1504060b0306010e090a060e0102130303090e010b040302090103140a021e0909070b0307110f011a0103180b06040209060415080402 75
    0x14076140040306400320b600400d125203125880f00c01500c41d201240341ca20001d02a8242640e603100e00b82510504121208006120341341c0165040d68240d65140320038203c00700b2581341c400000d440b80502c1c01c0040c0103a00042e1158105506651040300d1070120041010801c0301c003900c0e41d644541012000d1304040c00030350f0141030660351004a03460720580684d6602c00c110030042c030b100c0c2c1d1413001114180c3d00b94145c401e0181d11051401034155241002000038213540901070010145c10700000301d00b41a00201c0301100c0e400790a40b02c45a2854980200a1a20380461b1034a40209248400181e1702c43e100001c030015020040c0200d01c80c075405000c11010000d1412200347d0103114103000d0065070405aa600c0301c11481c1c00d03030020050401c0e10b82010340c1820308a96641c00e140c0200c408208030441d820400000b80d904105100d201c0e140340000c0350030400050180c01004d00425454140740e001044c02c040c003d400c50b40b0340f6690300d484d0f00b41850000500380024050206120852818100301101d = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 156474820 1106 156473714 156473717
    0x140c0d0b0316030c0e10031118010b03241c020105040f080312060105070c0b0d02090a15030e030315060307030618090c0501030c05160816050c090601 66
    0x782c0100728081115035044240000c80c1d0b00a8010010f44601c441900b441c2000d4910344400e030a202c0700c0c00946400603003100034003564007100680203001b01402414a6642c0c502503a8281014004e040080d010003481c1c044508556241003143d00b00842020400040900c24401601d480c80b43d5400500c020f403003d04005119400407000d405982e550150a10b20340e42c2d14801110386116040c1d004291519034a01030100a0f0030717802404007060150801842d02215100281002442d1780c0690340c1103a20001d900d1926600d4040c100361422880021811030402c0d01c02c2c4440419820059809000c02000181c0000e12a4000400614490030000c6452203001a4040503000d00c0302c2c16034000c00300120004540d413080c0310f001c0f6041e00b00c1c2e4403d424100440e038100b00001c0c20a6080da0740140c18400102c5844420000d100080e2040000782541c4e0320100c180003104100400050 = true := by decide +kernel

theorem cover : BRFrame.Cov 156294964 156474820 := by
  have h0 := BRFrame.cov_init 156294964
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156294964 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156294964 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156294964 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156294964 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156294964 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156294964 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156294964 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156294964 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156294964 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156294964 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156294964 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156294964 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156294964 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156294964 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156294964 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156294964 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156294964 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156294964 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156294964 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156294964 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156294964 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156294964 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156294964 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156294964 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156294964 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156294964 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156294964 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156294964 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156294964 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156294964 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156294964 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156294964 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156294964 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156294964 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156294964 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156294964 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156294964 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156294964 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156294964 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156294964 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156294964 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156294964 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156294964 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156294964 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156294964 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156294964 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156294964 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156294964 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156294964 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156294964 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156294964 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156294964 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156294964 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156294964 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156294964 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156294964 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156294964 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156294964 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156294964 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156294964 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156294964 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156294964 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156294964 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156294964 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156294964 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156294964 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156294964 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156294964 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156294964 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156294964 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156294964 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156294964 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156294964 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156294964 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156294964 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156294964 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156294964 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156294964 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156294964 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156294964 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156294964 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156294964 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156294964 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156294964 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156294964 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156294964 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156294964 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156294964 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156294964 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156294964 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156294964 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156294964 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156294964 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156294964 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156294964 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156294964 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156294964 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156294964 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156294964 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156294964 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156294964 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156294964 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156294964 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156294964 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156294964 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156294964 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156294964 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156294964 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156294964 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156294964 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156294964 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156294964 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156294964 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156294964 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156294964 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156294964 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156294964 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156294964 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156294964 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156294964 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156294964 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156294964 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156294964 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156294964 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156294964 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156294964 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156294964 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156294964 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156294964 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156294964 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156294964 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156294964 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156294964 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156294964 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156294964 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156294964 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156294964 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156294964 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156294964 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156294964 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156294964 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156294964 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156294964 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156294964 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 156294964 ≤ n) (h2 : n < 156474820) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
