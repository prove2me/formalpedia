-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2880
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T08:01:19.200886+00:00
-- url     : https://prove2.me/submissions/c107c5ce-dd96-4d02-bd1d-a59359805b4d

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 517805755 ≤ n < 517985611 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 517807005 1250 517805755 517805767
    0x613050603121608030103060236062b0504110303030c0f0d090209090f010c0f2705060c060a0c0c0506040b04030917011a030106060c080d09081b0d090506 68
    0x80600000c21403052444403e07000107020391a40300c0940d20a80c0200d80d15540047c440c8003042003910b5a403100c8041000302c60655103818060000ca604003209039100d01c00028400b5400c2c007801c4000840c00c42c03260380104000c024041d040004203c03c0714103440e01d42c00d01d401e02c65240380c040200c83c41005500c091270b0500d010b0b8a5800c1c299013082c082508e8060340c60035003101582d00d110b034651040c814040104142c1d925a200c060945460240140902c030080d074507546e038107402031500024030307804050a0008800b0070100d9680c106a42e440791341c00c401c00103208a25408017080031481307200000014880042e00280840b8150f0511034003034080e0300320202040c00215904603040c0c001c1c0c001d01e0001d0805448800d04030400c43c8242680700d40d617565001941d072000d0700100140365003108900030020b03180380290142c00e00c1c4107100020902e00b000901c41a6044150b8403003c0c205810005060b280da5070b404e41102900e0582c481c000040c400c1502d500c807114410507404041e15006090942056 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 517808255 1250 517807005 517807033
    0x705030d03020a0e09090102131e0306020f04150807080105060301122a08030406020c090609040b09030f1204020120120a03060806070c150506090f0915010b030613050603 75
    0x74100e82c10043c02c11585101c1e0320101c0e540d014803240106000030005135a8044106101500001f507842030aa004040000c03034001640c501c228021030f0f0308144050703a50603205e9568031051049030031042003181009000c2200390750000c200782c03207a5010b40f03901c0f05a036280e104100c1e65000034810303030500307202d40d40140c400190407400707240001d0f54201480d85c4411400e504200600020f81141e481540003160410ac015410007450500c000140d591131000e0600300045802420010300c045c140121001c08200032080030012120622000920207840b4501c0c41650054414142e41c1607001520b021440c11248541101b81240001c8000c024007424813450b0110211360401929036007850341c0c0b0100000d8a04040c8040c5110b0790707483c0d4840708070880c1840c15000c200c1c402d085440c0b1181c40c00301000f90320744403040c0c690b41140b17a07145440c901d0740d1594607844c81c1802000d005400c80246800001c1c20705607442c091402010101c800e862184003c9005030115101110a00d515900a81a1050038 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 517809505 1250 517808255 517808257
    0x21c0209010e031002030a062117040902070803040c0602011b0f021e0f12040e1923090606120a02060706091704031b1401030f0209040609091101020705030d0302 71
    0xa81030605041502522900c000b90401e03051000c140030f03140d0008104070301c541451151f039018040e8020811407480034400c014001030701c200e60040c080c1c801c0404c4d510812103140c0544000300828182513565052501d8102c40c00c2e0415641221343c0e00360b01c2004a415401801000a002c1c2204040b107050000810116a10000104030354258000d00310302401d42e0780c5038410442a0395110004080034283c2000c56440c05d51181c1919006403002c1c0014401183c506118071f4001c1810140114480060603002c00107062410a0807180e01c004484110079800005103603204184900588810b60b0390071043c8152541c816044010a4020f0b01c071000062030208080d07e1130300d010350800a0440696074031008402c07001005040030a002250400c1040300340314000420807828106840041e04c1e10f09440b070036580b141c244906150302c4201c0c019a406c040d6040d1060020001c10034030603c9c0d80d071001c1200820500e0000c0d01d8000710f01120b40c00ca540001030a9080300c034050010505509041800c40003 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 517810755 1250 517809505 517809517
    0x103050f0613110d060e0c1c020a09090905010b0405370b06041d01050105070305040e190f0207020f0f060f160501050c0d05070905010503062205151201021c02 70
    0xa1981d50f038903c403c205103004050901c203011010000b0b615801c004240e038410100401180d603461b4200300060642d0080701000ca500c403144007025803030310700040080c1c074040030715046403605c00e10f0042e030001804015000820294010b840030003950301c0da1442c40341e03101d22075511102e00d4040c0140d0340240380c5030000c5002c01c12255100000700960039800040b00b6520580c444a0149611045c11034200301c5001918018002401c101d49005402c1c0d80240c282d01840c407807100400c40c007000295580700040b12001706880d092030100f0204010070040340094028400503406040014a0240542014009400c2e0f4040040c038044c01d1203003501c46c1007429030021044140c45100350019000003030090182d41d005030785100715242c903460115024422500300404950400504400c1003060b030342c0000841e03401420903600e40c414a0b02000e01c00341c004081c00b8034200b0745c0345841d0800c60000300340610490407180850310030484000503102c0c14280d000c0c40040e540000f02400445000b1501c07503006000c = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 517812005 1250 517810755 517810789
    0xe010e0a050111070e0103080c150402010c020904020f03060103031107140603151309081206041802090705071a0702120c15040c0914040203070906030f0206030a24080c0103050f06 79
    0x100e40303900c80d40c4117090140281c0c81220340070720200e2480d0100074280219200c80091500d1005c03140381540009100400700034019028450701d80120301552696074003242c05040250480302c16507501c0c940201001004003040c001030290b00c41c04103015980074001a0b010b400282501c8c156147c05683c21510401d000c062640b0144080c03000f80001140d00420b60307028040c08650f41c0320650844202c44080e40105100c2c452460110000e5214030000d51080700584c0517118512690707564441a500c0f80714000000e00401c0300000c0342909d40404040941c402c0e501a4242c8020350040b000c40c90301405000c1041c06150040c03d0007032501d02c1c1e004c03a4070b6805070184401d80001660b5401000460b0340c180005816184190b0812080d0b080401c0b041000707240c640401c100e1180b440c1c03185c0100c507034444402803140c400000070800b032068035040269421402100c4400c0c41d0707050140e890b8080d410f84612540d50048800102c3c9a602a22526114051101d20071138250740c0c0000b0404e0821020181c58 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 517813255 1250 517812005 517812013
    0xc0106031506140108010302030d030b150c0601140a0e01150207050d05060403031413080d02040801050106090306050c040f03110406081e0105060609030c10020a0b07050a0e010e0a050111 82
    0x1103540d40040c50451654604002006424440c3c154520031209030002d0510255200400058030005641600c08515240c0081d181111900140040c0d00551116009032004a10f85010b11800308445041310f40e01a401c4503809541428440600380360700c0780d110302c460301500422402c82510300c8407400c84c1e0703684103917003150341c89000040c00b500326100145c0e51940300600700030401d60103126601d0400d030025102038036850148005000e20540c000d000700300300e8010965444012182c2c05540180c100341e40240125a103070b0100030454011484203841c090f080c40049061003100c0f604030f80036100000c0e9910101800c5131141183c000404442e55081039840320005a01c4c0020b01c10381c0014001841014651089180100d00356a0041c000d14450401000701600568000519001051003640c141c10403032400a400d86c04d0914001010300304031207500410030b84ea9480741c01040016031940711a414a40004011146080d0b0140e2a503049460b109081c002e560052020749100e0f103140d0125 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 517814505 1250 517813255 517813259
    0x11e02030d020301141201110a0e011205010305010e06070810030b070c0b0114130e030909090a06181a060f060d0e0708030918100b0304030903120e0405060a18020c0106 74
    0x18000ca0348244c3c4985411040b21003140c0d103601c6c06014807200364403804000c0c40742d0002c0b1000f110b41e81c41504d16074170500c00041f01c41812640140041014020040420406581e41c4c4c182207003e0443d40f42c590300d035030080f0360000f0341407070103040d51900504649814074020fa0035a69034000e0a8009010a42842002014900080c0031060641d000c0c0103808100c03092002c107442807021f419805800d05900f942010110b80b0025000000eaa0900c9002c6542d0682c5803540914282400c451040240c8801c0c200f68502060000e41c01d10310741218030983c0751500c004d41e101904000d041e025182e06601808410044410f890042d0140001060312a000200003401106113480d0074034952001060b0340020401e480903140212080c04092015a8920041d19000048080850171406150106003000c004a01031621511001c0003640e40301c0340c507552042c035250025000040099105108905080c009800c03401d0000c203250440e1003040c100300300c51000086003c0030b5049480d1500706990b8039040 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 517815755 1250 517814505 517814527
    0x110706230313170a02100f0b090108031e07051009080918041a1306020f0d0606030b0f030d171e040309030303140103080f03190e03180f011e0203 64
    0x114040d140900400c50300b4400da14103a071000e031200041154542041c0a800c1d403a68000c00c0c05465019031000020306011185541d50041440ba98501e8100501c0c2d0004101110008014240d400da034800d4603101906800400c1003074451404000c040e0340000d80c1402c00b60b101a00650b00c079074480d4002a06144184c3c01141d9800d4500c410000d00c2001141400107005808640ca0901d0f007100f44854104e2800c00c140301c003d03c1c0c489000501141e4009040400c50444800341e8075009000078040c010300f41d8803d4010064056a00c43ca449881807844503201450b0010350403881d034045465241400140c84850000c0c04001011300ca80a14044032404414140d41142c0780f1a030721a0b201c241c8240d0035420010212440068914003249071040140041542107069401101d00118000c2d507c0c3e85840324440c480700c0050031104010709003a1110000d10000c009005c90b04140c008052002401004000302d8649800c00c26020179110f00c000341034041d00303151056041c078050041300d180c041d502d44 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 517817005 1250 517815755 517815757
    0x8011e0c0c02031b0108060f030616030f050f0a0b090f0118090606080a05150405070302040903030e1f0b0a0e0c0a02031b150603031201090203091e01091211070623 72
    0x800c5030b104d82c980c0c80b410795030b00a40400e82001080c1d40440a100340d1501007030399444050101c10f0141c0102d540010200d01c20f40000042c0365540006204509140007100c41108081d500031070420b0519003051007c2c100301940900c0384003205c4403164280d180c94010295060010000d0301c845031284041004101c032401040000c014940080c002020142011030504610441107090000c0d4002884003140001608400f9030f0b80444d00014603c10510382500104400680002c0e0b602581401d003c0302480d030344400d006220440410300c801140d90041151580043c005c908800b002003002c54000c04031100030b40f01c0a60180126440c01407000d440d650110700183c00c401081e4820f05903035181c8801240c0c2640c1040c1c00360020760500c0d03091070080d061341a050040c0e0110f40da000c00095042c10b410030a0149981c1c0d05038404044146003400c1a02038074000e08156007044200034088440361084120740ba080c001c5001410081c2d003440b004440c640d00311010400c4006010f640c220101c40c0400c = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 517818255 1250 517817005 517817023
    0x50406030c060306080307030203040e0a2403021906020307060213052112030105010804060905073b0709290d0c0201060603020309101e09080d0608011e0c0c0203 71
    0x104540c01c2040c03070108010291840e0b5002012a0f400a014650001f60000141d6050f184086000c130950758900318100b0041140d200b0044400c12800700d00c4103680048a0683e003540c1c025516145030f004224051072030b8540500c030703010060f07004100e900301050455018201c03aa00c0301e13032443c3c0c03110f5a6900155508103411252001c9034100b682c01002c0c21010000b00d00650b200b00e10701803c562500c400030b172400c45c00500c0030f0007440e02c9102d004100907052003041c6c0509443c03218054a805860050002c0742810074081c004046140aa41c051290109806100311100d0382c4920b03000341840110010000b0301c04516482c00822603100040160503005000b4401015000242c811000d80c4001c0c29504c15503c00d0090510402c03c1c4020001c010520011a58901c9008142c95641030710500841c442001043c846601d0300c0100d000304030303076940204000d40e0004428003400b038480b00a1401c940f506410000d6030000040000e1808800340c0084821038003c3c101090702d4804da4000c00d060508013 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 517819505 1250 517818255 517818263
    0x10f11010908040e0a0e010b060301090f09021005070b060301060b0417101b08060d0b061507080304030804051c0824040c02010501090f0911010302032e03030e0904051509030405040603 81
    0xe44104171400905205101c40522003c0c024070601c000d010102e00a44010301500540c0c40e11850684c6e451103080c0c011440440c3c1c0030f4100d0322f4031402c0c0340e0014003a421140e8100c44c2e880e00344010031590729050048109885071400c40601d00340c50280180010181c01510309054085ca40c50b0403212100b511440f64642d5000c01c81ca40c60700c40781040180511802803042e48500881c0000601180d9080703d500c1d8081f00550300001081022064039503240950b0340f005003600d1001040004040d44005034a00461150080392105804a00c40008003040f4210304000201e0170703800030740d51144001d84120300d82500c020030300b41e9043c2040810195a01c1001100c050307034540004124001c02e03481140d0003440c03810001c108464903907503a240b50040c81c01c1024100f40e0003101040707400c80304940c100c2c40400b01805460700d261a051044d150070b081ca100c00d07004140800f900740c0640c2403500b21079100356805006000740d0074202d03200000e99900078000a80c2448140301c01f18003030f05d642c810321000e103001b = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 517820755 1250 517819505 517819529
    0x306040b280501240302031603020f0d110706150602031801030b06071209060e0112020a090f0e0f1501170903040909050304081e10020d09082b020405010f1101090804 73
    0xc0c2213500320380300d100d800c01c0c8040520400803c2148661b100700603c001089240140e910b00c0c00c00c544040a00a00c88031444003454441f00d824021080e000605100c1e00c27480090006030740f450400c643e002a28070468000d03800c00c0046142110805400306e802e000b0505000802c803031110b010078140e41020104403942c0000d00c4040c800c05801c03a0b8540b000f0701003854050303070b0320b404540024214902c1643c0075500035004108100e245001d0036500014006a40000382031940e15811100ba0500a507092a11080d055010a02c0c4e03d000364040d02c0c0c46501030310390345850490a40340e030310792000080154000b400188404a0640713014010110258007a600450700d490401200f00e0805007480b0030210401c41045c0b280c040302c44042804081c4000c001070058980301c0e00c40c0080050319000700007c0c200480040d0300b1520440107446e400c403080f0344000c4d0102e6070b0313400001f00003203114501400707000c20b03070a081c0c0151861140c4108c1000104540012030710070340c00d59a081268215400095140c80c0d = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 517822005 1250 517820755 517820789
    0x50a120c02010e04051603020d0f15030c05060405090f0a0920011107030209220236040209010909060908070308060102060f01030317040f02101d0306040b280501 71
    0xa0320144003406500c0131101041142050722031000b03215840c400364010f041d00030a061002c041a0760201c802a10402c0b0240881039090721022100c0c50240421618040d03041c1d00444c15081c10810394041d280301030044000703502c1e801004200c0740070003001d2407862512401e50790001140201e00c1c07040e843c641401d604107068644005003500072234225500a07030b8400c4038200302595a10205d01c2c0c00909100c60050300034405c2035001c8845020b030030003940103200032140c09010171006004884900d00280e0034640108482e4044034000401da9010354404000f000600109042d03070b00082c1020712907900040d44074502c0d6117000305074000603410760105461604200305943c05000e15640a17184030400f020940c119500503090b04184900703500d5001c0003d0001d0108107020694035807151300180105046820424001d10701c07600203103407504417481c0800030f00d01410f000450300e01541e40442c80d0201e565851840e1000280f1803044185c1658182400c1000d8124038480e083c040c190001d12425903070 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 517823255 1250 517822005 517822007
    0xc0a0c210e040f050912090a0f060f03050906091b010219060c030b0d0302032a25050109080a020609011e030605011d0d020904140d050c0c10090b07050a120c0201 71
    0x2c2c0f03210164450181c100020070500701408914601c1c1d0014681c45240c4420710240802c0c2d0840094100b420884880240800c40a4201402e43d032500055507062016544021740300351202001d03500104654054084900003810340203624201c1c0d24103104a8060070310407076149280310b01020055400da940c0c0e09084002690500030b60a200b88242c0b1000c0000c80e0588d802540c9200f030760403001001c0c02e050003d40026200e608405040d8070000304803210621490210074450f0280d07851403500da10808030004007540500800c100701c0da810400381080030b1140c0c09106040d40000500c03410064402c9400d900500b882c50000054a56070340e0001e09242400005031503040c6080e042c1030002c2584100c200b10741d039031007070180c0240d038181c64060598581e454800710050107070540e02d02c40d00030b4011034403c0540c414007604200c2c1e1030000329601071030716005220020079050942c0000500880041c081d140483c801811f10610560884421440c2e0f0746500403014039110a82c000030b112806418155 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 517824505 1250 517823255 517823261
    0x240703110d0302030103082205060c0f070f0b0d110c0f0312060f15070201030b03030309010b01090e010b0a210c03060617060a051c0f08090114030c0a0c210e04 70
    0xe07002d0404614550540d12039030f5440c05000003440c00a0071038281180ca50340c11070005001000d002d442c554580d20002c0619407604805d2144000c60f04c0741c0000001c0021081d0420001c0300c0340385000f146840c140910030340142444584140101208000c0c020080d041046922407a1613201c010315118886034500f8032400001510f0a40300f1018214010961340d60000c101110f255050001a92404c0a01c01079000e4000c2c0081d842d854007000c07080104101040d040001940c40c2603984040301d6450720b5645c000c0400a02414881c4a002d1214502b214040c403030307400e400d5a0404030013003031400030000c420035100233000ba6000a81c4414040141c1034010a02c21220810034200011515045d000720749903980d2403003a6882402c03201c0405855102a0000994154010110040b8180035003042400e950084090f2400034500c001c8a03015000c1c01810b48c0e0003442e42c90082c1c3d242c40c00042084900141d01d0700c068812120040c2e96201d6194100c01d600d510000b40e827110f406008140c4100011 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 517825755 1250 517824505 517824523
    0x90302060c0a120c021e03030612011401050f030a1514130210050f0f04090207050606010c030906050a1101150503240103021302160302011401060c050c24070311 71
    0xa041c0074042c40d801c003600302888942e405102c400c00214a020325400300d01e05400741e071400c0706081c03011404244020010009521414043d504940b041a651400908071410501c9600e8061504401130001c0d140152401d52480e40003402c5034904d03130b860780300d030301140303074804082e20003607568000254203c03840025003a130044250082602218507038020505a031180c0e41c02c0000c000e00080c45e00924800001a80d05050710750034000c0d215605d4118800c020b62155900340c03964400d5100103001588181030f2512401c0d070550311009411300d040400e5400e60850141d44050190800348407403101001d21a422020780c20703094540140340381c40103042c100640d00e4225151042480540c2604540d020038090443c0d50503610705005441e1084404000c3c0255001c084d800e07881d00da810401d141d4150440081b01d41400c00c211401c0c0d0b40c50800340c8180d040404010026041a41030201c1480d1086800e048013a84039180c010300070f40101e8996840c0d0040c1012000310380b1408000348618020401c40070 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 517827005 1250 517825755 517825771
    0x1805010c02090414011e1a0a1a03040303020702090a050415110a080907090504030801090b03071401030b0a1a04062006011710050106050c010b09061309140f0109030206 74
    0x501500d8603004202003100003000904140100340400070900c00951186440c5003801c181c2e00d5001145144220280c007880786030814190038101490494a050740481040394807801510800d032080300d50306c21050300020700540901d9402d01c940000360b10344504d001d110301126000003411b4900303482c22050142c072180c1e820215038902008580010032000440314101c1b2a07007060707102c5645000340d0900e41401034010400d001c1c1004148010141c2068080b410398545810a00030000c094091690714101b511034004100110170400702194082d81c8910100071015100200c0640c944110000b902c91a00c40082c0460340090208032003944544618110184c0030111100ca01a809409958440600500300809080f100c042c5000314104005d65a50880210510803580e5400e40603085801013440c2d055a942848181c1c200ca203465101c0d50322604c402810b4140381d550a141c564000c0003410340846000c400703d404c2c0e42c20034608104203180800c43e8000800c004019240081c01c040002d82900 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 517828255 1250 517827005 517827017
    0xe070e070e0918011805070611070317091c020603011512060b0c100b241e09100e1e060d0509010c03060510080714040512150601020304030b0f0421180501 68
    0x1790014001084a00448100b841c06808480c501d8a40d1820080940d000620300c5040b84144c0c3c00c0a101c0780050948000110742e0502008904003071039500441c0444029031041c02000140003090039044204900529803901107084000032175400d04541298001d0200309002280c801001c40041101144078031010707100344507102409021840000d078002c000d10000c2c040706030301d01000900c801902d15500c511159964020407660f0340d1203284c2d000d98003180c05441c04140b00120750307018203001021301d074024041c01583d1200c0701240086d20b000b000e03000d42c4001c0c00c0180e05200300351406001e000383c82c07002c00025180044c070000703412101c5581c415400f41e60143d6080c1010f6410151556111a035800e000c1c00414101c05e640c1620301c5075810003503001ca071440442c0c01c181070000342c04051000c0c6401c601d0b20390316074500590340e9000700c0c40000c01c01004335000503202e29090031780a410920608218400d103a002074841c034504c0d20810204001860301003504913082040c1e82d0000100f2080c2030007 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 517829505 1250 517828255 517828301
    0xc0301050a0b1c170d0c02070b031608151801170a05071e030c0b0307020f03090a050f2704050606040c08040b040201230c100e070e070e091801 63
    0x329000502d184018070300085010300c6441402101d40d110b4034402c40404e1071598400d44038043e10014100b1051000040c8110340c00411400da100d42101c1c080e41c0700b0300307502c81ea900610340c08540c500001047c04c0701002e02e00d1035800030391f21403814610300c04040703110343c0d0f19079810806001001030010000111580c021440701000c20b030003107010002c1d40da900a101c540c21002112109581c1c4891340000c256041c11000061210443d001460086940c2c1d03080e211401e4021190307680d82c0c02440309290f48030b030261004009900e841201101601d002070701c14501d0f964014280b00c3c4160315010884101240d0b0742c200b100300b2405110450b032151003200c00f0001e00c054048003c04003030b00140000d084000c42d0000c5000e5a0054142c200102c80c00481c11000d000109265011504030903079008283c40b540341252540c1189001e08190300c0100002021001d141072800da071709501c0944200103000c150303003040101d9110071070000c0c40f03039029031607078400144031084107800c40c1c4201460403010320700b001c45 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 517830755 1250 517829505 517829509
    0x60a050a260426070804090b010315210c0f1502010204080d08060d050604060f06080c0607080318070306020403030f2606010e03010203040b010303080606030709060f0c060e0c0301050a0b 82
    0x280c10b07005904912050031040345240d00c0510701040c421100419080400c1032410000305400400c25190100420f1180b5031a03e8015010359480280c003d0842000c0d04040c032581c1c2d04040f21050019030340071010f06200741500c1c1c8059502031500000403d41c104041802048204813138880310300c1c00f91008510741407624415a4035607a40c00454000c11a00a001c50015a61195161441a00101039404a08013860014001c1286281081e5140c1c00d0034000142184c004c1424001c400700900384a1030084c4503501da00c810b91000b4140c0c0e41541000316540c0d54201c0421101d00610b1040d00010303580c50031410054180200c0c0b03010001001240e40011080400c405040c0b000f00d8000d02d20200d4076211301c0010784c1e8012582940340d4256101004000c1400714040c0594100c82c0241c840112503192407007070004c3ca02c000c58008000c6040c180c0301b00051480f070703040b588902d1100d02d044180c40e18a03940b00020380780183c0d01c03084aa8441201351807280b4080c440c080e08040040b10410001c055000 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 517832005 1250 517830755 517830827
    0xf01050d23012702031503061e0c07020f060c0f1c02061b09100e031006031e0215030a090206070b0f071119021516060e060708040f03090302060a050a 66
    0x1508603000d4004c0041860b0740c2040090b103200000050544182745060840928044944640e05001c080e441003c10340403c000800c851425030090710215082007000f0510071964401c00315043d07240b207020800250f5800c00e1003803180308503103501e51001941048200929200b406420f4030210303070089004e1240300c0568800c617000300c84295040421b1404291003918510030040005805026580d00c14500a501da8809403d49225003040d20b0590034154404008645420000b9044030038000080d012061600c051a80000901c42c0440d100050b680800c40c50f070800c440480e00044000107020a0405042a06a00501c54a00514100d49004110350340b1540015409030b005243c266510030f45d00c4580c1d90b25540130441000e690f4440001406103810f8240e2030064030300317500d480142d4100c020040382e024000d9130b8942da1090a44c032507856501c02011020400c90a0140b840d6002005840c1c0c0b4002e4001844540c4802da00ea80440c2c901404900d6814184000b0403074081709030200355030b01c0b4 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 517833255 1250 517832005 517832069
    0x6020111121612020310030c0b030c070803100f06030e0c03061015021005041101020d0216031e1407050a1202030304091e15060f030b0a050f01050d2301 67
    0x840240b0210241d90340c241c0d06400c5050764905494000410050b1a0701280502c0045901c12240d078462259030b4a80305040340400da138004003c0303404000540204401102441d0880420075004140d69a0f8000381321803050311340e200c2e00100fa02d0300c40380c461400050000c4440400c0c141d01030000e621780070740790040c191341500601c14640529032410044d14400c10090014030110032040000d0300f801d0400c136004861000c01180144640c20310740030b50300c2c40400c400082e41c41d031501c1c01c1306907030856503010704100004103204100080024900013089141d410015801891405005a503003002c0c1440000c8550390454220401030851450050710300100702c40454a1b0003100081c0f040c00001040409103403e40000341d140c3c100100c171b00c1c0071460241410100e46d003d44410010505114040d41500cec007101807550310283c0050f04120f0b50901c01e010800c4090140b400d075180004040f0f0441c00ca601c54140007203203070f841d04c01055000030700a041c2405460204034248505c5200116008410803003 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 517834505 1250 517833255 517833271
    0x102071503090b012619020d0206120f041106120c0703030e0d260717060102121201090506060304020a060c030516080d0b0a050105090d020f040c08010602011112 71
    0x100c640e2158461003580610801c642c0000301403079550351070005d01014400c01e0300389100303042c2584140d089400002086800d00d081c6041c800b040701c055808100b006125001c050f60003042c2044600d85813a2090071217440389016060b8010303182040d0622080141d080681075000359820404840139101581c90558001100718507559140e1891600710090310b41c00d000e44020344100c00b07590405c241c00400c0304604098240c4420402c98800d0201c00081000ba18044040307410140c4076000590a000310a03800f00341030040b510440d51200202816030710268035074401021003001807103034181074010950002c0c5c4c2111002c2c19070420750009007a60171684203980038403282403505020113020310107481962a062050326455119400d180c4000d5100e820745455803031038030461403824075003010194140c1d00181c5d200703130400c0c07412402c0c003901002101c001ea91000c030401c0340c840503a45900072001034417007a60b81d40385194035043c806800e4807441c10660005040a00c00e81d413072241686030f4943c0c08072074 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 517835755 1250 517834505 517834529
    0x6090515091512160c0204091103030f0405090901020301031e0303090218040519051c0905120c181605072a080c010c110108040206040b130302041802010207 69
    0x2480c01818458400e5008281c0c0001191a44080e00d104a101070a203040c101003800300c1990f240c2099003141100e010502000c1488485068007604142d848209028402d640c0b046198005100007031441c1c1000b40380740c920a1001409003c2070900300d5090340c01c000085c001b0350644d41075649d0340344440400d021700400c581f52200000c003410300c25004152400e802512218550109181038041c0344811101601e0501c115201c0c1c070341404210b0840d000c4180c00801800000083d10000d800c0368420707408100400c140b140010410303a41e4804000c241d070b2200c500400e01c020304a403c1c48103001249082074420709000b4100010161080d0644841814a2600540d20f00c240d01d0b0415035440d492814000c640c0101c550340080708070040700503081e528105c1c00c9866860008004441c80111090002c02450352480e040d0031a500414005400a1005142d541050740340c442c42e1295030040c0407584194a0080c00420650502c0e200d52135140c10103004010311111240c001031f50b124510b00c00c00c6e11400d0 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 517837005 1250 517835755 517835779
    0x1021209030a060c12020403030806040501050f010e060d0e031908010e10050402071e06060905010801022a19050c0114190e1306081005060102030a0914040915020a09050a060905 78
    0x2104170104c00c1c0c000ca101c40119190707501c0f0300700201b61140032110a8001d6141100114141c544601803000040f0140d60b2a403110000300144407150700410b092005050b225440c1c48a204400d20140050000905520b00e0004010100401c4503030107900c04801c80200c0400d0001501010500308191403060310701583c1c83c519440d0001d44294585039903a0440031184e500000c101c504e403c0141258070b040e8040c041d590b280c0d080d0038200d00c14404a0751070f0f00034004040b614021aa00d031807480c1c1d0f413004140c07840e0a024240200144c0c0340c0060445d081d03001800c403000c5543e004030b007052034482061806414001d1055645644a00d03007100407060144800320311400d40d4404528007082084a2414080a5031320f40e5040c0c1c2c0ea00039070200c500708908010009a00754030010a803000706202d5541c109550703103031510009041034420040e80d0443c1e25105208d0200d5610317000124210440040165580f04c0e00c0c0e0000c040d8001074019610031040243d040004560280320340701a100e0464002405007 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 517838255 1250 517837005 517837007
    0x7030c050c102010060b0a0f0509011b0503070503031003060c0e0607031b02120706030515030a080307050f04030c030b0f010602030d0b060c1501210c0905040201050706150501021209030a060c 84
    0x4d1012514980d05030706005020848107003800140c210442140c03501c42c0e1074640d0070b406540500541d0b0030180055080810003030320358080010021124005d4060700e285c41650f07251541954421655242c40711200b2004004000d82e41c46000e00c003110707501d440320b801d121560018006104d240303800342c10028034055800d410040301c460516181d50081c6540700845c440c007070013500c0710050b00c1440042482c00b000a140200031204510b24010001d01070104954595924402c03038001601060812901344007000c4150b0b1158000d0000d0b40c051000c60615528601d4405103000004000341d0b04404c14400400c02d0b10b07000026210140d104001c04a00b00c018131010070028020300010303d100c1e1058011074040310135120340c001e05860754085500c000094034007807424101c0f00d04100520707602c0c041500300180c244030361080d60001e00c1490700500e44600c81d11040c05489080049014610032100200050340e01000388140381007010303550318200b03081e55000079164000c915010704400d07201c0300056446 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 517839505 1250 517838255 517838263
    0x904050703090c09060b1206120604061505030c06220308040311090105121507021f02030a0c0f020d12090605160210150b09040608060f0103051219140d0207030c050c1020 75
    0x270030803c00c2282c034246000d003440c00c0036041c1c04400314032941c100140410603080200c0c4001c94032001414551a000503050b90b82164104941c0f15021120001da010001070398110080000758080c00050020210030001c0109140040e44080c1c4200224a480f000031000800c0c03000135070300816100c0da840e55515030140c1c20440c010102c81788010380c041203008050b000b540a0340c003a0560351002c02400c070144200b40c502d0101d400101e005603000c645401411803203640110f00d020007601011500240d555a00b0059034801e55104400f1410120095400c031b0341001128a02c10304940184400c00c14000c1c0c00d100324105000c2c5001d001c034001147e014540700d5410010003030580d01d0441384a854078214008407480c081c00200c40c0d44c02540701407005035503030340240c0301d01c010f400a1011080e030040000f80c940c030f03e910200c00c1c0810428054403828400c18070140030001c0c041e80341e191030010711303141c01d60606400402c450703c94409d17905100e010350b03071029240000000c01c079011042030050441d480d182c = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 517840755 1250 517839505 517839529
    0x110d0b0a110d18060507020309030a1203200901020114011503180b1e0108070f33120b09130b2203091d090606010507080904050703090c09060b1206 65
    0x11050a002d00803109803d00402e500708a03000e0700c0200403544035400d0490f00c1c0e205080402e5030540c0010303044004520120f0809080c900141000107808042c80c4000405c0c082070010f06110b19800b0a00040342d503020302410341c030311100c5100c104c0340d0341c103040c802d00000e1800708182c0b04069840000e00416a90510204100d90704006440524a040d02401181d0703c01140c01900444024000280403140013649006407952282400001c1e030800c681c904811a4071032401a180140c2103010003169604100134403400c50b07aa580c015861285010b0300151740c40c61105901490712801044100720980c900c208000b81d00105080f003c0d1540d12482c4002c0d0b200400400c41210110113101c03c00d60000034038422100386020b09203454484940d07201c465402140d81007d241c01040c00a08158880d00051a01512071810359003040c5e000002700d412510102d40000109a50380700348014045490280b01c01013801d41c005114190820200390000e0056050791460003d02030301144a6540c0c44143c640 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 517842005 1250 517840755 517840777
    0x12103051b15010b03040302070602032109151f06090509060114040906060207060e01030506031c142a0a050c06030406060503030307030b010801050a0b1603050c1009110d0b0a11 78
    0x795071144c04000351580b003910220054440c280f400903200c5e0001c0f0603a20b00c4842041031229807680f9012000c0342000003404412580100d0805101c0d10704030301c0c4001d009420b0480740d40d120852401d007079410011070f44c00c6070062041030031040049941d0343c4062a4031810030f291900746064488080c400d1801560000c42119081010112301170b40d001071040211021a43c9015508800c1401035040b01c00c1522083d4140d041010240001b0110328a400c4952a940c50003c1c00c404d00780c0079503210754010b04020a50a1441d4900545d1b05071180b001104403080c0801502040000f95282e590b02c800c9030b99024020107000c0001800d11041d54805070042a000d800d03255a403a02400c028010002c8800440c0401c0401002240303c2c02c01c40703000d030f0076a1000c0c00c0003460803098070802c515049441d6011410403608120720808c4040a0029085a0014071b0021500844501d0030480c0440d8054040f400b0300e1040700140c0c003281000380042e422007065540080c9401c10704e08006601d21480c0d0720a5 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 517843255 1250 517842005 517842043
    0xb01170a080a0c031214060f130e24010810050705120f10090c090e0c0412030207081c050715151811030c0909100e0c03012103051b 58
    0x803951540114020f00b03054885e5452030b22103284911410200c4000060304d04542480d48002045800c14007c80031050b00300411401200748494141e5090382c1c42034120301d105821a501e40c00c0c220f42c13640c0c1d51243c03003111048940a10340c100120079585070784e144007084072903440c3c0000c101d50b81d00a40032508110400e021250759817400c0480707454000c0094800c00d18441c0040000a41c1540c0b52084050000c041e60f01c241c805841c020340081540300280c00501d10301800c01001441d080d40580030a56144242c002c2d091062800d2241030800c150207040e0151819600b241003146a4088126000164811007006c106107043e86898010302c075031241c81041400c48500460098590b0664900001c0c0e01c030000d004a4420422400c1940000e0342c250302002014041e900c40762520f001c100b54000002072006c0d0b142c6a4070340700e28001500940d04041d85031800030040c48043d0105901d41d0b090701600d001020351442682c0c0091552241c0528241d000041003903000e20312800340614503c4101d44005a = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 517844505 1250 517843255 517843267
    0x509070f081302090a020702040623030d02010605031903050c06070e1224060d050105071805030105040f020411040f090c08100308040311060706050f01030201080c070b01170a08 78
    0x181181050311a140c0c0840c00900000d8a0324030300c1d010740c5032480e0780a442c040035501c400414002035086007400300d0740940ca41c00046000e4210b0406902b1009044c040034241c02c5450042c1401d12041100c440116418142c0510060300d00040112072042e802c10b200c40180c020b418105c41c103001d4080d10b80d00500440051006041e4404110f88440108942100348500c60000b40303655611080d00100b61152840210070a004042d4100b5521207009051281c41d0b401c10b40e00e003401c40700b040b1402c0010454821603c1c1f06206d040482102402d015070007003183c1c0c18183c0320036201e0601e03036400901c26074580000410012103031064030018032100035507403e41902d420f8000064050408070000282d44a000245000080c5480720202c9410076182c9142c00d09540350446803222400c120b80c4c12a0042001100080b0240b061034441c54440107000c0d401d5045100040c585030002c0e00e4091403100a04c04100800c00702c104040c11180480605030074415950046810700940b90009400c0403400700c0d074 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 517845755 1250 517844505 517844507
    0x9011a07020d1401060f05060a0909050429040c0b03130f0302010f11031b03010e0103060f150b0d060e160e030f0616030b0402070f030f020106050406080c2416030504050907 76
    0x4284c081c2c6c0c004d50014100c00b5282da051242d83c0c00380310409000038920752020018031070f1950180b0340150180c240350005032100c0d42e00c130351015412078284801c00340e03083c2004207000d8502803020282605542191560500391550100e0006c00003000d00403404420700d404c2090300035448024401260441030144018412441000b5002194119100c00c066850661b0100c5c070b120403681650080d00c0e4110b841d0b42182c907044000c0015803488a02299100140400070b00e007448048001c2c6209440190348403085820841680c0181d4000252103064106000400b91600355020501d0b1003450001207114454002901d4a203c0710070340700d42401100288148144298241c12620342c0c40e89050100e0386a41090000b00e10a13103201138240785801d0b4074070000a02c60a60b0101d004218030010403003984840001d000c50301d83d944001841d6014504d81104c81c1024901041011400b51007661b09903070203440982140b0a0a0700c4801c002601c041003410540210191400741c00d015140341940d20f04888 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 517847005 1250 517845755 517845761
    0x60507020306060324100e0a050a0c021b011115010602010e0f0f070b0a0513060e1008060f090417030c0d1416050a110f060a0b09011a07020d1401 64
    0x80141e00074001c0000041d2503007000a0440c1c54411820480e800d201c584d8119826a004003402c001d2800a626100145800f1200c0060340904580c2c0350000f554100380224004840207052840d09540240c0003021102d500d003181500c00010a0910980d07080c085071080d0308110307660314410008140e05d8004940281d0542c07042c0100c440301000c4640c0800c160009650b541c3c0360b82690783d04c2c1c0d4403469061008104c0600584294444e506003c0c1c2003014080440c4004100d6070802c100161090156407c5854030740d404032640c4406041070b080301e041c06008111124203440c442800b0f4107208010604200084c0701044911110700e0b590b9403a41403100c0203164980c806500b8206c060300700083d8000403c649015503015502040340055007005241c010b0313540d50442d642200a1000107980c07104619414444a071010405034080e103103500d0001c0c544070407152070820040c0180c3c04c0314018005505000c07040509190100351880d2241c0d80c900c0020200701c4450802820f8103062020300b01c071404150 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 517848255 1250 517847005 517847017
    0xa170c0115090c080c0c0d1404030f05151b0405191a03041718040504110d0c030b1f09050a150e0403031a0109030b130807140d0212030a0213050a0605 66
    0x65911100c075221600401021b02940c400f241d0b95400811a10500d5409000101480034504421906160b034039101d209801c0070460b07040d101c6401200e08098020858041e065000025024451800c403111385243c1c041d000b9401210700540c06080030007001501c440c2d0160041c883e64422002490543c0c40d240350070742043d1012280e42c3d407480b03107050411003140c041d20201c9403c00c1d00d9443c8080c0450412020342405803059a19081070f5220210540380c0c0102c0d464507600030128a0360340c600d180360201003c0f10080100050400d04142082c041c008100c0140403203910340130204540d1110584a00200041d60440a1005d10080c0000f0740c10f040d400003511440c029102041030007003901c0307001c25080e9031030700003800280c041e40107000045515240700e0704410070740801c003012040344da20000c2c9940304080a1f6020a81101e2108400c0c40800196003444075920242c0f182000762a8400054003014205e1142c141d00818080c04001200b03031007000500e002449030100341d0340d1f403c020300a41e0000c = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 517849505 1250 517848255 517848257
    0x390304060e0d0519020102070312021c0204080c0f0906010e0d050c030a0c0302040c0918020f27150408030714100609020a0f080609061c050a03080106110a170c0115090c 74
    0x3e2040000903078010700c08c1c0c9100c1e03a0035466450300700c6001840c000003540401880302c01b049181c030750b801c4018514806000603203e02c5000746240c0740800200100c0c40718210788a0b202d0400d101c00c2240706d9074040480e02e0720302802e60304c1d01c80c41d81c02481d2250826a50180031740d05803213200340010a000f4900c91074804c0368020390303080240f9601404200c8499466025016101950391214400000d0f0381e4000c08543c2440b407182800d00c8100c84030780208406602a07201c08044940304c01c2c00074940008003180907010821103074905444c1c4074105031070b809200310140100d244803440e9550b1007000d00c034980d101050403004214041c2c4136910003000b0740042207a02c0015400a0822403a41e0184161f603014000003050324800f542c40d182041403000014400d2024089440f5450700040c0303041101082052103034a80080c91b40c10301d07400410f04000f6100c80781c625401058a034000c1180354a04416440781080071607030398010680418050510050140e000f41151000080e18900302d0f0f101030405103131 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 517850755 1250 517849505 517849537
    0x304081b06250804030e01091214010c09060210050a1113080105090d05041401171326070605071b0c24021f1b0503390304060e0d05 58
    0x25002c40d48068010418010124403c90085404240100c0c1500c0032080145800000161181e01c00d100000300c0341422a852110721007501d0000000303000316101512a480e0094903030b890000000e5503800c0d8102e80d80350700e0f41c0e504045101e51359540c00003100c40310242c00c819591042d00c1441103101d0250303c40c3c004194a0700c00802c007a0200030448407084070300780d922181007600b400c58040c00690041201414412680b80120b02c010140c3c141034800c5003403007c400340c0044e807410700a40c40014511882c0c00300070010301c03a1507801000000c2e9512280c01c4200001c141c1d86080099031400a01d800c030080e254040c00c41b1504000d42c000304001038032401074601c041c400000b800c070520511560742d40000345e00105030b0104050030042c00c82c0c2501c15180340c046480246c4e1715031542d02c00302013804a80059000030402044030058104070549560044502c0f14084081c400403201c03481d180c0300b40251000020104041c0201500000200108071040e541c2c3c10b0b40c2110081c02d150322454840c029500 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 517852005 1250 517850755 517850791
    0xa032007090c08160315051207240f0203040506040b0706141008010e0f0a03080c1e030444090a060c02280504020309011b030b010e030a12050304081b06 67
    0x48030340541c0420301d40d4185100c11190407e008c1006008910300340e82014802e20300b0009050300d500e08882095406050207885003a0300b05002090303030684420403800c2d540b04000c1044980c851104640c00c41c4d19041c005903c0c0c0580d80b41c494041c00f48505441000b40c4030005003c2041304861241c8101e500442c02000f032500c0803000d440d1601b0740505060b055802c8101e0356400b0038041c01440342d00070126202a840c00044004802c13100700000800414150048100003c20071002403032408058a4020301e14001c19003841480b2079001c1c1001c080c1010a810762500071f400402c0e003510182e5070000c005241081c1c4410009007800c126403403c9c0c0c4558011866422900115000b10000b61070050540050606000c14000030750710191100c0b2042d036846510005004500820b20021220b0359400301c1d0b10584640010001800e4605241c882e41105520b00000743c3d2103c5400403901c06404d10070340fa60b40b9828031340210300801c0c180c0400c0036440c0c6401c42c9001404500c0d14465180c588140300124 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 517853255 1250 517852005 517852007
    0x30f0a020d021002240a0518070b0a0e040e0a020a1502031603110d0207060305150f0910080a0c0501120204080a030c020a0f080a0c080a032007090c0816 67
    0x20411000650400714062400c0054200049aa40010114011200d00c448145c500740c40804e000c01000e080411030900344407100a0034080c00c1e8100c102c0003108081403214810842c0c840a962040d130011032000508281803d000707800b50714640400400030842042056549a00c0d81c00c0400c00300e21400300700700040b030b144203070795103204004509500444c10480220141200007102c3c003000e40c03d11002001c0c82c3c1a120302040510800c111603400341c00c1c110700c0d100000c0e003501c17005000c41c401505800c0b284605501d81c2c07039030a00311950403944411075894070080d1614100355900862034900501c1e07004000e00070304582100881750280d80d079071003543d0786403607040c102c0c001da001b9110300c0d070800c81e542d030b005c07074854008408581c4c0020400c00e940f503507030342d40d0800c0300030582e10689503900100091428000340c081210b00418005000e0071246d01c056a004180c0b178544507407000c0098103a0030002d0801d00800841028151042c002c0140407803d401c0646804004c840000400340f0b048400c83d811 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 517854505 1250 517853255 517853263
    0x905010503010203041a092e141e0c040f0303050c061005090a09060b130b031c050901180e040b04110a0e070c030507122c01051606090f060b030f 64
    0x92500000ba004101e2980d0500d0080790707002801031140c40c4200304123100056241c0e10718660050610801100200c207403048001603030313030400000c140501180100208505130f03c007480041c2ca85040f007804613983d20b0a810f4124051604030800c4020342000100405801c10028040044007070b0844110f030383c8286454041d0742c0d09016481e00070303066034045081d007109a000740024521424001c101c0030b08030408107641c0301d040d401a28401c0d445207048089401d00f40a020f1b048983e0559000e201c2800c044064214420580366504000004101c1004003d10820f05406000e041200d02018142401d2083c0d0a50301920255040382403491481e040740b8001100c04101d81c030650012013650342d00b000503550186051020750501c0420051500001c00340242e0802d9090240c9903c142d14400301034039041c0880304020409408000540210305a81000036618070300b0a42040300d80b20059464184060265000000c0c01aa0207a410008014980d04541307030311041501115800b18090101ca603407 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 517855755 1250 517854505 517854511
    0x121e070e011208070f051906020a0f0201140601080711010903210b10030f14040b07080612070e100b030708090c0a12020904080f0307020102190f200f030a0201060905010503010203 79
    0x90f03a4420425500081c1307401d92101c0080c0d009209440e005980c030b80d030800401c010904100c517111760016541c100150000b212500107121407000b0007408842800950002c24083e2406050104440014011920640c4185030b507410030302c000c2c00504003d1030702412110082c0241c26102601c4a58009458658030819688000040120198480b48101a03008002c03c200460034940c80329000c1c81440204009540118441e0140fa160392034003400c0101050b00140815101c0c9855041c002c5403004000340301c00903a0000c00030541c0c6600d41d04031010403403045911265111758084200218190400007440c410661802a00c951042980803c2403010582c010302400f081145411001340c1080c900c0d041d8882d2081c4c3d98549884075070000301070300b07400407604440141e4001580c401c11003120802000b4401990404014600e0316080281441c428416144e0b41d600130306400c0040f540080098100e1f02c2d40c401c1c190b940d50100010024080e11190003a107030402e05000000605060500c21030744 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 517857005 1250 517855755 517855763
    0x70605060d050a0323040303020f210301061d10030b010807181413020316090902120105040c120e0a02150a05090d0c081b0f01030603030e121e070e0112 67
    0x14110021359425030340030400103024101c000c218140a0702c104801c8009201540c083e030001d0004816044610389886402035030f00ca10980b158072008000d41c10001600e065848604080d0070b030031041c00000c1362080c4034600c000d03485000441c83d10441d58041d07114074107655082e650804c0c5641d0750102030750009080e000070070117088c803444200316481c40c41e244441c50150007010406c841841078443c0341a40c02c107403a0100c500841f400c448810307540011340c0900074840f4000030350921010000d10341a2440512415020396211821980c4003803054592200c0c82c03074020300803c88041c2210040395500320080f000c90080340141400c1c15407030300e4182511400307000c5070341c0c0d00e191022010501402203400c44040f1940c3c0e10107031000c1b806010502040200c0030302528031441130642c1c9070030081c1100801c1c100c24103040c5040024008a984101d00e640039120680e02940da01e50810401c0d45040c62281e18040046000b03421006a6031010a45004403806496614442c1e601c501c0892500c0000e008010 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 517858255 1250 517857005 517857013
    0xf062105181e0d0c14010501060801081c09030f06021605030c0d17060f0d060e060411010c0b070e0a0909050307030207061b02090a0e100b01110c011709030c0d05070605060d05 77
    0x7000c203620404110141340c0c03189201c0c1860720303810506142991070030303003104000c41d92190040c00020303810040703902c41c140c0d4203030030038202400590040c06895042c00054500703606407865405010380f5404541e01403e1200304c80290b01098102142c598100100b00c80c178a00a85540c50b001074032500542e0181c40c4604480c1c01240c581d241040a800d4403554001e40000c84160741d10041012445464998200040078114520b4149040d501501c0c08210b50341c1800b030401005808103290400b5036034031292a003041c550b4200b0b61000144080c0c0e042c2c0c0000105428031181d081040001300242507650b2003602140c42c3c42da1210750a44040382c1180040314080c82c0122120091b02d41506890740000403034a00198030110241000d003010400ca0300b44209988801145400396880841103083c0034035180600802c020f40070008106940442d0303001224a0040042100b021042c8211800c491300c090848140c0c400d4038901800d10381003104240d0380d10340303440c00143c50b900b4030f079492460080d80b0030094 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 517859505 1250 517858255 517858273
    0x9070c0b0a180506070c1703010305060a0c0318050102070204060f0e07030b040609050114031e030f0f090a060c11010203070b0f07090e0c0c01050604060f062105181e 73
    0x1c000101500c5040c50072040400303060401040703061050324010138440d41d4070840c2c01110304010526003541b0ba4035008100c0200010030101384081030b036540000b40c1020100720001c2809003140a0416005c040c510750300084100c4040140550080800314425142130024660302c250308a48499944030703c0c0c0300962030000191055107c1e40c4104001072008000042c503030b4840901000700ca800760840d01600c1c500064140032031804200c85101c1c0d0800a20301291040784441c142d449005615005850400101c0c1500c1040d00710025107405000140518803090b95030071004210942001d815a10011038141d400b840c0c2d440441110032160700b0800d1240705485102080a240310010001d03003c0022003e40403078031810307800403c0d0091480349401c680320340000480508481780681003d00c50740c90300030f0030020035801d4502181115828106a0000c1c0e400c1000203008051030604078566500d030504028040100c4040c00078055a510200c84408050a2072115400d01b8404241050b80c805840c1d = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 517860755 1250 517859505 517859521
    0x8010f03170a05040b04090b0915010f0f11120a1b0b010e060f090103050d0f090311060703051e0a090b0715021e0304140c0d0b072003130509070c0b 65
    0x4006040d043e00d0f016240650310101440300743c10030740010000301c0c1c640720701d000289840c8025603004440000c2040410f9045000a410341d142c552250b0305128035000002021030244001c42200c03042d000a403405800c030714001d0052503229410110120740581008035840d048520014202036100340d5030081a400c068403200c0b02c1c9801000b155128001065008407912408101c40c02103104034014004400854800742603054449600340401484507820404075121111b00c0e402d00005807801c0c0e80c0e030b8946040844482c031500070401c001c1d2032001c600101000000005000e04581035584045207512600032001030300c210034000d00400e004000020440300940e0042800091303c030481b400d05420300b007261080d41c004540c01c0d40c0010a941581c40b104105004482c00700c1c4040b01d0030a2107a4044e52140380126001c5c05400400065070000312280743c140d41c000c8520315100007100d484407090020042c201d210b60103444c0c0605600c40200b007a40b03000f003440e01011641301402d200b1039503840c51 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 517862005 1250 517860755 517860757
    0x8010821040b1c0e0c010905040203130b10050a140f040b030102210907050103182d120e0102190b040611070c060207320a0305160608010f0317 63
    0x1103a040114041200042c2d14100d01c004000020781c002c040f843c91074255902c0c9048907450000180b1980082d4407441080e0703400244a01914402c8900680701d4952042d4404101080766004149081000901840860340b84045045070400c5680c40c410544855100300c0d442c0d1180744043d0020b5100c540c1e0040c624050b042040fa0840140006050854114810803000030300707079035401e03108140014080c0310441803048602a10003802d0074018890b140801c150048a001c102070100c0840500c1008002c02e00030441907880408260f031441c008040c00c200002001404003140841e41003594102c0650020500101290400224400700e03070141e1282c090101008100312402507945a41c4c0301200100300103044c005000c1c0651801603030070150041d2425045800c601480070407200040c4190b25005001c103c02c598003003904004a1014022816150a0382c000034001c3c0101440c000100e41c1303941e201c8046801541d60442903980e20141d07074004031424000a8181076104418501400030300b0 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 517863255 1250 517862005 517862053
    0x280609050601031707032f070b0d0609020c03071707080d1b0903030203030a0c02070902031f080610120302010e0d02010f0b010e060d020c0313080109111c020411070c24080108 77
    0x2101f4030100b07d81c012075040070b050707811055040d500407802c0c07154a1820712a4402414205c5800c45c90f00480e070900d10340d08d0184840062802550905000b0600d040a068400407640f02804648506440584401402e5025559080c250000c0c3d50518014800e814503800c51340c241e0055455a00c800c18003401410601c12510154880c1c000c001071001c03024401940300e41e0140f0988071995504c11950046036602d07900c0405140d00141c03d106070070941094900071156960881400d5004500d001c2e0301402403c0c50820b160300404103140c036000c1c1c041d002807c1e910304a01c02000702c0c0c041c1200550f85030000c0b01404d50410030a00c0192812152036000b4628249040c0440f4240411360980c00301400540e00a20301c107944031080b9504100b41483c0104d080038040f1902400c0d05452a060603c0e100c0c2010040e2040351210a0400c076080003000311000c0039000100b08551036200c0c0304181c07004000350781403012407001a01c2d8102c028450f21917039040c3c0d10040c0251040400700c80c03d035002c0040301c4d = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 517864505 1250 517863255 517863317
    0x12040b0a062103170106051c060e040c0812070305190c020d062003060609010c030e0d1109090c0108040b1b07051b060c28060905060103170703 63
    0x800c804100c0702e2418140302400c0d00100401d00c00301d4410320b0300a1141c0c404034800100841603034010701590340c00400707440d240b007081c01052094030a22141d0501800d0710743e120b0418018820240400e000003d4407050075100b141044480c18240110026818420705202800042e4240b1060321f41180d00c5510240c29071a52606202d40059a0009100e00c4900e20044070b21603603c1ca900c94443d00a0b00c4040d4200d5240c41e482030a40ca0524086543c0c4d108a5007107c2c108883d42c488031040600442c1d44d620f03128009004407114120502e009a15072181c400c1561007460035070002002c20800152040032544103a49026081c0c880d40c1d56844030a0015100068480340340720000019402d40019168a500031002850307550788104c13803e4039591500401500460007006098401540000d81003040c0c0a0b00c3c481500ca8003814140c0209900038120081c15141400b4490040c45800516207060324000e85151028002000d001c0956120321480280450062260b040381c810240048a50711140c1c = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 517865755 1250 517864505 517864511
    0x10110703050d0503070906031509021309020301230a050a0b0f0d11032514090409060c0e031006151416050106080c090126070f09051b12040b0a 63
    0x12607950a051090200503440040d401004015034030b40e00c990300c1c0005051604080000c10703005089001c501c000d90154850703958000422084000c03220b410307800200f403980c1c401c5499585503108140030281c0c00070003004580a002c030b416820310707200407000f0482d00014503005005145c08505546c40e04002c5c203000c01326a007404002c40002c494000c0310701400c1d01c1720784580e603850b213000500e208a189100c2e80503c102000c50703107007115030000303512211092030401c0d042c1c9804d00100080c002d04070707042c0300810441c10310031484842c1e034002c0c603040b1940c4800c60584640e050380b1161001220828854190313406001c207180d1040300d004420010080d181031241c140361501500604036807608005007103030503039541c0c4020030410100b8480201e040c582100c0100c0315501d002148041c2c643c500c1c0301002c0c001600b032aa400d004008000325801011007280c00c0602995a42c4100010202100c3c210382d40c1841c203c4245021111000300d5500076841d440d5a0455211b940303c02c01c00f000018a202c44d00d590b = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 517867005 1250 517865755 517865759
    0xe010b1e040e0708010f06020d0c03050c0a080706090c05060f0a0e040f021b0706020a210504050904140607030b182214010c1106010b09150307030914030306101107 72
    0x402401c40703c0c89903081e0740301d00341254035101c00d000307185901d42c3c403040c1150490004800426880070107070b0074403a09032034419101d400102c2494100046c2c00001050074100107249000c10040d80c00c826990381c00750301d0b1210903e03a181f09105c6188590b0466882c0d56808016030302c0c005004400d8241e2001c40a440011710f800c03080111401ca034800e00f404203035010528403080030301c00c0410001000c2d04030340c4040e0034140307102c4d5113810781d01d2000c031106440905401d000480740d0344524256130084c4001480000941810300741580001e8174200075004502524001494040c02070252080e20b03000542940d03450202008002e2041030064400c01042400b80c010b0485c140c80028840420b81c020050700148480d40304140f800c46828404110512a8001e40c0f901003140103d642030444448000c5186c0c0c42012000003000d00360f0300c034a820710100b000700501408030342c10b90000401d41d12500c0060355810301081c00640e44c0c081169040e41c842c8840c10001ca00c0c512800352800081d0b890021500103c2d = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 517868255 1250 517867005 517867019
    0xb1b100203090a0b01050f0a0515070f08070b07080709290a050c10060302090711030d0f0b10020a0804141201050a021c090f0204091a150301060e010b1e04 68
    0x1910585554002c0e9102d10340081c180940300b00c0803801040100c910452441c100c20219001c40070900c10700703100d0310304151129900c0ca417140480301d88603800030240c101a601450010015007000c2c400307855120002000a15050042030302d24003800c07858a65417036040c6044290491007400700420b400704c3c80b40301d1401162032183e501600314440580c41d219141d00b0140c2c035261602c1e8007a2251035485044c07010800258a4142e2001c5c1c01407041d10307241012046145440c3d166110301e580c1030480500e400c1440c0b480d4990355002c41e401c880304684507450758001d139000f03da031141a0380d40546030010030841040002e0074083c4006400b080684004a0710348407210040c03c42d0070481c1c03000201d540001c1c52922410311b51800f51951840d40400b00403e0b06a6210b4070001c01c001d10000780255a00d01040040c4002e100021014424504110456190004247c600800ea10301e8042c0a90308048001c078043c4002e41c4110f040e51442c010050501c2c4018900315134030548500680d420010820011800c0 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 517869505 1250 517868255 517868257
    0x3121f0303020601090b0102010b0a03020405060616060f05090a150b0319080301051513060804030c0501020d1406041a0d14030f0403110103020a020d03052205060a05090105010b1b1002 81
    0x40d40a60042d02c0c080d890031507800c05660031190b401d411a450052420045e942e800044000e480c1c0540e000115031791603c000c0781044c81107800b007500b0b205510010b00100209500418040841040180700585a1150890341d40701c1114000f049403403080000140c024440e44500e5a4100007002c0320806c1410300800d5851f19400d00064641034030000050245003010005050b0001d1280600e0b40740151160640b68608944e00441c410410008041028140302d0034119022982000007195102c240d405844010044550195007424101002502520b0984141100c1401c07101141c42d500b9840300400919030941c180c11120b80c101d646205210380070402c00340c400000d41d42401744e511070031810303c00082c11117035a01c24109030041000305101540880d203146101d00605001c0340e2500c8a031807401d9014071001e440c81503080c0c071040c0c0f030781400400a003c0c1c0c0908104e21003040366484201c00e80b400e94000f4021007201500c02c0216035003e0007541b20b038202c0403035178800307413410400328545503003d07 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 517870755 1250 517869505 517869509
    0x30f0601031b020303060f0a150f05070606060c0605010509060d030302030a020705010203010e180a12050d0e01020c070f05030c0d030c08041d01182703020c0d0305040806100803121f 80
    0x513840130081144900f00207940c140c44802c101e660904481c505071140c1d6107118a80f02030410421f203401c6074403000f4082c40a4030034043d03120009020094441c50700602d0384000b00c1064800500b801d00010b800c1c18036021050140390050104c0801820607101500a90710150038030308456401c025042c00303d80c0038030285018000c1c0c03001910f0a8101018001c100c1501215440215002804148001941c9209008060a050801d140c9410206040000428606900c40340d90350002800c4000040081450002c2c5d0321a5040c045d000d9485005169072841c01c0310555800c541341ea030401d000710f0301919a5a042e1885003000c0c51a203500d6111503082c018001018901d83d45400005000100942c076910b0440d60007200d04000342103088042040400181d0004440c91540700380d01c0c001d0500c00e1140d0b040700c01014180c21016035292900528641c060b12882d00c01e0b0040501007110040e03903802e680211070f4068003d40c10100c0c0071207442103809020380f550350341540724481d4004440003207402c040 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 517872005 1250 517870755 517870757
    0x2070512030901020f120d0e10060b0301180204030203030403111507030504050f0d030807110109050102030c210702060c370f030e03030414010e0f100b0405010308030f0601031b 78
    0x34442c450403002a1900000102449050b0400c615082000811109a0f82d240b150128082480000c003248a03051024032400361507401d04003400416048640b10046040741d80342d5001c0942c0080310003400080f4086c6000096041c0c104100810101e034941e1400000382100410340310a1103030190315401030354050002200810b00214003008035180c20034000142000a651400c146c1407203540007416007030001e1420301880f2104c0e1850000d054250b100012480c0d203c0021943c90602c0040d0726515007080110110090400e07075000c5096400c076a03124080c0c01140c0003044030b91a6070300400300e150088203c0e20000b01d000f40038641042d00c442188940f6003413903600340380030000004008000c44103410307844052508120401070800310010450364402c0c0c0045451042a01c0401014090315422551100c10700c40c00e40071400b2000d000c0381401c4150101c940410000d0003e0341840b080da1800d00c0b026107980420f100141c1111071205105600030014035001a0502c2a1040e8041100b07000da1480 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 517873255 1250 517872005 517872007
    0x70b0c0a08181e0301051008060417090316030c08030705030315180a090b06060315060708040906060207090e1506010c0201030e0304140a0f0b09120f031903051602100b010207051203 80
    0x3601504086c4a20340c0c200604047d0114800d01b0150303419a991806400204000e00c803456012106204909076000150000e064800840b40b140191035650b00c180010360301b9100c680800500c3c9030740082220800356021001e18119a12480c03003001658019880a40004070030701d0092498100790000c6102d0000c1c0200040c4884103800c0c0b29010354001800d4500603502002400143c060746c004818100d6070031035103503a9500306490503021390700a0754080d030b944605100000c10603d4020855034140c86400e48100b0501c0c64025080b03580e06407080600b48032402020204042794490b442c2007441310b0048c18041849032003071101a00d07690156012040301100e56040c60058a003401554005158a007603086a09003407602001e40c80c400d01c001c040c8070340a03001a040241400340701950860300e004003525140c0000002c155080600f030b400311400203160100141d8012280d088502e03030011503600800718404421400b1005009410001e13065100b20040041c05a4032800e80365185d4000c08051 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 517874505 1250 517873255 517873309
    0x80601170c01020a020a0902090f040911131505010f03140702070617010308030a0905100203040f03090e0f01090c0e060313170720060d09050c03070b0c0a0818 70
    0x340d05214400040c00e0441d00101032001c00b5a80f13528034441928100000140e17074034800e00019454140b1651481d0f040f0342400c01c0502800003d00001c0d00004080d00c504a8401c1d52501710700407201182c400010303042411006210075441400214a0070645060014022032444840c2c0104401118001c0060340001d90522003554070030900000c200c03108602c0041541981c3e00d038007181c0802000041d507990384461110074001e04000146025616240c00c56807420103041c0213803c0900000140d0100d002402d000809100c002420351083e15a0a1035500c16420301031040054078000980101704415014419081da0310744c4010740c002c040300c041240014201e03141c0920000d000404081e014001442404041f4616120300d160f01400540c00300f00c500c030341400060032401607042c90522075180585440801c58002f4852101507070880807161555074510414203103109040d1488810341041c50150001000c060141c81c06861a502400315a070389200850451401c11584003946125a011 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 517875755 1250 517874505 517874549
    0x403032a050c1002070308030f0c07140c01080f09031606020d061e06050903071a070f0803090c120a061802030d090e06100509091905090c0a0b0a081609080601 70
    0x81880403e035540003030f01d2003d1454840c910700c0c0c040240307a80c0b40c1c0c0020794009401e9020320000c03a00020340c00314510305d03c1304030341c166940d55501c0d80a81034003042005002c20000894011042c3c03042e46428015890090a1003d000c0300b500c640d2011103209030240300c010401c24007401510064a81c8100d902c0c1c0b8008003210100f43d00d00760b81d103c0801c0c058200004040c6032008074040702035070181c145444030144900c1c05460503126210740546145981c542100c04c011a210040d4001e4070b05004940c101451a000c100102e68181c03554411036002c411584e0000c2ca185d0815207800306894071064841031036801290400602d6806c1d4000140d500006008007510580101d40102050701c0d981110940d079600030703003135106020b0118460074800e000281e41d114940c01d0380e60030405034030051116050a60b46250f41c5e000d011541e903c1344040b040302148818404c030036202506a5641c0d06059034891220168030b8a1940800c6020414136000100c0d070254200305c1da42c000c01444020390744064160803 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 517877005 1250 517875755 517875769
    0x70204050c16031b05060a060305010b0312030109091a0403020109140d090303031a0a0b19030b060414011715040b1906080a02270102011107080403032a050c 69
    0x3181c0c80c0500a201210301c581184204101141c1e05080038061090702e00d15031050001e0502000303150740b00301c00030003106403070b590030520440307109100034402c4a045204050302c0c0d03c1107400d00011407400780010020741c205030b0400840d050295052000720f0464808030f000e804000c45080e00035070745030b446040400046039003010f8580c54100141c0402c0c441644001d0409180d4031029041544450722851100496010746008035002881034079110340c0d8803054043c0f600511904541c0860f082441c2031f0080c06406082d40681c40108403500c0e240c104151561503801040f15141081400c10092684070b07110030001d4094844030b8450803a12507402d040000399100010058040c080f610102c520101d860b1404809641c51800c040a0903030300d42d424480240203000c1d0300d000031310001d459009a0080c1540450141c01c1c00c0e4000d00090424400f41d442c148528200200b07140703000c01c000c00100784100312112005030000c580070f07500d512000030080c1000e1851425113031178001c0100b040491424803 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 517878255 1250 517877005 517877011
    0x40801060e09060c090d020f0d0b07020106171c1b030305010f05060a05030601080a0e121810200a0803040503030a0f27020307171f09120f2307020405 66
    0x401444580303041303000140a4003600540034050b01a500e418000c55998513003407041c050f40980240008009030900a040c1241525200050f51902c031002c01e0704a4841241120368a082004109800c11400b8101c8601e41c2401070404000518120302100b4007070352a42031045000f541c2c0400c1039414142100148951548418844e800400213130f42003540180c15294440d809007040600c6541e000c0006002d40903039410503013203001d08c03c1400c000176071f0325001e404145100e00c181c02e07003401c0c110240010907169000d00310100d090003900220b04004059240c0c18841000f0a03a40100201c3d070300c2c0b1440740c0083e5001c441c160404420402212450304c40c4446a45e40180c0901800d28589526004407820f00e21000c80d00da056049401991820413107017004000c030700e464440c442c100109842c0c64a5002c1d0b5108031080340d00148520032040b0740500e84243d50031055840c1304642150080d101c500941d80044c007400300540207032811500c449c0344000302000e050760083e51000c0720320400040b82c00007 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 517879505 1250 517878255 517878271
    0x912110f07050a030b0603010e0304080d08010509010b070209090c0a06050a020c0102010911060c030f0c01020406110c10030e100906020c10061409060118090b0a0b190305070302040308040801060e 86
    0x7010400440d980c00039003400f1240c100b015802c640d1104800300303004d010525010b040d10300c4005800200e00030000741203d2a805e0984d107812180c0d88030340030041071820a100c4d0b800740740c0381031002c0c0025182515200c0d4112014000f115903484e501130210b5400c00081d4444008900007085541405405000d5aa8181c00900c020884400c6582c1d903201406d5410b0072a50199201285054400104008a0b1102e0458500301c94440c241901030f40d000c0d51040c01584002921031280080704040020940c1d0304200040505000b000c20840840003030580e0445c5400e40d218044141e504844588036000302d49000340405aaaa030011040d1072501d240d419080d50703440c2c0f8290b02080903085101d09440401d20444003c0703c113031180c200407124522604002090000340d10382c00a400d0409070f002c0c80d2114000d66903003c85950f120038078401d0703000311038111081803030f08070300780020703e1095206650010207030400500346a100d0f20ba101c42f9400ca908000c505030354818043c400020b810301010790202c48 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 517880755 1250 517879505 517879513
    0x15130e01120b1e0a0b0604091401080c09090c100915171b040311180a0510060c1208040c08340f0b1e120610110a0807060912110f 57
    0x6a115000804040204011360b51540d8a0340c0a0b40d641e164800c950003001550002d0104800f0654000b950610a100c1c46070140319554007418141054540e0b00e00c6554150040c1040011540500c02100c0000c0030710010407140c8240410f41d5800107500113102c2e1429034070420801c04002c0061001030740509010201070320401e194540503500c00403101580d9012203500021420000824248505110091405428442044000b85603980034502c1025030a01d224040e65840109441c47c2c1c0b1181d001034111540c242401c00014010360f4511b130082d115220800681c1d07661140c40341001442240c000c04c0c0e030122290703000ca241d241d801106588a41c00368492059240901d41d0319008014031403c440704902042c3c030f084848803581c1124803202c03404040e0796100500c60390207280e85c50440d000c9105018550600c18641c0c816910401c0989128000b0721500f00c0980740d451035608101000c80c2c85a4880d5000e000040d0402d551402035880c0d52600800440110102801c110300300c9500d1240c2c0c4c2c0 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 517882005 1250 517880755 517880791
    0x606020a1b150507060213080f0120070206031305100b011d01091a070c03080a02010f1116060b1809120307020d0c0305130e060103060b040515130e01120b 68
    0x40101c2c0d60303038000d4206050460307850605240a6010b4000c51401b8100769004620024076258041161450001100001c025241c034001c1c1070440c2c40200000d00300d900105014200c014100340c3d0045410401c0c20b95058403814480c0c6d502407407c018141c413800215100c2000f0341495030001806100a18264010084005400002003030007506200d056540043c107107041803441980303c1180c9600d07030403001c001d20315034503400d200029500000c080e100561800d240d41d9014507007449800c0c030800701006807078078289034202104090500d4040942c0c0095039490005881d9441403503401042d40d4200000c001c0c1c0ca4010031142c1402503c1c1b07140041d20804100704440a6800320351031084100d40c1c14079101c0307890241000c41e0a070007941c1010b526504c043d01c0103e0741a8000f5803207486200242d03001e1044a8944074070404a003d903109068208951840c05655515207102502c2068101039103603840315640c01500248160a134448070005a0700c19245052040403250a0f034411513030094000303244 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 517883255 1250 517882005 517882019
    0x1111209120f0c240a020102120c0712080703151202011e02030a0c080724050c0a2a02060f0c1e0a0b0901060b2a0604020303160606090606020a1b 64
    0x1190608264400c00f48040c0c400341081c01c2c40f903040340031440442034640b01e4203817460282c000d5000d115401c1001c0c102e18005050300d4000c0c001c03540c201d948034103440c0c120001032900b52004240504070a05258941d01e1000c2d0302d00c41c10400000a01c10300080f49000707040e600000d0310740c1d00c001092030310810454a46080c50f039000002c96496441d107240002c1494060700b000440b82c0a4850001c0c905240c50b000132805500486c03900203403901410007004540c83d181d02014051042820610210300384003089440c190b2500c07510000306040004201500625a000031115400f9100c6100c441c8000318aa440901003084524034031060402c00b0f00d16512b611580d07555800c0e9004000348a008000300095228000303400003401452400420b5443e54101a411300c909001c000b1142003c0358042e03070001c65090002406801250090040c604c1d0107400000401100d10303a900c1643d80541310000010003440c2440ad00c1c0043c807043d4050080341c0c40c1072912544940e9000d80f201c2a088900c241032100c0 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 517884505 1250 517883255 517883263
    0xa080309060f0f071406070f08010609030b220b0906010605072019080a0b0a151809081305010e03120318100624031803030b01111209120f 61
    0x1454120456120f80e1000541c640030b10541c000100301c100c400200080444000517841c0c001e030300c135886500e0000782100e0f040f60406024410ba500041420b5400c0000c07030709485100d03400000c640d130310342a240c4074450300808010000c1d2085510703194110070000e440c2d0f03040c03000070f001d4510351038540e2500c81c00c0d80f5085100e507170386404045107451000001041c0d6450310365103060003e0342d40031490615a11031205407500c62158080e175126800800160390000300c0d21860810000300c10401000740c0c02c0c60300300d0030204500e403400d041541d030b203130f45a801082500014100c81c1e0640c0c00d84502c541c1c2413030001442c155150140d07500a90011056000400e012800e40ba4271400c80c505840b03650181414503407800a01d103840f02c0d21203142c5030012078030700d0110011050400c003820181c4400384410100300e0403030300e001341c03041c1c1a842504050000039200341c010040400c1e05242c580c00d07001003c100642494505500c4a20000c00020246141d04144031652003104645028246070010041c1503612 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 517885755 1250 517884505 517884517
    0x403030f0f050f09011209050615041e05040302070806010326070f1212020417060f01240306030615080c04060315240602060405060a0911041d030c0a020a08030906 72
    0x41490100d00030340d09911a0944046c07045070800c0902c9900da40382051506e03081c0c00d03a490b44820008496550035402c041c081d441c12090484102488540c404203040000c08016000702c0844c059440c0028640c4002c000090203903010b0100d94254520321281d200c030001c20b151080d0f00d00001417100c8800300c2e50000e001c03141c141d003004101682c039150650403580d65034040b600606240c0302040110b400082020780e00702e0b04c60103400312200c0c1e444512480c210318a0910841c15401a1400700c060038024803103202d00107030020b08000c55040e0310307940c0d020b0a407070541150100704040740d102001038000801590803003060580b03040000d90300f55141c0640e10702c002a0301030222034035001c40c860302100b44040e011019103032441d580142a11140d0081d140d400560f4151420311600c0d01251000f0341512501c040700b60b05c020400381c019540c006000c00f4210483c54412910182d1100035043c06e418401003205100c4c500184c0911040c0b0f20401070b500070716070030900c12a0310510020a20340ca810301200c078 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 517887005 1250 517885755 517885777
    0x4030503011409010347010f050f090a0b0301090c0e0714031501080405030409060303200d0c0204180209070c020405090606060702010c050a061e2d150e0106050403030f0f05 76
    0x2001415181c40403410040c0380c440681b000700090130b440d00a0120300c00c424140c030030f00d40c02c41031002c0d40c403001c000820b203030280c405034007080404c0454000009548040000c00000c0e001045003806a1160010304020398010550b0318064000c00c15003940c4030b001001b40340c1800c03042c6801e50078071480d00e4000200710046581801028000300781840300410a58000782100c000074842903440745001010210b403020728001823280804151030084e00461091495111507488007952003560302048094440c07080050a01454800c0c66409a00c580a8241c440c003280d407070741030341c0c2443d43c41800200c1d0070082034613845810000602c04c5540d110301c00c0f40c0400c0d07024130306032a041c016420f22a04040e81c100c0014641c1d494217006100305452101c00c85014000050308100c1c1c242107a41d0010f0031000700901310040c07403a007004100040e0722503000802803101c0800d24242e5a031900d10720145520288c000d000820320104040081640c0289020004425031404005075481000060145d000d0000544 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 517888255 1250 517887005 517887053
    0x10c031a0f0303090a03050106060f03290105090a0b0c12090a03021009180c09050607050703030513030807051006080d0c060906020906070c03030305060f01080c03100b03040305030114090103 84
    0x5500d65000c10959000c0c1200030440c05c902982c1c0d10f8a1402480d45100e4100403c2860380160082400303882440b8000300e414132154094249025442e00140010840d181441420b104415103a1202401c00e00038084100460340d803107800303a62051800801c20540106840c0802c55140c2d103854001c0120200d0b60b0541c0c2640c40314880304000e540c3c00840f508142640042d814880d4001d04464011071842402d0f61a00c07007180f6154003c2c480180f04101d070140040d4400034040000920480c0100320100d00e0004280c403484e16079807410015484540255011fa014012040d903142d098400c007001841000b006100d0001c40d1103003c3c0400c0c0d030980002d00700c0d581c0e0301e0001040c0300c00398040300e500b80c1e0001c0c111545e50780740c0d02d0105442e40303840c003060300002c0c94200022520300781004003080010b01612055010740d40d070064251070382c0c001030803440307030341e415010004036004c86070f01645c09507200382c441ea5125810b1240d240d607448044800036209403003650041001c1203ea82e60355400c080800c92030 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 517889505 1250 517888255 517888279
    0x1401030b062e03090506090c01090501080106020312060f0406060216090c0215060d0c06050d111e091c0f2001050715060e1906090516080417070f0302010c031a 70
    0x143c004118828002e0810700a903000c125069070007188407030144030240c036443c4145440d440112041c3d0401d01034040035a000300b000303882d0742000ca0714150340702038002c200c031101481c0341d804074041d0703486a444040564020041e10440701c2c0300303020510140103880c004201518035188001c0d540d82c00d0b0b02d5428001400c1402044498444490683c4100d402200348070856a45000041c003540c040c22070007401618140d03c0303034080c80b1100c040300d080c04070030140d800200001007100034555200100060784280c400c0c8040c05041200003400d01441d00400c4558620318050806461701511840344222041030344600c1c2c1500d0307800c081554085600030040b0740c0304600304c02e0400020320b00c54000400b4100024204603001030903801c0c028280510304400d006441e0780f00003200a40e01d064800724041920641023101c0b603840350f0b00703c5a01c41e024005000740e403c3c1d50000401154410700054860306070106d90002495024011030790310000b81d140401000810140c49010480048070107842500c0764144 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 517890755 1250 517889505 517889507
    0x10902030309090a020f0a080601080703060303270905090109120912110303090a03060509151303140f04121e030903080306010c02040e010204061701080604060b131401030b062e 78
    0x41d1801c6d10f0800010035a40c0c0700c6014064040c40d07044480702d0000f01e90a000569240c400d0003480e0859626458040f5020784100004404100351500448820a540300024000021340540ca02a10300000001562015402c0421881c07400d00d100d40140404030200b00708248080c0584007026130812200710300c9658010000c0c0c114400d40d4034183c0e20943d0100b005c010720238903501c018001d15079001201d505900d040410000c030329044565440ac14007607500e20300800d004100b00308001050000701440c0250700c14061400e42c00540144003441030241540f0300b0048050b10107181c1e20034032001000c00005694009044a1190200a041402c04001305403a6401034102d10219030b401801400b002d0500f0302c41038002d4200b44694800030300c00c20b55200d42403e11043c103030b05a41d1180041d0200e65200e450740406807031060a4240c00a1034043c44aa01e12005d1103100208030310b03821580065499070500c40f004001c0501420300c1400c000410300e162892014070001a0080c44001d81250000707020 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 517892005 1250 517890755 517890757
    0x20d0203041e052d0f130207020a05090907031502030f0402040b0303190c060b09010617091e031306090f0501270b19021903030e0703050d021608010902030309090a02 73
    0x40240d8000100001505000e040c04542d0104804498000c8801e40c030342e0010000e03d502c0345c03140d0642240c02000640600c0020350000c100147c000f41108021980d2000444d001540898a0882d640c0080c1000c0c402c1004100c0000c004171314040c1c055046041c118240182050050b01c028800c954a1042411340d03101807040d20640055084581e510303803221000a048442402000c0703500390724004a207600c03481e14a079094103039001aa034413000d01c0c2084111078218a0081c188000501c28004075080caa41c0e444662039028418601031503c0303100b01d80b1302580c440666080982400030006081c0113640001d80d1a004a4109280c207000360711001070361f10002d212050420607450109200414407010220040903140c811442c5a0600c0c07908090803070322644250071403488100e40b60050004688203800c6010404281015944a1981e03541da4500e00b000403035120b00560440d00d040c103a0304547e210204010603054000744990b20103903002a07103038418400312502c9003140344041042000c0c0b03a4 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 517893255 1250 517892005 517892009
    0x31202040e18101a0109050a030b06060c01020403050a0f0b0f06010f210501060c0b0a090201090b0901030f0509010509210f13030f0819050702132403060501031101020d0203041e 78
    0x710f004c00504208a1182c0e1188400b04051030104000441c0081e140c100070300494100d0f80c00241500486e200c48003001031540c040d603407107103440d90284404404900d042c041d00907c94419040b4100500e000d28144d009940c00400654011442904102d8981d811080000f810784507403a11011105690150983c1301d9100c60302000c4080c9041c1c004502150410140000d182c003401500d0615138510a1840039100040c00c020b0018800d94002c221110381c3c0f50162151200505010070120310f038038904801c0b22000c8622503116074444040c09200802030080242d000c103000b260845078510b170888210300303100b011040c4030016030001d40c110300c00c0b124074600d0020b9540403c0f5880032000600b04070015411000e07990b03900034110603000006e1406801245c0d241d5034003516140011824401500046c00e030942c1c102400300480d1090080f8000100d101d0002d58803400c0300140c5541181040d16070303484821482415580000d01241c441c0340c00109030b5041720008200b80c1d90400b0f03c0fa80340c034000941c80d = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 517894505 1250 517893255 517893283
    0x503070306381602040c0c060911190b0f03100f090f0b060c0a020420070b0405010f021c0c1b0506060102250911070f050604031202040e18 61
    0x12205940d4155000c030600030245100c10b0340b0520400d4040a80940c500c10012200e0b2003010380c0c240c03000141030540101d1240b00090401401c03d00007a1aa1416950b8218046502c411642d540b0809881c0040340300300038214580040d940303107044c440418800d20034090039801c40c0e100071000a54055281401030058001c1034081070320181d0707800800c00a80f041544100070141080c09191241c10041d041d1052030303c050006102d04011a000e100003003d040702d0313140c0c00d1030f003c80c03120712201d0416008000b200d01c03401d6508803038070b0f140c200242116881042940c1c07040c01045a0940c242c461780300d034074200010403c00902c010400505491020190303190b80000c0c00c5a0f201c0d80144440407a80511071803082e001c1d02e00740d1040b00d4201e408100d02560021020841850601c0780c00d40e150b00c0f070000070310f0000d202450283d0a45a00d906238171032040031201e90340403008000804d64400c1c820800a42845000e5041c07608200107120744030b0004011071559904c00c048002d207030400300400d0884c0d03448 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 517895755 1250 517894505 517894529
    0x12020a03020a030b1005030d050921010e0f0c040b0105091003140a0b101701090c0507150501031203020405130f09021806010912050316050a080c0d080609070903030503070306 77
    0x42c91501c080c0c1000c1c111852017520f40a240e001409090102d80018145480d6861f6845d03c0313249010840000c1c10302000381600356102c140103245260034455109200c024100601403504540b12107072924584036441401503040a00c11046660000150b4a690f841150039048010305800128024031000402c52001107042044c40100410380c0e02000b40031805a80040c40311050203000e88505074404480442004031800404c40180c07107501180d114401c1d840c2452501ea11600d450f0180400e5011401070b140e5114010001c0010f0098000705905548c1801d500301803401c40058122448030071400400c503110341c00354000b501160f010b248141d9006009008084280c000120b6402045880740c1c0440c0c02c40d04086010020a0400c403e01503100c002585010142003500c540160740c607000301d615200b94207050f000a6044400f8121130342502c402450300c1341c2403200c01480c422020b04254014048101404940d65010300a13109403030b00750400326966111080110024040c5600840d8001e030 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 517897005 1250 517895755 517895759
    0x40e060103021b06010b190c02010f181a030702160f0302040c1215030311161a0f18090109090f0f080d09110909010b1c060f050c1b070f12020a03020a 66
    0x9200007c3c140952a494110840c03181c3d080060b1400c22403000c01030b0104264503084088181701c0c40300d031600c400182c14114015552950401d80c031311600208000d50100c0801042416641000005003480440007035020b054500200b004030120780d1701010b40150b4469203030000b641d0091002100040400b0010000070076520710040904140d80412400544660600240044c001403d40440c81091250380c076910318202c020700c0c0d10049500ca03201410820b1141484454052000d000d80c0803101c0c104455441c9208200080002c050b004081260715101850021440c8003050080042d40150301d130600c610f40c0e0500581d00d006000c180721070f10382000210020090741c03a5028981a01c25544051541c4807081d060342070303070020340d80d00e9000020820411000948202a604164042d040000301c0048c0d14101d5000d42d001142c2e00482c81d41d000410000b91110410405850102880580641070a021007003242405500c9204c0383e010021445905541c7c804145e030340219802403404117416 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 517898255 1250 517897005 517897019
    0x1a0f281809030305150a0b2802060106030e060c03150f0616020315090a021e030607090303200706030b031009050703171812010b040905160902040e060103021b0601 72
    0x580c50707400c40002c0d04210118911500113041031003040340052096440304d0401400342c900e0f4005002170400320b60403508d0396005201c5800500c20860315540031300459810614050103440c40c20341c40d4290750b4800c604221400b442241500d420210401101040010040c00a5401000d030440d2945c440400902031050400f40c0c040c190b41c45100340c05488091a070031980f13896849044074120402d400c40381e01d0708010318001003852042902c0314120780d6000d0f800c0011a00e445000c075559008100303e054180245900000840c6120344413107a03090000340807801040d141e5034244544000c0c1034842a890b11543d6080c0510301c240e80007200d0410a01c48070b400c000d40e0320003d07440161440d00205000c2c1511140f440c040b500802c1d10307038542c180140f102e0b00600804c6008107a0381002c03556642da8030541990343c1c0c06007401e281e000300c00400c00142c1c004a0003220704e480c1d80c468000a881040100000007080140c0360788040242001603e40120701c0d10321065510002c5020800d01400e00041003070 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 517899505 1250 517898255 517898261
    0xb01090e0106060809070e062407030e030307020307091503050f1b0102030f07080304020d240e211e040e100911030f0603031b011a0f2818 61
    0x300d005030080c02455994402901e0055081d1650031640e04042c0040c09403424003031a942d0000d030007410502101c102001484031407111202a000a580d0001c5d150051503406001d104403080100d01035032814016500180da190780e0b030b114540c0d181e0740398414a40320501c0b581800005581004c19510803860b414540d41e100c4829011070791508040703210311000703948000140c070274002e6609015031418400d41c0780e801c0b1540000784103d0748142030f290b030b007030014622600484805020340410403c002103c0f03040c1c0c0584500150306007071130340000074803903c8241c0401c250480c40b00b000d02355681d816060701803003402c4503030303070066241c085000500207490400421150322514000d0201882e05407145106400c0d07540050340301d0010503081c0007243c50070328550221a08024014222850504000c08622aa50000c00240c1e02139664140c00489482d020341c4090700703594100c0f5522004043c0d41e000908102203440d468003480003038a03000b070741e02161101039800380c191050400311040d013801058002e = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 517900755 1250 517899505 517899521
    0x180304051e0a0b0408060106050f0921010b091006050d09020405040308040c0909080909420d0c0605030a0b030106030f05011a0f10030216080c120f250b0109 69
    0x440c140440000c54411000544d001d88503008040d1983d07910381082140d540d0068480500840c50410108046035115148030a41e0070b1008a40300c25007201032a40303400c4039041c0300d0040c091102d59040103030361110742c00360b9000c2e80e0385420420380360010300c68204000c1090340c0f0001c2d00301e89010244800e15030016402d5103e5403041c45100c4000d0303110b0500d1030945142c036a00800b06902842010110314141e0425503000480039601c2010b070039000301c0120440d102c20007442c00000301d01c1020b901b100326090004a05a025511544005410340d02d04038a00d2040c8503480c104203012001c6070740050240c000c00d003542c00080c001d011103512410b042030940381c0007808861039841d1011020000461440c42d901218000b800b40c0714400d891020702a0b13298903400c05004140d070070050380d545000840d040d102c03064042c0c0e40c0c013174549042c004c0991402d41e05100190354020280f14829024000d8412542062240b02c000351180e6050000d00e602105035072802002e48905000101b1105140c0d480715503 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 517902005 1250 517900755 517900759
    0xe01090213060e250806010e03100e0d17010306050709030813180507080414012a110708070308091f0f03150602151503100c170708180304051e 63
    0x8416140d50b18421101000c0643c1001100060055000500d00581483c6da101ca0706050480c80440c4000c0002d060840022403a80e04030341d1500c07000840b20b010072810081c0034560030102185803040c408140401014440101034607218800565039500c01c02c039842c01540d1021042d034075010344049428100b0310500a4510304a92025a045894803a000702d602403c2e0a4030740b000c0300e844948072850000c0e03180e0141a1659280e260101c0d407403007a0a11000181c0e0400f01c10060001c50f00300c02020390300d1003002c82800da030042070144034620717001c42e0720700850341d0080d03003240da6400210104034504d180003001c0c1c0001c181242c0780300821390080d800c1f410500c0c10b95010804c22140b40760706a1200d40600502005911035100c00407004c6030040c1a80c0c0280f00c41c50f480d1700000c1381c035002034640394684032a81c051513250242194400c1d0441200c0c1e808103d1400a144e49140843d4002d01040b0000d00c2805013114803080c11180d09002d0007118060f1038003514000c0000050a80c2c019407541c0210014 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 517903255 1250 517902005 517902029
    0xf030121021206161409120f2508161509030605010b07020f09071b05010906090515250f090f0b070c090c020c01111606080103060506010801080d030e0109021306 71
    0x7051a204003030034880e03a1000c40f51039051a9240003400b1244000c2628147c10744104002c42c08400e4040014491030701880040440356202904980f0340391049a0058880b036108201d40f004c481544800c9101761a0034051841c8080146c81c000c80b41c6c0606584041c015524200010880d80c002c04014201513000b6a9426404101c160034082c03000c104440c100005440f007070607030500e540d4030101c1486140c010800400c0c407000e0350f02c0d50011108152000c0b903107588041210340d81c42800303041d1250711419004a00210400e18503801d1009d42c856a0604108001d4120b03514a050042e0300080103030000400182d0003035190280c041943d80719503001c0c3c888402c07043c0001007249250007a680500b64660250070f910048400546024659103e4201c1502a0710440500f41c504c1c29035441c001c2c038440d55141c6c01549076082850850301c02404540c10020804018000c2074800144812001c46510300007a45e08100d1544900400700303540002c0d4010100c04030030180c1321060b0058010368403681c07444 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 517904505 1250 517903255 517903291
    0x120a0201111f141e07031a040c031407020a110f030f1c030f020c030a0c05191b08010b090609090f160e070f08010909020d0f061505060f030121021206 66
    0x9200704100c48807400130a101c440004055601c01d802c030a03d603031400c00d015032015503130f0000507042c0c0382c1003c41840000c1c0d80d590139a4064078201903c6030002114000303401c01c0c86c001d44a60420b41c12009281c0d00911182c200022280c80c20001e0074040e441400c2541c98880010200d96000c40c800407190001a003880700910b22000a4802c454020140300c0003189082c080b10340682d28100b01c504103464500038010194941d42a1400b620000380c0318090303840c40f10003848841007641045400c9040745a241c11445c06c11901d402b44219005881200e40304c165540c2c886025103031402000e0826442d0003a000c0b0300326141315800c4103506603505440700021655a03110201c1d220408490b80000003079400004002401c0070758003036140c41d8006810b070030070a0383c1500d5078441c9480c042c03c110b407020b0b43c0d501343e0622030ba0780000c0c00020f0501185e003d403070913045a00403001804103009480c00505982441c00002800c518082e000c10740c040d001080e10680b00b51084d46400c42110342d0f4580718089020 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 517905755 1250 517904505 517904521
    0x30c0609121809281401090b1011210714060f0109090201020a0c0323061e06030a12091401050306010f0309050705090c0403030905120a0201111f14 65
    0x5030b03075480c2900102d182031070300440c003042440305015054a0130080f10000310107015403081e502d402c0d800201140454110035441015404c40c0c8168170007190540f80116400055139910200329030074240e45003540e8560441074540781031800310703c07a042c203524880b520301c00300e0348284003d044031170b000c0c20020852208181d81d05407078890407607104030f0500700c05e0f005002079010360b48012000c1d40188101c0b840380d0050394a07482d00d40f01a42069a458041041c41540888002499018009018054038050038511748404083c5070500040040c0030100f40041c1d8544c40c20084907001c42e4000d1492005a1540301c03014080c1e01d440c0c0110b80d4079000c4407805504950050041703a0040303d060790f6a8003c0028200f00310000c0604007012030342130155a00c00162643e61111003405006040c1c40c250b91107141d458041c10202550f8895401450390710040e40c1021000b081600d045c1d50203007807000e0640c440c0c113a0a0700b441e8080314009048182500302c40c0d4038a16a80c0a105824501c45800951303885441e0303 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 517907005 1250 517905755 517905757
    0x501050306070804050f011103160905030c130f02030403081e0f01050d1407091a0307030206090910030803040b0103121b1202010204030507080a1a0108030901050a11030c060912 78
    0x1116016885640840d41642c443e0b0107180c1d2140c02001a200f03820a544015030a551480010100000c1e0101c00d005150743d0620100190120608284010501d4600429158005800454401c13a06205040c42032400307070b04114005150450b0455032854140303400b6104200c19144000c0102d4200c0456040c50303c1c881c58140600a001c0c10f9100503031801041014100090800b03c0341415022060040ca820401040300a040920804104000c441c0d0f4820722442c00c0ca80528429400003c080000da00c4010483e90014410348100312503656805072070115000c1c0740d00044c0018800030400051002c0984e006058901c074000c046151406a0380845203000822200c030503110300c595400000600043c07801458507485c0c0009418596070743c580310b04025441c0e1003c08103801c003000240c00c201c50040204400c1e140c0b50345c54070032541031070f024035036178040d0030710301818040001800c51485002d410299a00024042200d50340d50075003402c961205010b864046c2c203841201c3c075407d01c8602c000 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 517908255 1250 517907005 517907009
    0x50109060e090604060218030a0f0204050c040e0604020c160306091e0809040b030f120c0c010207080d0e060f071209080d171e1006110106060503041b08060a09060b040501 75
    0x42c024000c50700c5a803100c0000798024010350a01010048070b20380ba50310241700002d030150084081584990090040c0b000f81c40c00100001440f1200700300a2194510f45190f494000e0303000c2d20010380382d10700d11100710310f4002191071713404903c0790442000040001c117400007080c0324810080b2051190b0a80102036401c0030215004144180501640d981070a140d808102c0159006040344c050b0703042100c080e401c01d000071503845003400c0300060104441c10100040003010b1020310051a1892801501c242c03240c416a410034100712800d90307900c0c0789a403000705540702000c0e0760907010b0790740b0a50704e0540380011154114002040f0115070010f581800421042c0780003041e91590000140d50343c0a158044000420850341d03121401c2030030410725244621507105079910b4a0300040d05040010290000440718400011a0b04061003400300d141d02c41c1c10382c1e0300b0542c000105204900c0819620020100c9a00942024481c6600300640348156401c4046110b01a0500b0020441c2020500054a00034 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 517909505 1250 517908255 517908271
    0x70311060f0901050c010f06150e030f0a020907140d0b03010e060103020901090b010c060c0903021f170606091206070318170c1009060b1503040c140f0303070501050109060e 76
    0x203002d401c00300e501a900400501c40e03024000180c2c40f850700c150b241151110382201281d00d21070350240314803981250381521260401c0b001841d050030017401c225902e144c1600000d000701880ca002c01c1d80e05018041074640305036024030b26601d0300c4054980d00000c01011924034820f40c01d140c8a4540140c0c0131640354180c9030041c145620716820031030b035140900000c0502ca4104505070402c003012500ca8410494ad00449a550351080c61031401000b6084e1001400702030b005003861591a0316035041268100885411080070f180c030f03a18400003a00da0b0003034080641c0c10484040e02d107040c8401c04600c0c6880b42e0f00c517850802c003248906101121007140d614004088009040004c0b1060041c1000390001070150411039489242032000745084e04c3c4a40790880c2d800f0b46498040b545403408003506480c100000c0710407801c61900740c650300240911803180410410340001e008400382c030390030002c0e00c9500004d81225590a030714503220b4002e2000f40b1030024a0303850f1900200e01250041101030081e421 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 517910755 1250 517909505 517909507
    0xe0a20010806012a06050f0f01060206041b0803070b16030b18060f0d0501050402010e060304030806041e48080c0d0903020607030f0c21090b09070311060f 68
    0x1403800151020310010402c1480320031413030380c2000e2600d00c0a0201070018490400456a41032440000e8031900d0060644041507500314010f020f62503000400c90b83c4517801070507485440700103044101001810f6000311010340400120002400b0320040b401d0300489500300840746582c2019021000c0f1400002d0241d802044420360444482c8000105ca41080d4000e1a4002c3c7e0443c180006d1080d8001d40e01c1199543d4454080100399a000903003040401e8090340d660307140d45401d40d03008101c448020f10702c501c15541c4000950340002070601e0380b160b40c01200303010403104151250710394044480c10b80249a0303500750b489101042035810502c0112800281611455130076442d0241e5004030f0050028101044c00c2c44907155180e083d024540915009402401d80d07401c2601004003643c0e03240c1d0b68007a00c6400c28404d0407226520942c4442a1540706000c00180c610122810007d409820360180030414500103104d000080032030700008072480742c0890f45284020742f0a0000c02d01403003400c0341100d40 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 517912005 1250 517910755 517910761
    0x15090801060518040503190c06060f060c0807150e03042d03080c120a030b1009031509050a050601060801050918060112061803021e070b04050103020a050d0e0a200108 73
    0x100040f6030000e1160f0252401c1684003481c1602d98802d032441d510002d9030615416060021074881d500281c00b013100c2030194581003203809850031801e5280101440000100c900a20090f644580440498400705200f2154009039541e5603070800c4c010132013104650b000f44441d40c900c15001704603650301080c0e41e0740e90510b1a01c4101c07940d00410103030321850003a007a407400d0b50060400140101da0301610b0001c0c80440c14001d02105083c1c00021400788a400581800441c01e802c0340908000c82698000c6101032072460200d0821400140c0200b95100300400414840e400c511194141c071000d0303600340c03034580e00c1c410200f020120000302c040f40c9400c503000601c00e00c12107a5514101c0d0f80101004116410043c207000b0081c03001e118150011f800400142410300a4491441140c102c50b200802a03282010800c21040c80750b03206090515a0024005602c1d0307029034191011203001d02010400c2d5024001403503258200480c00b220740c11041131843c42e44002e1055940301030b03801a91140350366a = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 517913255 1250 517912005 517912039
    0x605101802161e1b0608010e04020312090301020702060d020408010506060f0a030b0a050d030e01021e030336010606020c040c02251511070b0309061b040b0301150908010605 76
    0x182200318440d07075000d00c3d1030307801000c20785225014501c5100e42442c0d00655180250040c40134a06801030485030002d0014840540d800080e8404100b4080b00030711740c0d550344c110000b4020300c10b03148000d400c4240450180441d0f6195805082212001402442079a46080c20403000e40318202c2c2c03031301c0f070030b4014131161420900c60342c803420850201910f507070040d43d01c5000043c2081c03505441140000c4000d1391208041d41d040c802d03810703402031010004000c0c00080c2c90007600c9000003462407400c010940d6032500003160a005d091740d0602c401761041c01c0d4649420340103010f08058028800944039a85c452295130500b0311440c0100b264940c041c03c8010380c401103500c61a07444126049200704862000320707200c004008a072007807150ba6200c8441c5800c1140d2800d00701f025692050b0401141803082000d040000b1803400d07840004816108506a00e0707010b01313035050207160800d40d100c103c0400045414040001980b240c0c012607281e02c05070035034484900d4241d074058040c260f000116100440511 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 517914505 1250 517913255 517913273
    0x3020318100507080915071112070f09020306040b060c0a0b060603130602070311010204090e060c040e1f0855021c0f020a0b1801120207060510180216 66
    0x210000803d0b11b400c0f00031040b0403180640060405503402078480225001610380800c00b1803000d450b1001620703200740b03030074071404101489109403e400e6400000045807a91a64021100490f00a06450b2101040c903502565001c00b03500884841000d100407400614148098070700c074800445d01200d240c201c1e541d40034083d400204084062048454070404049400e0001d0400307403110310400200901310381461440c01d4000f410348000309400300401e2040e0740f15540005d5000d8050b00300ca220040c2c400499503070a9101d9846030b0070178040d64449160b800000140b408150120b68091000c5021a03d800d8404220460310089010340c1011011800c2000b0303054400c40c40e00040c00407100002c0c2c000002e444801880c1c0880754942011005800c504d440101e820181206034036041c10240c0f1000c0320381c071007801094105d042c0141601c50500451680e0111198140e002105000c942015129400400d11074041c580080c0c665031584900d05103103100341c81480e16501c001d140c240d40140c4031220f81c = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 517915755 1250 517914505 517914517
    0x3030309030c1502250c050f1809030a1d0d060b0105090306010b0403061113030b1b0d15060302070b011e05030f0f06160806041104050406030302031810050708 70
    0x82c4042c035894100420909103520030942c49010025070388420700c210140e1903000500350101d240c5090340c0580041002e0600324070603207000365035146c5420022030008428540c03007042c000c011040042001034424002c4050003a004450b248c540d104101c086550b4241c55203511080d81141c020703880b0310b020403495045000d07640010704244c1d1520700c00070b000c40d007000300903000020f0300d0000003810820041a823251200e034020103203406080030204e1030000c0c0300070701d203101c00f520b454031280202c0c03c442c0780f0507816190fa03022a984640e0b00c4140d400420060500342da40c0b808075507840702c00005c840e800303802242c203001c2e030050140c0d2890b0b08000000c240c07028000700311702c1d140f04000008909030f1020401d03034082c1140c0e04028613040a20007010f500c3c0400040c0202078025418419540740754220284581141c4101c0c1e0100d044000c0c98500151400f6662186a02c10f040010001c1410f40202c020242d4085900103111003d20350010f121a4035a10400800001d10401802012529990250007 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 517917005 1250 517915755 517915757
    0x50310150b0f120f040f0327090504020111070b0a11070510020303010f05100504050f120d0903030801090203090a03050f09030618010f0b030d0302090d0f050f06010605130303030903 80
    0x1405512156811401e820820b80d070400d4001c00240040040c1103502d0030f56000e5910750304100240703003980d43c01c80c15006000c00201444000301c0306804c11140740d44025a411443d904804605503201c0c131175000303010280c4059010804040303540d0612080401c0060942e000c8500e024548038041e0022100c460b0307528050000b50054440c00b0a207035035143e20058050b61140d009507125410702c3c07100c040c60041680002d114a02400c0d0004025800009450803110201c070100000d0101a01040328a039403500400d4260048010128000d41c0040201c42078900a0303444898582c0c132060707640100d00c4240d48024156000e1014000042e100c0d80c014000000020f40c8681014074060210740380c610240c0d9480c60076180320b203002101000034461500411542e1409200328140b25020949aa9121541d00e08158001501c10b45076190780302c40240b49070340703c1d015189103601800c1a070384070a1140c607407c045001c1c0c40000103100d0f128005455011540c5c0980c2a1501d20310355084c4c0083c2a071004c118 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 517918255 1250 517917005 517917041
    0xc060a180b040321030902030604020906060c06071e020f0604021c080a030207110108060904020f0f06180415030c0b13090513020907031406060702010c080703030f0c09050310 77
    0xc1800c2040754042c00c0298880c0040604c803540c2c0c119a4450028600310b02c03810145003030f4010000d60b038002080b40d0080d4040d82c051126445850120f61140700d00c9918100030701c6028103100d81d03e584001a8540441d9044075260b10f04088401244c955401041b02d810300d0740510b012901600e05100103403c415003280d10140810300300d50341d507012500210041c50110b030b400715080c01403065a500c4030b002c0c03210920b07040140d4a84940000c00301c03040075101a0150800398030070000c54076445d580c030400072801800152181170302400340d005060403412003030040381040010500c03a03000206c00410b80364001c0165203c54102240b050241d002400350b002d42205000d000180c3c481c0034820603002348400e040c9060321204a006002c1e08a40141000301058580305c0280c801000c03400b40550050400c813040c85d65034005d030004a6540015600152400d44001000020150140d00c17007031204080752030034080100c503181d00b03803010b11407031040c1509034001449010786002554402d0444054980100c = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 517919505 1250 517918255 517918259
    0x91104090218090907080607030219031a040f05040611072315010303021614030c0607050a050118140601060e01050c1e01061802030103030912050705090c04030b090c060a18 76
    0x444403c01074400d00000d030032000003400048070a116003a405240d905040d0300c0c21841c4c0354843c402c1c00503035034420300309030361100200607a29250703c0c400c1c107011005205010400744071441c00b0040800341c40c126a03031858444a48070194032074003034038100c9400a1031003140c8501940c08204100361283d0007803075401203010000072050707002843c40c041d6000b80d005040306202c0090b8100710160b41c0d000a2183c214140c0740f10b141d40d82c00100310314840c80aa800e1601c0b01c0061030310310300c0d080143c1002851942080d116040c500b0751480b90701042c6004460b0700c80c40074000ca484030303142e80080c080c5100090203103048013102d5000700b0003015a80140c008079106481600020344071100c480d50040c0c0303182d44901d401c0000c20103400c9600807a04050900f107156515555002d402d00410b8455101c0311590247e00c003040c0401809080024100645200d0692a01040765070b840da0040c0030844001c404c078008a5918200066001038200c0090220303858501c1401c0b00341c41c06510002081d282440c40100 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 517920755 1250 517919505 517919509
    0x190813050d0b04031106010806070c080d0c050a0212030403052a0105091606021209101103031f060302070c0918020312070327060305220c03020a091104090218 70
    0x40c021140182caa480c0503080510300207240483d0001c1044480d440703000184101d9401046803500301c2c50b1424004e144003d02d08d0840018080d0743c0b80c0e0b1180074600ba284d9006d880e000b03801849802899825a8140f0040c50940c03031450000381c4007d00050410b00c03080d4100417000c041c8803c9050808129112007c13181241802d64100311000e000c0c0f60010024800e24440b01848100604294006002c500650708520151400b96111440c480d021200303c80c0c048a02070310a0b078a03051011000c0d603642e484c1200c0000c101407214800760010400007000007038028031a100741c0300002da200440b85103d519004030303500548240581c040c618001c15498100580c0c0400c5044440ea0240c42c82da5104e13030050601030004035107044444080d40e9802e41858940d43d007140c812040d034055040018040c1c0781c2000240e001c195510f211000c041040b41240103101d098101c150444e882100c02598540e1540d041400380c0b4040100b414450100788030900c5607980036005004500c00d04000c0e09101d8004c000 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 517922005 1250 517920755 517920769
    0xd031109030a0f2f040b04091b0303020d0e1e270609060103050c07060203070201090803040b090105010b040501020c09060d0f1209080606010f0c0314191119081305 72
    0x4440700c0c40214403060801644e000d004190000e542d2400c032080c41d01c0010b01001c070144400e0140308603903803802120195101c0c0d120081c41c03500602c003550b940e0f188004846580c180c43c041500580300b248031504d2480d1007845096400200035103600d50008034020690318054030701c04c41e0f6a20401c400003000140110400076050446400b030300d0070a0342425000c2c0000a1005000c0c1030406040504016070a031a00f4119050640d001000507520307965005c0c2207004008101008044c050000700340014030840008050040c81d011000f0811a45d8070006402d030f0784240d00c03c43c0d000d41c1194403088650301d40491215400040a0a0040d5904480d0b650700490020101c0c205e850741131812a03449203e07400070b14100030741030f00401400141405c600107091042d91210b2001040b0b5614001c204041c4104055100f21b010024003e48540c4420302141c410416488602c0c002412040e44060504002681d41d001c080604c0300319803000c41076240c492003a40b2070303188060803580c0c2c52000141303a22094 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 517923255 1250 517922005 517922023
    0xa1215050a0b13020c0a030c051204120203010b010804020907110c09100303090f03020f040e1e030903190b07140c0304030c03020a1212051b071403060f04050d03110903 74
    0x4100103021000c060400190f09000d0307020040d00c030b1060016098103207000401403102ca415003405c00c0000c0d02c074500640f034a29024806401c20701c0114000440820b020b40c07109000307101320300a004826000004481507101101c000c1d41c8903030142e02082c8403d015082c18889082c10348162540003a0007030102e40c1070ba400387c40d895001790b8a2602082450361100000c805840780c126014110351941d0002500c0503040b02501c0e105a9584100c1d1200745410040c0100c05085030f80002e51a54136000801c0d00e9130440320a5500034001c1d00c811074102900e01041040055100e500180c05444000084038644401a52080402820010b03100381000402c0a84015489211400031180c00c510500110424940c00701d1018020b2024850004104540307803034040c429458516220445020781c44550348401e103a03403010f806003003170110707110783d848401c003001c1b007815402c03500a138607119000c800007103084070302800d030303402980300a51041d200f5000030b80d1135011844000e0402140400090401d0424 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 517924505 1250 517923255 517923271
    0x111151807050d0b040c061403161116180c080a0507020106050607141b061204050102090406030818030a0b0103060b0a0302060d051b16060b0604091803120203060a121505 75
    0x10100420421404030790380260246181c8400e91480800e0300f040c16000160ac01142600d1503561218038034801d42055a1103800b801c102c8521200d1031007014040040e90190a03804061802c100b0310303d0029000c3c203000c0e03003115076548516540f0200607600410b0064801030455490708000030302031351154042d1040302c0c0a8040c04804440c0f5005080c0b41074480c41100200101c10314000c0456518070041e2400071107594201402507446291040c020710941803841c0d4820700c4d056022042c030000901a042e4183c00101c00d40304461800c040544d10849030303000a01c000c07420001880001c0542e00724144004001d0700b0800b4154403980010000c5d000381c01c146901039585e00030020942c0c0032503d051015030451500c5032074502828401ca043c101c1d910b201038842c544450917a04c041c0c5410003203a0041202c4041048080f030b42009111011400c4501500018040c1d2014243c0e00070610840703019440c014600590107190a90300000c0142a103401e40b000d96200e066140540103501400f4410410 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 517925755 1250 517924505 517924523
    0x20d02040b0a020c03150a0203102105061b032a0a0e010216060519020a06020d0501050307140307090504050a02030a0b011508160c170403110111151807050d 69
    0x42c0d150024070300f42e190800e00788268840e02040b420122152102c0303401c001c3d11403025030340e680c901204208041190307004c402e029042c0c1ca260b00007561140e049415451140098a1080c5c4800114884110808a4801c015801013000c1411031035103803c1d034a000f644146145104000400a50649070800580c03a004074084448025140d0785c188501d54121202c401c04410481c00c150008095004000340c0b010420151410503006ca8001c00c0000101944001c09650310906c1da290500581003c3c82503601038400c0b0640803800c102030000c3c00310300d400e0240c0144900d61030300140700b0150101500903981c034041d58200c4400341c3c8040c00107074030035401032210f40c2d03080d4035000000340701420b8504e8207010401120180314886100007891802c946007460b001207410000d007080003040c0241c031840000c2c0000020b0000401050300302810381007500762604252004035908450325058501c482180d1180c504c0300003002c0648610f88100d50002e41000c440d40c0b6500c0d01c010881c82041c0c02c00598880714 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 517927005 1250 517925755 517925767
    0x105040606050315010305180303090106030303150602030708030703230105210703141f0605030606100507170408420c0304030c06021b161203050d020d02040b 70
    0x28180500c500510091800a00c0d500d001c0d01d0018202c49014101410141c84401048806110020004a48544000341c0f030383c80c1421030740c042c02040c40344400c80c04242040b501c1c03148100d41c4000a000c4555580107140703003c1e495510250643d00007004003050680d100c01d103060044244943c83c031587c001c00d4070741da8a9410700d0b04020104000030810b80a00c490701a411000e050049002000c490f48122010018510f40320300905040d12866500038060034001c0901000303589802580c1150010b8040d558541c4075001032092504a68010304d022980400891002034010a100000c521180c4041400c0540b0384124a0600a40c8409010f1040b415841020441910700c40102c4503c0041c450158400d03030301c0e0b0000161100140904003030340011002078141030192144203017660f4800c6085680f000c46400d8aa07100072010314000051180300078100c0441c100044a0058424400a8062440c02c41e5030448003540484141008160248185500490300d8009040036000280c1d02d40d840d80 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 517928255 1250 517927005 517927009
    0x120212090f010e030a0e0d050a080c0a0b0c1e030601030e0d020d030f0204030c330c110d03140904090b012d140f040209120303190510121403030a050105 67
    0xc1c0702100f142e14070f07800c10002105030f01e8000d040824110000d440400c07580885080560404000301c101400081e8009061640700c1004a00420080d101e091001800c1c0c45560041500c3d00030a81341d0545144070305211b083c0601c0c61000755a21100c14035011808804403080142841940c0b02d400015a1000c01001002501801924040a901c41e070440c2018956104c10100c40c506101c2c000c8000c080d180c070351560310f8020088003403800d103010080da983c091082001381040420391040e110350203902c241100e94030b840300d1a0700711540c0598a8100000a401001a296100d00e1101e43d00680e140e03510700010f82c0003010305000700f40c1160415202030704541ca0003000e03060800d82c1c90303c2d03a0b001d40051151451076180e88180c12401e4482c194604810b81c0814024840c08100e568010754800b065203581034000011445580091120115043c0c01b0540500340c940548001040e0071103204240111954a9664030b52240540f40045092030250110b0f030860740f041e154003512580b5603005201c03038 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 517929505 1250 517928255 517928261
    0x1b0a030f143109091a06030307050717030903100606111c050306040605060d0f1802010c260406090807121e02130612050c0f0907120212090f01 63
    0x250a110000d2803800304004078103950401400040c44108a20b0100d20807030241108402c4003820300725070204002e0146050452901c1c2006040c488454138281c0010250300703010083d521902c0d44a0024604c250800c1d20b0202d4503000000041e090344404d03c01d61005d60380410152040702800d00380091451309080d0020318980d403520f003010250384018250b8184044190400c0e042c201d407450185d8482e2034001c0018050071050b0303c4180e01002c04200e0090468041e8032200f403e00002c0c1040142240c0005580601006018040d010460500242010900310b242c481e52403940c180341e18021041604200302d0541003900480c000170b002000034485882d040002c480a000f0b0401c00400b220641c1c4c3e244600c0d10b0700d811b4007925154807078035010215107a203142012400c80d015800d108240d110000c1503400011150300750b0b02403059903400111800c01070302003201e409001c1c00d41100c0703507100101030354590a80054209a50b07400c012100f20700c01d84650040c010444d560190081039841c416007030039 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 517930755 1250 517929505 517929527
    0x10602070806070e01030603060c030b0118080307030804170c1f060b04061803210e060c0304051c06050711011a011d0307080111091906141b0a030f 65
    0x150360000400784001500010002d82c000050302d4101e1032030b2400c500483c0034050940c40208150306000c8030400c101d805410000c85580280d03940c0703003010150a250015080984039030f490f20303041089003401091040381c00c654001e00510011980b0000403e00160551000071840e429402120002c030582420000280a40059035400c0c4965030408010b4841846948104014044440c1c0d0ba0103400702551480c2004540102c020325020301e240361614884008944803000049500132001040e04d081804d4410008a00004604103410401488005e0805425844803410740c0891040001c032280101442140c495840322200f8144050b000e0a5a41550070080da401cbe04d01100c081d40e90b40554110801c0d0062142452200b0300100440d0410702c42e41c000c12103650070011003e035901500030040ca0b22120075900300f00701310150216084030007ca4050800054216000704506401040c05000404c6c04252400581c5407507800d0103280c0210304030114081642490412a456004504811 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 517932005 1250 517930755 517930757
    0x4020708070c240f020312090a0c06020319090f030b0601090e07050a080a0c020a110406091b0e03070e012304050403020d03050a1e02030901140a02041509030f020f0f040c0305040b0106 81
    0x604c00e03510035406501d074080c11070000b80e103036043c500061405104101194400380c104001003440d135242d0b48000c1d01c81e44881100c4501003440350302d842c80d00e441901448222a4a10f20f2416502d05640e21160400c601402042c10450f5442d80803c502078080c58032070041701d041c0c0700c8613500c86983d040640b200794018550403c41b4070f41041074400ca0740100382e883c0d8071503002c400c1c42001042240090001c0905410440f02203241504681019550084001f90401c2e0740c0c403400b2121030745d04101540e41c000390044e00360011031000104903c0c004100d10422108014034808101d8442201103000c48a00300c80950040c0d0102d00801040382d010f11910f41c0100010009008003005400c1c0c1d6407004688581101901c1d40c0000010100002035104c420303c400c980c040c4101c030f030070500c01260103034220380944c2c0510080b10300c104251a02400402c012603610140c4094001c0842d020460f000c0c004070341c0382d5040021410704840c41e44c1c0e140b041c9554403200e80c030005040c0c1090b0030840c0940740d058001d48 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 517933255 1250 517932005 517932017
    0x1027240b04031a0f0f07050f0c061015090e04170703030b13270f14060117030909190b09070306090b060f0306090721090b070c1104020708070c24 64
    0x80104100307801079440145c3c101d0904250315a02c03011281752184804404030350401150101c80e103580847d000b070141405200c01c04800e40c0f60585400007495000b02c1c40c010801c0d41d60704000d81080d004120354081d00034103081510b440503c40010969100600442c0026591506103005107411103840c0801603a0f003a040012220b2a0340c0c04c00c5010201c0c0d084500204c008400c1010464000c100d082c140c0d500c05e9180c1c03c8418042956a940c01080c0600c12210a02d003800130032a500010580e41c00420007004603078551a80703110801030b10112a59007032615100c0341e05031456180c0c0d00c13485014110740e80d00018641e02d4004180111005121914400c050030400d150580807104140ca8221004031007140140c0c465800c00d03078580c1c04441d104220180c03612910b00a10b0010743c4207001007405100722040341d81d1403810403540b84990703140003003401d2044003803c1e585080039406040410b108180061403d40e060301d0b05178034210543d004038402c800071a0340d4484018682d0303c03c1c00e00b0f0887d080003 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 517934505 1250 517933255 517933261
    0xf030f0a0e0a0b061509130203160c20011215051c050c06030907090612120809120a2706030c0203030c070803101206051027240b04031a 60
    0x3c00d02c0c0080107490ba0340b05119201003100360009560840350310502c0207001d0568140108814070103508200ea49803200b841d01d5407687d051501899407040110791003150408144080210b021807036001411881c1084860444603482024605c1854085d01c2d0720024060103c1c40d0a040240035107913600100324209082c600040059000200c010f014001110b60545a5961210103484e01c0708a5011844e0182801c10000d0302c03680d29000c00303804900800c0001d800d0194010241da006e40c4c16201101e0325880300741030010329001400030f00b00c000500e20300719140d542890fa05000ba103080005104074040042c004005640d014803805c103003002d50740051402c618101c002e500d103038090300030040e061180000004804d071020001e010003070300c0c00344800e81492007035040400081c0003c07100c01032940d004440c0401c01c100f80f0f52104000ea902071000103084117841c00d882c005441d100c42d02524096a00c0048218441007000200150112044864480345542041100c0c0e03c0c60031f4503540c075280100b0078 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 517935755 1250 517934505 517934513
    0x1209060b0f0a031a090a050304060c020a1d1314070602150a06080d0c06091a04020f0102070b0d150509010605180402071a040c0f080708010f05061f02030f030f0a0e0a 73
    0x1032181844e440c0c50246000740d45119240e401c0100d5007070010454000060045042c5030020024030903240240c6039804e01c151102e01c90380300c050000c500480c0c1c5030b0100001a00c182c22103020306203103c2c42814140983c40da1003918500d008501c0c0c02190251304242c00703c481c0202c41c2d00c1e9050784181240814059140703031145140c2c503010007403a05004c01101c4c1c11150203000841c3c10071502254031440030802c2d4201440141402c10701600c4c12441200c604148444a42c8005120005d8401080e9000e240600b142c51050041842442404044c0301e03d400001d42a521a08058000c000c4c1e52108c682c1d840040b4140d4100300519400a40b00f070344140448000310f118550394440d0015004e4281c00c1c5030311203091069a044039680b100030407403290f6802050845000c5801021604004001e001038868a2111400d4070030455045d500300c09080101100952400d854020040c07050050b645801e404c4035181c44154011a07400a400851106008220b8000d228640d2203091500c041c00d640d0039030707543d = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 517937005 1250 517935755 517935773
    0x15090b030d0f0f03060e070903050f160b09031606030903091208040603020a030b130b0a0b032203050c0a030201051b0a093b06040507050c030a08071209060b0f0a03 72
    0x304036800c00c0601020301c100e0a0090380942c010700201c0c6d032015028500200024080c1c2c0f410702049580d405144003185014100147c442c00130507e01e040318962908000e01045690440e0700c02d01d5142c0704000d01c0e40e43c55000a84103c02600d0b00e5134000c01c51001500307028012001c651311a400c0c800904080101240b107006c152016a40c1c41c0ca000740e81c50100002c00c90251001040c4e465010b62070707074070204001040354802d01b6a484140d40322a510b035559509000e01c1d00040f121901501d12100c0700010001d04c8180c003514151190400034107000990402c203103880604030040b0090707135550741400690f030755180001c000e00e00030402c0c0e03074540107802500400d00c01c010310440d60b030070021601d012805458003a0324207011020004200701003401d603162640407482912500e00580c907241c0400d581c0d62091080f6911030802000031490309080c3ca038116007a03000205040100000f44e03005444e824000c0c000c4484150264002140707504507001000300c2c01e501034507100c0c400c207001d8004100284c0d00d00 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 517938255 1250 517937005 517937027
    0x11703120f041e031d04271202071802070318060c05010b100c020915151308011b0f0909111305042c1c02060f15010801090b010e0415090b030d 63
    0x541c05c24046881c0045000380c0449801c01c2900c1160742544280c011172603048144103402400c1d0400748042500090f600c800ca5401400300ca0aa01c0d5489c00800a40fa002401c01a1003071070301600508803640040c9252085412060000f4610400c42c01400000d0095030314002d8201d500601d1503c07501c50243c540c01009400a0086c015030000800300708221060f040c1c1000003130000038400c440c8070500c1810b0381c410428904407154200c80440c1340c0c07070148901e4910944017400085030000012091350600810001c3e10308000016202003881075031401044c0204940a0800d5241c402d5049210100720407904060b001d80d25001049880c0000e07003030400706590882d0034a21ba40002c030303030f0520f0902441c1403162101c03050b11088207141590001d030640c4a151810251139454461003e010310300300d4032440660008078003034014030406a40f60300c1003265510505007600c0081c58000030038180c640131401e81244040382d0104008000c00c50040815800c4114047c00d004416803101801c3c0c0a500 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 517939505 1250 517938255 517938287
    0x6020717010b0d02091003080307020a0209091627020f0702040f09020f060f0f030c0c06070c120e0409020a060e03070e04080d0c120e0a03140a0206011703120f041e03 73
    0x4200070404800b40c07034107006c01454019070600d98a1800d048040c0d5502c2c2100f1049001d0307c0802c0004c0c10111300403c0001058050503841e0040d10715100146441c40d0105a081c0d0641898a455903c500e00702d2004140d2425001c1d80c0e20345a4001d801000304441a845035510301c181000400c000503541e450464501e080221074241e1104080c0166035200d006204800458510003c00d106010040c5000b600110713001104907005d59640302c000b1039144401d075a0051610820444e00b010140c010000241a8035010344005866003003034001942e808400c0e4028008185165548649400c0c1840700d500900340c98030b104509820f0960b1020568816020340b00281d682d0398080c03e4400344901c507104401c40020b1800d001e40380403038241e03d03115540c9500071000701d0b45603040c008400013101d0582d6095031668020f044907a2a1400400340709030100c03400b16007400200040111354000b441e079540103054080100c3e54030b1070309103022500d003080c2542072291000c1103c028000a680300580605240f04 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 517940755 1250 517939505 517939519
    0x3060109150902040b131512020a030b0603070903051b01140d0908040314010f0515090402060f0c01051909080d110403140105041101031811180106020717010b0d02 72
    0x2a0400301c468115080d0401c9800c0c03800000c00240c05424071000c0d180d03901125a0300c8001c607984166802001e414541c00c180803800c801c0460842801c1580a00041c103401c0c1008201210310750700084492748101d03440c0000c074071800001d0040c0801000808144022a1100c1c60a00c01d1040007802d80100c030004030b40805000114441904050b8000c0c0b030f80154030040590700d45440f80f518900300c00e000b103c00d84542d880c120020700341d5201d5014050150051000c1c003801c1041c0742043c030000c010000e1069800190811103405504d04200c007c1145191000001815090901400368101040310100daa0303241040020800300d0400e0341141d440003503100c40012000b0800c0201c00c4070740140d90020340020103140c1e41070b042c1201900080e21451054001e103e200d40c1040054003140c19003645201c1d030340e40c0c4031070820005003004411541404010010560b06c403600b141000070b42000d13081100160007203c410003200c410381c5402040554010024007003c81d0910100305a000c1007031019201d108 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 517942005 1250 517940755 517940771
    0xb150d0207050f06180f0601030201050313050a1403131505030c0d0e030a05030f060108010b09040c02030d0903090305060a060b0d05041e060b120f2d0d090302180603060109 76
    0x3c0001007096400c00061301c100c0e207495014407003403822443c08400d442c080d0381e180d02c000c8600440c60754140caa05865260454980180e0b10728a41d005c2c8a00725180d200d80522600458210b082c6007055108a80c015542c42c450b0038a8030442310359035805241580c1c6034104041d0b4a41d040020380394000d92418401740c81d0041c1100c55005000030500c040b2250100040260403154020002c40c429075004e403540c00641c6407000111000c14091296400107802400350b0f110925050b0052400c0400031704c1241e0a01d0340c2c2030b10f41c00444031103402c01c5000c250290420000c00400340040f65012501300c1c01017028518058920034288a0100c42c01c10490384d03100000c04110484101c050726046402d40354041011b0342c90290003c0c6411403403d4460a488006130f445282d0000300c20000006010242100541c0800300c00d40002c1400070542d00d00300320580c036034450f90080021048a81d01c90740d0b003130b0300240717980140410403042c2071880b44e01c84041d00821880361400030340d00341111070709079002514031 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 517943255 1250 517942005 517942013
    0x3010e0a051b0c0604060c0f0e01030e030f03160e03150601081b0a0e04050117100f0b06030702010b150a02060f040501150803090f010306030203120f09060703020109060b150d0207 79
    0xc100a0090a00b100d004106a100c5510000d0f9080c4210f100c0d040400c0f150000c1042038480d060542c1e011000580075142112555101c1d030032a00c410008042101c3c20942c240900c24000d8104850718480c0c9010803100c5680b45034001d50020060205401070100708165204030882c0000007402541445a4600030514800c00302c440108c01440e08418240c40c0c03003178610010400d102d804000c3d403007281407070004a203d007003400c07060501c640c52900600310b560070301ca02c0344003602011354290a0a03a44610300300064541c40c004510580003980005460746c611403c010340c1083d411665280c1100030300c0030300056030f00044c00035009668110340e60110350b9a4507026014003401240b81c9044000143d001640c0e45000000c0d201c0100d0468880c0c50b455100c0004408a459611020b0351517840942105003011566008000d05044100320a10f4a00c0850200d1180e500004040780141c0d5103110040501c011032241ea0031847c41180d22886401c0312648020b60380c05501c034080f040584c00a0f0081c208 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 517944505 1250 517943255 517943281
    0x1403041d16050f07050c18090c010206070504091503020301150e1b09041a040f06061b03021903022109090609010b030a0b0d020d050304060207080f0316021309060204080d030203010e0a05 82
    0x241500610440c00b014001e62000320100d01508e400c0003c1c410501b20514540c0003048403072041c20160b4501d402c00740781560034409410300c2100345005a0302c5190110150302e0a00843c407900803501c400d202001c0c50040305600114004050000c100c1168005807141c14940e012130308010011039021640c484410603841d2184400786145a00500e400c0054601c6461030300710170202c2d2041c0d221821403500304242564440d4150200500503000041081240c2c903d000344180d505000c0d02c111030a0000d20181454680c409000000d0441d8001c0741d031080ca4600406507507070082c4261090442c1d5450610f81c1d000700d00024201040d0a51074002c480f400b81c0741d03030088201c040c2e0021300e101c9200e1968146075840b540b00b4060880140502c15000c9040300b00002d400c0a1403415000840c980032944891a640e64859a012680840d40c410a01d15000c118010145154014a40141c1d0780380b424cc8001d10300003054480805050041c00100421056051625840098440042000c1c2d445134008a48 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 517945755 1250 517944505 517944523
    0x2040b18090c04140907050d140a030215070302070215090105070b040c05150301030f122d0f02011a130219080412030e06131403041d16050f0705 64
    0x1081041010000420340000e02c0c1203140c031050f82d0804c0072000392503002030380a030100e8010b581584215010030060908195031054140101149201d90600b1091242414084441078005030b02c2140c1c5010030000300990345400401c0340c01d08501c0c12a280c0c6c007240410f40f400361005030a5001094640f140e901401c100d41c0b403e90710a050380b1192501d0b2406165001c85800760901400740d0050900e071060944046a0607a0b41000c0c4510428495940d64804050810304140c100542c10681d203a6416407203039001091200580710784103c07154444000c040c0004d140c4070004680c140004400030b1417168103d00c0305110150762081080036007103002c5029100c3eaa0320701540094200c41c2a0300c2552010655004504c1200d040c0c4111f018220308400f80c40744072040902c0747d0400c4000c940c503480c29110010b05903220702509041140d22207802d506540069000902515006080d140c4000c6480080c0758004200e0400402e46114060010541e0107010511a4452000201a014401c0420070100d03 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 517947005 1250 517945755 517945789
    0x1404050a06020609011d060a05040f06060602010c0e041b050c1213140301061410020f1b03010f060f2102060d0f050702011b1b0b0c030f1302030a02040b 67
    0x40d4199031000025942c1d1030480791902e265203840b08908442015120910216034100c0c010103190b00c8501c0c10800520001d441110440c05514404000500d2405a14014186a000007400c0c81240c18081c007008030322450300d032280d40307006140c090883e06050903504282462420301c0d20b80d200c00340d00600e08500c24400b2090400041030b012080c140c1d204440054521450075044421440400e050a031a10713801543da0f00b610056a00d10a42001458202d02030703042d204036803d10344081980c0d403c001e441a02091f150400080c00c0009040034010340c0030303543d40c0d8003080101514180c400b140e00ca0781401840032450f061000c20b506148492501003d907038004019075643d1030414841c20050252550a541c0035041200040e416070040c4185400c0c10303a074014800e00c500c46240e0448840d0b80340e00d1000c00380702198040801068182c040b191050940342d002c9552810300d426000103841b001026601180c813055240e00040c0c8010808010b160390540e4003080000d5040001000c000119a900c0303 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 517948255 1250 517947005 517947019
    0x1a09011202060f0c0c0a080f0d080726010602010c0203090a05090702100501090902120606010c020103020903011e05061801030f082a0d1e0903020906010e030d09030b010f06020607140405 82
    0x43c1307401d0002c0b80013035030040200c030303281115552520107688034002c00810030040d0b000ba0400f100d0b901d0007903c030203a0080881ca0f00c0880e04021809801e203440a141c5450041e4101e0401440919024070551594039034038002541800c4c40240040c10400081c05518020220798002c0350180340200320004842c203a0b26028400c66850311141e038000c120551080c0d1091480c501c400e1400b450200c2d51364003c904c10380d0303041c0c041d40c0d4640064000c0d51060103006e40540d030310044490031003030fa042d6800f16030034001d00100d44c2d4205081048081e80000175075800c80d080c510010400146209a4032208641c41561240c481d400100c511a40419000c40b80082c0c408005410340e20190104080d45582569103035844601d03458003021168421801d45407000c503840300b0b020320242c54075a030303003503402481494801c0809440c90080703820001c0d0610f5580c0415583e0030144204807801e04101d000d800c032980c00c51022450400025580c060103030041c414490780c401c22501e15180101110042e141c0038001c0 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 517949505 1250 517948255 517948267
    0x2180102250b1602090a0c090510020616110d090f050a06080f0c04090c1e050921010b06160b0a1407050c0703050d110c060a05041502010f0906020901031a09011202060f 74
    0x720281a506100d4400030300c1c86231001c5107503c0d02182042001180d54000c01c119a10118503074210540e0014480c280000f09011166a500130002c00044103902d6031009002440c10004107140385250300711902c10f28446800784001907008035120ba1180c035404c9100c0c0300d6110008900d119124540240b2000c6081c0b06107a056250440002020401050540c00b111105200115128011021070642c0510715010000d1006440c500b4406001c1d565000021000ca4400c0050007680c0310840303401c62402c0905580c2d080c0a0a44040340d480364040009002e92800303843c50546545000386503c003841804076000b00c0060b4100410001756034040e08407118415082006402d02c80c000a40920511400e0900e542d2818804140d4440382140e032151070410741011403210320207003617903903c50440d0358842c05c00c0e400b18094043c1001c50383c01020010b0b80d07490b900c030006050350031206c00c680d40c1500c11445083e8903142c1c00885411901051b0b88007000e0309040c400610ba9200c3c19140010900000c503035 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 517950755 1250 517949505 517949521
    0x603040f0c09020d0204031208010305060c0903070e1003142121090606030d0e060a0f050c03030703090b130c05120102040504090b09060105180403030b0d050102180102250b160209 79
    0x104187d17030003100408900d645c400390869407050240001401500301c00c2c04900f011110501401810718001e00359200e854030ba06d01909400c01c02c40359500d41180808040041c000c26058050410b02c0030005014107129629501c011504103595140605000103030952010150384a48201545400500c03150ba08144188964460301903580c071344039010342c43e0703800c401d0360184410720307020761003e0034060506015900a49420f0040c408010600c0410851010110b0060005610801590b100010b0745001400c00781000e90303006010500344000c6210b51030105281c1c100b60000c8541c200e800d540080c0010028a019015680c0a103401a04040029041090f203075039991259a0b110304540d090307a030303420410500d03100d14101404590312001c00301c0c0c00b20b4440c0d00445d42c59040949411030400d16940c44508a0703006903000141d8a180180104c5103603818410742c6200070403010460001103061010b6101810540b041d00080ea600245580d46d5018104000302c590b074001b000c850292030401340c = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 517952005 1250 517950755 517950757
    0x309010c03050a09110d0c03020306010303120501270f060513060e09030304030f0503040501060b07080703020f0d020d11010b1801030b070c0b0708180d02030a0801080c0603040f0c09020d02 83
    0x40c00000c41d0801000031411080e51040d00d440640046040c003000024505002036104420426205d80d85020004405a1001c00c60350f4006c62080c0d40b0210260b070008100c41c00c885043c3c020741a0b120420680c90404915241205450550504005880c2111030581c6000704080c0c1d12440e0002c0343c401c0c16600e0ba8802d0360102085500c0c04281ca0560741c0e13200501d03901c1c1d220480300200824014454243c4142c424005903034407e118100014025494031400c4a294011680c11191003000107161010180d046c8040fa1264400c07000410410401c001c0107915401c400300b8910401800790b00c04000d006003500290b4030402e01800c45c0070b5000d0900710080081d0001d0000791781441d10900441c0d0614031a8034001e40c819003040ba10581c0c0d0715400030450320864050300300d05503910044003540d03d55000f8005401104070a40055584282c0c404014020610592201525400c4164072075015224142107952191707008030b0455250400e45000c04071210590070440e4110704c04510003d0044441e4 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 517953255 1250 517952005 517952021
    0x70c030f093501020403030503010b13120b06031c0206131b0b07020114070206030a0c110d09140d020915120118170c1209150d060608010b1207180803030901 69
    0x708650542c0002c100300e1801c0c0e119a00c4000c0c0021010030040000c00c05010140c07a0f21441d03400c4400100780d8402002c0440c007003180040d01e40e01404010300c1014036040082680c103c180c100c03802060320003200f000c1c0d01e400c40248410251840403d1031410004041d0362602d03a106140c0c216210941c80310340e4182c0036003003604d0403404150b11810106440201c501900c2800d54000d02b011314583c2d80d07020020150601c0d14400d4103000c4c490400c00050501444251950405076031800030407440d290000d0b40e00c201003025203000300100f884000158445500e01680401000080901c942210001c61100c80d1030260440e100e500c0e0072031680c10203000c2800c1c5400796009520003480403440c1e2a40b0503140c892042c1300b003625440b00c03922814031450b182c05051100300007000c0da203030700c6c04000204010350310464a0413503050f5a0030090080c07d4012031a5409010403580039410a80d80140b456180c0e1405800d1000303214080c1048951001c1602c0c4078005048060240e80c2c4038242071100368003800d200 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 517954505 1250 517953255 517953329
    0xc0f0809030105100b0412030e03030a0315171005090a12030609110901020a15150806090607050a09140a0f08010b0f01020f0705040b18090601080d08070c030f09 71
    0x40f0f000301d50030b903e00c1c40010307054a0170070f0003443c034151415038001c508100e42c40e0214240b00d000d11000e4010381d010b0001c2c02c011a910385006c00c120008102100c60050141c10401440f50201c0b25070b04400000120f900d804a841003001882d40c0311000c15038942040c0c0100103220310350072001b29a402d541038100c1c00c02c4444080042c032882803840c46c4c0d81d8940c001d094065005078030150b910004107854440711890000da205000034a100507407010941600b035a0062030355680302c10309100c4506010002c0940c028200e181482c142131044100429030310042c8169001c10a83c82203d20041d41d071034140b040141402803125140316030f1441440d01903d804100703e4856045004103000a50010850340d17040f000d81d2000c5e00f03c403401c000800000741800c07100da5401200c0000c070b00018248102080f4003500100c40201074641c03403e403a0300c4c5843c260000d13020030000e80000b03001045801c4440c220500d070b40360a00303d004605000d01120454650350100502c065410845074000400814010f488401 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 517955755 1250 517954505 517954511
    0x50a0302093f12030703051005040203090d080a0b090f100902030711150108030429041d010b0c030a0f051201140a0905040503191205010b090a050f1509010c0f08090301 74
    0x858520961900400303d07046079404010000508280d110f580a50b5006100c40486503216442d074002c64101e80084804114603800b9180003400b454000030003d601505007403041c0f2515038414082883c5490140c8100c005048640126500304c0000c622000507200511046450b03240c00d060062040d03901050013501400703054800f140c2c1032141c401180c141c0e5120380065240500d8550f101421524144460780c040018000140420389244020300080c101c0c64030408442d02c040074520440101039010322203e01040001d000441c1e0301009541c50401e89003440418594504816100b0b48130b00100414010000c40000c1075003202020342810820084d109800d050303807101540d0086a038181c3c1c015206901c20f12803010050f003420003c6900601d5440d20f040b6045000b000b840076104281c1000703000300710104601e080303800c20f0f400030001014219140d03440300b8032070008100c412076070302880006601e00050104159020300c11705000c1540c003440660010310a42070220f0f150708815842031095003 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 517957005 1250 517955755 517955869
    0x20a0504090c0e090408090f06040b1b06100311010c150e01050a0c090302040b190b030714070209060d06110f0c1605030d122a030c050a050a030209 65
    0x100ca940e4100c8500c401601342074950f200c0351540c018940007480e929a00181503000c0340001e417a40c1010700000c4c00b031500c1747c07620303900c40041c0016001103550002415034000020490417541e00d4144104a03074009020361034001c2120b004880f2400c4448025210f8951803400c46210350303070343c5e0056400b049807078020003894440c0340da43d5003500c22181868000070320203401070025282c56409200088401060b04486a4944001009009080c2d0042c14045400710410009642040190300302444140003140303094442e44c0040c88511015100a010b110705148000c10400b90f540305d400c1543d10020100c0d1030b020615007801140c0d0100d80c1011441c05400098010b14030039003000c0742524130003030140416404c80e24048644500c400c1c141044591139070300c5501d41e03510011100401072109401c42032203160743c60f4040c1c00c1ea1031407000c00c030800030704000c0500301c568003400b80c134000f06003484c015039200c0c0034900044001d036562030030388801515200104254810000b48810703c003200702a40074105 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 517958255 1250 517957005 517957007
    0x12061205060c03060a05040506060c0a0c080606062a0705120120040f030f050c1c0218010605160f0b0f041b0f06050a110105090607110f03071b0801020a0504090c 71
    0x400284d500b60381009802600b03010070f03d032540043ea8480b6002d0708060500c00b01da02020310385014011300b07403410b008214041c00f14200c24403170b85500c45003d8840300c2c909801003248020f1882801e06040503045040e0007100011f10034045900107080003054501903021861096000785500c0c0940154401017110070003043c40c00d8004c0d0380880d09005a200c1c0d045155846000300d0184c128001c8495010700f5513071038a543e640b00d02071b09001c41a101425841003d610510074400091071041e00011084001082000c0c2c2c00401c0300c0d5000039002c080602c0c20041d151080c810403105000520040c1c55000b041811880c4107030719441781d4003425201058002500e096610f40c00540105081856124001e21070340d40120001d1241000350b240240c82c5962540081c0d00b140e05c1558078070400c0e040b4006002e00d5591260704110ba03550b242c805455000c06091100e642c0f80b04140000340300e500e086840110300014064404014010a0000c0d0754446035071100500310360050240d03c1c000345c070b0504042890307 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 517959505 1250 517958255 517958257
    0x10060305010b09040e03040b03090304030606271107020607080901030501060c120c0c050d0f0204050619150302040f0909060c1115250507060b090c0f070312061205060c 74
    0xb01d550004030303032074500e024041c000684485000562148010400014040b5500000390f124000d100301458884c0c0c15480e00c0303410381301d2a900602c4492070107418031108140e02e10008d0071288010000069601c0c11040c100c003980140c4402940c0840081048070138410a01c0040544030400d0341d0420950380c0300c0700195043d4241600160400d00040c85084100f0b000d002c40328a000d00698100e000966200002482624448022201d0300d8a4090f05002c60915019890b04100100c5010381031504820704c480b0365845501c030701f401031a203509100030164081d90441c0d000e06000c41100615944610186000e445640700c11124140f80c040e000e203829111314403a41030403200d080600038100200a10250601c4c1c0a071500c0c03a2001e030307034004043e56000e0a1221151340700c16141c0c241c5800b181e0400e0300450300e00181d076500540780d20041082c00c80b1320004680c075442c50940c0141e21444141000c4909038020618007509610300134011401803034044d900c4031914454411103c3c250b6400b1020341003 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 517960755 1250 517959505 517959509
    0xf102607060c0f141207030c020a05060f0901030b040b03070e07110a17070c050306070e010305011202010e0904060e01090b16030e030906071e0f050f07050f0405040f0f0602031006030501 82
    0x5448000030404002451310a0b0104c44143d50011140c0d40d8000a207100400c0d40300507402c03004140f18061480850810609140041100300c801c2d0341000010728005007503124a20006040599580c4007050694940e408000300810180803901178680326103403810107041c01e8a511002c030366400d01a0400d1480007a03841001503100c21140700040800d20345203219046018100d940203412000450710f51070230008107104980c0b542c1c40c0c19201808600243c21501d0680201010706840400100507036000034000105101c155141c201d0b559480c1000401401d05030001034440d401d054928085c410900c200301c2c01012400160080c00380e400b0f20079402ca44c110707180510b443c1c00510030103c1a24151001c0c10700d413801204800c1100c3c0711220810132405640e0011a00d44001c1e030200012f111003081070780310130060a00100b409070304000028500c1620414024403850f103034070000381000300c4003140300340480c2c1c13040038108420010329014010390012560000d070700c4a0b0001c001881c5110703000d0141 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 517962005 1250 517960755 517960763
    0x90605091513030e0105160b010609050f0d120c0b0103061a03060f01060e010c0519030207120b040807020607120e120109020603040206070c050d11270f102607060c 72
    0xe10b101e80d0340907109550044541814850180520400b00541d120104000e0341305a25400b903544c10075001400f080280d4201d140a40c8000500143e245c8465440700322260300800c1404080a24800442d13000d106c4a10003009286004c000108110450b00502a807812803107441360308022540900d6a113200844107a915a01500f00400000340260341040030218189801080c4c034000e5200e952074418607617440e01181d072502e1340041c141a4140948030140c100200040074003d25529040e46080000d000507200c0100020f21504650f070300400c989465a114108140d18403c910000e04110842000a805441c1044049881d0380c07042c880d19064a50041030281191520740134410075400190084484004100d00440d00d41d0300d01507007410540c86803032041112940002401942401d001415002c25016031186c07070140310000880e54043e12007080b02886039100a64003003004002d50004c400164440f881035034001d2100c0c001542d070580361b4100c85030207a45a508a41c91384c4c0b80300d4060 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 517963255 1250 517962005 517962031
    0x1b0d02100b220507020c0402070b041e05030301150905120105041a01050307180f11030412020118031206050402030c07050c03070806161403071d04050705040504021c0906050915 78
    0x31440d0841da902858000b00f545c81121411200440442c0807640400e10a95071071001a003008100103c20b0045800031004e00d03000e0f8100c9200d80d48a90342e900040c09481c1070320080c11a25442544116004001400000c00350024810382c0e9a24600910040c0c9064900d004d02d61202c080101d0004180c604942010340240000d0749030074480310709100c2d50400082100d407146011002e0544034000d00c00c20710380c000419690780c10145482e12203150400d42d401c0540e4102598545040070300d502078140039400d42095003445454030503280003495030307400c125442840801408039140c140e801500340300c0d209078220350000c0b600404040d520000c078411404160300200001d0795251040041c41c4034509641058042c0c85202030104a041d0000c0360050005804140001c1d40207120305814411028140c82c10020f908083c4001411381c4980e0107014000d540001e0818803100c80081c1d0036044000c4036030100240c56042c60314501620098034921042d00c1250752200680b040c0244650040c00308410345 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 517964505 1250 517963255 517963309
    0x10339140a0515090604090f051905070206041112011d10020301080d0c0213051e070e0a062106030f02010e1021090203010f0b1504030201080c1b0d02100b 68
    0x155059100b204800c0e08190709000c001861f118500035001c05841c08040815985001d030503040f0608240070800c040c3d2400e01c800d2110303e0f40c0105070f6079003090b0412203c80d80740c59000041a103008000481d920150328120102c0d4a80681c00707215040380c4000c4054a1503078060915060030b901003030140507100c0c1c00403003903246001d0040f003c280381c01380b0280010381e5885006140504907082111881010880350340b2140111580c000c44039071110741030804980c5090400301041d5032802600a02d424482d084d0040c3e118008141c0741480001100001801104d440e4504005080050a0b040f40462070040b50200a0704e1312200a203480210355480ca0031000c1d100150442105440904d0b1a1017036070703000f100f00036031401e015484c4100c0c0680d00c08a440c0746010140300943d00503051800002c6000d00062006070380c0480301c5500500d01c44150345d12030840094601600007080903441c0c91340f04070601c0e4000c0640204501c038141c0780d565020001c031040b02090060380303600c1c0001441c10701c01c0b44e246 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 517965755 1250 517964505 517964539
    0xb161b02040603050a08070606091b03050403020705100e190503120706140f0f0a06050f0d05071502060a0b030319211104080606030c0306010339140a05 67
    0x5604025000400200b5201d907030341c03260f41c1402114901598803040c00a000300c02e0062900409005200e40c050070000590844135206800303100b04000c00801d0307124008a018148204554409040c00070000c00071182c40c00381c0a45844004c1d1440c90251110748401440241c280c0c0f000d600f2214080d0280c200500c2964030011181c0c00000300b1110356036220315a1861500101c0c038140300700800c01294400e400e000c0240c0e01c80d83d10040c40201c455082c15400d000c0c0c0c0d02c6200007441100001d8442005280701c0d40707026400e00788141c0000100c454075182181c585940020020301606500c2d50410400d4820001e043d00d07413040c0086500c1005426000c141044d02c5161645202d030184071440b103000e524440c0072402c1ea0459840140a020301250a218415007404825080300b4210b001b01080c040a80101e40c40300b50512014044010303018180f00d440040d42c055074540108a9441d040b0100410000c42a03500c01c1d000c0c40851030040c140040181c105141f0140913103200034001600e0b0744e40311403 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 517967005 1250 517965755 517965797
    0xa1a030c210a05030a050912060103050c06090f030316030f0f0c2004050109060f0902041d04051c031a061309020901031514030d300209030a050105040b16 68
    0x162180741e9104418850011640c00c0c00503060203046540c41a54400c440420810040f01440c40151150440d800400020b4000074014000c00c4080c1d821544031b0345e00d1800070301d1420503200c50300e0f0036000c0094000c1e210903001201c80c80e071511030307201c4080e1840b0b5032004450f21880707a00510049020b00400001080d41c2c1007003039190f883c90844040140842c80c020a09035070b000e80c032a110040c2c40d070b1010f200080c900f03220a00a0061010114106460045103060206c000e05e202540c0c0d10007400802d00380507080c061088110044c00700c3c54980700700070300e0040c020450352800031104140f134000d100d0745103402e0084031250300c0d00303c0300500c48604202c400030095001c904414185580c400c40d026085549143c000001e024420f40001d42c040e0810505080c00c050305240020070010700040c0840180801010380d480302c00006006a203600c070010400203114044035240d140c49403d04c88810010150002d520461185841c002161115031081d0000640d0704802408254588040c0001e031301d00d0301c = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 517968255 1250 517967005 517967059
    0x30f0a0809180928061a0a06020d0c11040608120c330703181506090b0a03060203070909021911010213060c0507170f0c0f010e0906180a1a030c 63
    0x104c00703800c4002603951850100ca40420300c4401d2030002000c840c00e6031801d00321107001884240094440d0954540340245401d06482004242400500b00c0e01c25030b4403140e1114000c0c045000440700c841002100400341a00201701c00c0c0980c0c850002c0345c1c201c41d01110602c3e6a580300c0080031001c1208604446881400b0050045003055940c415280e008103802e00c0c10b055107805040c213420300a200e00b8808042c0c814680002000c1800c200301d101080c0c031540004400c0b203400c03000068403500c824500b25000506903101e50f0400c2e00104011004080100e41c4411500c3d070b940780c1510301980c291450f400c0c3e01502000c090003003808002006403601803003842e02c41c40c0c420010b5070500c075100d40c03024207000007a0002c402160f00002498412000800000a0704401200d0201091000c032000824400c1654400c501038040c18020402d1900c42d50b0307841590298145030741c4914075000d44075800620210104c1101480010880342c62070a020a401c00169030186c18846881550102000718078101 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 517969505 1250 517968255 517968313
    0xc01080a0b18071110050702070e0403020115060f021501030c05190815070f09030b1902090a03150f090f030332040209010506180f030f0a08091809 65
    0x1042c00440c03244910b030465803051a1507141c1c5510101003110b200e10b010054540030340c02070701d88030a1080c501c3d00003501d5011502c440c2c41796542990740e8a402c901600403c48107201075100031001213440c030341051706036600d10980e900301c13044d0840301440c00c902400d081c8000751080c91012014070a44c2483d981c4440e43d03001031a6009900c507581c6040360f207400304c0c000d5105280303a4007800b4031101c40d50140c0310410300482850f142c0d45040c1107032140303c0e030204094005020b415041001c1c450789922901915005480100340d400600e9490400164141c510100c0024143ca046d480140b01410740c415042d8554000707200400d07d0200c3e0340e0580003400c8142d280104a00c1300640b036402c0040552640806042c0c1080c0e011540c2054410302c1065881a04150f01c1410140840c05040501c0cc00020441c402203d603620400c2481c400300c0d007440781145464409002e904100c0e424403200344010610a06c0a0310200c410ba5191140107a1110040d00c040380079401c0340c9480101c05160704001d209507410 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 517970755 1250 517969505 517969519
    0x24090604150803041206140f0c160206120f07090b1206010e270601030902010c1101050d0c031a101e03020f03070305160806150c07030b270c01080a0b 66
    0x8820510385180c005503c260b481e04501715104007001180e004000c210000208000030070308000850290100c1b0082007055518000300d086086c40b8000010040321540203040a80d84034092214024004411140c0c0803503601c0541c04103c40510800c2c051045505842c42141851005912442d0700b00380640010b040000c80c0307030040c0306076450326086d480032054001100d9500c50b00040002d40040c00a080905051078104ea14001d80d07048a007040285600840400300d0004440c0180e680d40070721254600011300d003a0700400c40c55016840b0b0a80402c1c08580704601c18100d030200551030140c41e007200f00045240d000301c0c0030822a4602c41d1007181007410054201031004a40a0440c2c0003241c3d2a00026141c4040c4440c01980000d40c1c02c2c0507601e450140402e10b021400f1902415101c04a1010440002455501200c0600c90540034541c001040109424050b9070f4034080c80600c207040449524504030050380950018141d5514001078581c058281c0d2145265802084090491307600202 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 517972005 1250 517970755 517970759
    0x51c1202130f080304090f09031b1a1e1303050a120608031611011e0c0501090b070c02101805100203160c090e010b0d020607051507082409060415 64
    0x881c0b8810a005441207000840d1102e141514010540e0f03942410348084c0c9181c0b42d828008a075010030000120005019401c80661180c070f4040441c4d03004404c0401030300d5141051040020040b5060341d108035034540c5155154540d01010340d15000106801804280204201032455015240341100b001108000040741030b6549805811079004070010807101d0300005002080048480013007001c24401e00e0258000e01468621311803002100728400d041c08454500141040801d401c035810301076002504480505020801400391080341c2c004030710034071000b00a00e04d820301c1680340d1442603a42d540c01c0c000c0f0310b00c0d003000c3c0201403205444103030031404200100006a103066400501030b9205442115419113094412811510141e4450110b64103007041480d07590350749020412940d4048034615580c1003c3c1c604603140c172200c0c0f042070707040710404410170181303541011401b8030a89101d004030f5186001104460040040e815140d0341c046035140108881e0b05099200342081c40d028409603017101d07 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 517973255 1250 517972005 517972019
    0xd0f0c17150114242205010201050c030717180a030e09090c010c12170702010b0312040608040f0305210105030709050402090408030402190602030304051c120213 71
    0x422200380c100c0d1540064000c1d11403892040c5a5801007140c1c01c9850503000450b400204419510503030505800d260090700800c2d4000b0008403804602c0c2e0302c4507800d40d41c40b00003075a50400000c0c41118055443e003400900b81d4101101201c0c4501c0303803a82d0b24101583d00d156440c0c0c00c80000780c0501030a50030120b455040100030801e05210300c0c02a15050a500d02d4281040890340c4014604e82c45900000b8800303620b6600185481c4a090344401c00081c146000c00c021203010000800c84403140100300140410345030107500a4050000030360a60b80c618445611180c1d0511882c400c0c100045c92400016022882c2104035044d01c512910301b640c070705090b5250800700c003d000356400d014035201c03038010041403074100031503001402c40400511980c44c01d50002042920700800140030810300000003421507844003882084071074146211520320751a4403000799203800444040785c00e0b2103500c10142c0b04034550b0a0a0605031f004c0d580ba10041d120542002c0041e41244110086042c1c0101c40400c01d1 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 517974505 1250 517973255 517973279
    0x1808071e06021e130308093c0103020403150513020301060602070509060301060303050313050a051221060a05040902040b03060f16050906091c1a240d0f0c 68
    0x10302611000d41c03a07040302d418019441c003014800ba03403039420130005a448119400001000c80380c1100140361500301c1000800e42402c600c0540120341c1080c000c1d4810142c1c03034144071490a01d0307584151209114644015800ca100d01e0002404103130380200d0310083c505440d0407031940040300106e2038420386d078141d020a00b9039030300d03820200c0545c0003160f00303210070b061040000b9844103080b40284007075450360700d02810350700c0054030084207143c20031b10b02414004100110181c1c650300030101c0751350019035036156885420241640300350200030002c60401c000c55100050207100010462580140380c082048020f00c1d2100b022600107403500901c0c0d2041c0e40901c0024841c1e0010484070f04546031200c1350002d01d6102c92424420300800f804121501d441d08001d56181d9032040d1a500403a82403d40714a0784900a048000c00d0902001004d41021a014403614080c0b201c01200400c0d0850324010480004c000402e10f0b078000040000b240007042d940f41e000f81c4014000c0821114064440020b40c0034 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 517975755 1250 517974505 517974563
    0x904060902181614030a0908120a02030708060103020a0210020922020d0b010207034b03091a0906030c1308031306080903090409060b060408010e10180807 68
    0xb540104001c1010740356050807807000c51000c03843d05800403407100d09040744500005c0d013a040b0241c2d48543c000100090141141d01d45180414032580501d8444107a0300a135000b141d41074001200400810000d502900035a9010721103a000752020b0ba14040c01c00d4001c2d001075490540c020345130103d035003824210468101c5190410003003d684c80d211020100c0c01d0b00c1c011038ac114119440303a42c003080450301401c6006d80c8141a003940c100c0211040211031b8440300d20341090241402441c13007400e14842050520f0b020b142c401d03180c850b01e5903910306110014407818003102c0c1070628100802d292500c0c0600043da03120900c80500c900341001004800302800460f0000f0103d984005103134002c84400b01102801011907240c09040c41c5060714916031203004000903503004544a04c01c6804021f04d81d004100e081501800315501c0702d640b501c00c107010b400c04da4000055800340e80d00c40082d03100e250080780d20100203035209030000480741da203c00c0694081c140c05d8850580120002030540414002620307 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 517977005 1250 517975755 517975789
    0x1020123101e09090302100615080106080106090e1003080c0d09080a020618030f0d0c0c0b0a050a0c1704030803010e0906330d0506070813110904060902 67
    0x80300385070003040c041901400340c000310007024046281c001d60108a12002040d91850b0201162007076030741ca826441c1030100d0202440240c00c4c258040748104040c010400c80004076614005240d9840c2c0741512801405c0c007603003000503400700017403001c0441001102c0c1c0100600e00076440b05680c03a1180003080c1c00558244015030803858100c1b03121a0b21005082c00b52030404007410fa5a1490760004e030051140d030003018001d03414007103140b1803940c082c0407900300c40c21210151076034a4100c0301300800d110341c81c5504580e108103509020034000f83c54810b90380000516103490349440700150041e40e410008030400c0ba641520ba0340031070f00d001d00103405400110f00c14040b1944030750400308580c076a80030040504c0c20650050b000c101580481d910032000c0b80c00e010109034120f00034004903503000c46c0b0040880341c00120100710300d0100080040e00f240300d0314131a91085901d4542500e034100d00d150b03030070020782140602e602800c4075181826426403c68400e41000542c4c55250380460310211018450385 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 517978255 1250 517977005 517977071
    0xd0309031505100807051f030f09030f12090203070506070c030602040e070f0f35090d09060801060e042304060f0b01030209010504090b010201021b030301091103060d060b010201 78
    0x4030003c4180840504003100c080c21089051501052080c00c40d183c403180c20f04041644003481d00d0190b40701c1010a201d104041c8044000740c24084d2560070a14002c0c0c0006e01564481c000500c4544100ba040d00e5006010f88111450601044200d400c80076055441e50311003000040015400d00c0100028000c02e0603419451601080140044082c52450028403119004490406a000720b04c40c407100003a100802c07000001484018100d100c0800043c1110b5844003070101c18400094240c0c1c17101c4159a48082c555200c0204035200142840781d640030030002c2c000500a8502a0040810b18a4544204002104503400d1190201d4103440c1035030900d0783c0300004c4c1c40105003405131034001c410a081c2903142c508440d00003031075441a03104d1452a01d40e28074411955030b100b90104d54003c1d261001195070601d20000058881e0300030301c10203110a241802d02a9040a0101905e202c0d004c01040d00c1145400d0380c03222000b8140f50700d142811556203800540042d11401c8207100c8941c031900e030403 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 517979505 1250 517978255 517978261
    0xa030f02090a0504080a0c0c09020c100e0102040807030f030c1709041407021207060b06041d01050a03020603070f020114010803040815010503250506030109091509050c0d0309031505 80
    0x200c8001c841c00340c280400681050f0402022030003100c11203050300074515107004804154200140914900d80000d1001e5000182d2003814003c0010b19040e2152825800c014426560700c400d4200d110f00d02c51919141c224040c04c09c08a4011142c005040707000707060a0344002d08036602d003941081d00746c81040c20850046000300389030400340310f6030845114800d00b14030142007400380690b4075403071500b02e0003585030300080f00c90400007160418034001a014144a444a440d050070305e0341c2066610b94803010441d43c800001da50719040621034126071b009010145543c035040c204440400c0541c0c01c140075503489a6a24282520100a850091501c0c00c040d42c2c545041846142c1003040a0340080d20f09800391006000310380e404181d88841c5c0000844500da81180003046c41e541c005580d2041d81d100740c012000140506c22a00b00400c0e2521404001420391071149080045640008002d40079074000e1030b4081c00c4e8206880d00135400c500900b40501c0999407550342d12907020443e4281e041d078980305e0080c = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 517980755 1250 517979505 517979509
    0x5010e041109010e0112150509070501120209060306040902120706031e05102c01090b0109120f0b07020703020d11152b02090409200a24020c0a030f02 66
    0x90022107440481d20000954504205855101018040c071108175540d98031070003c0104240320f03940c00500f00310b800d200f28a4064105611214036210b058003050388a00301c02c0e030a403118400c50f800140d0080203142551117084c2403200802c04c0210403a04040d03998a007902110041040d80002e041c641d401003500441000003103110f0711428524050340d030800081c0400d181340703080c0e980107440422011007010300400c2450040100e1441c1d2040d00d4200d002c0012800340d22541080c0c000101c00e032540e40405545855001d41d0340c4411101a091040700080e580002e80c6054030241c01a40314811a8001a165000a680c400e40c0311000c503003064880d920300c1c4072070414010705005039445448140c1403400a902800f18540b1100803040740c100616401400040a0b505592140e4800b0300104020b500a10303140fa401a040540700c0442c01c1d0004422400f464200c0c104c005644803200b0541810401e400580f0b402c00d454440710003503009040a5410796143c0e141c00000441c020101b0300c28506007801 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 517982005 1250 517980755 517980773
    0x601051905090109050901150b03070305010b0412030c0c0b12040c09020412084504020c030405040f090f050a060e06040b0609100803211f0302060708070605010e04 72
    0x40d18094016654204100e655510142c40781101c800b2100481e107551080300d540d00506040040c0e00784840704010220304000b185010318440c60180d1820402641c9070040b80d5002c1c00b941c810902c0390100e0b13840000000388108452501c40740309030703041600d0b43c1c3c0f14640400150402d042064941c9100001c04c000d00c050030703510000402c081c00381149080d0420305045c00103064044043c0a03d240001da40244401c403c1c4c3d200c012150303140a0442c00a2501c500c60010361301e484404820014240a500440c075181c401c442503203009800440c074061400c1c0510026295900b5041c0c1d41c2c544d00e12401011900038100380c804540720300d001d0b003545106850081e0071161188800b204903407005040000280800c841c00c1c0c1c00c008100d42c043c4e01c0d9a15604520700201c6142c12081c07060001040d0b210302c140c0d07040403482003020001c64084003527494000045884000401c1400411803c01042000d410200b0051032040c1c0611101d034645203503a251801660001e0380812109000c12080105211b0004 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 517983255 1250 517982005 517982029
    0x12070b030c0c0c0f01081308070501050114040b030c0f040f020c03160c06080c040506070203210d140631090b0f180604020f18090109120903150b040b040e060105 71
    0x204d2502c055541c40d0002080040c004150200400b80f1940780750a20000314195400e043e88003000b40180d43c0c4650349034290180540c21640554201030035400c49141c00700b491041810060050240340c40c203202044040c0586500103e0290b60821028000301d2043c0f006003c10210f02d0980b07200c060300d502d04602142980e170710240412085805109181d211401210204d801c01c885054480140703000180c00c00b4251295803031072414031b8910405186400010700703509412000c1c00c01c00090501030003001000c080324516440342c04401421280b00750034083e50f0002500a41c281109180c1c020b08038100d0380d01d001e041c1c1780355400c0810411036542501e0f4403a40507441100768960f03240d44504550ba514000f4000901c25003004d504001161124000c04003209200c0c10020220f04005404c0c5001380325005041d903108070a011140f803440d0254902000700d0360310030341042c0b04820b002840c4004102c00103c2c00c0d8032035150019072010307946600583e8021222003010788010752400c41041045084c2c0 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 517984505 1250 517983255 517983259
    0x14040504090f14060907152a05010605060f16210201021c2306060f0403060207020307080111180307150f030c0f05070807060b090705030405190c0512070b030c0c0c 72
    0x324200b00c0300d00740104600c02140c51441d059840c8074400c1c4001d9400b800c48d0382e9442031000303c42440058031145a0f20148481d40504001c08c03c0d151100d003804451310440d070b504800c0c074004200111141002d0000d216281e0300032032200e84031034262041d8405024a1141c407400503900840c4402d6103c3c0c0c1030180c840f186044020030043c00e685207035481c102d00d82201d410720002001c60002400b5403104c1040782d28502c1c0400c105a07030341c1d0722403406074000d400c80c0d08203074020300c0b9640c0003003900c80c41481400c107440c540c40c401d40e040111b1311807030003100d00440b8042034141c0180078000442030410f042d2409612459107801020b000d9842d0000c0c1154191503c100400000340510b070b003182d4000c030482d0641c5070040044c0b5903800c035600b00103019020910656800c00114010000d541e0303070003800b0b54000c030720a80685014544442d0b9a005c40203c2010181c05001001400c010074a003618580f000000c5513019a207200d559015480045d030030456043c441c4000c0022003040000040c050080d0706481 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 517985611 1106 517984505 517984513
    0xc0d020a06210501081b06030606040b0307030f1a01180f0b1e04060503041209051807031b02010e10140a0e100510030c0e0402090714040504090f14 65
    0x1031001e141e96050b142c00c0c1d50054074074007031f4100e90242d80d0041c41d07107003006e05000418000741d00c0903041006265980000c4680740d412406246031f0400510842001d20259070005030001c1c03c8103007240c2e1883d2190f0403c1c440c1c44008500007003035503a440c90f0309031144810607070700321700c4907449859400301c0001040000b42940d10030002e6115031301c2075100380b18241861000740c80d40f49890258903401846100b0324812440006c020700d80c41402403034042000b2303c049003030400c042d60908640f0010303511010304101d100410801110507031000d5034200507240084102c0c24020030f0140000d42c4060300c0342d00803105402e01700401d9040e008003002c204010700346441c00881301d110030300c0100c503040c0744042c0001d500240342140b284941e030042c0400c1e005580721801201d204c10207130405502404244404101d98a85200e0b060240e8812081c1040d851041e0401c160300e196140c0c02e40040d944 = true := by decide +kernel

theorem cover : BRFrame.Cov 517805755 517985611 := by
  have h0 := BRFrame.cov_init 517805755
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517805755 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517805755 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517805755 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517805755 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517805755 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517805755 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517805755 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517805755 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517805755 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517805755 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517805755 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517805755 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517805755 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517805755 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517805755 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517805755 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517805755 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517805755 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517805755 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517805755 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517805755 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517805755 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517805755 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517805755 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517805755 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517805755 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517805755 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517805755 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517805755 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517805755 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517805755 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517805755 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517805755 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517805755 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517805755 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517805755 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517805755 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517805755 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517805755 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517805755 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517805755 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517805755 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517805755 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517805755 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517805755 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517805755 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517805755 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517805755 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517805755 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517805755 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517805755 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517805755 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517805755 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517805755 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517805755 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517805755 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517805755 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517805755 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517805755 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517805755 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517805755 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517805755 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517805755 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517805755 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517805755 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517805755 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517805755 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517805755 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517805755 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517805755 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517805755 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517805755 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517805755 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517805755 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517805755 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517805755 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517805755 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517805755 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517805755 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517805755 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517805755 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517805755 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517805755 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517805755 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517805755 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517805755 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517805755 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517805755 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517805755 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517805755 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517805755 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517805755 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517805755 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517805755 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517805755 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517805755 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517805755 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517805755 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517805755 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517805755 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517805755 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517805755 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517805755 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517805755 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517805755 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517805755 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517805755 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517805755 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517805755 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517805755 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517805755 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517805755 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517805755 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517805755 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517805755 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517805755 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517805755 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517805755 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517805755 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517805755 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517805755 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517805755 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517805755 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517805755 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517805755 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517805755 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517805755 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517805755 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517805755 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517805755 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517805755 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517805755 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517805755 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517805755 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517805755 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517805755 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517805755 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517805755 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517805755 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517805755 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517805755 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517805755 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517805755 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517805755 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 517805755 ≤ n) (h2 : n < 517985611) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
