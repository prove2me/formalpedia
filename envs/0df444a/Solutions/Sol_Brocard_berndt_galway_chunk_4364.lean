-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4364
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T12:23:15.940745+00:00
-- url     : https://prove2.me/submissions/006fc099-0052-4eff-8c53-c9d2ff021284

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 784712230 ≤ n < 784892086 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 784713480 1250 784712230 784712263
    0x32a19110603150f0d24060b0307020304090c171303030c0e1c0c08060403180506091e040608030c150601260a060b0d050a0c05041404050604020412030c05 68
    0x1410860041c0d180f20218150140c0240200c600c030b6410341d11074440380c1c2c8800760440e0380500020210350305440c0f00c0c2104514800002c0c00d0043c0420003c00709001c81e805000c2503002140352600c1c00061030b0182c50010511014061558104101080c038000050702c68070704002c00d541802c2142c500034040742c06140100c0100804000e140406446200040c50720b24000f0304140c07403001051516005d25a401d4005401d54046c0b034050104168005460030072500d91b20a17800303001610784040c80528054000a0380d803102102d60500d4089641c410403440d055000383c4003190040d110080649941d00441c003d0702940d021001011020b8141304074240c10030401d1a040100f0045d4070002d020300d03d510028445001484070100d084607a0320707800346000b890714072181d0361074448101029004110441e2003061407400c0090b5445002e10440444040d00c60300140300c441c00c4e4102e420322008040060400b41c01c1a070802c0085020069100140c070854820750303418280c24030340d2924600740400030403003540d44c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 784714730 1250 784713480 784713487
    0xc2a06270b18060903031201030605070f090306051305120405010201050c040308040312263702090112020f030105120105010303050a08070e04060f081509032a191106 73
    0x310030640e088422140844202d00c1d00e040710750001440b1032090541d0706038184800119001c2c90f0300e004200d00d0489002e58010041130303a42584c2541c0f0817402c55221030008644000038000222182c0c05140c00184000c038a100001866981c18900040c100c2c0045000201085c10072039036909014065014070b6426545040a10759580c1c00c0d504c0c021030200411100d442c40f49850070601c00e100300800080306039584040360303001c0c203800c1240550549046400e00c000910041d0240034900e09148521020b485100601e01c11f4003d00d4000d40086110341d0420100c999900095092030010b01101c0d8a54505295694540301c00c1010340c507864028419264101001000401d42010903035040b001d0509003100d89079500401152800385140d5166801071504801180c01c00510742c3c10740940d5110012160ba401980a00203140b54003100d0304c80c0268001c00c08845040040207030303040000d82d1854012072a04400340100c0c14aa407500001d1003600c00c813400300082c8014841c80c0d20000d841682c00b68a0b = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 784715980 1250 784714730 784714739
    0x140705040e071a13030804090506060711011b0503030412180609030303020a0509030f0706020105070203180d1a0a02030703110313061104090e0c0f01020c010c2a0627 73
    0xc840c4614422803c0c04402440c8150780d8840000440b40c07180c03040044800c0d03c42e1a0f19148515800c240244200035160000003441410854201d9052a07000361200103185428401140c10140c51318541c900580c29800e06000214108042c40c050391142401100c0c101c5e01d444014842c141c40000c1700d2160340c84c40e5081000c2600300c1c00c1e103000c2e25014a00980d4601840c0000e8480307119800400da014420316121402111002c5241001d4a42580c000e0000c1e84440f0000c80e0380f80a01d2801804001ca00075562065103070003248010380510034008083c05402c444025a443d483c21640e44104540001c01c11422070340c50300c40c8035108003099041c01e00751304111094078181071a00750010074495841c80b581c8546851031090314020294400144035050304401c10b2601d4862051030b2501801000b04100e01640c00407a0b409100d01041c5d580380301c218442e45400c540d85501860a000f0501402da2401003843c06041c404050040c42d1140d482e141c0c4c0e1030508030a0048042041c002040f00c50f0b60600 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 784717230 1250 784715980 784715983
    0x6060112020a140d15050109050f010c15181115090f1315050111010603051f09051221010f060509040b10081801020702030307060225140705040e 64
    0x219003403003801030b00c0360107000060360801c0b00f80c1083e40b441d850125006a04485582060500d02d0414880d030060b907a41d035005403028050760068070741c8200b02c0d103400da96951045103d0700c080c13801041c29001940d1010030802c202c070203482d000280401c0c40c802a03070901030200b6007010450400c1e01d600307c441d08402c08500341c50080c180031a101d203215410b28109599043d0100d030342514030803130030404c1d900107409003080c040b070610599003c680d1611500981c1c03101031007000c003180d030000301070103542e40003451500340e03141000e590b488101e070380d0a0200081103003085082e1044c010102619610190200340c103a0300036140c2243d10071a0043e000611024980303203141c004440890400589460b10280080e02800f600d540682c2c03c1042c000e1012142c0c0d42c403440b180c0c0103424840c0c3c503041e0360b106141c055091b40b040c03600194242d40100040000034846600a001718000810f203d4207200c00c502408044c145000002e48032a00003801a1400c00002e1001030300a07d01160100044183d081c43c0a = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 784718480 1250 784717230 784717247
    0xc09030304210b01060306080c0312070f2301051509150f01142d03040b010b0d0b090f0405010f06060905151204060606021504020f040903140a110f060601 68
    0xc07a8060710441e1100c1d04107501c40060402c89900043c030000940e120348000b0010f011500c5a90401e1066100f110035600700411507042c2031489400d418035210158551410040307441c68101c030074641c00c07200b030700130040f0301e0340e0220300320174014004542030401c040c0c0003203030444040119105541081c00d11007015440201c0c0c508244013524070740c180c0409a001642d0780d40300702140f01c58030480042e0b24581e078035003203d01e034051a51307402c2c0d41d00356000b007101485902c0c00120303401015002088014042020450040c04419030340343e0012800a15020100381d86100c19121140c00030040f41c10700c002c122080c010942d0034224039504000c001d1410100500d181c82c10b00c00e03140200305140600c13803e43c54800031954000b1801007454114240b614091000b82038611603200180a81c1e40b003035540c030140c40c1540340515002003071040c852403000100001041d28200403428001c045c00409074040c0301c400582481e62658031100a0480e0b040e0069080000d8903102162a40044040103916a0000140d = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 784719730 1250 784718480 784718489
    0x6112a06011d04060515030709061701020304080409050a060506071a01080c180618070206040b1f180608011a03070b0a020d0507050c191815060c020f09010b120c09030304 75
    0x1c600307a190050038815411b40b0991450301805041404107181e06182c0140007115400e500a9641c281c910740702600300e01040e40c0080c50031a04000400590101c1e820154000c244031000040640d40c4500044895000b85401caa03060f008400c14400548a03041c02801040e80c44040e0000620540000c4c8082d01004441852003680b0300205a080e01c0f109411080ca0002e201a414142070080010750303100800c80302111544024400140311881c11060010401e41102c444a03101e030804045032a05005080d001107807c2d0f5490f000145414240141540c0640c0700c0c1c20903020240724003e16040c922075800001c07240c00100104810240d00144240754030300c0901d08a80c940102e89012410150300c80c25490f0720183d4041d00c2843c0400305c140d800116000760110303c803083c0c4c0082840c2c0903107000400201c0b102c440710400b0858140154180b0301110304c000d10310081d00d034a010008030000401c0e0000295038201180300d9100801c440400c1d50448075141619050001200c0002c3c1d50340700e82e000d07 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 784720980 1250 784719730 784719743
    0xe030d031802040e1515090705090d0b19061403070924181a09063c040b01090b03010306090201110109050c0916050706112a06011d04 59
    0x7004451803450071a411850396008000744540c2c803480d00c000e035030f0340110b0740d0b03c0c1580c0401d1808a07180d502502c080606204014080c0d030b00c59074480f10241e4498100601d03154204000b1800c080001e018104030342c0c442c01410084d1044451001c8250080b2440c80d041040f2514060740f641d001d135500014400304840c0307001c902152041d90841c190f801a0340480c0700c0003400c1c410705400b1030200a40013007007941840b1a181005000c0ba41084c10f403e1041c240259a08020030f4408a02035041c010800086a040030804940d15024485074004560380d01400e4200341650305041c0e0380340d00e424025240e0b845c4091034051542c60400010107010700c0f042c070008007090f607241c00d11411a40a0500c089400141000800c0380d511681402030701d0301c1101c8942c030711840d010310006000b1000c0030815010402e040e51680d0500b009565618014146405400c501e030700140036000450300601c05503103400400703180000c030f0591301004036850418182c20482c11050004049440e554141c502d95510680080c0f = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 784722230 1250 784720980 784720991
    0x11100f0e041109091315050118180311071a091002062811072a1505130305030a02071e0308180a0308210c03042a051011010c0e030d03 59
    0x3028009a1645403500420800c03420102c0034006e90140e001034100c91b8181c500d10242c6a214482e0401c585021f03020300921880403100700302082c8109030030380c0303030310b22507012a2120313511542c1845c1c4009101600c05051480000c1844c1c290520088414900025000405090500d001d04815181e00307500509860a550700341c0480d10640c68104544525202407140e903100883e04010188160348005d00440e100c0700e10031402444e5401d10040308035a507081ca044122824014103c403c1d40c4002407103011500144008404a07106000410b41b044940e00107155440c41c016511082000e424040041c021030f030042040851103d400b150381038258036103507188080b103000005400b43c11036040502950030100d10103c0f15000180c2a090400b40403080344116560700508500d5407000700d5004024203030344000310f80036004005280101216400001200c5c0340c464002c203c81000002e202c0000a004000c0c0d500b03411020300c0356250b1601d842c0303803e40010072080003080c2d858114496540806580c0c0 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 784723480 1250 784722230 784722241
    0x30f01060507030c0812010302041a031e011b05030906090a08040302040f0e010e0106050f0306150d0206120901020405011e0c12140708040603050106050418020711100f0e04110909 79
    0x2c1c03040359005a0301c10f02441e06c03481d0024524110000034007040380500c0c5000300c000b03a00a1042c0b0302c0d0024950040c0148031096980805039444000826070300807641d21132071111042d12480f800760301d1100082d55542c2d1245840725045241c0540501101d580b03410481030803010502d144110703010340303406440c0400c100d140318111400411101c0100d01165180c0300c920388140e071040d0054421030f0000c13180880e00403801c2080544484080ea00c203898000c84900b035401d542040513085e0b400c5030004081c3c1f420480c13094003e1142440459100e601a540090306002e6580c200c1c100c015a440303283d1000c0103010094101401d42c41302c01d040039086006a44294007018440c1e04007010810704102d81ca0344500b40c0d45008011a0000e02422021034141400800c0151141081c0d400321542032000a82e40181022800c0096001b24026610a064529040d07a20341f143c1e07809a05d030b003070103680304021024014402009400c49a08840c411810241110100300058080c0c1d0168842181c5402c92511032 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 784724730 1250 784723480 784723487
    0x305161a04031e02010b01081602010e070605121302010c06090501060503101407020a0c0312230c0f120403140f0a120306120206070b06150c030a02010e0102030f0106050703 76
    0x240c900446010395510104000c1580c007405403103440c01115641c0c3c8000707101d900281e003683d662440d6140007174401c800192149c10901c0c180c501116850000145c0840740540c014200340544e00860003282e000206128100c602c07070701d516441140d01456000d034140950008000d000d4203c406443c041d1100300a01c18000f080d403000c001000000d04641c0743d000214091800f4203480341d049281030f250710000814290012601100003030b4091000106036095540700340d0102261401d100400c014240004c2900d00c1101c1c1c048034610407006015150000320f4686450032904603d030703800715005040144541e24030001600c1c2501c0d4003000340312880710408216443c0c4070380401002a1407048524120a00031404624440b552160780c05000f80783d00c4801c0c02e9a104031110009410003020400500811252090249c00100040c00083e10050ac9504004070341c020304a6031081e50000201c0e82d0f2440d0b0244158085103020000039415864041e0080e10b204a05204400601c0000100807040611 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 784725980 1250 784724730 784724753
    0x140d0f03360302011508070b03370b030106050a140402121003210228020a230913030509030f01050a0b18090c0f04061a03071803030516 60
    0x10708070388400311018035605500400090790940244d441d15200d250041c010840400503249554010181945428209000f40e807004003403699030910019103c1d07100c114044000d4182100c008520741031031001c103004d401c0b46c0201e140b03240b09a02d044020402c58450220140803a400794422008184111022038081d2140c568100008040300f030400083c50424003861040e0b900035021744030718181c0300186090740501070f182103000d45d2000042d14550b4080d0040501045280340f90403d00d00d00070381c0440c24115054001c2c81c003040001c100c0406002c0e040c0c030031100d07092048626902c0c0e800d1902d800b8030851441e11002d0204040040c0d55501c9440070081c940004240c00020000b07450040c08460040c51001b082e01d215910281e000e140c00548102018011050407014101000c2c4d54001c01c44010002c6241035001a1036010000e401e400369107407100150141c0f400503035a481c2c280c00c01003000d141d841d0080c000000c0e1410a00202ea480800d807005460301c004c030340c9030320074860801041100 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 784727230 1250 784725980 784726031
    0xc060105130f051806070512040b06010c0503210601050a0509061e1305041d030d0c180e0109180f080f1306030f1401050f010507060906060f03140d0f03 67
    0x60400f414409040f030003040d140d02c6241d00f0b1081e101c0391388411a040390746100d0f4915034080c0507140e0380460041141d1801003600a80141050841c11600c1d680781b5003181c012000c0c0d00a03c4030820450101241c5940486901c090246400b0b868076440610280c401c1c0038045e0010701900010500d072400c00651070361035000c02e51190f40c03940c498401800b100c0184109018003401a410300e290000c0841071240f00c2c5032256512000386080c0038405003000000c00e80c2204043c104034030305c0030b0858401d54407601e080290040d2a989203080d8107120340c02041d00c0103000e9080759140d03078005503404100b01b0581842c41560041503281c3d40d01242e02d1010043c00b66041400105114120004100d60981d0100c00b60458120080c08a400000803018003400c0901c00c00b07400020340304445d42198842e4004081091040360000343c0c15802d510749200f2610740741c1101085008440090050000600e0122481c008d058024880c01c40621401491b1401003810002410340300c02001100c140040130018030030 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 784728480 1250 784727230 784727261
    0x605121f0e151216090c08010308070c0b0a0908070f150f020a17040e060f06091302160506040201110303190c05070b10090e070f0314032701080a020c06010513 70
    0x1510003c80140e11240114a130341000d845151000034151903c0c010910394074a030385c440500d540e20356100c0b614907a01c40e650880300c80f800000041076000c2d0b0003001d8296103c0660b960140641000d10f0f00d032801040f07420080090044100c100400e015124134005110014644034110542030401680381440000340102020a00c00c407501041e841c02c8080c1080700c5aa1100c6034944d100c240911140000070f4202c07641040041140314181d04107140039038400030306d0b060300514050f14980a1a542065920b04491300e4011000340020b56901c01e948203491002070f00035610f5030070200b40069001e40448141c5507190781300c031a05501130703002c0d8050b601a560085070103200743c5800800a007820105000c0d074020185028249584050001015401c0e140d82da83c2a0700a607055031110f006601090b00d01410310300c410055001159540101500b5640142400124050b0340c1c03030000d804104000c0ca03800700148103110b0705031b491500040f03050464109890100c00e40c1902c0c0c0e061005040c00c940d091a04 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 784729730 1250 784728480 784728499
    0x9040f02040b160c1a211003020405060d0606090e011b1209170a020f010c020c03060a0213120501092d0b2a0c0c090702030a120906060605121f0e15 65
    0xd84034580c002c02400119041c54191b186a091204201d842e05640220081c3d50502040c0b0060825070b20507600048010000e0303c1501041c0d075054161045a0081c0c000d544d1540500740848100340140f00b502d03202c041c0003a0722540d206d00014190081c2c4400324002c035855400500600c81b24240102140c03040306540d581d07800890307001a65844500f1000303100b641c608428020518408a180c0c816498001d01820302074a91290036806500000c0441001d8001d00d4800035000500102c1c03c0780742c038841c90011030095050f00700070702080b40c14400040d401241200380c1d540034506412148040382d02c07481240381921004064030100b107007041300c81110707101c1d41d1031300103001c40c0c00001d0a0780046490485241c0c0c90701c0d2003441411442035401e46e026034818000c60203e0340c01103440040115540f100000c00c0503281c2c4585c010740f0805da202c50081900002c011b00400c400b074045aa110b050b10007940700f646001031402c9010201480384174800c066000110700341c440400c02203a0303030307440c0141070b07015 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 784730980 1250 784729730 784729769
    0x1203060504020f0306010e0604180b06040b130609060509060d0c020f06100f090908031308070c091d06160e030c0406170708071a0c0102070c0b09040f02040b160c 71
    0x3c46034805c1d0390f000d000c106c03881c261905a1074440c040b80c0554088110300b03010700d409a1104805480901c1c49240e00070f80910020590000090181c4102c0d90013411200d10180303000c10103403c1d801d158100c4020840e0030010124192904c0d0122422208280e90000f81c07415058001c03030900108200c804500e0060303c0a121600d002020b42a05682809000c040110344d91485d03035007150f0a188d8014030200c0240700140603035010880c040e04481c0a1070b80700e441c001003581d841c80303401c00a41080f072100c0e5440e83e009200910a03080c003a000800180201580d051404480c041e4485600c0740200304041c00009480d030362010700404142e45d40140051180039102d4184804510061414030b04a101e09900054100400500f41088455280c1c0740a144294511000060352204500c44075541d020018040045d111148000c001c01c446032139191100084c0007040705880b0b003c442c00281900600c07040c04080c101504440d000031140c00d21101d88402031034a404601c44070380c4115914040106000b1 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 784732230 1250 784730980 784731007
    0x60d0c0b09040f0b0a060c140f060f130b0c0a2307110607170f040b1918030503091201090f06020706050a11030630011401080304060c120306050402 65
    0x1e501c601100d0500100100d001940101c0d0b01040c0f50703d51141c0e0703500c2d081104c2805142c64480c00c6004204020344e9800141929183c40e40b90002c40303042d98081410080f0b070748118142143c105051000c511100b01d030700e8036010040d00f8007801d4042c44510010b040745420f8000d20120b88000000300740ea074410a00000180d1940c1c010342780982c1d481103010883c0e0410304d402000c4504542d0f0000c071001009039241c4428035160401f1259607241da01c2008089889540702010b442502c0401c40018021908420020241524092001e0040d041081c05100240c0048169064540d090f611000c41c41a028801805815040c8001c0c241c040c2c6408904c0074044160000d20000703025a40034003070b035200c3c4040101180e0310412219103264050000c40d045241c011015000c10040c000180c0d0042c000c4822840407021406002540740c2d1740b1000e080c2c80e800107041c45801440c018000d9800d03d4684000034010880c43e81c4000c0c9540051041c98880034001d5100700003919001d00215183d6081c9880c24 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 784733480 1250 784732230 784732237
    0x2a080703060b0f10080705091807020f03031e10050d0f030e100c0b15090c2208280c03080304020909010c021e01090f0303060f0609050d0209060d0c0b 66
    0x2500c03900d0400c0080100b90030700c48a8203848820161401940300d420300c0b0101e030355030740181a000402c0410440e90400b030b5560094802c428100361040c00c0305051450b000380c070b8040204040720a03500144108100108400301c0c00c1003110442e00003c2d0f0b1955100031280815a59400070743e031020b02d904440d0107004c0340494681c1041d200780c03900d49408110904000e010030b0042c40f28000a0030400c40c540005400284440d04242000051480361070030030000f40e2010f80440b0017013106880408c842c80c0c140311130502919101035445420302c2c2d080c1031001558480001c299440881e50440a5000e00100f0308a44001903607001803505408588030315000e241907100365426840307100c1d64808940042418851902c01c0903e5400400c03143c2e11144000c46c4484081e154207225542c0c0315200b2020074400440d06060344e121381d800240d00c40c05c00b41181c0c00404903800010401c0b50501040c41503488860400c20300680407184800c1940d80c0b40000703000b100940d100102000c5e200d0400083c416a440046d = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 784734730 1250 784733480 784733483
    0x501091d030906070f030309050d02010f0b060301033810140f030627070e0709060804120c110d030c0309121703090102040806040308040c060503070c2a080703 70
    0xd45905840060045559000b0b824000c1d90002c810045003000598a80d0340e58940c81c86401c002c1641e5206071112402e0219003031740b020140c0d440e2000740903400d18a10400f003a0340c5007221414259415600c61907007011035141040000c2d444403a101c15024851071070480d5681442ca03205800e450603000c00003d00780c85100c1c10441c0005080c07a140613240c481c08080525401030000c04c0651344014408441041420401c0c4612258913840d400810301801482d02503d40c5603060040c1d030400100c010040140c03603000100300300800c4140000500304124800c2561020b151003981d85001e0f0030030b110082000a40250f0110b03601c801d080c200341e0003a901041c118026160054040c0e540c801040c60b48240700401000c10343c42904014844c010307040696080f40c407403030005051a4440c00024600700b000c3e50260b0204403000100020448001f50f0306000c0c014924207103045040c4100060720b45001c00c07200402010894040d494109c01c042c0c490851070f02c06016088000e41d0700c07451035841c0c4119000 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 784735980 1250 784734730 784734761
    0x6150a090507050921033403050711041b171b09061602040203010b28080601080403020c0901060c050f03070809010503040602090402031005100c1211030d050109 71
    0x800185060240700340c40c071800043d00c55070b00d07180c20502000f50801980324110340321034400000e8100d498082001c0c0611441880c0c0d500a8502c5441c1c1542c0300d0600070f41240361a04262460341e0011790b00c00184c2d8500c0d0f42c00a42c2010140411b000980944a11202512010a85a800a415540154011560750f0403501f2074049480f81c00500d480700c0070003803401b60842d90800400100e030501000400c00740780501040001481d03141c0c00a01640d10a0340881c2002401103006070346030020062842014100740c0103006c08088215000e45a80740003420f03541030109100c00542410300a20123140c448c00c2c006e2602c80c8543c2c45400c050158400e200e41641d0a10881030000600280042242c0c1d0443d000358007642407020b4000111200c0c4c1c0000d10890341c064003031041110b280c80c0c0d070010f18000d00620311004609401c04052185a2154081d050b00304118a45004040b801c041c07a020707000d2516252401c03d02c407148a14503e513204800891700350b50b01c1c0400002d2000c240e503101001084454a = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 784737230 1250 784735980 784735999
    0x12040309030b2a0f0712090618050d06020912010f0509010b09091507091a120a0c0c1104060314030310050612070318080d090308130c0e180615 63
    0x20610b05100440c0d00c0303465030405192080300b85280c0d0f03503800b514949040343d420303500c2c1070000c1ea80d407240c14100d0034010000c5000c00c0303000c3c41408d41007203c144c00218004141d00c1c010740b40c00d00103a051b000100e009010660300045031a0b02d505c03400034410f2180050030081c88a41d00700705051004001c00c5801940315480e010940e561880c0102a6900034200700c0700a00219a28100d00300005501600046c01d1049a40000a03203a520501844a040c1c13141603248e142d03e070201c9d020000102c0107000410641c40c00f8200200a50400d64403030701160005000040c0d107040101180c0140500d4001410520001014018001d4000000d620443d12001c101c1c200c40c1c0c1d46d905014642c0144402c505005124000041d5202d10a40c00780400d180d070990541c0c03c40c0700f07503100c1c0b84055009546c10540c19480e04192418150080741036600325a45140c40d190103606a02c80303600d4140710340640c240003404c03980800d81c0071071200c030440b00c1c408a200036210706040c800c1034850040303c00d88925000d0040030 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 784738480 1250 784737230 784737241
    0x16060801050a1a0a09030210020a03030c0905031b040b0612090f0a0203100213050a031a0f0108030a1115010e040b06030a0804050136140d021c0812040309030b 70
    0x342c03480d03000c40f41c41003030350103449841034681512a04040708410070003042c408000096030300e501641d01c1c2044950090107542c2408d042c02030940302640c0001d002d01910000800c5a6200025106061a10325002000c405849000100038208034056598003120215040800c510880031490140f5007417812116403c41c0d103981c0d1794481e051340c2806076064100f02031107581011a0f8004004161081c03010305022510750b80041c00d03d5196070001c0d03502860540111502c01d0034040a50303000781411101b04825072620300b003d5540d00c2189628130410009004500c42510708106440c4241980c044010141d80c540b83c0d0000c017401c00301c03000c1c1c0c0ca22020001140c103e0801150040750550080c190902d0706042000540310105074540803c18204010058603011008506c00800078084010f5a400c46140985080c0a50a5409800e02c581401088100143e13140c18449030515000008449040302c0780c00d00080e14014075081601c45840c1000b00820150711054600a89129012540268454 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 784739730 1250 784738480 784738489
    0x803190917090315180f15061507020604062c09010510090f080312010b120c0a0e090c030604060807050d11011803030c15020306103615050a02100504080c1606080105 73
    0x402c26a20010480c2800b20b0345078140603484271090300e50041900d203890800d60118030141d0103544008002854014071422410041001200d4807000741e00c542001d240d81c4c000500c0b100018840ca910400b9108089100107003d04a500002d0454410315900b169648030702a440f540080c01c0081241d0b81c040000c10203842540035107444101e102c41000039640d07410f100741c42c0740d40320b807400d041408030107440c80e0150b40ea84000c0620821140c50f00d16200e04100052006651050b08400c8854020400030300442e103504459041143d0072951f048078000c00381c0010313158020001001103107150644c0e8007005060308042e00c1d944444c858902903010455a0344000100e000540700c4d1a8803c000591007211144200c10b0100307409034040904150807603800607081981d8803104001085c0d026004204082c01c200c140c442c01c5400981070482ca4178141c03140003501c400301c0109040c1c02640d20710201d4280552101a242c0b5065618201c482e2200c0300c0581000000036481880c0024211000201d481e041 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 784740980 1250 784739730 784739743
    0x414150316080d030207142a01170f040609050a080a120207030516110d11040e030304030f080c0712050c0d020d0504120f0206070803190917090315180f 67
    0x2c92400341400c00c01c0100224081d40c0401000d940b0210190342c07241140b00709001810240d501402e54500c517404c580c0c0c601c580c60212145690511403000840c82c12458032000d03140e03201e6400b10b804802d59480740313070400003481d010300003330543d11624101104000b0580020041f004042d00c030024008800b00d00c0700142d2080300301c000d00141c030a00061400c1c0c000c0f503064a00341032080c94000601c40a0300042620307400c0420056404014400907600c0a0400d07110340c12503210f4140c09035240d8a020344010785021258412101040401c40c00203007030f400040156086580c0c0a0701646011507154002003ca030000141090940180c42c140e00c1128000038140c960302005485a608041c6807000c01c03041103510012c01c0d1400340070854001c00607691040144452032250808941300c1c20040083d4800c000e02000d034081d202c0c0341000c20008100882c1c0c1045074440d50251150703640e401c0c2d0021a0030040000b0502c1c280f05a28410b000401c80e480c1e80d0000300914900403690640c1015041d180e9404 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 784742230 1250 784740980 784740989
    0x1008060105060a0810080111090a09060e06060c3a0c0b011e0312020a0c0902071104020315030a060c1710061103120108070e01050d1101030b0414150316 67
    0xd07420007041d24032a004600c0a85e00c15406605039085941d0b07140b0603030a4504030f900742440010b0004840d1a28545851440c000c0c0540c10400c01c500d2b8100110000030440103410a0310400c070101d9030412542c0c0c2000341020b00b401952100611442580da185a0340468540c01c5a8130b02c04d41c90307101c001d02c0c03003010340a620a42040c01c503c0700f41d00c0d010701030109071214402501e00c24000c80012000c503540d0041d140048a09070300a115854882c1040c0a0700c1101d500861100350041203201c0101f1080f0310b0780d03101d40c4021600140e41e61644046121450381c0500c2050b014080d6040d460140003043c0e01c404521031454485030752400e9051509406031790100d40d040e0a00040790001d001261103000c02c035066030100b404580c5071180034803040303c100070240d00c42c010950149005100c0c2011804d6610f0060a060398440240400c2c1e60720244900008401281019601d02c11088669555003002e200200302c4040a04a41030481054540c240c411101c9400380c481d060b4099442402c1107480021038 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 784743480 1250 784742230 784742239
    0xc010c02040e01090b090a050c0a080c0103050601030b1c0c060e0a1514040b130909050a03180f03050a0b06120a0b040f0b0916050906010207060309080c12031008060105 74
    0x154440e401c01000701209108004150f694810200c002400c03481c07028081c1c502980103003d0410301d442c05500e41034071014071310b009a0580b43c0801100d0400a080314441310242004100d694a14004034000c2c52610364007a44803e4600745d40462031420910602c009004070049100715458003800d4501d40050b42e01980c00c00c00d006401c110303696228001140070402071600961090a200b1907600700c0c0c2154003d102150000124035150344201c2070040010014500280310700b030159210340d500e07551400b4014040c4036000c8400b03042810503088000140c64543d014081c01341d00e900b03090b5642c0381d8803007044401400b0301c00490514501082c140c110b26a00c0b100410940074240d0f12142030010180c0102c0344000401444000500d940313603121f1240d80307103d0003048035249003500000400c02e1a88818017600d4140140300a80e43d01161792415500b4a08000c10340d880c9501d4400303058451070101c400c43d030081d0a42c03132a00c0300c0c28000560042408004d107144540e102d402142e144c41080c40b030326034030 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 784744730 1250 784743480 784743497
    0xa085a06010b16060f0906050403080f0106020c0a090f0b120f01050f0402100f020109050706110606041b0311090303040b2d04120203030c0a030905040e03030f1f090c08060406080c01 80
    0xb03413a5412450b4040700401c0b010510300e4141d9205030664405490440c0442e180707004000d061000c102c083d41c01012148000c10541c504100841c0d41ca02240c010586019203039000165245550380143e1001c5130042c1c0107001400400c0c2d800b40c3c9517041c00035138081650914000c00c001038000ba00d103a000d0f176001440301502c603015030b00981f00c0140125a4909654039036642c1070201350144002c1d00104101e0322030021050003101c8050614100406403485140340c0240080c201a4080d4412107000b03407800c00090302c900035001d120460050703420b440e905200002c0e0214650030804003030180d41f10030721203081c004203145102c141d1005804511144901050004000005840f280c4400550000c3c0c152460444010800b5003810104a01036011038803a00c820056424140324903101c417080100558114107049003d0004910050844003000504d5000f05600c02d40c50000c18004140b0601d0422020180340005854103000302c1c0d003503100d9850510001078030140845c8150540105035141c041 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 784745980 1250 784744730 784744733
    0x702010e0120071703010312080702060403080403180e0c0415021b04020a0c0b0a06061209020a050d0305120a0c0201060515031b090a060309020a085a06010b16 70
    0x40fa002100e0903192a0040c41440107440c40d44001503000c4d40c0620294010f4802004029200000c09081c400865020000b0400401e41c4091030503007050f4180307407482c05c04054140007040c2e0074a41e0001524a030011307050108201ea0304000300f046410074007542109600e0301c80e059072505070f0002c3c844008030030320b0b15850852503ea03006240811003030805007100030b07440d16090070000d41250003103031035a80c0b0034040c41000c1c0c1199041038102c00d1814144083c900c240e02140400c0780340c1c8a400c3c041d001e070030f11000c1054044c100781c801c51113031418299001e15184030390002529407c14031001551030098003007142e080401818003103007881e1103898070b551603591544071103d1107030707440480000302030103440740599402d6030040040c2110b0b40c000c07500300b05500401182c3e9032140e00558142d840120040e80381510210750181c00420308034084036403250801314071910620380c06d51f2604012499420f51107402c00c44004050226148104d0f83d0036030b00c0e481030851070700c659040da042c038030000100c120 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 784747230 1250 784745980 784746041
    0x70e0a050c0441060d0f0905010e0a0b060a030b06091816030b0a05010821090901030c17160b0c010e060114090702030f030c0d0b0310050702010e01 65
    0x1d4010100100c458a01039450141c1c0b10120003a01c0d55403808009064029141d080c50079590031800121680b94842c600d0060009043e48202c0403020504d80e1541d49104841a450b442110010341004c002d01c41e0031440402c940e1641e00e98041191100500c5004c6111802e0807482c420171b89510007059005911410104428407000404404840340c0c04111944139040c11300108c03180200f132044d1007049901318a06507140540081c04001d440b0b1400e001004458000201041c06100145092140c540704100c001e80a104408074a41c0003d820720002007000001c3c05100c04403800300480e28401d40012500580303032480b0038032456034845c4200041c405812164003d003c03900703425000185400c22501020708013442644070121000b0400040d01240c180091040e5020055101842c075004440619100d02e01020740303c82e800c60f00103d4000003212a41c2e01821010100404440050030100c0100002e0082100c0e143c0041d400e0900482051405014456803181101303030f80141c03c043c02c103020 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 784748480 1250 784747230 784747241
    0x10c020a1e021201050601020d17011a07060203040c0302040c03020306010906081906260d02070b0d290f030a0201170a060f03050708061e0f0601230d0e070e0a 70
    0x49030344200607001500143d880c0c000c540424588040041803038078151001a007410365070000c00c000d00050904021910300925405c6054078903038207070321505440c00f41001c4024020960000d021a10000074003041c00940d4508800b10380c070840f4244207000740550100e051380010390791103002c2003035910140300c0d80c2d0081131910f80c00303010380391048600070000ca010310517903c41d54040c07400c071692051000c1c2004411081d01200401600023043c51140013070340290341346083d00c0381205490011034101544e81031a0481d1038950401d12801c0245946041d106614020102d08140309020005c00b51005080220322074505607016122440102c0000c010400c03012001403141040c00e55032800454508042402503015500500c001c0070200d080000751445d00b04040c0845c0841070b100c016110b510702c5002c111a40c000c40416100032107407501c0006854207040e422840b04a00c1c2d4004c080d00d041e2190740080c1c0110107070200c003440f458400444554440a5502425850f242a5400110b0605940d00304 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 784749730 1250 784748480 784748513
    0xc0c05060408030921010c0e18091e01020f0c101a0d0303050a09060e070f0e22060e01060902071a0114011d13050412031b0c06060e0c0a11010c020a 65
    0xc07422417051070a43c5400c6510701802c46020540c0280b81c40d03003a04021800460b000d504903041d904074240f0040813552100000c04403400c100b5500c1003181015420740503140508000e21013141c86014040c64181c4032011200c900d40c04c0c0d0b151071070301205034001c2c260342c000000c4068105030000b069524205c1c0900b000a1250f100300b51510300d00030000f18144640c5108034408000341400313509040c41c495200300103074000008a801d040c1444011204030103424240200014280e0683c0701074680f010203010502440511546041d1000070f0110150700288041481191070380ca05081c07001c04030343c2060085c00340ca00c0c400e9038a02c0c116595402040300740c40b11030b050705000c00340344680000521a40c0c50110030005203074645061008009850b01c94040d401032904040c00800c20400000c41c00c0321842d0003400c01c0184030101202404030360b0740040094200d50000f61507625002c903100140f581b03c20f50f04000284803e101102c04541031180c00c401c2210780d4058088038600c8d48860800003410002c = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 784750980 1250 784749730 784749769
    0x90b010f0c20011704031e080702060613090c090c0923010813061b080a0506180703060807080703260702042a020607030e0a0203031b010902060a0c0c050604080309 72
    0xe41403840d802c60b031598415482556050b01821910100004901450a5070b805000408c0141f091503070300031840c01e40c8541d01343d500710a06c0300740984203005000c0036040980301034441400454600c01680150140f151147c40d0040301c0c5581e024149800c41c4000040180703600860741c8200c9541c07184500d40d0308a918403000c02c036040c0c0f4903100c150490350f07908484110700b0301c80c10030140882d80007200c41c0e0703000c0f0400200300a107140c4800460f00100403220641e0080c240580010503050091780050058144c1200b1034845e20780b940c0c0c02a507244500d00041c0e5500c4a08600c0604001c030100b46ca0008082c075800850410016034240300150642e070011600000484120b91000310b448070601d004d682d4258021f010342d041841001c0c0446400d01c41d0205950851800c15025031000003c880700d0044100c001c2c03070001e10049055004110700c0000030b500480000b659180b041c0c1c04001c181d800e501031a20703c001942c0c0d076002c1120500c40c03445080f1131030304248030a0220f80380600f40b01625440720358 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 784752230 1250 784750980 784750997
    0x90c090b0d020a120501080d0c02061603230307140901050d021809010b0c0a03052805031f030c0e040f06020f0d05010803093106090b010f0c2001 64
    0x340c00500307500302901c0c040c01c440e8041480840303103901c900300030038150102004001d02e5042440242d110320440001d501031010070900c20045403108403c4408208032103060085a05151030002d0a5100041d51200094025091178110810090441c0d0003507070b0f2516600c0c0e454060a07102c60072a00118200d030f05000003401208000c00b07050000b008505c0d00c0528040354428141e08104400d40180c100752011181400040706840000815521071601414141e0715418950060010708903444040803150008046045046812102950190308242c1c0820000101102c0003c1035a0461202805400b885541003280701c0c6440145a003150281c02d42c80703040d01964880109991001810059003240010080403800f0984640c40c09001d500e4091480e03e2090400109801104d81044114100e1109124549140500d821007580402c120031300078155550340c110010704400017400c0c0404c88a1086003080c500c1140c500d00d5260b400811030070000c40a00c0814030440320511054113001810 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 784753480 1250 784752230 784752239
    0x10f030f060e090114240a09020f0a090e0c0306040911030d0e0f03010b0f120a14060a050601050a020a0312020c0304080714060304050303011809140601050a05010513090c09 76
    0x203000307240182c803401c02401501d04250880d00e0846052080c00b50a000080b001c0c410300c0034141480c0000b01da200c4804441441030000041c1403441113601c591070091000404034004017800020b8000e00c5000e4582d09642680e403128600002c1003203a15103110308007000010517130300e09580140d00c140d0080400e0700a0b07250400109103040c40c640e840c04041384600d42006003d2800000d5050168001d900a201d410112008104a030064481483c442d100e41d0032074440c614010031024012640104030425541051584140c42d00e20644524030a2820200001d059501920071546121000d80c020019008181c4084aa1603020380240784900e400f0462441c1c0548c0c00c10140024003620f80141010b1480c1020107580034180c150694020041401000007090010040d00c0c1190032000d503a000f2003048400040c01440d0300f103002040162448180c426850000924a05986085c1c880c038442e01d0300e5000644540c000c2450051000c0035591050154050941101d4ac80310b149040c114540c607207030b = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 784754730 1250 784753480 784753511
    0x30b06010c0f051e01050703020a081b0c10140609071b05211306020109080a05090402040e010b21240f2d0a03030915090306020309071a030114010f03 66
    0x80929401c1300e032400c940c031202c00c0284180340c0c20a01600381186003052140700504001070042c03041500c80344a01c2c1d41000d081c030301812a4440c010240581c1c0e616607840700781c0b400800041d0581c0151201c034130700140c5181801c098190042c10107440d01055040c040402e07907904000090304560901801e041c0350000da21027030036201c601c040384001644071202e11080714a101840e91003003045a040140f504081113800d02114035180041c42c10668444e03240d000304010b481194050000d00014100004a041c1c140c0c0c00751081812451b000e800c54039980090040046080d40c07005c4010701c2c411003100000141041032081c00c64003905401c60140e5a00010700250903003000303e009003507100701016003042803021203207032030b101150008046419a2402845613005001e00050700001040d012203040c01044810b00440d48120255036038540315000e162107145030710549113000c051803402070310805020103903810307680d8031008113511441100c011103006200282c00401d055803900342e404c00602 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 784755980 1250 784754730 784754743
    0x130c080f030c0c150306120102090915010f0e0109090b0103060314060612030c0d030c0c06091b0b07080d270620071106180a03060603020901050901030b06010c0f05 72
    0xd000a15142c80440c151242030030401c40001e4031410104043c0001c80c081903090300c2d084101610644002c1d0040000740c0d0092023450309040d0300101038800c0007803c4182c0080135070040c000380c0e28107441d45020030083e23a00350050707038170b160110303104003c01e11841300d09500209050005240208001d556a22035412001d9694120420341d08482c00b0003030942072a61021202c25179100c0154a4100b00d0401e0b80e880d0041e0f90342207030815407200c2d0440b65061180480352407490304000d0400003441c0c14a0030425068620350071110401401c400000e8004596040d9000e082d000a4aa86420b44002c0e0680091208904803400401440c5d10134a4100d003681240601c07500c1080000350000e0003200000321083e0b040640c000c1040300b0405813002034000425444105020b03100e26481e000011240c213607224002110301d030001800000002400200d420402c212802a140030100741d880d0700c2407001e00e04003400050152040d6801060403075125000041b0002c0c01016510307104000c0c6d070b68007820b091 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 784757230 1250 784755980 784756003
    0x2060a05090d06141617041a0f2a0706090606030b0a050106030b09220816080301090b1017070c0f0501021b0c03190503120705190503060108130c08 65
    0xf981c40e0079130290942100302d1150132601601201c107044402e8a801400ca0b642400548521100c1d2000308042001c40340d018162003950001d526542d140c4102d240f20300e1101210030290b110740c10b076140f40c0c403103606100045410348070200381c61610116403120310250106d02000c4514039512000003000c00c0304622501d00411580c1004150b5515041009040c0c461002c103543c4603101c0b80c0e0070320050241c04400342e103000b51601e010588001355410b021450f80209402c2001100d41c4089090400403c0001141070b039000d900f0421410b812103060010500007a01d642d80800c0038504140c0e12500b0314405a039015020b40341421120280390f031440807185002108440507900032840e1032003000441c840202c3c00354214014806082d4a10000340c3d19008001c1914003281156803001c2404003d00c1150300350480345c1c3c28002e131420b20900050035503000f4581c0c0c50741c0314080103581441e1841401141c5c0140c2c4143d542072240d448040c282820007112100c00c6a884e00e40060000c1c404400340b018852a1 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 784758480 1250 784757230 784757243
    0x170c09030307081c020a08040204050403030905030c010c23040605131508040302060a27050111030403090305061008070b0c0a1502250503250c030b2508010302060a05090d 75
    0x1344254600719029001200c09400210300504ca1030076072542c40004184d100d90100d401242546031400c2c01e80c014804142d015259020000c0e8244644005400101540304203955444030440701300004d2241e54980c0414200340c0004100c1009124400c00251801030fa54030141d0700701da40d0340ca01c501c01100c5c08000090110380700d81c04000600d81c060050550103165814240100c000a46010341d000380c02e000e409078050b042c0600c803030030701500354031054001e0411152180d403820304c0c0c100901810b00520007142c02c3e10074000026086640400144100da41803002480a203040c4484a610b98106a100300003600c00e60b80ca0a0115035002c085051141d1004e10040c1e035011041c000010500310350407058180341403d948600060000000c0307a81c00103611903040042c540c2d40041a0280740b0030b00c0301400040380704002100348000d00420703500440c403c2c004001d403210010414459001c5075030240c0c012400c0b204c0104050b0610307900400b160a0307603140851801141e40e0029180c50700000c2c056a54 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 784759730 1250 784758480 784758487
    0xa0801060f050306130f0b1302090909030c0303041101050c1f0507050901021506221a010e281e0f06021c03021e030a020703081006170c0903030708 65
    0x540001c501e80050450386085495842c11070080707003402e000c0700070401402c2e40e1400c080c181032030070ba8416458000d00400c0c6688038141c00b00715001a4101700620b40c402c00450000c038007040e00000881c0e5903822200040c6086075031316106c400c280c003000010603051007002c1000d220859401c1c00039000725103449241d01c1401301c03000150812503000420700d1040c048100003003502684c00248200041c003240b81c59680503541c0401240016045150b06204c000202c0813901c03550180da040002101c0010302d04c1d03d18140010700440303500b031480c80290b800084c4405040ba201c2e5000c07030b80000d61454048141c1200c0d507503140000c1000115481d8021760b80f1698018800b007903c995400c4000d00c0d00f48001d00603000c8a280d42c0ba480c208244410040c581c0c00282d0140416905900341880030700301c20516201d207041a40320019510001048000030346c1178000a1500c1da001c0c420400341c90055454840708110030703510040c80d00d00540320130010706091104c0c60365658200028443d851003007000a85 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 784760980 1250 784759730 784759739
    0xb09070b03130c050f030a060e1c09230f01080618070c1109010303050f0a09030501090b01171c0f0207050415080d0f0c0321060f050a050405010e04060209150a0801 72
    0xc4007113400451098052a11040c502ea4001408241d204c1d0070910000f64040c08403410307031400c00020040e02c0640c040362030a40041d60410a804100c880003c2c84a10841290345184000c20064050b250300000c13030582903486510030300540e0741c0300d00007030812042c1010f4007403040340090086071081d0010b9000950001082a4440d14042d1402c1c25111070104c0e50459030080e00314040c4000c80c180c140004505104110320035401c4000441d00040200b000304414101070610f82000d0040413960044c481c8030702e5803407000140c0100351031130340002c140304840d4545044030244200d20300101188964080442d4940e2244904948050071007410001d0300d16100c03400b0b05094000380020305000b96440c46004042e004005e1700841c5625140a00091f965000248000c896100c81450218030707050340841d403002041e00420940d44215001d04403183d0340e81c20481915800d010b02d0940d014841d002c90b000560f503802510040b0380003410140004009203040034190001583c002c00621070200421 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 784762230 1250 784760980 784760993
    0x515040c051e0d060b03100204060906030e0c1f140d09030e0913110622031502070f060b0604050628030b030a02101101020a0513120b01030b09070b0313 67
    0x82d0306480001c001d00520690400200a040400806001c55440e19170801c41c595040c41000b51030b0003807200440d201e03074882000802a84682c000c0f0cd010900c0d0000d4070782e900400090701580480000c0c22403803640c60104100301c292105440c48000c0c080820a2000b03842c0086000d841b0841c002c540008042c0780505008002c0c00b0403030003d50281a0070410f0140c08043d03d04459800342d0495060342d800c1410f0404030b03090340324152050841101b501010200c2003c0f001300001203900034a054071110040040003402ca214840380208040100d01540001403141d030800c900501d030082000d81030070341c0d130008100035501290891181c54a05884140c080340c10710b0500b03c000c41d240c503081101a82040c00b0a94803412201c010780b107482421020141244143c0304070b8101c1010790000d644a0030300a9000c4c2c01da4018140082c02d8000040d4041a498058040f41d0500742c2c00000800142c0d00c0c2d502c2c2da8100380b0700688840030700d018078a00401d050742d141004501a03030208181c04100d4071f1506214 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 784763480 1250 784762230 784762249
    0x5180610030902151c050a05090c04060609170a0b040b180105150f040615020d120c0c080c03090a17010b040b030c040f09020d0813080a0206070b040515040c05 70
    0x2400745072511001c81c025845440d9010041107204420307640c0c3c1d11280e048450b984a804680b02c440b10b08004c104080a01c07243c0000740030301b001c8030481d100c3c0c2e01b50704204410b80342140038200c009502c0200401c00000a1034880002840a40540c1d4000c501c0d5150185d13000c2c003c84059604810308401d0000089542d000400ba50124100030002405c1900450b01c01106d859403091184c8080501200c040d038880d4043da00501803c2000c440030b006030034011b500c42182c008410041503081c04008000444c41c081c20034084429036644e034080402d59241c042039007021120420f94030042c0040d1445458555415016001c40c4144036020400881e005095031003010629001e80d041055410703150b10002039000035007004a0b00440c0b140b00010b1404010010030300080d5001051141080038020034074020115070010801000c6003035290b01c2c2c1d142d0765461a42000713410080400c582404500d1010344260058811001c0e6200b03440d40081152101030182e40c26200304450319010002449c01c0c0380309 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 784764730 1250 784763480 784763509
    0x12030c0216060503010303080c0c07080609010f0510052101020c011b0c0f080c011104090903090509100b070305040e071d030109080301120c08030f0705010605011e030f0204051806 79
    0x103212241c1856401450f900042c40020188880c01c80401c020515070000c0d02c0f02c0d83c41000887d01c506507134900c00781e990001034507645915440d1120f011000700d118025144280d02e0852130480d014a400d05210075000648002d1040b600743c031411811010080c00100422004170b0000708000c119040c3c0b0194102103040ba55007801f901c0f004180c0051104011020041d0300f0000c01511041c904415a02611040c641c0807810301c400107001c00e6100003030b444445818001d60b207021446d1741f294240001401c044c0c50350811200d03010300400141444e0380c000c156441c0300740b6109062958514031001c0c007100541c0c012020881e003600c0c000720740c0c900400c4000511400c500901c07104004c0c2c1c540d05660320041c00f810000000030380030481480043e601580050400b1011a640d5078441e03500f03004603400c0044111269401d01000084640c818851102183e928441d5101c010500710030580040401c54405601d00e5000d1000003401d41e03070300940241031000c5c40169461840e02d10704209081082100 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 784765980 1250 784764730 784764763
    0x1080601030501270b121005130b010308070206190c05060f070e0f03010221090f0102180108042618090709031b030c091e0b0306060f0a0312030c02 65
    0x411840400f10a13200f00d810078a400a140154800c8242e0090050a0b100f0f40e04041701c0074005800030400a1440c0b85640307411001c1291b500d65022561900c100300b540505414141001031010070f0f100da004040d000c0c4010300c81864000a4a00c000d81100c110b0a60008140c100d0400c3e03060220034412280d00c4101171032030311258038020a000c1c104e0458000201d0054001d2015074000d074070254100c0e100320300c8900042c0c1001180e00c1400044820447e4130025074000c0c03011340d46820b40d050003907901d46119002403086412420300111480c01c4010000d842903c0904070344600d849200c180007038007082c2d40f0708450390b84210030f070b15504204188200b00e01444240c82004005c135403144803001a0707580644e810304500310030b00c460301c002c1c0365035000540030404401340040ca5101560052000c1c40e020300004855900304440c14045461200394243c242e00440005036282c6450a8481d5050f0002401035083c0d549035120580b03824070718410035000c25a158000141c59404001200403842d0b00c94 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 784767230 1250 784765980 784765991
    0x504090f031d1f091a031f060c03030207020d14030a0e01090f2606090307031d130e10050a0603020108010f0609092007030306050103050c070506040f0503090a060c020108060103 78
    0x4007041c0800328078650010109000a80244168410390011004084440000b0b5a40d06014905c582c240d00aa81e426220070360784030340800000f4445010011100e00b0f4461158640c0640c8058002c1d43c440c0c2c4040740d000c0d00c0101e2540c00108900e52000d65840200000e64542c48c404802401411882c050305041c444901000c01c20118818a000b0039a500c0e41540e00710815100c000f038841e0416040c03a00480d014400c00c01c1102d01d80080640f003228041d5070b4819041005201c80c3d11604044952185c02c020320402070a260402e941144800080311b01c125510034000300c2401086420175210720a10540b120020000e56134230110180c09018010745599031540350103005010074a40340704410701c85031204000b113000c0d0b010b58007220440c0e4810a080b5a122014038001b40207100e035006641c0401d2418002c50403010155040c1d441c0a9400f0004000544460303d60204402c0724480460389803100300000c1100741c0301c18000304024280354440b00c00c00e0507944005800345c100284054105403404 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 784768480 1250 784767230 784767287
    0x50d02130b01050c0d0503070f11190222060f050105040b160f0b0403021011090616020a050a0b07060b06130504180203160501090902072402040504090f03 68
    0x5034540204210452400100000d1040040c0c0d118010100040110300810b01d030083c1c02900080114822092a55224405c0648000c15113024410804072412540802c502540180f21690881d42440c0000e0024031580c89041d42001164030300c200b10894252a03410030052000740301c0381c9c1c101414090030400e00702401d00c0045003050240c400308102d141c41500c424014000543e01110180b03030070085907445450320342406035030b80e0a510466980641f0f411160030710054404181c1d0405207008005614258042401c9102928044000c0e64001314401d0300061595800114500a04010094545941c09400c000b03003103030311103e10b0b00e004580800c20090b014a00314000c1c2c043d110b089800013000d04c40d5030382d40c20064044010080d00f600c906d00c400b803d40741294101404441c001d071307240da040c5600c40b1007200680c01ba10100800f81303850300009065a00c040b1110340182854000d005080c44d50b42e900050696009034004c0d1100c400d1070040030241680040b160701090005051010000e082 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 784769730 1250 784768480 784768489
    0x27010504030c08161502031f030213020a050f040303030b180105010c0206070f15061e0e0103171309060302040605120a060519050f0132010516080304110901050d02 72
    0x8407100400034070002070801340d01c1e039a80e62850340d41e0b50071149101d420800617400500961059405034107040d0139218509036070103400011004e403907000c0c01031400e000c0e000b0540c4020b5044256a041405406e01409842049100242000f14080e55001c14003081c0e501c103100076041e00116900d665206c01b0014006139803c100340003069641954801e5030b600d014200a0f041e400c200d00000d082c12111015040480015000242500c20144070500c030707442d4008407620f01d41c4403440b078055401e248500400100f07841e01e0000c804c400b10584040d02d0040b4558011429503001d4000c44ca000d036aa070700900c01d50030a403041c0800b50005581c102d8200742800e903400d50394000104003e08260700da9000460200700010108441441c554082c041401d10303c00210082009014041c1d40107035420f91118454041c1460b4104401c000200082071481000112030560018480441c6503440f680c2c0d17200024800c00055214600550b402018509020104801c101060f400310b882031404102001c0543c0d40c = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 784770980 1250 784769730 784769747
    0x14010e010b1818100b070b0c03090a0b190b0a03030c0210030f18200a0303030515060d0e0f0106080304061805040c020a03020105061c0f0501060e2701050403 69
    0x205004503403140b51841d211010b200307902e04075a4108018000400a10300b000410a02502c0203154200700783c2d4580811010502070031030050041e0b00c0780c002140c004030b80b42c4000c6400041c604107859040c4025141c00041000540354402ca0050104446403180002d110f200d9480204941c0c6442c82403464500912240c030302c4102911800c3d000010084403406503001451103d13031118180030000c0c02d4260004601d00c51030060741c1107100c0d0b015150f0304020340e04155607960703401004c95811501b943c804900604008011501c104246801c0c9600e6548880c064044100000800b16480c04c0d22440c80c2e080480200c494209030781451010b000028020058a0540d11940f0f00030130092825142d11801c0c50559200940042c9840001c0d41d41d240c2c04120400c10b103020f50000e02c4151500340520812a80d10050a4bd0f012100c0d0480400a48400c070002a40b500030307400454115281c544d440c9924500f0b403200024402500703c440314070040c1c0301c1101034103164000204424500791310090610300 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 784772230 1250 784770980 784770989
    0x1060f05130605190623030412170a020a170402101409130603170c1b04140a05010513150608041b08100b0402090112020307030605030a051014010e01 66
    0xc044861648080065001c40014a801013041d00207000b1038442d1024820940500c800248000c00d83c901ca101006040c81c0003244402d90300c40ca50b1b0759548880701001010b000382e1003081305083c00c42c40c03400c3e42e00484078041c80e00014010ba0701c89144001400ca0b444004002010079050710821015a503000c4503410321005504101c24602c8001c1c42000c0c2c14071440b1401580052401083d84005040b90f000b4000d5a106202c110003e01d002c083d2808140141c00c1031150542c000e5000707022080350249400c19070315015002290343c200d80e000e040c42d02e0604589000c0340d03641d901c00401c007920345032025a281074104c42003080482c47d03400c89440c604000303000708014030201802250802c8858500041a00742c040503034000c00307440b24983da8130b85800040100c4401c0c10160724914270f00d458400c680c50000161601d58940400084010294000414260500d50f55050014050f00d00380202440307036110300041e00300e200e04001904121940302c81c070309250203281c5006100c40354210b1401810765 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 784773480 1250 784772230 784772239
    0x803071a0708130b07031814010e161e03021f02060105010f0c02090c0f030103030329030a060506011103070f0b0a06060801030f0804170c041b05040302060c1e0d03050901060f05 78
    0x5d60b600c450940184c015010f104801010100114050203211003441d0840701c8030318020704c80704032074520855440c070b000e002031280092201000c010740c80d40352106d102c0a4810100402c2403a65a80010381001414401e5044c40448402040b03241a414412107001d0035003420845420350242500800d6280343c00d900130300502690003c0798035810724000b50f401c02c40f400a5036590780d607124034005000c2c06e125083d002c821102c011285040000304001040c8521014008004014446e100c23038018081c0600074071306010314031010000c9007806200520215008420383d0340c412401d4503060031240b00040a556880d860420300b4465198460b003214112078121f080c0506100450501d1140d40c071455102c1e50f0300780d01680420101040c0072400310b0345841e04031810031804565451700500c0c440c0c2c0f03100a00000b20108400e00051a0400c01b030721109042c502211032a4401008003050703044c401e5036001e050341c000d096150343c0f96031500030180d026110200a00c42d8502e400201080d19213a4024240325 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 784774730 1250 784773480 784773503
    0x15351f0e060414070903060c1e030f1b020304030b1312050c01021204111206270a05060109020403140a050a02010f02150c09040f0203010f1208040803071a070813 71
    0x80359525004426890341c2c3c0b4a2510381d03030900080150030100d5034403044901c2d41c00d0462034501075000300011440c83c0070012507000707a6032104204500800d48460032180140e6100c04c0a040d00300100504d40c841216034000316a20b03804d40c02c5c0f600384040003e01b41082800c50f5a100c50009041d5030b45d001080c04c860400d43c4d103c8041c0d4041d1400780c001c001a5040c5510024200018403850b4418022003180680da008040c005481c0804d482d041c00302e030410040c0781140341407140402001c1d0050112101c034010383e070516816940f1207007070103030030f900c0115001c0d00400c0c24000d02c040a207a00a541c2c442c0390081c221003246542d00c68483d0301d1508080c0c148030806250912040c000c1c03112a2a8100c0303400e0000491400002c0c00707000da0010b201c000e01440c900541040540f0b02c610072a4166403050381c0d802c2209291407072109400c500210111440041400300207560002040038041e5503100d105040c001050040c2d0419030740400a000004000102c0144030844110030302d60100079030081c4003c2003 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 784775980 1250 784774730 784774741
    0xe030403080a1205100302011d210c040504141c09030b06040e0607021f06050d0803040201090e1003110612130219080f06160915351f0e 60
    0x145411081c5010f00f00c0c07800d000030042100a10020402647c0c406d0302c40f0010440e5129400410a482c40704058010401d038050468658102d908001d8050110003140d4401090340d01103000e65405540440761541074150280c105e52092202181e4121075401c00b0078410a00d0100802e20170740f6100107403c043e030040105006031129040600b880a46404607605820032040013940d9005601e10154a10001240d0040f09101401480304503440205892400c94241c0c4034060f0740e42c03001d40708034140640c60000041c0c000c3d4043c80e4a00c1001001d501107a0240b9604001e20f801813042022442500b0801000303820b89400d4205541124080490035001122407022032000309020b0060180c83c03200400c00200464005507010228000f4001d071006622440d006644592440800e40d0200d01441414002d18100790301410440860386001041140c1031810703450654034503031284c41c4d100110701c6d000d843c07205005100350704441c3c1d91b15048a13215105101c0e046003115030040302c448003144408110f = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 784777230 1250 784775980 784775987
    0x1e0206091b03011808070303110301050310020d0e0a050d020f0105160c0302070302060328051e0a020d050c0a0f020c090a0b030c132306010c0210020a12110c040e030403080a 76
    0x10881c461301112204080b07203810b003e070640c4c0000104900203410130041e0316100c0c0010003503e0403a14042c0040c094a290100083e010303400890310f000702c141c0e4480c01d2400b00081080304003620340c0140d000d00034090700d6010090074400300d40629000d81c1c1c101020701c59100891070280c1001160380ca0140700e108c000e86800c9091088550010f076001d6030100600c500e0035403c03068401880c0030507a04c40010805600c001098640c00c03900e04010480d004410f010340c1d03226001450b03000740001401450078070702c644920101c07132040e20702c01c1b0084404a0244140d82c0c11401c510301115850008148509040c3c00140b10000010180d100792501c0d00c88480e0b060b20100700d000d41282c401448200d94520310904900140301c1788106600b0702144580c143c01d18203142d141a030113808180e503030604400c0c198007404941d9070a4010202107120f041084170226000010b40300c0c200005681e050419810241124a09600180e85600c11403a2050b0f20006540000458003221b512000254407041822001d8 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 784778480 1250 784777230 784777241
    0x108041a0403081f0803030609180a0503030417070203060613060b030f06040b12060f0c0412061a01090b0418140702150109020a050922020a1e0206091b0301 69
    0x1082144500a1204140c0c1051569115644130070859004c8604c1e1010756520080e5441105125081000429494100f2002c40b0f40c2c0105400c650040e210028141c1c1c5250090303031034003501c080e00044188403c0003400c90740b00d41d5841421540b2410300410f81c002079250032014046503c500741402441c02d0500c0d01d60400b40c01070403c1b0340f0040d2640381c10031500c0400c1c1421141d0070300c505c2c6801c40881d403d1401340803002c100c848450003850165030b0344401103648130016001b0000140c0a0000081c5840744070500c034800d43c0b24079004101032001c406880c44500e80c002180b818041400c03000e0200c04a0b11060718212480112040c007562004401c8400415070720a094149040310000c1018041d00000c02d15401154a048045203a80c0d4005001c203d00849040c80e0006100300104d000c00d240102012041003c02d2003240c040c08804052641240d03c04005040401c050302058110303050828440703041c104a03800076120500d402d05059849008900703803012980506584030010b92401d5208 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 784779730 1250 784778480 784778513
    0x5010e09061c020f0333090d0309080909092407020c01030f02070f0c0f0602031e0c1609091103070e070c030c05031215010e0f0402090301110d0c021c0806010804 71
    0x40e29002910303100100254801100341e000b140103541b988410000307200c2c0380c007071190120300041d19038400300b44400c501615400400b518200000e0001004507070320004024051200e190051400302c101d0150301c01c040c07240c90680907a400c54007040041e001d401258140f043c10003440c00290318070003011488000d0245c800040c00010818404c00f040126000b076900c256420340b10300700ca100750340d80012070790303841078540350b04d8003086031141240c1d4002504090a241c0520800703991300402007200b091442102c9502052a4584444454052141c90b102d00030305039409801510015080181240700034902610340c0007080200840481030600c1980a01e001c164010203076540e804d210aa007a0140c44240c2e610141c10010b2183e680310341d0301031000c61804d0340d805480740788124603d00c00c120094101c3d01d1055095500c804004102d180914000c0100344101c1000003030001e0703000c400901c0c3c10196400384115040700f041c03202150741c00502550740032a09180084050b5558a89107800b607000303521 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 784780980 1250 784779730 784779733
    0x30f14040f03021e0706050a021c0201060f0608060607030c17030106022802010917030c070b1801021b04020a050d0f0f051e01030611090a030b0105010e09061c020f03 73
    0x344010052906006800103000703600b107500c070100050000d50a40081c2100340c509500ca080208601409400540002101401902c826290070441e106005250148560050355102d80a0083c00d0701581018040d10844c13600c080f040c40c1c0a008581c851180c800c0180c184120f032591070003007201040490070710240c3c3c041081d8403542d60380c02c00b030358608102c0c1c0980f815200e5444c02e21045100480010926a01652071000442c40c0030411042c00080a0b14816140010404815003201c1044400010021030001036030740d0090144007200f1031080f0300b4140c115004500768031800020080940601d40c402c41e001680c507109050207642c184280326000034400e0420120a141076000d91240180603907051062042c0d564200c28410542c41804126000f25400c00040c004540c45902000740310070158183e034602640074000514800d9903900441f507030349845d030040c0405d59110380808103443c0b0542d87c0c5410303410186c002846004d4070090300c00440c4602002081950f441140c090250b0314040c0 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 784782230 1250 784780980 784781021
    0xf09060d0b0a06020601051311070b0a0e1207060e070e0a0b010c0b0a0921020d05031008121e03060d03261314060708010312110102040f090e0d0203040501030f 70
    0x6006511103a0034452644600b0001c8d010703210038603407030081102200c05407048a107441d260341c4d00c01e0038103c00030b0140500b2603070300d200303061a59400b044103000245044101c41e4030f8004520303000d001d86400c9221070300c10707400184d820400141e103d01015085504101d0104000d6080b0f0b0040324140d10131080500310000580a02210350000e40c449100b084c09542c0180302c65074400c0000241400301710718540180c4c0246140d010961261000c1c540046038801ea2050341d9580e411500c3c41c00101c1d18a0582c8501e00141d00c00158000c1c000c0484a08420080030303040d03140c8240000d10101c440a005021b001000300c40380c451554070109118600704484119645051001e005282809140821100f400390b0071070400d004803001a0311071003002ca590f541c06403a803c0d81d80c0d00784c4014214925209001d070180303400e42600020b0010748040c244023440d010f415840d04490b1b1003500c1b4140c891039040e030065450349042941c040212015200c00b07007404519010411503c200800d0000341013040c0e5840d11 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 784783480 1250 784782230 784782239
    0x8070606091d07230604030606080d0f17010603021809090c01110705090c0f192c0a03031407050f0f280201080402013c050f09060d0b0a 60
    0xb0b03031100501e4490700c84510400606400c0d2076983da10140242903a07148051400f03542c044020b0483e281c421009448a41055940d0f52001c05440b0f203504280050340002d0b90411701e90383c0c442c0100303d2000d580d140c210307420071807202d080e0f8074003806001b1041090340006a51010354224003641851010180214440d0b141c02d51569468000540e60540024110324045030100307000205481941c400504102d080e44038035090781c0040c0d0040159560380f002c14000c040c80d5a50f00c1905510b9030b90303c0d1300ea41c00421101c0010341c0c802540601005459403545040040d03507250752904c402580e42c14100810840484c0b00c051005006400c4000c08a11842014041340c0601081d100034020b040000c0741d180c024200002c4820381182a16880034004001d030000156200d03080c074580041c018106150003040815030405d804041c00c55403000e1800980e407280840401d040d005490b03900394074045d801e16030b82034000c2d28948619051284184408146070b00300d03000c1988040400b840003808005401d030344 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 784784730 1250 784783480 784783499
    0x10030608190312020c03030610090e041a060d0b0402091b0c1e19030e0109050604030b0906010509190504020f0a0e0906011208090613050303030703060e06030a0209010b0708070606 79
    0x1614000c800060b89468400283e51a5009031651070305524040e505590342c1c5410701c00600c1ca154050707410006107500014107402621601b03030180e8024100c1c1140100000030710311802c180502040e000706080d0032442c001c6a034025405401980c102e540121030340322100c506041d000340460702190718ac00000c1401855074006102d5840c1e0700005410240d20041e50f610507200c01c0f0261180203000140407148000911032080d070f20500c4414180f050b02c19881e08003017501d85d0440d41044410404200034070001880c200540d40c01003008886060721480c000046d40c59800c2011104903400c1e40b40c801280456413504107040f40d949014042680c0213a84030208103100800f039800c202d8074020480041a800003480d5481c140c43d030041d00171460400304106019035940441464005880480004a00e42d60203200850041da090f80e8042881400d03e203451015540290a0500ca640820b0007800181c4030701c0d10b007034119882d181c007042c2c54080505000d981c5100700c00c4002d00c400d141c0b0902040e03010340c = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 784785980 1250 784784730 784784773
    0x11010e0708100b0a08060c1e130528170c030102030708180304080714010c0f0b0105040f05011a28020a12020303041a150301060312260610030608 64
    0x505500500c070a0180070f041c0b09101189000d880b031240c01160014145100c244000c04140c0391540704460400c0c52007890001c1d40d0032604014a03445160b0b041004180303421a07103a01007850320078040030030701620070b01d80b8181d1086219407403c803000d001c0801c07241181400302c1c07980700401a000359076070300d0b0003440200103030340c122028164211040c407021024a40041660260303000303540100000c074203009642c00420b0072a4281c50420110300070650000c0d2007110035640052041c81548031a504000410003522101c000c0354417818502401040102a10300650b941c410755401070641d1550507081c0502c244205908022083c0e107054030383c81c4802c0c0d0000f40074000714000d010400350780000390030403603c030f10007510090800318140140e040c44d111500c0c6040e40203001c00d0424101c803d0108046802c0d100d40354070583e096500a880d401160340c0007030b019101e01d24000f11540b401c03040ca1030360b800200310240c03500f4002c103000e1088196007070080d80408050400303003084a000c2c0b401250b0400a215 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 784787230 1250 784785980 784786003
    0x120403020406081b0409230a1115041205012007020a1a0a27090204090506040e03070f02040b060708190306080c090a02074d0111010e0708 61
    0x149082400560940042122551000014504e88030b40920000704005042000402c0c0d030f407411100b01807001c101c0540620b002000c4824094008641030f805d020040c0701000d50140d02442000d0813a21801d0340b00c8040f40c041d20810589801d4552a50a1003401490707240c1d160700b00451784030585040319405102a1404a100315552403200b511f507601d006900c81e25940d0180c1484050000d02e40d4107000e95043c160003492600b8044911a0307054040783c110485070702040f912903000a081c801e03138610b4000c40b40e0080f0203480070300c09035003800010ba96034440e20002520243d0300c1d100c000215501d03030b0000804054020021610b55006082001c000d5026814030052041d004e0036404100340a409454115000390000d4201440e20340103100d1f801d4001480d4186065003088000d0001e14200c8000c0c002420a035801c03609120601000e080a03c41c101201e600d071402d510403003058404001001100100c2880c01a1121040f10314050161080141c90021030181f000c0120310f02c44006114803449 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 784788480 1250 784787230 784787239
    0x60509120f0123330f1017010f0e0414010b04020a030f050604110d020708070b041112030c06010b0901180303030f060b0c030304030309081315080a05090c0f030f12040302 75
    0x1a140c2015801c0c03c0b1a0700d030808114500d01940781184001c82501c041443c15000d4106445c5900060008a5548034070300582c002c51010303080d00140300c0910b1003090150038411009040d00c2d06050104001c800b00a000615003003041d02001e051030320039000313a11072041c00381c0255107c400c031306000380c007512140d000c0060740c40c1b4000c0041d40303034074140c0a11201d03103050f0240c4a1501e07106941f8400a9030010f403082d500308004104100015015042c440d2007640501d1000d6a0b5030400390402084440d6900f003619a40e000b4002e022084002058590442e104980107070382d00e0040800580d0542c50343c55080c15200103069000041c1a05a000a103010180d400d0807c4950348546c0c02d64814002c1d4003249101d40d0092000800180c000d9111500a13030141c8507640c1420071084115844d5030303080e0031100100e440794020507505600485680e810aa5090040c84207142c500c15495a42c40041d10f0a4407941c4160004190707034405101c00c158498100c1c0035a41591542c20425110750702502c4103e004 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 784789730 1250 784788480 784788551
    0x2d01060305070e0306040f03050a0302120a0e0c0603100e15090405010608010507031a09130804120605160c0b10170106051302030603060c0c100c080703060e01060509120f01 76
    0x32440c011614034482d987c490310355028800c20741c0301184c65402c58002082416800c000301c0a5001058500d03901c1083c48100c046801c60081b1074060514010302c000c5401250103200b4029280142085503044c1d0f2900380201c00669608000001c011140701c805580000007613041c030003844019005a07069030740c480000c1c003294071403900440488801d64025501d0f954520f001c1d8900b468000c0b241078003c10484250340000109803581e48091744198011130010b0f4848908604000c4a4002d6030381c40050038408441444a1039006400c1f0303510b118006006414990000e00144025149900a4a035046024080b03904014604e4001d02450007038900c030f001c62030a4000001e0450084034881e580150150082c3e4442d900e0b144641e401000522141e4028030403401d0085580e0f00c41e00b21600510360350003415013003461024040702c006c0c3d003003203203004504001448075541140032209501e0041d6820400c5030303c28a03905044c180380301d41d82c3c5001d50a041d0703c241c0305559100001c410142d0550780421 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 784790980 1250 784789730 784789757
    0x2040b012610030b0a0510140a0308130503010212160504030c09021b0607020d17041e05031e040306051f0b0a020f0a03050301030318081b060d060b03150a0e2d0106030507 75
    0xa29240d1032300443e901040c0f040003440054141000781018541000948d58910b8445000030b00303903000942c50001010781c900801803508200608c10502e00c484d4101645050b055031100d40140d40c16000c1c00080e60740011790284412180801804030080880c195a0107040200b4000d441c0c100c50002da00c006025043e901c05000300d0b2580190041d51320071404841d1490510340c410500040d10000c0d1401c0c0000d2004010103010001c007100c03840300c9500625a02d508510700a000c42d00d0103080d288209020f5103d4680c0c0c40c0d5a85402000d84408000300c503210540680c0407440d10900518070303ca5801400103500415401401440c140c9100e40c0f904056604c818440c513517000ca0301c1c0303c3d084080d03005419001d00318030a1101c400400300081c004901d005103082044007558000d90010142040020801401001d1100030f00180f2404842800f5146c0ca00308030040d050201402c00e0080d00e41882180c121440c3e0541d40c40942a0100030075200f03583d403220041c0007440d040340c441000c505d070001000d4 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 784792230 1250 784790980 784790999
    0x603080307020d020c280b07060219030c08010b0915041d0c0a0e3703060f09020f3f0105070e09042a08010902040b012610030b0a0510 59
    0xe010001030000d110181c0c3c1d41040c0a6590000706d070f45244176039201008505010810010308005000c2c01000d0394810b03c08280300c00b0441c482e54401e00300b51511584490700c0703030f10200860440d18403410320b9440ba03c1e000c0c006001d0921501e000e10f031408001a0000d207803104000184030b200300070311254145a5034a0000383c030910070b00b1030a50000d1b608107184002807030100c4c54012000c5240c8440d814500f4596601c00b20101c55070008450421040810000c006142c02540344407110a1b1f8144071019071940424030346403540e0080f84c42042070509c0000ac4081d2140d4102000c00280090141000080d074061401c101052a070903c07942803a00113000c2d0790141110250302d0320050030703100040d500c139100c005003c5a07400fa0b180b4004083d0b009042488051a8120083c00040000241061561040104480d024100603041c04411417004800c1601419a98201248011820455503a40c0c61440b046502608010400c0c4009003c0c0854684107030312484c410b030080c0c007000d01d026840d00002e0 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 784793480 1250 784792230 784792243
    0x504020f0706021c02040323011a01050702040207061e0b060403030905041a040507090914010e04021003090f03080a0b011409040b0d05060f0405071e0e070c02040603080307020d02 79
    0xc100208104890019000341d0003481d42035446850318070200f426221040680e8440c0d841581c2d01300000040c000e910f50070185c8201c032040340320300030401030000c410005c84407410030711030354107101c00071a202056440b0380d01141c0b03440b41c4c0a201040808058051001d096501e50403280700f280c6400602c8411b8204407084030241c0703815403121011113180900300170182210016410901300f9082d80c0000545580c080d9078014540794540744012030403c0d524a04035034450312441040c5d00d61800400001c28240c0343c0c160425016104003958000c00ea4041c0c0281c840c03484000d0040c14512115418507500a4500e800345040000c180001d501c44e100444150700200307002c0308212030070005020130b86865840f0300b0101002809590030781c0103c0e203a150034100120380c169170030880c5000700300c200b00c0140082400352802c80c910040005a540c07180481c0b032031a0003202c40d50100303040410341c028003e00180230b2541d4000c2040c088961240350010103500705071102c401500c620140e600c0d42e21b0021400 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 784794730 1250 784793480 784793497
    0x1080714030c04020d0b0a0f06030b03010506100e012d030b0306040b0a0509010b1f1704170d02040b0c0a110a061e1b0f020f0d0302060708150d060b0901050402 70
    0x10400c2002e0101040b00941c4420002405070382c4c0d8030050900e40d00d600c8801d600911448200f210f0b261326200010301505d0120442c01d22076494402044a1f0344d0760841418590146031804091101e511001a14000c544440031088945400205006c400021403a00c000744031a907010301c6020380101c14150350304400d590003010003010f81c00292040b04590b03c00356100d0700350700011400d491044080760115030300f80080390a0100d141c001c4e1079840e403c0544401c1c01d2089000e1296589420b4440c11135030303030301030207030320700d240b10008030b100302c6214540540300035042c58172145945401404081c1d41d82c8266a03400c440c1090b640705000298504000c20b00200c07142d540321420b580e6030401c101c0790343ca250100c0d580184229284200401e20042c0c40d0010100c3c4a1384500f072065450740108030300510800b40441c410034081240000095022942c2ea82100356410002166250080140303442d8007042095504210141c1135071060080e44c1e042955058010744210a00b6621f0b071050006911a2150 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 784795980 1250 784794730 784794733
    0xb1f0503130c15050304020f150f09210312010e09101508011d010621030f09080316030801050f0a0b03070909380a06030c02070e0a050108071403 64
    0x401003404498818071852280a201d07500719140c001c181c0781000141c40520004070044100411410083c2c0d80c030751100c00494846002c4114004a000544100c04a1710aa03c0c3d010441e80b01c691a041940842c04c80c41071142c440358a0201c2c204d503900d03004400014104189070000080c00c04103059014014603022000c0c0c41000340114035480038250041d500000341c2d20210002402002c02e01c02e400400800c0d0f500704190705545854142954015000000003243c40c002c80001030120030001902260b1508185800c00402601543d20015170350104046000010740900c56000e9072081c100201c1c803030b403641c0041c2d90329501070004800b00b56806641024101c08140450801440035640c06920381c40c00c00101c80d102c00c5d080c0150303410310404400c1401114282d10805120b100d0303408071488015900014000c0c20030016507120694810071041c941d6a68034561214801c0c4407c44c040cac082c40603824191f00b00202403800070030003482030341c43d10f008503400881c41c280e0304110400041170017030 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 784797230 1250 784795980 784795987
    0x418020f0d05070b04060504080d0905060a030b0d0b040506100819020904170706090c14090109050703020412120807020a0803160903020409110f0105070f0803060103021c0b1f05 78
    0x1800706403040c0c0303002035449100304800050942028001000940511794400d0348480c545010035207000d10b400301c45018000c44100901040c0c0380e200030303503050714804e01d804a40e08182ea00031070b01020b01c01e01d011340940210001c001c2407010001d840c0b40950300c0281029612941d504459450f12410401c02c9008800c85601c02c000d8984403407140d070000e003d900004618202c4900c5600c9a41c07015104407952502c6050141c24801c0000c0040000d002d1020b11502c500820400103801003014003480c4016651040402d20942c401d5040d10301500100750400100c40f03050401400f0411076400070000a40c142d00003561541c03000c180741c0340300c3d0341c071200711402c5403161054200e0891800d43c81e0400c21860b00f10020250f901c5004d2007026a001c0d02101c04e036100c00c2c2043c040e42c0d07446826100d05000c1e080214800240d45407030481c841c0790300405000c2d200e80f00c08004170301038424410840d80d0461505401954540140d115a40c0f0160855012280342e403401c105035001b02140100101254050 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 784798480 1250 784797230 784797259
    0x30f0f1b2b020616110d0210062301180b0703080405160302100c0201180b18010e2214010f060e040c05030708150a06090f0b07050c100c0209040f02041802 68
    0xa04c41c44a115005081022540c0c8900c50214582030703454125030b0060307000010f2107001480c40d1103010050010a603840071801d01a41d86110030482d0007400d941045410780840c03015030025801c2502034030b00c1c1c0c00c14a43da441507050041000d102510141c030306000d00d0804031814a2824089000c40354080c00c440800c40140405403042d0707452440603030521071b0070ba0801e06012901c1c0e5225000d000c0e003031b40303060301d0b6012000040e10410340c82c540c01d0705021840ca410070455950aa40f1800d84103c488459090400d01c5540c00141041004c00515204418000709140399614100e07419103419a8990f050281d0110070441554075881c50003020075420000b06040c03610074800d1a910012a00a0351401c0c1c2018000c902c80302210340c805000030744040f20034004201c0ba80c01d030000030140e44003507d04000050b2a10740c7c031201d0b0a807680c2d10502c11000d80036000d5019a001c0da082c7d0380c00034001c0c807461806003020005c51451070000c03841540b421001146203804019241000c2d50003078846c0c000700012 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 784799730 1250 784798480 784798501
    0x903090f0603221b0e19050c030c0703050c010608030a080a02040506090d0501020c0604050705040e120d021b0d03090c1e14030a1b0f0e09030f0f1b2b0206 68
    0x203000c01601c000400c84c0700d282c140000c2804100082c1800440c1e80709602e00030306285c90035102c11000c2c014090500f003d1000061400082c0d80e007143c0c80a000540e646040e280c143c0e0300744900107100416508211000411200c040060b0082c00f180781c5a1400c0d96070b64100000c101e22076405141d900940c24400500d10f07041815049003058494000141790442007a500c61034010111401c88140c2c3c403569050240741071a0041c510094120070040c040880742c1c04c0b8003036407400341e80900ba50150b07002c13600a039000d14a1a980caa0614800b055410310600028014080d141070035040d41c24001c10640010404011400089151004541f400c841070031318030b940071b0f59100300d206980d2500c6080002000310300c2e45210718601d01400504011518036080164202010f1a480b01c6141446042007101907940802107c000ca0b40c41c1001580c0d45800d04107441907401600c81c040a4504200c103814200703500050b54a420020b544140d0281c507100300720440d40301040203902d00068002c90042200d440d007 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 784800980 1250 784799730 784799791
    0x9140f0d02070b160501090606050f03010209030c040b0a0b0c0a030e0d03020a151514180603060117070b0a02030d0f06080c0d0819050a031b08010303051b060903090f0603 75
    0xc0200c1026030a03134545d240c640c25107880402c113589555603140104142e01d03081412600c810340c240c2c000d500340080e203800241c0b600d2402070f003180034940381d01d074261f102c4c1d807a0455040a44101121151600f900640035a07843e0a10b15040300412a09940e256251070401c00350480d56034140c0c003c0400c006c00f659860566400310400130340712070700c8400030309104e01000f503590040c05c1405c4010103507640c283c081114010700301900303503082c1440d04180010344d203010900a06480c1c0ba500341145002a8803a424680210784e84014408400401e09180166021008081d8001c049105102030b050100b00d100803604144220344a03a80810201d42c40340c20034014150b403450094110030b040109101039202c0c43c1c5d110800b4000059400607070841043c1d0140b145148000800c00442083c0c0f901400103401e4010600025080c010040b4121410007940c1d0a540400451102591000d0500442c0070741c2e41c0e044504680e01c10301d044029141c40342000c4090b248220b441600c0c031581900c01c9900740d100c444 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 784802230 1250 784800980 784800997
    0x11809110a0b0c01200f0310030209070903020315090607030b040b04020f0a0f0305100b0904020903011406030f0307110f0607060903020606010e090f0a05060d0609140f0d02070b 78
    0x140d0000514195a80e00d09100080c500210410341c1ea2444041260845003c20701c802c0500d21503180c0710344102180c80c00da904100f8071400c02c5a071307034880202040c60307000c881e03200a500c40116400c01680710380c0314440d481240e209904407200c0d041d8404820001d031008a41c450000d510110005203d0ba100c0d030007402c60440c01800000e00c21040d41f01080a80c0e00c20100107400d290006502100180e0003801038100041920781000281003909824070640c0c994030500402c04000f00d00c80340a955250b044410b0340f50000c008220b40340c51001e0358031244008658542c840e010b030101d110b24002c401f0040b21038543d0301c09000910b01003030000b004009036000ca0030640260f8281b0250000a42070f208202200340681c008081520300b45000401441c902d0910602540d016800c0c0603c080f007401c0c1c915041050703504081000c0c1d4a060100302c000c01c201101420f85801c002024092100748000902c00c0442c1e039041c0c803100360740200d040d9510009542a00e00680c0150010000d042c4580c002d0402e05c1d = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 784803480 1250 784802230 784802243
    0x3051903052418093d0b0109120c030323030a0c1b050303060301060902040e1311032d030307020d0509060d0608030d0b03120d0515030102030c0d14011809 68
    0xf0a82d10074041c01000304039070500c010b610005800c041d58240c1400c0b0b140c00c0324501011500241146214020401e820b420300c50b100b526070a218a050380281d082002034102c40c2c03165101401f060601e0480b034442d0f0b1005601043c07000d0120030a4000840e900c580244501a5052071510703624004401084518284c0d0100719207444c10b040762030703040c25450b201d05000798000d40e02c0b07090410405007101c220354042c16002c2c0c0304010030001880700c644d0060780880e4554441e2910302c0305007828a000413040c2007003035050040c942d031088100c012240d544401005d4040003407a0544107810750390380b44000da0321000036078400d010a14105102d680141039004000e01600e00340100050704105484850304543c14039000401c808001000ba403154000048044004141600d66054180300c0c174030940040c103260355200d0300040e40c0000511400005054064000c541d01e103464402c841560300a5500c201c0e01c130381420031001c69940b50842c207905a502d504042d208176100166884018800300d002214031 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 784804730 1250 784803480 784803499
    0xb040f03021201110a02060405060c0316030513050706050c010b1516061e0e0f010911010f05070c062d080c0304260c240403030b03070b07030519030524 67
    0x1d48a00c010744101202600101f28901341403a140c4d080984c020500403090400340704000b01068042c4400038210344508000903103454100081a04000045010f0101d00c21030030b000032010343c0305000b0324900c4e013804020403c900148041000e03c0b0034205885020340303014005015500c003411a034290152207040001400d16582510100d80764440260550469840c04c2030703071b030204080c019032150042e040001c109120195990014507004101c0080c100000b503002c80101500030400c88524982204c0300559075561900001c1c034021044d4031039040c5810310f554200100b441e0545003a4840540e4443c043c1d01d03540d0050101d01500020401c0c2da81e4501080d40e2542e625442c24241403040100b201655907080f41104c040c6400e80000c0c18649080365418103900d04484001407503003255142c0343c080360103441600000c1c40c3c541700d900300ca030503800001055010140c20200518a40140d40000c0903982c844c00002e8084400031500841c2200400d004641c0300401e02280c2c180203100281140300 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 784805980 1250 784804730 784804751
    0x70903061404060e0f0604060c170c0c011b1707031e0f0509030a0c140109050d0905011d18040204110a0c06061202030a061a0d03030b04060b040f03021201 68
    0x103a407a03946414165442240034842800010700840b5059080d0300020400c0310380c10048a6075030480240007a100316034981110200b10f2003541400d02041116061600074107101359440010b5010004045c955031a206d01d680d8000030340444452521015120101d500e010a040b01071013200080c00142016610481c2140c2580c52100404603050418400a00c0103400c490078011544082c24103483d41d441402420341c1940d001203210240303940500b2180340300c501c2e003040c1405020f24900050082c007607050440e50b101e9200c80304004854090380c41e40900c104a00c0b9201400ba150801d45405c040320901c3d0032003030005a1003007904184080c0c00042d589181102880840e001f000510700022001034045050000a0044c100a820742902900010031300344d0009603210400b100092419407113050301c2d6070440a0b41d900200c4000c02500d5281c4c02c0040b4030740100140541400240308a15210000c00d02504034400c0d6000c0d260546a005c1d0f106085400300420907210380385101316036488141250 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 784807230 1250 784805980 784805993
    0x604020d02070506070305010623091f111002130b0702010c120201060303200c1201090b010f0503010c030e030a1b050102040b040509070305040807080a030e0d08100f0503070e070903 80
    0x245841c003440244c090760070300101c01010b0b2081039016000308107142c20510074100502143d016100124101f4544e01c1d403803030002c150401c502c0a40c500c12280011450218150003d00c0c1210b44500c0e4000d44a20840c100101812405001000d01801000d902d013449460150700003400814014100043c17040101d65a10030003140d061030f8540180d450300c10030401c064011040c002e4244183c0340c2c929500c03015091490751030f0514038145104e01c1540505406102003907100114082d0410701c000400e68407003005811100700c0d8804c6900035841d01003c01050780c0300e48100480710030f01d103020b14035004805801302c4800c1c00350b107103102500c0390b100c402500242e000d100074070040c01c4c3c011010352100e1a100401641c031600621603800c2c181000c0400001900b29400c85013001d03480000706403580041c4c04120014050b1074615619413040c110781034481da4120303005a11443c4020209800c4607101d010560440c001445202d0301a401850144003c0403102c0669038454035034a05040c1c2c0c43d40e2600c2c2e26 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 784808480 1250 784807230 784807237
    0x3050711070308040915050f09061c05010b12010c09050f060c0105011203020f0a03121109091503071a03340302040e010e1311060f0c030904060e130b0604020d02 71
    0x3c449070000060308001d1075840740240e501c3c0b41251007444c1041c0d4a0440404c00990ba080c540320721444000c0c1c00070350700d5641d02d541c0d820b80070194600000e0802c010328082d402030110104c032520864070032111601d19101405241c01600480ea9040906840d0100388801000070158041c0e02540600a0400750340d801d1241078001c1c1400300e00c10461684604001e42000323100800c2040a40210b8140c50200707802ca4440c101a0b00500300000307080361081250f01241c0520000280e01000c8007007405458221040140500301d02101683c241558507070024072150030000d0500420310f028000501000408070100c102c400300d11466060618000002c8401d485044d8000000b007940031506218008420f444540501003928441d001414001c8054184d8100110300070040010390100f45069156101a1402d50148010742925044900135160722908100c0c45180550300d8081c00040e0840d400d001e590103000459600441d004094980a205060041c40076800c1902001120b902c1c6400d0701c0107 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 784809730 1250 784808480 784808483
    0xa060f0f0f20031e06011b050a150b0f040f06080f0a0302102009040b06040f091b0c0b0411030304060818062205100207060203102103030507110703 65
    0x902c4110660400d649031848003a9040764500900810601c1c46194a00840c04110a00c030f40b01190390300d200480d4500c0341d0040701456072060aa502080020009904010742d2040860300400c1c643e01c82c001d0112240202e065a206143c01034441a07400c1c168442844581800301c042603058807140128508002140c840c02c4980c0100c00d20814554148100c007404001d41c0740501c820041042008451005810700c0c1c0782c11800051810a2951035074407510001d0005042280c40315960b0001c508001181d22401c401c0c0350514400d01c610811840d10510409600c1d20303489002a010340300d240010300000c0045035401080744407040079030b4080001c2d00041c141555103a98619101015011480501c5c68040e950f611420520400342640355428444103010760f012050034076a8104240350907035013540b681030180b0028940c0107011540e00214411040d110010b11025524400102c0c1d60f103107413003c00e075003d0841c20003400191080d00b1150f040420b6180042806205040e40e03800d01c00300340e20 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 784810980 1250 784809730 784809761
    0x703030612111008070818160f17060603070b1321030908010c0206011802120a0c0f09030b0a02030705070b0f04020405010b0f19021608072102030a060f0f 68
    0x9003103083c0382c8603554148400b400e11300041117040554015240210142c040560240c504d0f090b580151400c1140c5001041100c5141c1c000c580c0d280c0100d01d07001e410f4000c4c0414890524040412021b001400d103021b00e10141c01441090314202151145801520746101c10700d0320002c00084040100d00c0304000409060200b440030741c91494080c000e80075981c00301d516a410402c030b120407683c022a8072411200d260110102c410345408003a8020b02c80e5041911001c80c030304082c032010b20443da000d83e40d081c007951600c0035403804007481618a80c1403031000400810b1070b000080c0000342190003458100d403880c2000ca041c02540d541c3d079000e100d4215030b00010424010100415440d280c0200b600601e40c003050280b0701b40c100c80100da41032143c00c4103500c0180191510f50b8a084c42003198044091401c19103205c0203456206283e164642445003001c0022504001c001d40050031450701049680140249035a10740c654402e40a040c00c1444000c0c0591fa6000c644d003a0320007030080c4066a980c516 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 784812230 1250 784810980 784811003
    0x50405040c1517130201020c0f0402130609031a06061905130e061906050d020c15010308120703110d05040f06050a0b0916051b03130b03061e010905060703030612 71
    0x1003c10b1042000604050000c80240c91180140c0d0300403e2014000406482d07000d440c580a102050203403144090381582e03e0883d11002580540c0a107045041d40e110f0026010440c1c404044403240d403000380d50280d070107013040096030320b41c00031560902e4945843e4100b040c141160007881109074440b41e0700175102c1a00040800070301d4a00b6610032990041619090309030281862002000ca015124100c0d551550008184074034502c1003043e1440320742e80740032105107981c5074074003000540c1115200401200e45000826801e6000c3c1c010400300401d1141e00904004d801c01800001d0a80034209883c541400314900002c2501c0740a050310950f5007038004240324408105202113030f41c0003445081043c101150b009440c650090403a0b645202090381c6030f0b140508034210900310b01c24038400004c148440900050b9403110400554803801040300e042c034086000d0b40362083c03800f80103040607001502c004814000f500d4020045c000c10b80c0a40390005d0302c50b8445581c000844901c0303c00b40e45101281 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 784813480 1250 784812230 784812257
    0x2d0c0e011d04030914040e07062607050a0c03030f111902120f0304170a030603020a05090601170a1d0f0c011809180b070f0e0a0b04050405040c15 64
    0x1400010369400820081041c145002d0718014080f280382c3c0180500141c0701c1015800135515074105040c032440e0401980e11031380c0e4903074019125401c14900d23100d20400040040c1c2e601090a810148030300100d4a07542c0c980b0502000032512850100b01c01c40c2415036919640c146d03106240314262421780296035055803080c001c1ca504480d8009101c46c10215400204103482e01103c240c150703100c42180e4025203490b51a81d00e0040c1c10110580c00107040d003140070030804c0c03d2a50640202045034000d580014105803a0020300070300f140d0480e00709000c074510044000e0200d4410f0b00c440e41c402510000010b81901d20420003e02540304600005581e11010329444a5881840380300201c4409081030813380d088041100742c080d90720701c2080c0200e50340310303c1d42080c2010860f000311105d5000300c0c502460f281240b40035000501034840340000a6400ea4800182d0920400020682d0b41c4650300c00c1c02e00e03142c40d0822001d020020803c03a04030341c180c000005d1401c2e804521844069964880c134600c003d16 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 784814730 1250 784813480 784813499
    0x60a1508240312130b070809040b0907050a0804031806030510060513030b04030e120d0305091b0d150507200d080c21090c040b0603042d0c0e01 63
    0x700c00540d59140030080489250b503000402c80080c00f18240041d483d0b03c2414103960300d051066100714800380c070000c0c80d03108022403140103052454040f2010011059010300344070031500c00711504400705200300b15000525000e00481a4810f02c41c0c94281400c041c03000307604024550070740c05540440c0d2214180315560284140c00c0d4041c019500c2d10b00d007461003444e400c40a903d01803001505ca403405002084c00e0500c01c1840e40c0e100140900040010340000d500325030781305100001980000e1501001c1407189078045a504090a001140e0760742c00e442c040c0030407406580c500012031303400c4810004806403145501a142c461566901d80e10781503a035031845000d0f541c00005810b0790980040a080c03407001d0b00300d814aa0003000711200c503a100d040e69240600710001c0300580d403100c07000110070088440c03400640e00c090540103a60600651110509101d80c2d80402da42c01403408026029901542c44048032260000f10004085070300c2c884180c5805080d00195003140e81418410700061200800 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 784815980 1250 784814730 784814761
    0x302040f150e0603120f0c010203070c03020105090606010e040e1e060103020909120301090f15030b0601090f0f03120203130f03030f180e0a1d0a03030e0318010305060a1508 76
    0x38102c0020200b85000800240c5502c0e01c00b41e003a0f801c90020030740c4c0902c0c0c1810800e540038031156100031566820007103000b5085100c0c0344021801903080c10001351110401040190041c031045e110001c1e00d40c000003c02014200841003c850783c490010721941111030b10800524007a6040f003c0e00d603950460044c03280c5224020030f050590b90150728415034440d01c080850b81183ca14000000d280c612045000001d083c001c02215001c241040c0044140800d42007564000e14098803428449a520542d1800d0300c940ca115800c000700414a0400102d904403c0b81050048c2d81d20580746841600c02c151200b4074500e1300039403620820084148201500718502c84802d20b901d0510702d12407444079165007510111802000510400c500205030700c203140b90002040c400901c40b5001c03c00c140700002e10f40c0c03a50141401d4000030304020307410308600300100441e04240500c03804010304800800054014041c050710494002c103105100080340b40c040c41c0500d01000c01541e441c03405081c1041c0b4a04143c0 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 784817230 1250 784815980 784815989
    0x1030c0e07080c0304030309020109050607150e0c0d060908040512030a030606030218010309050c040f0b040b040213120c0e0106020a14010506030a14030f0a080123090703150302040f15 81
    0x60341405000c0070900c41004e50394096454075000c19051032601c01200c441401b684215000400440d0010420000c000c0010700b10020f0f2400b04640468007186650340c1a6003040079400c541c0403c10b0380c001c283d040d041345649600424410346000d42d01c1000c00c074484000365102e19550004a04c1c030000560601400300203240c0b9280c10f5080012100034030070b50900404100741816520700c00700c1e0800030140b1400070116801401000500341e007607180400303400c0c003222503441289004140d0b26946054800c5d200207240800c441c0ea1800d04280d440202d956061030141c61410221800140110011041328007800c41d5a001d0012000c003403505440c1e24218410500e981d9051508005d41c5031400956441c042c2d81203246c80c140d00001400c00c90a500c580143c00c045080d0004161503241d0700030103407504071080c50000213003100741c02102380048c641c1030030003136844992400400d5842c0e1107600071688866604114600c0c0964950005084400b6016081200b0b612680303400440c21403c3e903098000d0 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 784818480 1250 784817230 784817237
    0xc0a0302190309140102280224071b0503070b120a05040506070507080903010f0b0a0602060408030f27010b01030f02030906161e051b0d021c050702040501030c0e07 72
    0xc4055640036100070312900072070070f101032903041c4131000ea8402c00400c4005c580c82000c980d2107420030030400c046405c0e80002640540021140310240580c2402e000424036500e00e40319040406641c3e9012305c5011200904180406c00b1101003107a83d02070050b01c0c02001c18101c0540d6405c00400c040c070414400400054403240303820100008104e0201c0c84544c000f1a902d4501e0303983c55145044c401c07030701420204581562a007003c0002c1c0300c501d540405c100c041c04a818180c031035940c00080340c1c7ca500403903000b44585070070310218030701102103805e40d0303000842c044090500348080410141c860400b18000c1189039102d00006000e940c02d881034108800450006500d1403400a41ea99540c000140160800c01c0242040310383c0c0303038800c101b8201624000910000c803501e5011000702a9040044103144220b5612042031701d0341c40015488102d0311583e0054680d94035080780c50812095403007400c01c1441002c103d900010f82e103900c501c0c0e0280d84180605c0356070030306015180204038801440c1d83c0c1030 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 784819730 1250 784818480 784818523
    0xe0117270f12090a0f030c0504050612030d0b06090d030e01030608031e21040f11060a08060d150c08150103050f01120503130e15030610090504170c0a0302 68
    0x990001046400104080000316aa03400f5904080340710402980d22600001c2a030b40ca0101c200880a080d803003c89408450900c000d46400b410040340031074000c1c03401c2e0103078010803d41e055156942c01c0364041d610000c00d860f052011080125000f200c0f07108040f00060349090304041c02c0c2d0707010700c1000c1c080d00b1404019170030440009004107070348041070503a10150b0404141115000d5518080541c0c0960041005405080501d40a01d0540308601304540702c0c058407a0760782071820004d05a813010341c0c080d43d920480fa211078080c020700100401c002d48400002c004180182501c82c018980b8850309591240d10f1407902daa0a0072513644050031150416090000788440070a54400e22410f40b00000c081220f407007a689011455485410005803400c46100e03000101d2401c500c0d102885200c0c039103d11001e800440c0701301600c0e00411038510300104070340d460910509110b0f521460340140700300700a16544828a000103840d8102c0011003a82d03a00c4015110101075040c06a82101007203030070303c03403107 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 784820980 1250 784819730 784819753
    0x318060603100e01060f0b030106022802010320190912030e1908062412031605010e0f0f070f150507020d02040c0504050a0f05100e011727 61
    0x490b42404002c0140c01621292248035a0000b9400040203094002c0612103255803566602c0454000340b04840141c02610b06004040b00d88403084503a8001e070303030745c0100c07a01d0701079006400503e440107003484007860760456043d010f90702000802c0310301c08458913501e42180d8141d0050031184d00d0703040320307003000d103050203c9000980020303c45100e03050484599840b03410310340c030712240c0c081d16034044080351150f0720a20020001304178100300c2c0c4552203003222580c10a480144409014008a06030081d80100310341521500040303030074242c8511640000c20306205a802444c502030500c0385c01007182d0408469805040010003026004120141c83c0c04080d5181c2400407803400e40400c80f078814084001021400c56a481d4200d40c08954020010059034100e0070780140790750003074007407940513120380e09010884404241003001120343c000c114000c80c64000e00101d8170940030b501c015040c803100001da50040410701c60a81e00c03804101c020002010f401c003241c5804a0100c40c00c03d8415009115040b9 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 784822230 1250 784820980 784820983
    0xb0c030a0c0c0804031e240501050319030503190518190f30020a0606050d0b1f030f0327030809010807090f080a120203030106050412030905090c0318060603 69
    0x24100c0307030081505c03415070000c103141d081b94000c010f200419039031003002c3d244410071405601803982030748084100616a2a4401c1c140c0d0381114000702040105120085800039110b9001941d110034020721004450741d4400c504019900c060b40c1c0b80508034000022401c030880b0401c100700c1003102c01840d600710168240c403040040c000003c0050a5580e03800c6800ba8034410800c0fa40c9484075220802070030f540207011009448210b00c0408032a11804d1180c005254a4a0807241034000d4214540544a851f0303081a0b10a800c1c800032030000c0e0600e1450000b0100f0120001c1c81c12440c0039807250480304021804190342007150401902034000d80d250f0500c04107d032074081e542207103401c0c00c00d941d59450742d000c25154000e02d030b4040f51300d400f102c0c80c000c110860702185030b90802c1d1007100300742c071032400c281400d0380c40340000d0203150005082071000300054440c0c148500c0c2040c0c064141040c80580341c50204521100444009801034000000d110b101c1d0300803000c00550241c4200545224101400000d = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 784823480 1250 784822230 784822237
    0x10110313060c1e030c2d050d11030f0f160531080d020106081b060d11040e04110306071d0a080a03090602060108011509050903070b0c030a0c0c08 64
    0x7420841c1d079100c944401e6400f803600e1824207020394040d4140307442201001800342054051040016811b00303072995012640892843c9407214040f0707170091000d00d014084640c1d402943d140030849440e01ca403441c0c2d003111000118041c100007040480ca505d03000341040040c4170054a0034030104600b4455402031680300068a2070702420703c0c00c02f070b494508580360044591011304111441c60100e900010301071000150754184121f075400034800c00b80c5e50003841d6140e80502d4440b040b030744800c000190072813410600034074040c103854000040090f000840444203800580007490640201c4d4103100520441020f042400701048000300150b18203003400521400005c286802003039178040c82d9021030b6031041c0143d4050b18686048524942c80707420002c02400d518840e60000d40a11400030600e10300600030b00740c5055a15541f10b4216203801c1800c030080c0401003003040540001d01803400024621480c444c000c500b81c448580e00c03400e124003034608a0746005498014803203c030520600261644096 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 784824730 1250 784823480 784823483
    0xf020f0312060402030a0e0d023a0c0503210402151602040510080f1506090103050723040507030f0c03060302090a050705041a03014b0803070510110313 67
    0x4d6160b4490100d580c02030481e1041d0452140901240d250015500050700c40311600000c500d082980c40c1d01502403820251500b10074014240b040040c4801c900800c580c07140310744103c04507807910072a003c00b03c11140124401c8a1a0032521040c0819071500c0d80c0c3d284041d030007030074085203009504400340400e1a84003100030700445c7c4a00000341c03c031600c600f101c8010607441058a03817101c12551174544920349003110074580040000480c0e6a0b04000d64514140d96206005003070b980d0034003041c3d503c21003011030100d10090313816911508503100c501445004200d140c6020410b42c0d000d01c4020b082c4e074182c115000405207032030230030005070303071059980e54020600c2480018151500c041c122504d104cd504500c000e802d03810910b5462250890040d812607800420621101c03401706204000c0700d5a8070b08410408040b00c01c180074142e203416403608080894020307600788903500d8916a0458000b00c40585440e000540c20515000c0640548404030503403104846c694a000c1d0366610386107025540 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 784825980 1250 784824730 784824739
    0x6030320030a0e031f020301051212030a02032a1c020f0a12150b0c06330d150e10050c120403020a0807230c032e0c0f020f031206 57
    0x1800c00036460074483d0051031743c48461454902c001c100c40071006940207110701800703884601240e079039011000c02c0c00050110302c801060700d191203144d10035019400c09818403100d1017008100d14910000d40a80d02d10003450a9000c0351a00e860005420a0195a1320901c030a82d004003d4a0701c2801ea040031102004400c1c00c0c10415036009900325001171240301a0000c00c01c020140100d0510803100c05850030750960812a4010783d1185901d82081c110307440c0364011020b910030420321880c11680b007800a09070180c1081c800f205503484040c40182d0403610f0200b469660b000084000c4814812208500900c0c1018021414154000c0c4068403d07030302000d2640404902040c10584244a80c0b40c40c03a0b04410070a03190700c0300b030510000080306140c0e207070480f078808410050040400708164114801c02005481081071b40c3c140d00ca003c23500e0600c100313244074a812031340e0004100f520507010440c581ea80c0d03519065400a4011f894541c00340c085188075801400109140c0b445600c41d42d600c402c0548 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 784827230 1250 784825980 784825997
    0x80c10020708071427070e0402070f290f060105070314040906062705040510170703060b010810060e0d080a0c06180b010e07050c0307030306030320030a 67
    0x21000c07070405449070066026030049510019500d4a240d070b010141c41421135410720f645040c561300c403512070424102e810300411000c001802c51401141c164640e11405000580703444c0c000d0b6904149100611001c8408130b00020020000c4083d019004040e521240c403500047c2c18440c00120300740741c00801d03007410882c1c0000c1c01c07010103201c1d460030110b28001c0320505841e07985480f690030240909010b8030001414055100000c1c05481c1181080c1d0320500755448103850801007800702a100c01044024540750b080400940d544070880c2c1001003520440142c02c405086203040400c0e500400d04450411800310103208600381c0c0c200e100c400300e070701350304220800700819000728036811001d00e00504003031008205c400f00c0700d800800002c0140d22401040018501c00305004000004441018100c101d22900600070010441c910917044500f0341041c0d4145401c0d01c03030241c80c640c00400110000383d00c3c2e180800815400a031000300e1103982d00184030b0702c4c40e904012075071f42e800340380710820410041c0c9 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 784828480 1250 784827230 784827259
    0xf0e010312020a1a0f070f0c06241e0e01051012150e090d05030106050d02030c04050604032301020a050307180503010e1e0d050703080a020d051305100501080c 70
    0x8000c1100030030f80c42a0101c10301240040c41341c0031800100c442c5c02c1100f00400001c2c1c51a4800c810704a1505034a8649800140e4503854039030050165200d410001c6140c240000c940040015814004120510680c020403180350182160a8083e40c8042c00156051006100c2c981d0f03160016005ca50207444c0415007512254007060141c90b1300007401c0b1490702c01c0d40c00031030b852501d605030074403802c040c00864042e0700c882001110540705c05d10502d000a00709100707144202c11550000c0d6040003240c1c0c2c85600742070319140018202d030b01960040700c103c0c240b10080d0140508983c4c1841922a20b000214142100e0140107007052100500350410052105c0380401041c5000f00c1d4100078100c00f400030490112500c02c8aa96044002c414104003640341c107210b04002c0c80020080c0103101c1c1541c1c3d003400c1014940d01070300c1c5a039018000e28580f80c5c0a0001081c0381c0b40600c651481030009941540c481c1003182001c40c2008800c20f141340241d420700005201002c40056440071184040c3c41d20045920ba0 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 784829730 1250 784828480 784828483
    0x2090408090616060b010804080f18121e01060b043605061e030d050f0d150f050d05060105100e210d050309100b21070e010f0e01031202 60
    0x390a1a694002c10118800e80080e21910095031180d218010400840703910800550301c02070304403002403660342d082022004e0965058090402070440e1082c0c1a041d200010001e109059804021545a031101d030011140341e048014000302112800020800941031045084d0346108a028180203001c126489480100104407210030040445014940d070440c03130a900800b81000344e40380c42c455662100f903603c1403000249940c50f0050b00800622603450f50307400a840d150050050022074040030f100410b20f140041c0682c4035040d41620b80d184200f03080c0010045c6c0c2c9002504901c4c060800b14202100048000903042d0545d50304460301036003412883c40440b100443c465a6a42003154808107600016111902e0000c20200da800c0d00e00c01070384030008480b14001100d48030071540c04620b508a85d009298031000b201c11020703218045240740b41ca00d82c0101611030016071107642c0941c0301040342c00c01d400702c2d090141072041014a500351810000031610031060201400c0310740e4040c040c00d1017900 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 784830980 1250 784829730 784829737
    0x15340504120b0402030c0105040e2a04060c15110703030905191b08010e100c0c0206190806040e030d020315100504090b01020303130b0403030f1a0a15080402090408 72
    0x54041552544190b140071500e9000a4070100c1c040e118584012440d5030181d01a102501c080b0140c00665503104c1e40107481d110003800d07130703009840c050a035001d00c44698240104041d000640302d440004085203450f2422140000038100072510b810301250402c41003034112415190145000301e0149203504110303040003500c002e40301200c1b009500c034808004448513107407913000d460100004040d90310304c4810700380d80d0002ca90072900d400c1200003001c0501268012a800c44580c505801013545030b40c0444d519900030316000642036044000001410b90200c1410f0788030106627407d018620075441d5141c3d40c2e0082d0b0300c2c8a41c1d41a000b0000074131000c2550500c170a0000014102008460522000fa00592060040c600c03a02d04254645102d03500002c1220b00450500d4000d54420700b580c2c82d01440207801030811401c02d922003100d0004030344540240250112240050b2034042035000400022001682c0b20500030188460b40070b41d85508440705592064040e18100010364880c03418040318031 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 784832230 1250 784830980 784830989
    0x1090b031801020a02071d010501091814150405100501120b010e04020a0e010909090210030e0f010606020f0705010c15110f0f0901030e06060310020c0309030f15340504 74
    0x10303c046000c1602c582d0004022046a0034540d509a080e8803449050742c3c50380c400d01469000c903140e81001c110fa030b650b20007004400f88400000040070f0348803014441c0030b40d00c00c3d42c3d03200280441001e000468a001e200d070540009030583d60300c004ca1b203080f001801021311042d22140d0b00e56a0000d03049070307074020400e00d10600030040c811966155480406840300700344010180c0000c0a005c03011030307603140c036100d091000c030b40080450300041c04441b021400780c8100100d4040b280511400310301c59079024001c040c05030090790060010090095802454041ca0780c1c041410000c204a5820210715a1840820b03100203118000c60850000c50b620079040c41180c2841c0081900010900e6156854802038181c5941c266001e01c5004051a04282c0d0303032000fa104551300d5080760312000c130445240e500504102e2601070640c0d08084d140e9000038100742d58544a0302071a000089031002c08880b2065080d44521100340c070705d070f00303a1380030b001c00d000d041100fa480746012585050900c203650044083c0d80040 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 784833480 1250 784832230 784832233
    0x5040b0106023c060406051e130b0601030605060c0c0102060a09030509040510120803070e0a0503370c15090e01180617010b0307051f05160512070b0f040201090b0318 73
    0x1800e107031a03e90b000304400c4944840381110044003070346244442d2a239902640440407a40302c0c5065a031074550740c050014100ca0305142e0307604400500c0c0d45461000e8102c100d052405042e000c41070380c002a050160003440a0809803401c4000c00020380c000085e902d00c0b00e400c2d01c0024466441454410148090390080c2c030300b0101c2c1d40e28800402c000c000c004c6204190f43d594100d840441102488003030381403400341720b60641024104010307000e80340100842c440c00c0340350b10085100a260303191424000c40002039a030040611002e01c140741e04d054420070184420328240b4802890148030a9107601c060203140e0720500c4500900c010b52540d03800140250500c441c283c5070071559903091a000f00750407a0101e00a0049000000d03607854000407008842440411100000301541d40c1142d00c2d610008040c1810344024811b080850301c01c1003403403691106d0700c03440c540e99503207418480a0103000400c0f10032803807030700e070100070040c0d03400354400040302d01d100b480036203d07124441094400b908001d0680804d = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 784834730 1250 784833480 784833493
    0xf070203070b4003150b10020d020c06040e04030c050f01060906060e030d08010627060e1201020c030d020f07200a062a0203071805040b0106023c 64
    0xa440345541c0807a2501c10a0b449901c0e480f15120700c52141c08001a040728200c44024040012030310148203120551032030300d0009440040440002c2c4885455001040164400890020361640401c040c03050302d0012202c00b400e140c9050040e136006640144010100060491641c04010082001081902c0068000e2141a44650b96030005010f04d100301b200007580d6004408082c00c0c0410030070006240c507601e081041e1b082c428103a9103c0c040d070700304030b02c3c480061440c00301582058644502130f100f641d854000543c1003100300824a2688085d003803d0b079104000001c0c0755000041118002c15203c100542c03200c03c030303144074070150081c5034000c0d1000d43d9540d5451350507070403180400c1c9441000c07190483c15a0300c85400b01e0b00728548140c0e030300b00131040b0000d1103913128900d140d501000d1710041c00c42e002c0589940d1142c210244c1c1404a450940d160020300c0108442c800040340034040502c0108032140c640030505002812003480c0b0645e41881d00c40c0c4e030f92811406440321000b04903400803100b4 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 784835980 1250 784834730 784834747
    0x312020c030619152c180706110c04110a140f040510170f07031a150904110c060709090c0807081008030c0a0b0124300207020a0801110f070203070b 65
    0x10801c0d180007a246403001c1c407500003a20085060f46540700c00b1446c82c0107018007030070320740251090580d641d5004080d01c900c2d81c21501640d00d6010361160f11a00c030740010748a009a11010303200b10418003640036901c0062090f004200000703001c0c1d900f181c4007141d600800c00c510410641c2d1f4030031800d0154014070000c0d001c001e00042c80350001405001a6a000c01a844406800000000d0308038140b5600000e410030b1008040061030180c101e84c00024000034404c08081c80d080640d500c480140c694640140741000f51345030300850f0540042c041810700303003c00d10f0401001440780c0700041050050001510104071a49042d5945030040c1c40e40d0345c201d941d0f46100031002680e40720044001c4484002d104000308005020324440d01e942c02012840500d85112010142c808802c584100f81d20800100c03600030280805500c0b061156074414401690b0b440c4900502240034025003241364035a0500072560300103171303480e13007103d4612524041c410384a4541d0b100190400d060340e4030168141d40c000c00d170181d = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 784837230 1250 784835980 784836029
    0x100f030b070f230304020f040606020609160b0f0304060908040810061d0420030d0807030c030b01020606060d060b0a0504150f05070602030702160312020c03061915 72
    0xa005881c19260b0311040d95940e0301c01c80e121030f0101d03465009030181c03550f00380e044561600910381043c401130034170082000510204080318155400503005030301070360a11042c032405004448601d40c10690046142c0d05110340001d17140b1444107103000070307000040018107108803603100081050780041913a5541c0d80e2034039103d5a401001d00382403c01d81c40c110001540d4800302036101d4012440790f2212145a9854854080082071400d60003512440c43c881c21685503010b0141410910454903051094101180c000b812956601858010700d8581340100781c90b682c00080c0541d100c01d003190195903e201508074a0080d10155000c440c5e00c2c28046103040c00550881c0203002594a00180c0b1080310292410484400e1200d0380004d000c1441004108041801a0011a8001c0e40c5004035144010080c8200f14680041c1c1c6c000c0d07500042111041104039414802915241c3d03080f0000c1c540c602b07101d15441d0101180519555542d647c5202c2c0344034001c87c89607440000d2110004010f2041950031520 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 784838480 1250 784837230 784837253
    0x6090301110405040e0712030f0c050601080a0b0603060403020a021201021e0306040e1c122c07080127050114090115120b1302030c03012c0f0a0605100f03 68
    0x49201d242084004040c041c5c0c0043c10408485250043e502244036503103003511803076070ba4107042e81041080b008110204104002ca640200942d000130003d00c62a030400300450480600f809200350040b0303003030102107907000858070802601280c1d00c3c0e15401c035101a880c028030800c0750820781008800c51040144e28040c01440c450300b0159014440c10b500508602d45400050942890359072081d89000e42091040d00000400a0f440303100140031500520034840c4803040c81c4910100c81415000f03c22212424450b040082c0300ea00001e00c05140f900c0c81000c1c0d40c4170560703000d040c82111042107009206003500007a5403900b0030000301c0c665052040d034040c041c0006080440c0f03003503840f6100003803520300c0c401c15854054111ba0020003940740d02d407098001c0403445100303980c50310540401042c01c0c3c1d020300c20050001d550343c44954421512a80740c07102c0d01d06e00c0e18288a01d400032115181c11007408103214110380d40c003143c0055140d54a0041c50307181441d5800114100f05240741c040200084034068 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 784839730 1250 784838480 784838489
    0xa0e03160318090501031e02030304091e060911070b04061b0503091506010c0f14071403010f020a020303060621070518030a0201090504020c0102120c1201090504080306090402060903011104 83
    0x1042d042601e8420300c1003920000e01c402008a898490401803000031401880403081c4001c0540307141c15900d03840348007a0380081c074076480310002d502518200201316104110040410081c01e100c0703801118814034107801000405271268401100041c200052030340240c1c00110b80c40c0d1092019100d08100504c03940044501001d10307c910505c504c0d11125104c200e51050300c4c140c2d00c203c886501070344c640201c0e0306500021550f60700c10401002092509100c0700000d0081c0e0490400a02400d20416082d10030b00488000220300c100500b80f080380d408012a50300c80003e40744555a406c0c4076a82c44050b180702024101c50001010610015550060041222281c00c01f0041003c08110042507200e8140c401c0c02804104120704c01c01150816401070031100450360001070400107030540c0c42075081c004442690b031405002400d00c20450001107042e01510541e401004645055a1080c4c1c1520014010b14403c50080000800310350304c0310704075001d02e50090004d01010080302006e034480e0b0454041d = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 784840980 1250 784839730 784839767
    0x504080d051e070203150705090a17100b0d120807120c0c02012109050f06130f08160f030e040507022109062b0605180a0e031603 57
    0x1400805610810a540e0350400000c0036980040725a00d54510651040d0f074201d800d0300804c584450385a40c5102024407400391511500d544080200c1007103103030544d90304882500c03518003c1d103607018800080d000e800b82c88000000a1901c02c501d0002d68140c2d49810002c0c503216a40d00c0c800d544030b600c003001e240213072465101c801e00d0005541c0c0341d02c15610b00c1124000010054500f034000b561003045041c40c140181c504002c544803251034070a058035000c01041c1e0b40c65000c02c0512061000801901d6402240d07028100720650760b83d900c00701e0300180c00c0c40c0036058a4020500d0b1264000c0e4100f2849001e902a00300342c000340075850701819403041400018419858100040c800034000301703040c00b200340301c03a410b120602d40f901d40a211310b07042403c20760740065080c0548916203c1c60910081f00403800030450100c02d040140200650b80d203600620b0050070005451010700415070b4150760440a0036101081d0028500d00f0245540503038100c02900c4045401c1c1c040605070040c0d4011812103000e034 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 784842230 1250 784840980 784840993
    0xa030f0605010e130b0705130e010e01060908060a0209010e0a1d06010305060f041517100b03010917070609020a090b040f05060a170319120b0d0803012603040303050408 74
    0x1c44104443d002190b4107486101c5003c0c0a00000d0b0a507002ca59100c062400e1140c20444c5001417002c112400b60009041007810340014808a401a03404600500d5146081720b5090304101c0700c1c9407520b00141c54a481d443d0080f405840e183c3c02020941100c41d40640015510f550f9003035803804450054030070400010410000c10140c0d4804e005291181a001c0c0c40030412419003c2030000905140809101541050300045181e0f1525049c85000080717440041082c0004a4888401c9074204851188682e02d064440c200040c090303007040c0c0900c16400c220681380d000074208500580b151a1000790701c0303041d070000410103180036131000e18001c0082d1400c100e002c1155040e0800c8510549120358002e030031700002c00c809009684c00d4190b445c081000e507824001420b80d814414044541000041200c0c08207101d6240c19600c0764980d0a181110002c0c540109902c502e803881c8018021005500c3c16044160080758100c08000030580d80301e000c60340e60707582c0c078140281183c0290082580382e00500 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 784843480 1250 784842230 784842239
    0x2070503060a02040510110718020d0c020d02032203081204050712020109050927010e010b0604030218130501050702010b01081f060807020118080702010e01091a0d09050a0f03020d0201060b0409050903090a030f060501 95
    0x5032403b6580c80e1500114034010100c008100000003040140348042400c0a000c4005117401000d030607a00b00f03c01c6608280c0c189407826030708043c06608164541000b424140000d81c3e8845e0440c0c0c2100e009842911007500c803200c1500760700058850b00048415078085003d00c05005501c1102402c80d060000c0080c039554100b002402d102d2484061351001c0740030002e16044400c1c0c80c240f0340240130f40c0030307096148510356540390a4807400c807620390240c0d544001007103603940c000007ca81e2059011100ba103201c0c6901502e0045417100d40501c0f030800000000040c141d038000d40c41249001c44144610303034001c43d6071420203525807200000f01d0005005885040e265406680300e04113490040090720a8410030558051035034110b90304258040d0f4171110094007045080c800c85150758050740d0350003c000c58904000e8900302e041c09105c1c04581c5001b41c02c2049013401003c0d038003618042d10780450252107419400b0f140d802403617840c2c0c1e80400c82c40000401c020403c2014515184208000c2c4416a03a5 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 784844730 1250 784843480 784843483
    0x5060403020f120a0203181206130203070b041d0a180516060503010305071a09041103060114090d02190504021314030a030522031202070503060a02040510110718020d0c02 75
    0x1c0044e0400541d00c103100381008041012452160780201922407036821400c1720b0403d2404c481070300c41e40066005001a0307419800c0034410384000c0d009168410340340c980340c5400000345016035000075048280c088082900c904d00354210100d110070412411780601c02d0317401d010b45c9503175007428020585009881c0c005800c0d406182524101c98005000c5c1c14203070324040b0180c0c03502c291260104044841040752103842e0b603c03840303807400d040c0c11903402e0741d120300d4401c001411000252000d0640c00704148503a040039550f580349041c06580c142c9140c80d80340324000b0641c094281e1600203035440f5002140f44141030484951300012202d039403c1340f121040810382416260782d016000139000a2041003074842c1684402c041100803480f07881301c0b4502d02c1e07584c0c40d64003c00002c9045a03005801281081102e468100851900101c10702b0003140b5052400b030010b03c440b0380b6004100c092040380c07a807560200005028210040581c200310500103508128000020b43c4611809000c50380341040c40c0da80a0b10 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 784845980 1250 784844730 784844737
    0x90102011521050106080615011107030b0a0902040209060f090109120b04110f0a0e01080d05090f1521041e1109060d080f0706061706040f080705060403020f12 70
    0xb00d1440795400c0700c9180b1001010342c1e030001403e039840e6403240320000c1c00741800c000c014461140031040c1c03089600680b00042c400c3c24090500c500a40c1700c0001840815031400009401072106800055950320382e101041c017a0241012156022070045102000c02d0134183c010062440709a81d49640c40da100c421100c080700482c04044c08511070100090001143d0418104c030030080144a85100b403400d00c0040c41c0458140c120000301d03200103004002c907040c1009026aa0101e605000742020303c2c0d5004554401c0e81170506a02c01e1450310641203081c03603003200710f4000840c90806028441e072580620626a20184c1e000c444142c0880c3c848030707540c00c500c20000c1e011640b003100401c1141c1800100084100090b1000350b2241112168400184044c4020a00206500d811036100c4d40c0320300b00036084800e2503002001040003514100e1a407100410400e43c4142d200e6640340301c1e11024107041c1c4480c003174004024110700c540c034140000d140c0c000600981810084088030f14803024500c14150600 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 784847230 1250 784845980 784845989
    0x70b0904050c03190906092f030d0e04020f160813060f0f030506010e0409031d010903020622090c031b0504060f081e130c05010201060303210e030c030901020115 71
    0x4c00000d041403a2449500642401c038080c00d80411a00b210340c5614250240c0309803059103000d140ca61061000800300c900b446441e0048016056005c25820701a00c25410b41b0f9609108550003e8045030786451f010a0307802c1200c8100c0d60065010385440c001100b0340c85201ea42d122038000d8500018042d02c40c99210300c0404560743c44d100d0a100d42e90042c1d000c0d12010304910b05001500744000d116440340d1003003400c4036009070350300d1030600c8010b08a00c12a030b20300c2d09254100800e05400b880980c40b208100c80d54074030300c40041c90204c3c0c0c405044012500c0c5039009034003110b04168180c51020b6064100c200c4900301c00b0041110041003007001d840303502c1148916000b01f04225032a003140c0e8001c50a0550024910401c030040044400d00b1041a040c1261402038941841d100702052100c03d42482c005468280020000181513860192100b1008402d860452005004441244045030001c00d9030700c880070200da40710707070041d640c4580b2500926202ca0040d846e105030100d054203d0320001e400c85 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 784848480 1250 784847230 784847251
    0x3120b0105040308034f05070b0a0908070b0c100605100f03020f0703030603050d0503041a0612061920030604020901050c070e044b0203070b0904050c03 67
    0x83c91642c62180c1030700000c00803943e03500a20380f03000380030494600e10050090180c0f0401403028400c0c490300e681d6421991030912000c0700c0010039000920009091040d14045018a5180c4e20084011035003d1610f0f04918a180118580020b0f0080400081c0c14401c1a22041c3c0741a0060310f0300031803c0b507203580f2449030310412001043c4013560040308440005101d91a01612303103800c0d0112481250f10070380f403c40009540d40d42c200103101c82445a0b80402c850340c9031481c51410242c40303c140d088080344481071280004c0c000314005958a051a28041d0b11035400c0d00c2d0030340b4003e00b01d8559101d619103c5500780f81000c5245c1401c1e0f0050f0258800000341c0d156280c159250042400002e411400b06c01e418803804020303550344207104201071401804101040005880d1516000881900e0311841c101e035008003025100301c02e00300300c40c4c9240c5281140c55804030644c01000703aa4015004840180d018080c104010850020220041040300e20030b84042c0b289844075510240d07035100403100b0319003d = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 784849730 1250 784848480 784848487
    0x804021305100e0c0915030405060f1008010510081b0121020f04030c1d04120f051c09060c080f07080405010906050f07021e0706050c100e030703120b0105 68
    0x40c00d4a680125000880d404010761043e0300c811000760100b1054424045802011803408100e00d044030303011100904d1140042d04504081d030b91582d403690081c1c41598004920030000e121421105005401426010000e000c0307400c00da100303030006240368020000c0a02880440311401c203010140700c0300c4013030185d44540036070b50300d200000f90b160424002002096003c000e904214408840a407000d0340c02000310041c20707460700c03038515040c045203545031000d400d0300d07020840895284640112141203a00782a1281c0024002c211003d22510f617002c1c0b003902d42489544d24602c001d6111841c0d41744560b9007000502a0600c05840140b022200c443d000c0c8004000560b58501c180e00158105219000100c2e55031280c5e40e0341003c5c0c80040b11040145107640041040c050350400c0075884494032809018084600c442030941c540c9041d0140034280107002401c00c490310820003100c10b440c1054102000548410303240b80703499500600d07060700055058444c0348c02c6040d462088801c50b800c140c4a080c075 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 784850980 1250 784849730 784849759
    0x21c060c08010537080f1c031505060304050a06020a031a060408121b07030303092003060a0b0f03070602031e04122009040602030a0f05130807050f2b080402 69
    0x10300d020314104a400c5825a1380d4002600001000500c203c01c040e0000780c115a031060700003448100400061104140c20324030340c0c007142c1120840315401d80c0c40944c4c0c550f96a650b030f4142640b4211140c08003d282034400522000c1a0364181d002c011000400503820100842140420859008500800100750010044201e01d541040d0003858443c03100e0400c2c04003500a034003c1828580a60301c00d0303002c6622444450204001c06642070300040d408034007504d036181d20f203000c00d9a8850080250f0b000302d6035404809040e0780c50001d00004105c0080c100c880071622110001c1d1a50000e0084400702c1444060403641c002c1d00d0400e07078041e141035003079410010905442d4210a00ca0201c144850a0304c4409503008540307d0034281485175000c1c4c0030241c0daa04000d1005c1085400d03445032451190701d4441071002c0e00e0743c0d40040c42c141507000380080303480d83e06500b0240d040c010b100d50b85900c14494103103062900714040c0b5151041c00c004040401c1010703000e0030161282941102c0080d808190121600d1 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 784852230 1250 784850980 784851049
    0xc170a02010c0212161e030504050907020115090c0302040e011511030354100903090302040f020c0703140c0d020906100302160c09110a0c060504021c060c080105 71
    0xd0640600080c0c1040d0020364452841b171442082c09a0000d000007a0900540c1040c141300394002185100811800300d0200060040740706501030f4440322500c501034010041d1082e01612b0103130250484a030ba10303503901c4514031000d0301101c410344081861000c403803032105004410380340b1460a151030407001e003012802d6442d4001c44441c0d180c0814445021246071440740303802401d02070341450712240001e000421f00920303000c0ba504040000508100d80c140000303902a504804030b0f64151008180c2075203c00c186030203405a0f60a40d1494414000c00006001030344d980e006074400c0c4c203c283d071071601c3c550f000d11200f0403c500d0041c0d003090003800411007a0400d0310303040750108078074500182040c4044004125a60f4411016078a8405054091000d840c00c1d10982c400000a10140c92400301d0028006c0c1c0703100c00703020003c1e000c00d5550313001905540394170280f0071660300d00e00aa1520210103142070401811041900c10004640100205480c01c200000c2d4076152208442154002c90034100b40 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 784853480 1250 784852230 784852267
    0x4031703090111030708040c05041a04050a0608011b1103030f06100309020405091e0d020a08070303060e040803041527020a030506090a05190317070c170a02010c0212 73
    0x10480c0390f580308200401e844802024501070201075540303004906060818000014141d001644114940641840240018032510305018030a940c042110742d2400c0303000e001008550710220b401e50810415245540010540405200740b54440d04903048004204c0c075580d00084070740e00c61403040407021810703600c9c00100c001c8003c142c074500400c5c0071902d076000c00c05851050311600700303135440313043c43c102c500c1400a031031154400d120f4014040103d03040802940d0300e0040300060302842e000103c2d0810305200350428005801128104042418035140000e8240d104171001e403000d08104005404008c1c00d070084e81140114038280c058401c00c0404201130020300303620102d90041110100000049081c03200620640c0c051016041c420740078101036040c0000010940c00041404030440c0c0001d400400280d90f40100982001d803a40e290981510925402c540141c000f03904003541d4000b0341e5002c0001c19900086038000d21911045082c02c0c4c0c0c0d81e45440d0032014841d41c0038003001c3e0703000e851171240 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 784854730 1250 784853480 784853491
    0x10509090c07020310060503151b090d060501060905010f0315170327040e07080607140f03040f15110d0203040f12030f1a13050a0b12150c04031703 65
    0x1842c0340114a5001914204402a5508540c0c6e00c0d124204198036090001d800c00c50703a001c010569600c3c0c81a0400907661200c0007040c862580890022100c0e107440c580c25254580c052001c0100f940c44d00009040740c05a44a10b5002400c07807070710a00c02ea0320034054548600c640c008009150341c1445809040003549118032021403005111001c503003156810808480102104072081e01c1c081702c03042c070054880d00000190744d6440f100c0100014107002850b250700420318a0100320001c045030b28840c2c9413041c4420311028440c04020700007404220b14051107035501c240c61180049101541001c2664101d00182c01030000a00c0345021038200c0ea0000d60344241700301448842e50707206503a00c3d200d0084041001000036603079055284a0f0340d4038800c0c00c5401d101420180c2981b020304000508108021101000d8075440300040b03451800c0c160003921040500900f900812940e07010825503461a1b00b071242e0180c3c0007240800c10003961182164190781d08084141c03034140000700c5046059101401 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 784855980 1250 784854730 784854751
    0x151f0f03020c030d021206030c030d0e010903020d121e02070b0f040503070611070501050f16020432010b0c120f13030b0f15010806042c06190b01050909 67
    0x1500c0b04200148003c20340342c0d95040c40103032a40340d58001035407080401031010b03000fa40070541074a4280d41c001450780405e03480c0d140000d10680d00a004031350b03541d07599000940000d601c0c039800c020042e4030005d50154520326941c4444d0060183c0070f40790520902d1110b000540c00c11801030244402c0c9030014480551400c40041ca03203070351807011038506912548085e0004007408800c00d11302c90140b059000410b001d20700f2074140b80308000c100d000c510031100075003603100300d104450003151515000369080741c15500b14101c0480c401400306003450001f41c200c907440c02e032107000071038442c840b5002d50b51001c1d1004004c02e10450000c100038030590004943c122020f200b803000c907040024800e02c039400341d0701c500341c40c002c84e0905481040c0d01d184003801140c210071044644000300d982c0000d60580c001c108440c0429002913801008080c00380b2a070785001e5888481c0403940a115000411902804a040b030300800c0d00c4481ca0000d0840300114201400250b08001c2c088442c070780072401c90f40040f078146 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 784857230 1250 784855980 784855987
    0x1e03031e090305300901050f0c011404051e160302060319020f07060b04140a021c1d06010b0307141c2306010507020603010b0a0c140105151f0f0302 65
    0x12111407074a4800314000c1d0050700d0011507000d88441e680d04252100e58801c1300c2c24101041c8a001034100e000d202507c0384c28030000f045245010310300350840441d10648464034070080c20310f0b0038040d8450b07190f030f02002d1010040542e103940c801000a400303240d41d42000e002040b180e04660800c0400c2d400584901c25149003401c907050645603d01c024100c0f00d6541c0c288903a034a00c80d144c030300c054801000b0140c0c800c910300300e41c050108580d500c1c2180c0c0116070000c016035070200e640ba02d080f98a03c0340035040801c0d29010003030304d02c8021541000e851b09216022145507a0b80c540c40400720b032004440401c00210401039411848031041c1c09041a051401c0c040a102c80d681882d00701107407807443c014198801403c90025004030300700f10346134000c1400c0c0b0300720707180029540103e00640301c1032190041c0410300003804039045100d0310801148030760000c0d107005441001c1c003038240601403e45034000e01d07100900c1145000e01d070000f02900c940a04070010702a000c0d401000381c030741c01c00040f480f00c04d054082 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 784858480 1250 784857230 784857233
    0x403020a0b011e052e090303080c03150f15071b0f211a160f090f0e04060914032502010e040b150d02040807080a080405091f0303091e03031e0903 64
    0x1603080004158040e1b40700d590140c61814020420702014100c40940c103400c1050082c0d19000c59001c40701e0210646149007255980b02c04100e201507001c0744214007000202d006030800160060280004c140f5803400100070340c850684c1e00c40018548140940301d2605029172803012201d60402034540d000f42c5101d443d0a030a4010a141004119212204c4844910f800b282164011ba0349502da81000d1805030744990030400e4402c603410203405101d102c2100f80001804114071a00924001c41d8880074805c2c441781e450a03160390301d07005200c0a4130003125252805684e01498440c00403072a405039a604407400580c0c040c4801401420030590b001500e9400d032201401400303004082d440003005005075035900d0a900c1078141034494108881a40000003001c1c0400c05d031030141d500f900c1d41107a803044241c54204031006010110000c20b004070070300c40710010604d0780000c0840d04440403012801521441d42c020302c05260000d00005000c02c020540399500d401414a013400388013224108216280e489 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 784859730 1250 784858480 784858549
    0x105010b032e0e2a0405150d020d0b0907030504080301051e040507050d0617031803070f031505060d0512030a0e19030906080403170402010e090403020a0b011e05 71
    0x20790401d100fa20b40c40f100388600244000300c00501c0911071381d0740c0c10f80c41800784241411480b540c81090f104803503000148103a000c20360200c1d5901a84408119603031080801d404d40900f08200e130300e030b10035103400c000a6480c50003401100d00c80d17603100d0f00f000d00c1c5038201020880c080d54040025880300c10400406489904e5610840b406010903480e480c1c1c81e4a64144500c007a1900b03600500050600307400502d1602e8000410b5800742e4030504e02900381009000c1c0840d290034800c3c2d10000c02c0107140640002403043e1483d04190b440d01d1802d083c0320746c4c2d40b080180420000c0d10400109581d01a007007181c0707501c01c030b03201964018000300e00200e69081409d000510300303070118000c291125007424940080581100301c010091070700d030a01f11054603040c5ca01402d841460721044028a069600140071607200c1c0b442c844002c3e030003c2c00320105003001d0a0095a8651250f8119030409230000003294a050210800303440004d00b108208015092005000184070042604040d0080307840400000551 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 784860980 1250 784859730 784859821
    0xf0309080705030a180501170f1b04030c0609090b0d02191805060a090e03031b04030b041b0503070f0b07150603030f120504111903150902120105010b03 67
    0x280d82d91841c5d4280c8600642c020300810a41c4854180040c0c0350514200c550803200700c5d680300070341c25047c641990b0348800e4500c1900c440d00720070041704c000003000300030000700d20419020344505907a041011502c0e0b200540c11150444001e0f5404484103011900500e42a0029151112081c01b04154071b80c1d1341100e40409611034000900f111307224420003446080501a06008201143e010f00040355a00e1495469200c083e0010000c2d411401c0b500041410910440c0c0007941c0c030208550b0145081e0822005031100c1010310580001c1e81000001c1c640740008a810540c3d84461803407890910f0486172070b030319900c52441203a50000102100a608915124120042d80261651120354041d1200104107044005200304424502000d01003c01c1c8255150000a402522040105603101d5112015100e00d9440100340406100c26911083c803240c02c419201e5100369000550000e03641041c07402e85c0d80074007582138000d800b800054984094040240c40158840149001c031008010340322144a8 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 784862230 1250 784860980 784860997
    0xc1232030c0106061e09150c02060714010e0c060d0c020c10111912030207050a0b042306090c01140403080301030812090f0a03051b150610020601060f030908070503 72
    0xf503580c0d2042101070b4020080d44400b12844402d41501c480c0c00401610ba03442c5802030000540380f10041501090203003d03414620b580091145866a0075031070460702003103c20047c078a0359400d00c448401c40f0140064008040d1000a10722030070009000d41c50b00c0280000f406400c11441007410315402500c0702903540d84901c04550751851050b1402d556a0301d4079042001c1901c60503103221600d0085005a100c40703d06841320b00d005a42c6100504201e440c0044940014080390140014001045040301c2c408044699640380322510081e0340c50388070b445540844030100365401c1b440c80074045620a06051104c00c0c100c2c0c0102c1e040580f251641c4005400982088440030b00c0011880d05903280501c3d060390080c001801000c0140c0302e600c440d40c8420382c007100101803200119142a92651001102144e40d482e8412584800c0300100c0c45c5030b18540c05d860040c0201070512569504910100d2001d06031162a11100b00b0034142d0702044001301013450040d036514005100340c0000a0040c00140b4603403 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 784863480 1250 784862230 784862233
    0x150b04080109060c020a08071101140d0f1b05040e06011403090c09060d1203053705060301050601140306011812050f010506030a0b04050c0a120c1232030c 68
    0x12107245808000c65132919805002d41d4882d21400e000104010201c0307049651018801901d456131200503200100b10b8900451072400101d5442c440704440c3d03100602c2d8541c510b40511000d504e2040718002081d20b509001d0000340104021300002504400c4150849010324110103070b4080c000c400b10b0036070020346d0807000e02d42084103140b0007490448845030304101d00319080a50103066070b40c0c2c0d07040040440003074028151071b2000a4a038110aa6544003001710800074507505d40000c00328000001c00d8111040f0300d161420300810240d045c144a2a0b20659042c9c5503100800d940e18801d0440c1d0300010003050400800129412010029a00750401841d1600c19054007031020329000d410440c007200c902c1c000742c0c589402c100c0555400640e064104e070700070b00100c40503100c904009003000c0c0ca84580b1608107024007400540313184265401d01c9030a014100342c2540503201e081441d000908450098100c0d1014480d0a0361520820ba804140000ba0480f10b001c0041c10340509045421031010050b45 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 784864730 1250 784863480 784863491
    0x70801050c041e240908010c0903061104030506071b0c15020f06040503091003090807032106030b060f040b1e181012140114010f090c08040204150b040801 68
    0x6050344001c140500d0f115042c0c216026410b00d07016407941e9003030000c80d40740c050b00041002d0b040d41c0200101c00c090000103000b401001e0040d034014199031000d00c002c8503018540070322040034241c00030507282600d920801030320042d11500000c90f03003c01000d0f5121842c80368868004001804444544000d0514000e164002c034088000681001c804144840c0250859010080092004030840704009401c45411901c2220728030118001e0180c010000d2803a800001d8440034175800110b09801040c441c410b8165520b40c0190003001d4544900c4003e040b1001c40c40491803a10340702c4075190000b080a0320026480e4003d42c0003a0010099203c18983c8003403140034242d990a2032101181c021003801104000c1d4103081071000a02001481514005503a81d060340d010032050810070119404094002d001074401050005a6400d080c4070b1409000d80840001800080300d004400600a0b02d031942e0226540d15000d0201904a01c00c181041da0404480401c141c4021806000070700780180c0000346 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 784865980 1250 784864730 784864739
    0x221703040b011502011e1113080303010519060c030309020f0d0303060603050a060f050f041e1a0d030c06270609050c0d0506070c11090702030a0e0109050a0b0c070801050c04 76
    0x1e180c1030f011500d000b10390411415100c100c036100d00724048032100e103200107090754a0310f60001c00c80c00b482c054580e840c81480c400265100d00040514181c40040f41e0111000788400b085042582c41403240202241e071403040f0340082802644220601400509644101440c58001440f03901030030030200c0119540d0082413143d554148501035000819000801800d1f06146240707500178124803400e8852405045240c0f07507500e494115050740b070b9408040c2e89800c280000c1d03a4000e0564203c800340300403100c0002c01000d18003206810485038042c0c0712810780c0b600a0300e07004060b001107000012444410a1801445200c0034040c215050041c140001c15181501c2d0807410013090400d001d2084c85ca0f07194460100314003040241c1c00c40b4841c200401d9035022440d100000550540c1490781c41b894581c10007000540220040481ca0980d9135a221448001001034801c1003072030184503003209501b4420302110b91044000e214606c0c07403104945000e559000b4041c00d40794101d4036103000f008041020003 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 784867230 1250 784865980 784865999
    0x20f091005130608060f0f0d020306010312230313050a02030d0f03050606030c03010501180909030806090f0f01050409051c0314070302030f19180b011d221703040b01 73
    0x1009000213141c40001d504103d40000d00c0101030b403481e03d20804402d0000c10840e0b8803090404011035010707007601c2d0150303900c1c00c0c80e016410354420104003045043c541107031a4005041c45501c2c40201c1170335507040d6250b00002c40f8000281c1c2c1c00494040c0b040303040090140e23600b0030074450000803980e601c000221503500000e05444019200314080e0000b4002e00840b6044807082d01d040d2682840c10b0030304601c224201042d031401a5005144a505e40003d41060543c0101454450401580c036481075848416032100c00420464000039039101c507800600c22850305402036070a03603020384125541a081058510034000c002c050060100c0d54454010001110310400309520a580341000c47c00c604e030200700d8151081001380184840305e103001c1801507a540580c0544d1540d8034241c0f2440c0070000c0340c5051076a280c42030040101c00741159828040b03490741c03000d030307503201d6140120340d43c0180101080c10398400621740740031903240f200340040011001100740038501c5107000d541c4802413945022540ca = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 784868480 1250 784867230 784867267
    0xf1513060e03060406051321110a17030601030f0f0203061507050c010806150304150e191b150c0b0a0203061e060f0f0c011107020a0603020f091005 65
    0x803428092034000c0602190340c04140c0341e500030f03000300c804034040c0e48201c0c03105961205460002d0a90540601030190000003c02c055200070142e00c0e14409800090781c404d60764614004001d000300c1c043c4280d400d8540c0400050b54100b50181004100460800c14042c01d884407442220340896000c41004901e00d400c2e40c003c50003c5840e40503610345403042d00c8003034a40c1c80422516040c8000388012640d1515018030307000e181804500700907224203042c605118110001c184070304003203040145004420700c0205d80c02000403c42d060b007034181c90040e600c0c022740030b000002e610611003d000c00010442c0305184080d400000c507030303110582c03a0550b140070365259202402e03280c9282d105108104807501c801d40406c1c0c1e0584400b10040e0982802c50000e4150310860800c0208a030020030400d9885901d80003131702c0032041c484001c2c007072510303580403504881c001d1304004ad511481c400c07010441c03d4081d9000b0807000144c142a58a001e20a1020802e407043c1c0c0000d0703000003200024011115000c07001003 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 784869730 1250 784868480 784868489
    0x100c031b080f180d030e0705040207060b0f03070b12150904080705160f0b0904090c090f180b130f05070608010806060316062f01021b0c1e0f1513 64
    0x31001c240386542113941e0755131310b840c1202417654030850110825020081c00c1e004002c014400c2d50f403103070240341441c040c00d080102180110b500d075070b40c29100e02c0e000c18100309a90213140c64604010071204150554100907100044808003002d60700300a849036030000e0b04c10f41c0161190340c1d0f9000c41e480c00510342180c80e07000648400300303000107110600840551200710b5181d001c00310703200c0c4002c4000400400345810b00900300c40140d4000104120a50058a240c45103c4000c0001070381d110040ca40400e10b04a00030a109100d41c001400714405001c00c81070030380244600ea0381c5489a503942c0d440c0034090740018010610080040100d800c08012560b40700105401a000c12202894191940c82c014003919080c45030350103e03660081415420300c0c0c401403500c00d64030f001c0000580783c0c070300039401844614500350310340c90a64088800061600c1c8010405000c8a04080504040d080001e4104211301d6020201604d50540e035507403c0102c001c41c0e580320203581c0d501c0c14685840340000100760b20 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 784870980 1250 784869730 784869751
    0x11150c06060111010f0501060f110102180603130501020304080315120d03021b030f0c0f0d0903022e030c090614040e07020a0212010e061503100c031b080f 68
    0x41214004000c1000c541080d002e09104400d4030140914502500c24043c900708194504000080c115038043c00b040884996032711207601c0500b544100600380e106100c00d017403145200c1441000c86040c040001d41e8003c029410f00075480401d56502c600b6a401a1415036094401006114168444603444a0300349000c8032804400303d0280703400d5485201449010b13080c580d001c100c00684102c001c0c22486c0901c104416641c4d900e0080b9462052500f102109003e07a2090031034081c681c40000500b8800750b655512001c0000e03240d80d0820100082e40f5040000301c807441c2d061008020303524440d0400c83c4980307490208105100300302c02040322401c0d83c0300700b08200c024000e40c071845032400b0448041c0d40e45088000103603a51450709030701d090204000203420000b01501d030038007110190b008010144111080d1400d585405035032410004806001c00c0e85078000e020b0300d800600c025801102042820300b0b01051400110241c8103840c0040110355000c21000002c010843d005e07800619802103a418 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 784872230 1250 784870980 784870987
    0x224070e0a030f020409060b0409141b010c080a2102030f091207061a0d050703050606060a09150201061715090102070b060d1403030106030b091e0a020702040603020406031115 77
    0x45520300f203c004504003900503070750f030400d820900c0013541042480200180c4203016100075450040c0840080c50003036545030080465403252200e040e02864004c0c00141e482915146e29916601c107250b100d1340c180b501788a080b03500c0108010351094019490460108010b860345031480b0008104e50008251444980000c03800d031445d011800155034040d50008400280c40b040301d100444003856031541c540d4401e80e6a5410801c00c03400144100035070b84140c06480c0c8a0b01c440e01444400e00400351640e01040841d6400d100b031140e11038480642403c14030012550170360305c5500107410316542020003055000360491201e00081509500d400c0340c2c1000085151100b15210003a1006014008904c10380941d1140d0090201c205200c3d40c0c5004400300740c940d00d580d503d001400410746020f0703140c02031160310000b5400c00014030304480005072107010a181562003100100082d4414041241c1c0259500d034040056100c0d032050300051481a500e00c0001140503040000700c0c5010b05100d150b143c401c1 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 784873480 1250 784872230 784872233
    0x201211104080f010e21040302090a0e0f0d1707022d0c0604030807141216030f0f08010323011103010911040b0415030906090b010609090606050909070224070e0a03 72
    0x3401d16031000c851403108045443c1b441c058042d4820740e4000387d0b11980039001c2c40102c030050380c081901003002c002281c030b0803580088230603101c0c40b01034503c5d408031740442c201c49582e140858505502c100c0d03030310586040c0043d1103911904d076083d00c410854210610b10361030725001810880f1380e0145034120341c5517040c14656910140d4610410600038440c03a002c10f00b0091501c0b0800104c4426400c0c580e640e5200c501d101d1203660380c510507903410b070300044000005901e560300030f4203a604031200540d10340303105a086445000744400416031100500018039a540580314080c030401d00300710320300c002ea50340d65403410058030140e40d010119008018420082004514000380449085070602144c00c0410451131070140c0042039281005040396051003040c504118107000c059040c0d460b262075840440b42c0f0b401010007100d840d4025a4040f8804000754101c80c50000e8403550300c12461303c1240c0b00c2003221442d5031451605400c0903200141990f00f40f006860700081d01c0b00c0181e509654181055107035 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 784874730 1250 784873480 784873483
    0x604150c020c0f040902010504080a061a0114160c0f0602030717040518060117011806080c010f140714060a0c0e0609010309030936060806040201211104080f010e 71
    0x20010400c0c440e035038071005c031350840e4010010b0764002c100e240280c90b000c980768180b5002602c0410310b4440740301c62110100b0384035030140c080e0000c0e42c41117143d400c0c2084580403003501d0581407058156000000b50a0000e564040f20400c1c030080c058a0340030b95100e010307034500032014089002514064010038001446640c4642205034642c0c2d0340c2650f00714440d201c0d00010380d644c03a024140c0c1c3e8903a074031160000c07840e80403015005284ea00242e100704072040d41c070429144c852039040c00450000b140000f070320f004244a600c441010050202c0c030f0074505100c5544d6550024042604014950000010040c980c06e151040d401400d00c141070410007d44403100141c906d109580c04c0b20306040ea100d48860504d4821403600000e0105c1042d8010030322441007545800701000f00000344020541842070482c05903d02541e8100e94042c802043c580d1a5940155070b444030740d42041180202e81100101c046055015410011000039010303913582e41000c4e901c03410140400d078401c006038101595000d50500 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 784875980 1250 784874730 784874749
    0x30806010c08092110202a0d091403120a030f0c050408240c0304030c1a041a07080105060f0c01061509170303060108180604150c020c 59
    0x102441d0806500159103003100b040c1c0038441c0000d401120540c0300d9540a5403945081c3c0084003603208444103c041d000c1504240c482400711200c02e042d060300360100f01c014600c0580000f011210f5400e1010710030b4003c007200d940328404810742e1070b80500100d01045405c0050a0050f004914410307818240c2c1c000440d554200040c8482a010000a10881c40c54480c0d8040c911201c00582c05202d00030913180f00800b180c2240c01016014020b20700310042c54440340c0c400c03030b00c1c10200c42c00603062659603c0000d400c035040180198140308907180c0010025140071f100c071071041c510364415035503820f090400280c400d20803070781001d6119402046c804842c0d00040c5eaa0304440c1c00f250a90398801c00341c0d00002a5004950850301300e076007880c0e00802d51050902c50954851410b90303a5aa41c0f940d603410382e0443c00c21810080089420405c00708406500c41c40da01a803180140c4200581c0100207508a0b02e400c4085505135824418540820003121841c080c140c40000188024a0340c04011000100c1303c28 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 784877230 1250 784875980 784875991
    0x60f12131a06121915150920030406090302010615050d150f06081501020304051806150a020105330f0d06020a0c0312060b07060915020c01020901020115030308 70
    0x4020a000031800c0c0e49070f001c0342c2140c1c40110152034426003c620110050300c1221411505800c94090044403059207103e03a8411146031500740045920348136401c4024844200440d04510791030601004080c034140c011402148034410000c0c40c031034681802421210150042c044804003003001200480d404415905100700540002400109120041c0c0003091541d0007040052140c0078001045074008000c0e80c07280d58085581034080301010012600c134461070084581c441001000d01948c4004e1088040d800b00c00500705400c45096075022034072076085040c510006030344540c10804c0b1051004107082200c08a4207440800c0340040092014007292180711900603042d190b00079542d03a540c41030105803a50030100c2159180034503a0000c03c9444840700a5010445101d809400441d0520455048500e100a22420300c0b00c030342d0f034040181001d138001703603810100c0c2c440c1c03880d2005040c4000c00341d40344034100050350740c40a100064255400100f861001214541c000c001094000c0c54055100 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 784878480 1250 784877230 784877273
    0x302120609100e0903090117041a0a0f02040906060f0e0f060705030712020610120b0c0708120a0501090f090b06060a090f0806010f0819030e0f060f1213 67
    0x395240901a40342910b90351100c02011042000c0c019142e1002c4001d11095030280d8801a04100e14036444c001030400340c034010213800d0449400d041500d642c07007000d604581c0c00361021503030914610b62041603070029000941d02c1940c480c0104a0307241c000c03c0e15111561241090725000c2e880c107001039513030815004004d01480d4000341440401405000300d400c01c50344240499106009039a0007035445d031044404050603415135001040541c0d020500f11000fa0740030348a000c0e00e95512f100c1c40402d8120040454000c1c10a004992406285440310f600c107043c0200005030303543c034080d001c005460001c0800700c0c00c186800b65100200b01c0040d80300d6402041605e10780ea4a043c500011100c0b01d0196200404180d0b51200200f44400c0205015040b1512100031031006130b261000075460b0b6854090880704a01c1c001c000310000303070081c0c02d4003946101c0105011003d5000c0400b28103164840d6503e00800350000800c1c00e9078015000000d5000b00160f2801002455590785008400c02c1e004100c1100 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 784879730 1250 784878480 784878499
    0x402042d0606080a202d0304020909060c1e040504050a0e0607140403060504021f050307022b110f01022a0114070804020303090a0303080f0105010f050714100203040c06080703021206 80
    0x900e1109183c1d00c582040300500d070341b6880c0403175440050725082230381c04078460700c01140030507492500010090701601407400403a181c201008103c42c4000c55102c00021108410300c0001210354661041c0c0c0d10800070600045030307070490001c0560030002e00070051f10921040070070b40c5074981e00c11002c1c0c84c152648a080094680c9641c00000c640c11400c2480d07111804021120070b00040e4094055402184550220307100d42071591a0740e54100540d0700ca400c43d09103c00f080d2041544103030f141d211135007a0340041d40c00e1245900c00c200c0c01da80c410301004080d070000e5490b02031910128010440e030500400000c0210b001118401903040401502000c1045203640126003035550134021901802c0c2d0007010403400d07603900d140c00342c4040320840d80204411f68080c00007459501954041c0d042921564840707182011a90300d07042400c42e68041103046100311000c001644107540300950040d400303608299002c904d000c40081809200401d014101801400150000f02c024212143c00c41c0302102c0d444107 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 784880980 1250 784879730 784879747
    0x140601110d0e06190c06050c03041203051e010f0609050301060e0f0703140a050402041416200a0b01050916050f0714160906060503040b0402042d0606080a20 69
    0xe142c0942210304040d6460001c9a0310641d0700000d5005d10544100c02c1441141e03249080040755000031074019110703412280d4501c0d4040d10a038000766006400032144e4003030480c0344140c0140810f0907006240c0001d0f00c03081c103001d0203800c01e5581000380411402407050b60b04001500041d110301178881ca040d4020200403915550182d04000d1145481071b040c01e1061a20400e103102404007078400b03074001d0346460640a045504809054400c550300401c03214404c42041040f242c5007040031080305030340308282101180d82e0050106825407405148602083d5062104000240b031707019199241d00f240c0c0c10b0b0100642074000d82a02c850980e01034100362070300a0f03401d1814000701c811070748030f80c41d000b8000300d80c0c0c040040c6054242540d503c9982040341e40d403104420790b11440305a50140180032124000350052a0903007142200c50724249240841307030010407904214140040400d2070103038443c40d0074806243d00203201e503030180c0018801c0c451802c1c0c0041c10746c9003140c480044140308200150410 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 784882230 1250 784880980 784880989
    0x30c14041104121a190c03020a090e07141209060603071a0d0207050124060905011413030c060203221508041103030f070b060105041802130315140601110d0e 69
    0x5100309421300788091030324206065402180e00303414054006071429000c0820680300340309452101c203058590b40b0580c0d091070214581114010500c1c010071100c20ba00450044110010b003004100c0c80101800c5820003843e01820a64000d2100f8007d40c0134210400800d24031507070050341c01460380050f83d41c0c1c40c03220381a04064410000090059804c1400300e500f4100f160f8840002c545140075a0f4031680d03101d40048801c91610b00c2268005a0350b0540d00c1c40d80702d5442c00509070b010702c1d01c18080300c4645c1c0359a01c00c00050298003150241c0c002207071000c0c0e0424242c1203400090f04c0e1544c007180d003a09000c0c410107940b40d40900581000b44990004003000b1240b4a03412414900070105c80d00e035842901e01302d000c1d034445c51045401c3e62034038001c90a154094000e44042e500c0c460480b9940c400140c01c8540250081e044880101d01c400c403002000c0341400c050043c490f11504404522014607040c22944050040c0c0031074104420301d1040c0105501c04107040610307000b98648181c61404640004c1c = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 784883480 1250 784882230 784882253
    0x61404051b040f09050d09081f051302120706080f04030504030f0507030b01120629060c010621050c0f0f12010905030a11070e0c042d030c1404110412 66
    0x43c00320714034100c020400d0140000d14118144416500c46154a031910702182d201e10100540168000302400c501e00c0c4414141c0180398001c0d44100c000344044200c0d00042d02841003540c000c146034212160074458a60720080d080c1d8443c2e003210469025040c40d540003002c40c0306901c00940052092080e002c100300303007070140f02d0085811030000c40aa58482c1d604210785c1d1190201215494508010320380f84903010005600700071075500554003042150414084e040c0d000420303000780c1355078032100031545025408030200481030400300c01590f0710141c81c00924094018603107600c10200c0c070701c004d44d155541d481c0101240f0010f8941c404141300104006014200300b100092240c040400e4980d00c15030311001e19034020481c4411076010070b542d14469000c805041d2004043c01c002004203028010b0001e9844081103484616081d10303400c07402140080c080c854004542c8540c00038020804440b210944803030702103046404021038082104440498440d0303209404c6007005104946082c02045502d5 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 784884730 1250 784883480 784883501
    0x60f090b07060f0f0c0e040b0d0b060d05100614060304020a0302221805070527070905030a150b030d0c0b0606190e0a0b0702210f01020d09061404051b04 67
    0x82c0103880311340380350102801240040400185004646150602e400d000d81898803402506800300034080e6182e002c9119801041130b074000166031402000100c0400880d6080d1408040000b8014140500c0512512025200030b1046405106110140e46c40700c00034000c0301d030304850390501e0b003a000524800f800703910101e40784003610f81041c0702c100464100c044881c0c0c900c01c0d03044d203070031903101c204003c0c4420a040745030790015174400d5902124142c44090035001803035410250910381da036000003071404240c110119000c400220be40c0420041a01810000381c5017140500b90300482031400425611203103001914030b01900c400304065841e01f43c00c5821b02c0c9240a00445d07680401d0f64090890074003e065103010750140040010700c2801c1d481500d02440c2d0051549008207000500d0180c101e142030307444d9080e801003d84809141b4002d100a00c8010042c10001c00d50030810308101e41100c0b00380c0a0b0294544a078002c0100240d00860901941d50030802c2c1c3c10441d00500e0013090003490084507 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 784885980 1250 784884730 784884761
    0x51f1503090512310b040e0601030b1e09010603050603032d0f07050c0d1703061503072f0c0118030602120a0513230a050106030c060801060f090b0706 66
    0x215803900c4c200881c600d203403240b4441491403907090100005000c0302d02900c40c01021090900c41401120310408059420000c140b401103500000c0d54005a40071182c0c0c600d50962074503640d0360309547e0030420256070051655040c10001840d100001c80d403644034409010403031750555041403800020b003201c1d0720400c44400300d145446c0c0e034140903980240e520445058801d07102d81030707019500e4036280c1c000421140d8483c940384944002401070441a4201401c441c0d440103a65041c819030091b040e0240d48984007540d11000c01c1d58601107803061245014407105100d2400140c080a00000082c2d5600c455000786803030b000741e20b80b5184680c0e107083c1c0e0740c00c01400345000040741503000c0c1160340070601070803600d032007001140c841e16140351110680c228010000c210345844400030382c04e400e0081c024040703488156800c0e00450358031542100c601d50811100d5011700001442941d40c000515805080d4506240940c3c0a01d010040e21501043c0b042c500c501d000001d2000801545410591001c0604403 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 784887230 1250 784885980 784885987
    0x509061308071a07021c050c0d06021305030c0a050907020f07090b0a08010c0e0f0609040f1d030301060824060712030f0b090415020705060406051f1503090512 70
    0x51002d0700c03008648a030301c07045608030150805148030581103440c041d60003032000b616040c2036115440000c103580300c01e41d201d000301ba0b008030050321611f0101d1038061180200596034090100100610705c21500700e80c0c0283c0c408505c0c03060584a0b05e1805003907590480e80c1500940c1c40900c101c2c5040300c03400c01ca846074020014002140402c0c0d800c554410f040c115012441030b9103404c0d14a08030b0b40514003110004a109007440d82ca8240032038000301c9510f02411403072500303084002060540f1300c0030911282541d55020020b10b0048405e02031700f82c6502e02c0d00514955450b00c0c0c0300401008000d480c1c15444d0461000c000d00d581000d04044120040c0604a540c41f01064246140401d0b4401e9100780468203203060b1051400d071078031070080000001040001140c40740c1d1101041d9440d54510b808240b98200305c0354010940400400d407142d4072a04002c41c40e4a0705132145c10340da0258041d0362410206820062285565613022203441ea6121710340003e03d6825404c003c4d14010805019400301c0c031002 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 784888480 1250 784887230 784887239
    0xc09040f0f02123a03110c1203010e010f060503150f13140603010e070b160f0807060b061303030804050a1b050406080a05120a050d021b0d0305040302070605090613 72
    0x115140c0c1c0d00ca80580310000c0e10242d822139070b40c00c03c0d2010b00510034100554844a0005009074040c050200001e001c1505040104c00c0b80342c68420908d07820380104202000400c080359000c52203d000d84040d103a003142d030515141026000c1e00001d40f2583e00d80703944806d24199030311100c00003a54903000030080c52402e416180404000e045203d035408890320b14900003080c9003014081c4d100701e010444000e0070a546800b80c140c14541042ea0444940b04584030500d011032281c000d240041402902e070306540d0841c41c5001003c480f00d24a802d03010300300500c000706000720015110011641c144c20010070310340d10f40c41d10703606040b641440200320402000c0000030002c1b01410b6042910b0301590108201c81d100e0844d1541d50040e1000144280c0c807807030b103003070b001500039003e0403042c1c0e0320b0305210b41441311007146007041c0d80005e02c001e6400d0f650070101c164055010898641c40003003074101041030b41050f480013500c0303000390701502081c403000080d1184151100c000b210b04164806510301c4105444 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 784889730 1250 784888480 784888483
    0x51507120f08060103090506070507081207031b0305040b0402061c0c081f0f140d0f05060708060d11040c12020c0106080c032407111501170c09040f0f0212 68
    0x801c04280000e8400400614554001c0c03203040101600a002400c00b0341d6031410448055025030011510040706100e02940201d040000d140190459100490443d0310440c41000030300b8403c801404040c00c020074000801c2400007559040758041d206a9610f040942c200154900a05c82c941c403002d04c0c114000f24020f501c007180c603004807441d4620001420500000d40d5040f41a4012203590401e002c0e02000540d0240403030307861422001d0300085410041d030720f171074090b801c448a007502c1d030340c001c0820003502c181c0c400310344c6502050440f030358070100d101902c85011400e003d103081030081d5a59140c00190038050101292034000b00b00b015580da4190846413406001c039413251140900c00c3c111079428514000c2040b80f00c502d031600c07405d07209413000d80f500b510040c1d010784460244410754070034404000b802d0200d41042c0240010f121b00d1549826006030503901403124500d02500910001c445d40e80d9202c11560f005500030392000800c81c4c0794100718031044070040c0001d40c08500548a400c14140 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 784890980 1250 784889730 784889747
    0x120b22060503010b030c01020309060c01140a0f0c091202011202250209090109030c030c021c060b090106020115142115063106030b0a020403050f0a0203030405150712 73
    0x1000d0b8024000514242d0038035580b0840e603602c290160700248580a04c41c10160090402080c9075000802ea40e503850f0b101c05a128000c1d0350681c030b050345030380c140a0081e2440c00b4040c1e201c5c5440c42c0c81040b003450099100d260f806000030090420007855120070805183c1d0b01a1501d82c0b17041001443c01c03803050815640d5445290004074080c03c000b400142030000c040c440c100d03480381c1544401d114100386035030450340c02a006e1001c0360300202c5412039580020803101c03680f005a00c503c0c0c0014400320802c003009040b460591043c8210780c1080301004030810500d984030200c0d090744072842500b107041c00028000b003c0a6010014641d07143c4e1000321403a9000130449101808409002c0460301c0e800c0500a20070300000d159503480c588044140d54414603280e03a00c1005107596030001e000ba4403a5507500c1000400d035045003e450f0041400d0003400410b01009500104a4004060031049580400d40b24002c41c0f0505100d81d40410390711003921000012100383c039501800c00010003400d080c01503c4401e = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 784892086 1106 784890980 784890989
    0x13030c06140106030e06060a1a040b0a180b0f160f06091412030906010524030a021c15030b0601090f1d0702030307120b2206 55
    0xd0322031180c00e00301101144240c10652410034000c050b00c804a03918800d68000344140300c4030381ea07071040c0f41c0c044801420000d50b40b00c03240e001c95540e9004550001640306400145004181c0c0d006503451180600c0f138801c16425900c40790502d0382800b0300805c2c00541c540c10090119401e0300346810721541c0e4070441d4000800011503079018292154240c085403521141248040d02c110103020702446841d0b03804090782549841030290355605010310504d400b45420086059400001c049c660143c200e0280e041996030500004040082d800040c0b845440b000c00100d41ca01d4071818002c19001c0c20701c0c00000040641140c541c4500c19101500880c140300050f2400900c01d40050fa01170000d202c461003500d4503100110381000c0b204030040a82046400410030841007581107424820007401d040c90028039640164003003404030701040b03001072010046480403540c4509682042c0c0a03503 = true := by decide +kernel

theorem cover : BRFrame.Cov 784712230 784892086 := by
  have h0 := BRFrame.cov_init 784712230
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784712230 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784712230 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784712230 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784712230 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784712230 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784712230 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784712230 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784712230 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784712230 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784712230 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784712230 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784712230 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784712230 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784712230 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784712230 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784712230 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784712230 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784712230 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784712230 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784712230 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784712230 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784712230 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784712230 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784712230 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784712230 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784712230 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784712230 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784712230 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784712230 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784712230 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784712230 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784712230 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784712230 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784712230 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784712230 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784712230 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784712230 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784712230 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784712230 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784712230 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784712230 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784712230 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784712230 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784712230 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784712230 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784712230 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784712230 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784712230 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784712230 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784712230 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784712230 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784712230 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784712230 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784712230 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784712230 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784712230 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784712230 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784712230 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784712230 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784712230 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784712230 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784712230 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784712230 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784712230 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784712230 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784712230 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784712230 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784712230 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784712230 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784712230 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784712230 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784712230 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784712230 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784712230 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784712230 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784712230 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784712230 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784712230 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784712230 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784712230 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784712230 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784712230 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784712230 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784712230 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784712230 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784712230 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784712230 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784712230 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784712230 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784712230 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784712230 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784712230 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784712230 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784712230 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784712230 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784712230 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784712230 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784712230 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784712230 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784712230 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784712230 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784712230 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784712230 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784712230 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784712230 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784712230 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784712230 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784712230 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784712230 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784712230 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784712230 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784712230 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784712230 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784712230 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784712230 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784712230 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784712230 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784712230 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784712230 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784712230 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784712230 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784712230 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784712230 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784712230 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784712230 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784712230 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784712230 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784712230 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784712230 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784712230 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784712230 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784712230 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784712230 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784712230 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784712230 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784712230 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784712230 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784712230 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784712230 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784712230 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784712230 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784712230 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784712230 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784712230 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 784712230 ≤ n) (h2 : n < 784892086) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
