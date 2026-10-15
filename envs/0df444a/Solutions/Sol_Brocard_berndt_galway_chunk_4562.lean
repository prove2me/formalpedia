-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4562
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T13:01:21.992802+00:00
-- url     : https://prove2.me/submissions/6189330e-f7af-416b-bce5-3a3d794346ca

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 820323741 ≤ n < 820503597 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 820324991 1250 820323741 820323809
    0x21b011206080102030108010c1b0f02040f14091c05070515100305121309380405010f03110904200d08030a1a0d030509040b0619020601091104 63
    0x6aa4500c0040c82c0842840039602820b1079000110f0540041e40c0700401002401d0b03055400b140c80415082c002400c1c000b05400c0d010350565000c18407a1004540d41d0080ed420a5036070040f42065003000342c07801000c80c00b10704113a512807a48014002c8140110355a004d480d030010060b502880c3c1242e540c0f600c080384c00341e10400c0d100000405688a503580750520380050690100581c01103051404080021b0041d0090300d0402001c00c50f480c1a0707079034807d0b04910b240201079108820400103007210f0840c0e04580300c0c41000b40003407095595641d500807205c03000384416a04c1c25003032034102c00c1506e08201000d0140703400c00f41241204c1c040400c01042442410105075003c0101190311000610020145201c0e074041400012041f491120200c0d2060131003000511913004c8180703100001c8e0b08441074a841c00029072700010716403084e0000c42da80d0701c2010440820080c001c41c01c00509540001c000e0b0507074519004c140074194102e01d15421f036000b0740c014513640d140310510802e02c010800380900c003a0 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 820326241 1250 820324991 820325027
    0x5150412020f0d020619080703020711010309022709061312180e010605030f0108030a0203041a0f04230414280608010b180408040b130503071410021b01 67
    0x3032050f5038009140f90340b00600c8400324101c1c0701100255250411102a44600f0300c0c1000d601c0d0140683d40ca64031442702c0071029040c1a901d011180a54489140f1140001c020403407103201a141e4200c03103450744c6012185500036220301c1d80092840d6110301911455240c1c0a0601d5104000e40300c41901c0c0075081c114810400900090300040604100c2c840f24001c211680700c1039501c0c2440031018030b06081c16005204542e09c02c014111030150b000085038103c540b40400700011710810303e15115540310302040003000201c08640400c0da960a0700000451107041502c4c05180041901803105072001e0301810421220358034002004a140c10b0404500c12500341400304184250b80c580c0130440301c45412122061b90341d10490806400c110104041d80000c9000160a0380f03815076a42199105034081c8440c40d901c003090500c41d140d50341503050040c000003015158050344070003d800c1285451903140d41301d0000d12184009140c00840c40c0c0c151064600c94030100401010019141c1d001100b070f4034000 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 820327491 1250 820326241 820326259
    0xf0e0405010905060403090608060d0c210204020c0c0901060e090a020f27151e0a020a0c09090614090a20150a0201060b030f070f032405150412020f 65
    0x6900313004282c03143d4070030f071220300040381400c2c070080c54240d005141d0341c001c100c1d400310503000c59410b0140b0011603000d6600d4248102c103018000d01400c1d1400c2009410900201d5000e80c0c84801040e171801d628800d940c6801240e0b40c0b12002c844280c010390320150040a0507002c00d5040740700b03030001c20313840034011401c514100c409041322009000c0200103081d10b0b05115034004e040c1c50b04071003445010a00040d0103060201e41502409600d40d095400310142d0000200810240c0c001d01c105c140207070708283d9001c40070744e4501c20000500705034031007103800c0d6162100107140c0703100804001d4003801a440040c0105056651000104060483d80100700400b200c9212600e41e241c10180c07000070700780e0b001141c03240300000d0040e013034614541007030b43e10010600130403000821000342c5aa01c01524541442d10a45160342030380100708107524444008944a0404000c056840d00f03181110400e8903169528040c2c0070700c1c44464000d40c0980f00c59901c003104c46d030300540703005090706850305001041035031 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 820328741 1250 820327491 820327493
    0x9051608160311010f0e090a0b0307061d12120f1210121214070c05040b010c0302212503090501091802070606050d0b10050f0a03060213090c03060317040f0e04050109 73
    0x446207c03c40300a8031072900e50740b600c209402c080c40610020041400c2c00c00b03d0030404807200300014010481d443c000c0c406015801d00254040018011045420400c0e50340d442c030305c1c108984203a000c00d1a007041c2c9280c020204140d0700488245100721030f00115003e00d00d0180313581c0c0401001c6620344200c10001440c0201c2c0c0c0401c4417400400d00c2506c03e1506a01c0c603441d02060009541d400c000c01414440e200c0520310219401203150b0a80c8035510024400e40c650654080880e4002c061084150004040b0506009001d014075441b0039800782e199104002c1e13944004482810850269a074540762506644151001c00e80280080318070402c00484c1c815150b0010405400f004141590380d51010400d021304210500e244070050a0252114400c02d0851400300304540740c58800103003d50703800900d0a801e091a040808043c1884020a20400c116650001e01401460000b9600001240802a001d485007401c40c1c040303c000000c944600ca16120381103000c1200188142c940f5501c80394040 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 820329991 1250 820328741 820328749
    0x10120507030f1a03070f030209060909030c07090902091b040b160209041a0c090f0d0f021207051504080c010f02030f040e16020a020f1309051608160311010f0e 70
    0x6543c240c86203614030440f2902404141c13500e9010b034032081038030006d020203101586880349001c0d40544103580c020100d4580c8580c080c60761041e109550704502034010041179001440c2c22079540c80b0b008465410141e150091030503180040c80d41d642040440c2000304019a41400c00508a411030540d500e0041040903000300c2c0e03181100301c41c1140d10301040012144000c1016007000c1c2c00281002019092081100201e8101a88400704920900c07010301c990040046407880902a40c9d4098152401d07180c82007103a69640116004083c8994580c0c100e69200300000d905950846824500400b00180e00f40015145802c0350700000003103010421140d101c07018010000c1c0010120321060b0004c0b881e25460000181d144807492404640040302800f002d07981c0c0c0641201c025900f180e180550700b240c5404500184a4402c000385a401103010201a01070481070071400c0310b000c00203582c5000510403002010045500004042d81d110134104001035101d082150410740050030030810301c500e0b1600007 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 820331241 1250 820329991 820330001
    0x414030c0328090311150d021c0b01030207021f140c030c0714030a112d090702060402010c03080c0d060b1b030f0f0c01060e040c0e0610120507030f 65
    0x680084050440100c02c18502902049800e203151400d801c0b460b0866849078001004441d000e807140c00401ca120018403d42401c80f0783c490010042155240c191100d03070b081081500e40492500c0d0320340000401154007a0084421007036000301640e00190364102401c00c0060449411003c000341806403143ca00703940001007400184100096448841031924180340c00c17103a17000aa408440400340d81034075100011442d135943ea0102c4e1174039416a661011601c04448401c1900c1802212640d20b410700300c080d46480c0c001c00041d07902c44180d659034082a60b90303e2003039a0080c0003803000040c14021070311443e801500404603502c0380e40751240b1503105034143c485940000b189840009180c1c1c0408140b02811002c3c0542940a1410104000d022115600a80030722078160030300000d84030040f043c20341c0043d025006801949134a82480d00345072501101502807400d4410781c2c0030100b155460311900010007410345644200c1000130164003403003c0d01000e00b42c84241600c0360a296080d900500030307 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 820332491 1250 820331241 820331257
    0xf041808071a0915071e0f020c060315130c0906050c010f05180d18271103090d0801150f0e120d091a07080a090905010e010501080601020f060414030c03 67
    0x13032925888603c81c10007402c2c1c01030076550611141c4d44190513208144540b1009140c3c517401c101d8031120700c0388001d9042c044095078a42d40072100104201c031a0541c503c20b103586500c00d03500c0e900ca43c980095102c081b07070346004005c00410294103080085502c00c1005000601ca60000402d11a400001c607c007681d1040d034186040c90160810302c00d044808000c21442201245410400301a40412101102c4040e00400345019003d210910f55009440f01c008a00c6d56141400c2011200c2c0d5881c4151640064540c0c800c1c5e8050041c0e42241184a007003181c0c1640c0b030302d182e40c58540003c0303401038404109038042e29040c82888900703000300e50b498910fa001c8100e0300501800d240741011100034106280c5820010850103040b01c6291612001d8042e5202c0981c01451701f60341c5c0350b000b5015244d6810310740c803444200781440000b1811004100d0000d0484600380c03101a401d0712010010382e121034018404c0021907010800140c0400e41021425a4071884003040d64070300344511001a007158449a2 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 820333741 1250 820332491 820332493
    0x308300103030809210f0c030c010c11030a120f090f031e02012a0512010b0c0105060405011809020a0b0c0a0c0f0515090a21020f041808071a09 63
    0x8010000c0c190841e0b21542e000d0060703c094020b110580708841001e114441007954000d82c0807a20201010300c4808807400c400715502103a464070782e4284418060180c142c00b0100190f210b03540c00d24420f4001050340d05058540c0c40f80100c0c50b401140c400028003d00d424107030f0054503603d0600c0811252008400030750700983c4d43c081c4c5120701e020000300041e028144001160315100b110402c88049211254140e2480d4019094480d50700c02d0850752405483c5c2c2c16591085c14000005030181400000d000d5944040000e01842d40c6441c02c000440348240318140031840c0503a10304003202000e500001a041c8002d04110303642d625841c0580c0b0f2500003080d16101ca80c00707040750030144040116040000e10703401c1400740c2903600b40400b080707a1803070ac0242641b13046004548030f40581d40d070003006400b90106000c041030800f08074400d8807804004c5601a800b46010700d07140256402d2074014010407241030040700d80f07a0191655840380590041100b036036400a80300c240c10415000441f40c50251700504 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 820334991 1250 820333741 820333837
    0xe0a061404030809030310140303043b070909230705040e180a08070c05030d2106060212070303060506190f030b010f0c051501090519090c0308 63
    0x102c1d029010324406002500b1039030081c8100500c102d11700010a0a440d05158220b1150329100086841e600a60704000c100545009030092081d01244c4e03903000000c00c2c3c11082d042e241a03e56070300c81e181030540714100010842e050074001c1c44070641140803406c0d0f00a0880b41445180c8148030301c910f500741c5a00380000d100080410aa620000320242c1014a000c0c500c0c203020030352070b0b00715560045124010304210001c42c0500034081c0c51203502d03006090150558000b288510301c010a000d14101004070032410050403c51301d003459107e25402e441c0c1d1a00208a440380c01c1d05046c885800600040b4105034640d500880c07207481e901c0c003600000750380780101c1c1140b4007007100c040d02e036a03c020002010503161299440c402d07a480750790034080d41240d0400d43c1c441f68050501743d080c668006c1c41c0d050b00b041c4074070001858081c10340c00385e842010389981c2c5c905c4c00c9600366260000d03190300c00800790507510b600d9418000f04040d9801804040245540c2c2c59070b0300070300510ba505410000301a02e0f02c9030149 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 820336241 1250 820334991 820334993
    0x5010c0e010e040605030a11030307060e1006150906120209060d1506050a08040809010c0f030806040605061303060c0522050301060906180509010e070e150109180e0a061404 76
    0x40341450b000c0894043c0001400c010209a41c0c1244482c05081540004507030625034409100711100d69030400010b01c0741050585040d1390b40ca01071a00c01a0003440e0250014817a03c80360300c240b4a8641907602d841d0b8040c50f1039030481e4281040c1c82c0e46040b00b03a0070004182c90740e550078010b202645499501195440d070300c120300050740506912003000d21504216000007241e01101e140e60059029100d26141c1c400d51004a901c03d40e130f0107008100901085a502c181604040c034030f0702c12201142c0074400c0a45400a00c012809610107401038031365010070034070006402d600940312400c0245451420010341d010040c517101d0300c1c007819114182c251442440a0b0800303001c2c0d00003915086009100d028035000d041e81036410120300d0028066640c0c000b02d46440000c3d041450400030b10011142e480d83c8501c02d6000c19101600c20182020090030b40420769400746e0f5001c4100d07904c0c000c03161604440c443c0118050009026a1b401c54020020740c000010561b105080e880b004c0002c00010030304c0c04e = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 820337491 1250 820336241 820336247
    0x90c03050f0309030d03230c07060e030a140d09021c061103060f01030e0124060201060e0705120c090a0b0301060e0315070e06090904060e060a1b0e030a05010c0e01 72
    0x9541c00c032440035001040180d0080d240060307640030035400340c0783c00211440b111842a0398120407040307107101c081710007050122281c44040680b03043ca004d01401c03c060a1306000e082e03900d00c1000030003008610806070000d0f030b103510031010b04080008800c000c1504901c6500080c0b80da402c000c132201480314240450024000c5138406d00c0c0901e20315150b01352950411400203848241c1c0d52030401d04040d102c54162001400c290030062170f00368954000d0440c0480002c01c8202e043c1075024020056113031180c00181041201140c034025a841e4981501c0c2840008500c40c508500402c40502840100b01b110394645445c00004001d14241068607243d50405400414014070040d52a00c04d6001c10880e0260f00586080b09801000d03134188807088a0510b004200b8a0240c4659942d01c070302030a0801090188a80041d074114840d1401c1d43c6081d940d215206089030a56004150400018504044a50701a076200420980c00600f201e800707407002c0ea03d40f803c1d0740c411148800042e402c84100c54203560 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 820338741 1250 820337491 820337503
    0x624181015020c121e240606041401050c120304032714040b130902090123211e0d03062301110f0109110402120f150301090c0305 57
    0x40c11211128500e003040724001d69441050100070700c10a5500b20040319141c0030048050101a44c20035050204999910f03070342c58003c104000a59060764080402d05840708080d01c80c40f583c4010a86c0d0308142c01d02000d56810001c5c01403c6050040402001c1d02c1a40b08007c9103459004501009569141518004102c03014602c01c14080b50002440021143c01d4420540259030820889038501c262a40c00103010309207400009401a60346d4030359035041c000d240c00c54900030b4001d40b4800304603603a0b04d00d41019603411924a0369000d40310020500c152174907541c00892641078072024502c010030000d0303007404d004451111a1b9003031324046850750711103400e01c07090400006c50300741042941e01e0040710003142d80f10880d040480da40003a40c5201140e006240e4214178040d40000c0713038071140d00c0001003402803100344001c2c0c40b0441041d400c07292a260a008840da00c04144000d0300c4251030b80030461403000b0001d4580c80300110950b601c20416102440b611407414081d480780c503040c074590f05103581046 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 820339991 1250 820338741 820338749
    0x506040902070c140303030f1b0a0801030c0f06050a0309020d0215120105091303030b0d060c050301230d020d0c081b040f1808070f06050a0606030b03060906241810 72
    0x442034641018135079404016030340e0042101a03580340a60320415140200411840c0c000095200032031812002d5900c07140c0c2a060340d10580829410903182c1d5000200c0c42214820140019020000c031401c252080d0040000b4500c0a0840c5013103420590000c0c0c100809602142003102010465541314502c06200c1401008140c50b210324a00300f490400c20071803d0b4040c042c09054841d11030701090f445450f840e11040340c1102e010426401462002085940203116402400e0012007544108800c1d0035030700c400c4000001d000f80c4010344144e091210310420b0060607607012400890019100d03c0c240700313000c0301c2c0c00d40394020b00280307038000304204c01c40b103580030740001c29440c0041d031001c0803900e0342e65800380c00e07084000c290703e401643c54070303400255a590008150030f00304000d003e00800940c0200080d514103840601c84080500d06040c1e4440c0e044462a001da40400c000c1010300c81c401c1104420880c05221054810742c44401154400f00384c0d0810014a025900402c0316040003101808042c2c = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 820341241 1250 820339991 820340009
    0x12030e030a060f051b0405060a020309131508030903031b03270301060e060d06020c1c03050403080a0c0f05030c22031a040f060b120f07060305091908070206040506040902070c 77
    0x205017903640c002064015070003424042c040000c0d140301c1d0640204190307106200c0c014a907004111100750450094a005005007900254030034010030a45404810307200c072040050011810116494030040600c4107141585e0140e000402c44030100c10401c5026120380c1c510a9480e28030103800c4401e040c00c44080398400d002c002d07046c00900031607545030840c0c600200d411020240c0c448402c00322242c2010041d4054002c008443c2403000003851301500b05600c41d030301a480c0c00980f9620810008190f0b400c1001220020b0340180e00005168015406940c010030613030300c0142081030b5601c13510000c000d42c8001070310b511103814041003000010484c080004001140c8106607051650340c441c080c0448220081c0726076104c201104503a160070300c40f400320b00d544800f00d0300414483d00c1c105444101c0740c05078500080c148000122a214005081c402120030340207640718520154a50115a41162104070390080f400c100000e0b4595681000e000508150440140d550b0ba9601d098400a50107501c20081 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 820342491 1250 820341241 820341271
    0xd1b08030a052d07110102070e040812040c05060c010b100c0b0a0f020702100305180309010c02090408040b0325031103010611010e01020f0703030b041512030e030a060f05 75
    0x105584031003550149000307040c072412000c42e006142015040203e042080c0900040f5404003806542e4906150b213283c02e809444100b51640f040c500130980440d005040c6100c04c016440c0650050003000c1c0d84240100c4a4201030303030b101c0c0c001403030a034052121042e5903916810446407501d0300c0d29015240e0405400c4c00f90010950350745401606d00014100c6440f40e0703036204048036504040c0c0450302c8607a4000c2142140503002d4a01030010041542d00300c4540c0c061414107528044000125010814140c4400404030340a508101e010b01e4014411030350700c5018400002e0004900b009103000e03400e028401c50307410300001702998030b6650791908402014200b0b045a6103885a807401c0302c0c103480c00d51030031801d4a028002d4850140204d0305a800d00c6600c0014110181501303000902080ca119680520448030b60104210a45804548100c1c00301020f43c0c007000603080b00d4a080540a21a08007018805081c800090500604420540350140c03286506000e5803618070030b260740040308540e1204 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 820343741 1250 820342491 820342507
    0x90f1f03061d2b0528121514060913020304030804210e0d11031b18060a050103020c0f071409360c040f1a030307080304060f06050d1b0803 61
    0x10b6400c3d450341c0322051000008445150414044090b88042010009031500c8601c0ca000244103100003101225060318102140001d441100511812900c0c441206d80401c0c240d202004016030040c1c2006038815098650361f0440700c41400030b035100e035010782c41b4003001d07141c6420007403501c050318428401c40740100d261441960340c00c04e01e42e072050203080c1c4040c3c54400c3d0034503069004019403050180c0c103100f5000c26402e10301180c1c40c81010424143d80c183e900608540074044010400d880301548240581d030b050141d5486680a001e1608103003084842c2000319802050415800b0341011500300700000e404640d40c105609110f400802d0b1164400020000001010500c908640152026004151204420307442040140d00c040402002009444080654100240070140c00413951148000a40200f850044160f500440d003201701c140c0345075a503070f560b00010040020310005407940c0300b00c0401c282d11200c0190344114071402070b21101c3c000d04500e50070035044d2540998015801005000307 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 820344991 1250 820343741 820343803
    0x315051b030106180519080f120f0306010903080304080406022a090613020a0206040c0b03011505030c121e0a0c090b030a0204210c05090f1f03061d 65
    0x641141c045241110403118040003202d403c542c20740c03005a10240d03e007501901d0001b0031880d1411100050300316031184402c80c18481d1195588407594030901000d000780c3e00003045c810010f40e40117105240a803071150720390b900c01d1400c0d00251030a0743c104402084c14030810341c0400c0300321a60018004252003185ca08010a100d0381400d01d041d0b801740c81644082240347c1c803440c1000090040c03200d4155210812998008d5440400715410303100d030802c1e084002514080d45e011a4140d400020001c3c90040082c0400e990b90b51014080b903507550401c0000705000d4400a881501841072a1810001c0751000000e00c03942d840003502e184201441c20040c03981c01500140c0c001d0440740004d01c040c3e1241d4560650714001e01899220b5100d2402142c1210712060340707000800c583d18401c07091003500e00d07294400d011500300c0441d10b00301c400c012040414803214003828411003140315411901c401c1034590751403405803140c81d07082d0810340351002c139204804001404507402c907001c20502401c4015012002c6 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 820346241 1250 820344991 820344997
    0xb1003080a051903060f0b0d0e061326040501050310051509180c031816031101090b0a081909050d11010e0307020d02010e12060405061b0319050a14010315051b 70
    0xb40701200e000502020a5104d50000e41e02c20b12000e05030b80d4582f82a0703030034101495054008441c02c00300002103500b900032403500c02c280780c1100c14846091034100801902c031640041e2102c03600032400c1d40c0025031075407820398804a101065401607140c5003804148241458908183c0c2d032250300802c00c00044074aa0000c5d01d030300108014078203600c090b070140b9084c148141c0f0f810080b1030746102c103404414060b20400300010340d07000baa01d500f84155200382201090050300c00d55000640c140003c11140ca15084075084c40c2c014007800002e00016030b030354180c40e02c0528911034010850704441140070078028441c0320001e4042001941ca84141035001880b01000f4110003814400151410300ca5500d50800142c80701d030161003100e0755801c00b420710956400c03080b10711015450074000481c026600f0380f0162802483e0352482c1401094100300e00e00050400140f1441c1e40f80d554462840d0104a40d64900d8000c41c010384084030004454514601031790b00040c100e411289200e460304482c404d480c012 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 820347491 1250 820346241 820346249
    0x1c39060209010504081506010f1d151b06010501030e010b01090308031b04060c020901091416110109030e0301060e01060804060b01050d2c0d0c0b1003080a051903060f 73
    0x180d807a01144010307a014021600540307014407440110300c00d040000d486250047e0700988482d4401c0c02001ca00b2605111450700100703103200010003104060030221610392040d94160a05030809980008207510342c0c44003039500d075056001c840100320715605441400c0c00002400d0090108031040800030301842c502e8031004001d20030010020740c5124155100c0d443c003002040400c1d59841d0740b8400104a0134103c8070591141200800005240000d03200300c4c19a8007800b10708a20795550810405102c20b01da0740000213000707100320078440303500e0203110760303101540b00342c03912000960000e081c54215411a041407a03403056190060020325040500d8950156108101003000b01c2490012107a5003d450b58070040b007400d003681c6c0300c59400121984018401070b100d02d140701c0d8070400100343c6e41d060004000404580b400c01140080340e20714211710342c4541c140080c600f40c00c0c1d80741c1c2d0f00f003102c0c1e010460906c0080d0010030041c03240c0d4404440b01b85d500040d86824801e041c180380c40d0142c83d001070301c6 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 820348741 1250 820347491 820347503
    0x80f0c06030a0617070303120c090b0307020f063907080a0302040b07060b1002070303051603140a110f06150607020415090f24030b07021c39 62
    0x7000511a00d1150060000707000002d402d1310758002c00d0610f5660799910381c0400c60200b42018041c410b680c0940c0324908000c001039943c9d140891902100d20140c0c3c0c0060481c4045020350750288070400380410060780078003201c10007100785001d60341710b29000d51680004610b0341d06048812013041ca0184040e1182c1d660171092840e40d031440b69000f58000d204170ba00c03083c40a20041100300a2002690020355128400d0760140c910380070030b040482e140ca20b20b000080c08180d0a1101041c1810000c0360001e02c1d074468101039030034024000040315590898401b4800044100c2d02e20071412005025100807041d50300010101c60801d42d200e0045150902035071030003008007280010a566854200c0c00407900300c03030241c4520b5500c3e100d04802520b8600100c800003070400007904829091040790302d41c820440b000340320f0f0b40c40c25a5509212140090300c2217086208411005280c044402d5000345002059100c48000000240d0414071088000205040c103e55201140c002a11514045240c0d594000 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 820349991 1250 820348741 820348747
    0x108240c130906060203130603021204060b0d02060408030a0e030708030901081b0c070305010c0f120c050702031c1b0201080412020f0d03020d0506061323091609080f0c06 75
    0x800091141c803580e610012155061000004009030040001d201da031a696a0000180740c079510250144d105218000001c607554400180119000d41d02c54048500018000c101248150b0001a1150029081172440d5000003501e9401c80f07420915040c2c03014811b40c058040da603d0103903003503101c0c0180365040c1d052044130000a015280b00c40500050050700c0300d030391901c0d036840e88003c66487e141400229003562901c0301d20540c41c0d00409244103580055aa2b010b0300c4d090075071509000c0c081d0881e1210034060b041c0500d4005a40030320030000406520b1a2084446415100c010300c0c070035080c0d0031000c298482c1650140941d0348099096402074009030015075440308c0c80c0080b482c11200491000290041212007100179506400030f0000c01d40c4040c05000759201d82041000522401c0305401140014010400956005200c4002c8503103803000301c2000c2034008004a5080c0740c08641f8406048141462541907075003081004010b8000e11009249912502028507558800e40260900c180808 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 820351241 1250 820349991 820350007
    0xa03031d0a03060603050f0609010219141201030803041a010302130209030a08040b0711041518060e15010f08040b061509030307060b09071107050103020703030b03150108240c 77
    0x1104007000b03607800030701004141c4d80c0b030404903140c1600c5004c811850146101180281c101402a83c07004041c2200f1804d40d084440400c0d0f03003a40150b00084480380060001d09101c4c8040c000c21402903000e5001259640340c07a141c40b0702c00d4100d4807101c20106850500500c056100e0100b6040d80f952600401a43c40000c1c0000a16100c500c82c1e00411403400081d0102d070380140c00e4040c040e0035100320001c240040032641000107584001e081c420406040c1c4101b00b0421f02d4850300c100d002d102c240030010700d050300c0e5107000441a00c100c40c01d4a51a600c014a419103584c04807a1140e81000c070318202c05241072941d07440c0000c1c075001d0101485450242d000300341d00c0d0319010450b09101001421640d46020031314160018100d48015180b16400000000d000240100d405d0040c942c455009001c03124142401900290003101c415004c040d0307a0005a1005e4504110901c2a140a010207003829032510340040d10b011003002540318405210701e1500710b0710102452044d0404200304143ea25284d030 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 820352491 1250 820351241 820351249
    0x7031218020f0f150c100605130c201f1517030f030f010306050c030c0406140910030605040617030d231501181d1801060e0609060a03031d 61
    0x3c9820980d88484614020100030950400419950001d03005403000c8560030410300c0c080312014414240c020020885459445201d584000007061140c10b14004a01c041d2802006610016070f1101840d40012a82e481d02c12021580c21110206c41c02d00303200c12540d90721078403903040c0244500e0614032040e000115a0b180f0500c1031782c1492015070b50b40c43d12440c0c10f402c2020306280038441560000c2c0362030041000f04a20b00b003100e2040000354602d52900d4600f04040b15250042044803101031001d2101515a5441d00442c0c04851060b80e40480e0284c100403c20040350030992140814000b901321005140d02c0100c00e8804400b0400070000b0700741e0003d10024210034103c0211407002d04210208800e08481030b050480e02c1d502070340c59407070b980400d504901c0d518041d401204811002c0400703024240c841c115600358003030546915a0080300c1c1414400f429211160810120116a00e081200504110701c2c041e500403c00c40d4180c1d505440c548015045940192005e48081a641400040c58036 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 820353741 1250 820352491 820352509
    0x14190c090b0d0501050a060e1005070501060b07230106210809040e0318040504030512071e121a0d080f0c07090c1706010e01050c07030b070507031218020f 68
    0x1d501c500055844146038204401442d0074003803944a9200180081010fa21030b8410030810309019100240c440c09e94502038034130b9001a00219255921440c0100d401100e40d405054002e1080707a00380c000c62071080082490700802e9032075140aa1400e00e0030072500f6024a480942c2c0d0201003001c0c2c0712402c160502c9003451103030156817038002d41010044a00c0040010080c40c045065080394120307214840108419a18144d4020780001e005010241801c840c0d1100b09800040328204030448003202081641801c2e00c4e02100c50100c1d060002c1000c1c0440e00e0700034100451005100000d5841800300060805079681d140641000d01c08112423159925400807208103070701d5030f02201c0c0030701da46200c0c950240c01408080da0000d0400a4054030021642c03600c80d014030816140c0c50028012000110b82c250440140f030341d521b11500d4000000300340840b2586000380b4103603851503541d102d141005050340b4140d4030740041051600c51490b01028a030641c40b5450b1758126002c5a412407043e0000d10701e09 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 820354991 1250 820353741 820353749
    0x120b03162606310c03061e0c05041707080d050a110a121202071208060409060513030f0908070e070302071e11100206010e0402040612030e030114190c09 67
    0x84034160602c090140500399203e020480032407400b02c0041c6071002d032100710f1680a001058003500e0071044c000030700180c00105014004d01c010b00c81390b0030602e0502c01076508041c1d9403c0810400142400741840d01d0b840d00c1000c0b201000280686031414112554a15001d0403141c2005008102c011440d441606200700d441220703800c80d642c10700c4505044091411441000012694582d44403080071501c1c001d80f03000503000050480203980000e02903861500003040181d100d50394880e4000041c510703224207800b5040c411281410071801d0b15016200e250031119040521020301d5041110400004000e0283c0381008100e0409440d042810f4000c0d0180039001000001d1001c208100c040c10080f815888900510810803000c1d1003500b484a00000c00c0c00070030041e041280180700010b00e00c00507a802502c05080051080e580f50b40002000084400c202c001030070380c00d0a00b40510f4240107103001c08030014a100c170315090076440d003d00102000d50b0218166202d03c0c919100720301503c003250040c = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 820356241 1250 820354991 820354993
    0x80d0b1203120106080a0501080a0b0403020106053303090a1e06020406030e160f060c140d091d270109080f0705010608070501090b07050309030d120b031626 69
    0x14901e00c002ca144000c0c0074054500040c98140020300d025240d40901412142420040d00c00c0b80b160742c4411860f00c2c001401a802c1d992920000545034488600a4441100d45610340034580600780042c03c0440c000300880350f00c24002c1c01407000c1918085040000d9551213551440c1d031a5100086110101507003074044c00b1288007181c00204190180c00540d41181d4200030f44a0b003d001040e00178030740a00340201c0e0300b0558084001e10440c0d00461545821038040c00101c0102c410711034a9515040f0103070132400004510407400c200106c40103d9a082c2c0507922030b014042e52900e03071005a486080e45211403124480f0801c1d00b00e01c41004e5100f14246604401d150b40d441407007100c0342c10594001c1208030303182c0d86090340001c0c66060100c0e000042e650140d480d00402c5140040484142d04184c4040c0c640f40400c1140c80c5140d42c080207000e01c10107807910703070031142845001c0e12000c40c2d482918840c02502b040c0200b5075000001c0c004070065070000308581d40b0070102445e441406030a040c6240d501 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 820357491 1250 820356241 820356247
    0x10b121311131b090e1b370320160b0a0b0a0e0615040305061308130909110d021f0c02042408070e073506040f09080d0b1203 55
    0x5065012084d07100b90388051102031080c2c3c4442d01116241c041901d141448100c2c00e11a10300d0651008200d950f0b80c0100103440300004012600140070004440303650800300350740340500c91406180c608189129507141000754280740d262200c412098840e0b034401400001e207400000d02c0c2d03441d584c0c00041000d4000e031000e03110545034925115610025603e00348621050503480c0c41c050300307010850301502e90200189c08242c9400156500042010004031902507041c400501d11a004e1044c1d10300070002c40c00041070702c48480c1000210b8a500c85041e90140c5403242c001d00158541850000002c0340c4090518243da51401c0c0488148400705e400952080c10b01e40c40700400208015003010a480110440400c5a07551303031081c2c4e8030f011511815140d50030002c006007800d80500303070348034401c100340f12803c051003500c1841e81d82c40040e5641d020441138034002804010b081520511407075a9106000b00620401c0c1d03103c01070180514195001226284c103c0c41c416501c540c902e182800b55080c044a0f1 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 820358741 1250 820357491 820357541
    0x706090b1c0212070201051f17031204050105060406120305070f08091201050406050702010c0912080706050901020a030b04060501050f0c010204050406170d0c11060a1106010b12131113 81
    0x21030f0650564500d4019030030980800c00080c1f4006a41880a061f079214024041c500a800c600a00421070b02d80400d00080c01013840210b030003001c081c45544203800004552031701501708411100c25030054440c1002c02c0c0001c000190300300d030846034900c2d00312030030950800603031400c20540d00c902c1403500e0700800180c120040c3c5040540017035000318070400080c4807503900c1c15404c07800c0355030149941d000503030426010012010581c00c01c529540c01041340c42c0c54004a42c84100507141d00366925103050b9030000384405220342c148584441c03468100d81c107100d05490940000c240c1d000360701d4802e24201c0002084210030b4000d5046400400d00940b060020a40e181c600700d5032084100c2c0c902c01e0300d00418540c00c0c500752040100401c1c040e400192401d005000805000498122549100074850046042c089045042102078000c3c00e1401c41203039643c140040c11642e840c0302502ca980390041550a082c001261515000147c0b0402c2d14001d41d4030790000300c24030203407812400c002e00c050000c4100c51 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 820359991 1250 820358741 820358767
    0x1507091a180a080a1a04020603070c05030c011b020d2c01020712050607090b040302060313020d0c08030c010c02011e02070816060605040b09040b0a0b01140f07050705030706090b1c02 80
    0x1086107000720105d2880048003550801014012640203502100c10800208030340c0c007031010707821914018001c0f80d00b070007221242c060841c5c60361800d4410241100c9620340c949a4100004140d4101524141d0b0046000b4040c0f07200040302c000c0c0514042100415003030844e4800c1101034001e000400e00341401c12104c0c2040f54840100b42c0e40840040d03440580071551041020440d82201da02030031062450b035401d041c05001c40051b00307089901c210740d90038200101c2c0e01b40b003aa1019000b1f60b0040d55640102800140c03c54080819603006c0d07904160741e0a84000d4000d60100c0030842108016958124501c1c2c1003005114060002c0a0505443c4d20742050040b01c0c0d110100b40c0d00d00b135404011100030b410404c1140c8000300d0300105102d0140000132000c0c200c940140741c3d0290103040140c880c41803207041c50343c0c40e08801c800012003c0042070000c10b004040242200404058000c0c1039914180741008102050070f0240107118480086c80d0f4100c0405590f40c1c40320410512070454940c0c048401d46 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 820361241 1250 820359991 820360003
    0xa1505190218012303010612090f05060f070905030604080d02070506010e07090e22020316030b060420072d03031a0415090e1c021507091a180a08 64
    0x1440c005082000c107019012940041d211040b04c10840050846e03183c001c0444d00d21001d01c030042c540503150351524001030b0320310451070120b62042007d0009407501c0c001e0a0310f4184018148020401a42010000f54030003007030107504030fa08504416a101c2d414103696001e4031a05038014160b200b281d00018201d0300c1440d0f450b005140c1940e40108180c1c0e80c55250101480c2034031401d19804240701d11088100844682d1a145480a8103560340281c4030344164007070600070780c4142c86100700b460400c0580d2809118040d014402c0c015158071001d00040c10300c0c0e56025000009200080d002200300b080441d5a40c000300da11503185c07140b2400412440c6c011b0141085050412030300000c42d000c4503092900d40200310344026600c010500c09880c0904c00c601802400c540540c00340120301601441181c82038440c0302d9034003e80c000b8506141c0030000d560029000509000c10401182c2007031004240c1c2c2c840401d0f00c08520741c46c15450b070030700c1c9050504007508403ca05502203c8030318001a038603030101c1d071 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 820362491 1250 820361241 820361287
    0x303070b0106020d0503041502030a1e1d0601081905030d060f2903070c0c03020a0b130b041503091b061d010c1208100320120a15051902 60
    0xb81c44c046110a0016a40c50105550007019148404100411122950701850b88a41d4418005c240c4403040e12032107a4415104403200e809544a95040441403180381c3c2024004032418020306280d0b140c8220b8a4456084884904489040041c075a09106040094800031841010200700003503495440324280c2c0403610800c000d25081e4481c043c41d41c50262682d10b0b04401c04c0c0c880c02d00d95917074041e08554200400d44101c8103c00283c00100150726003065031005084a21103c998407203a611030381890746625440130a01080410007401100340710204940c1c501000e081c04200c803441c83c0f4000d02c41805226540401410100e03001602940c45401c40110711440708003607181c411403800444211500402c06072071035856100f1401e0303151007441c0d4194002d944031001d0990940341c2d614007080c16010039017016012000c6608030301070710709007000d01c920001c41002410504420380c0c2e83c0910080405208a0250b5282d0004001400d106164040e40f80024800c658074280f0000d54404400140382c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 820363741 1250 820362491 820362493
    0x60503041203180809120102030c04051504030c050f040e030c06160903020a0302100201020c160906090209130b01050405041d0d050a080a0c1b030201050708060915040908090303070b010602 83
    0x30307507000d01c030300a100b8000c442c07000350400b60340e82110f9101e102c1598170050702e140d0044072500070003096110038409103010b001e40189050741c461030003041250016000080e05d28900041004000041c2e584101c4000c0300c1d8242c0354490041c0c05800000c0c02001c100e4401000d900000910625070a00443c00074829842130780f04500c04007003030b0700032501c03c52035010003508500c0c419400d20241c41c00803d030030700400c080d01c005458000c0010f202811b04903074a91001c200c13140e520301404803240500640303003c0d041078901103060407916400203d007180e41c5c2d07000001c4560741d00020511030b482101140c000e03100c09801480343c1d44c2c4291002c031b8410056110280d580c01200c0c5042c800c14410400c03070343d1803011960703000381e203840d110440c900801010784148140060048103200c1540c0c08410003c0140c066000003030a8a060341020f400c0000081c400c501c24040481002114103008600107580e200035140000e00b02040d2402c8941c0c2d114201d11a6810310011601c24100450103407003505885d00e03a8 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 820364991 1250 820363741 820363763
    0x50106032001080901021306030e101d0f0607050d0f09060c0c0515070e120a240f0e2e0f200304050705040b01050d050103081e19140408010606050304 66
    0x44c0c1500d0807070207180c0500d628056401002c1044510070740000b2406003200d401e464500072140038500456070300d0f0403080301e441101070251245c0001444194089c2d1903c1e0054000362402d40f41c003c002e4424507110f415000d03034800d0699603808407a807085040e160700140401211001d914042d10303071082d240040307072103200c0c0e601c801c0205402c40c0c044c1e50049006480c1c0c004203080c0581000044801c20040490a11501c83c281002c0f4a90a0760000050348180380c1350507d42c40104584d00f568690107500304414106030080d2000350001a0141d0302e807208034185441644a44084104c0c0c0321007143c81403005003480c040e50000e00c7e159111011b485030b40108944040c14240c5c55541c03c1c001217038003070720070b81168100700719504294108810140c01403403c58070701b04000e4508001c0743c80c00c2e0810346510314007046251015000610424401c0f81c910035060034021204001c5110499103503204082003e02184450b0b80e90041d400d0380c0140403a00d00034030006440703502c020311a81003186c040e40c0d00c4c1c07604 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 820366241 1250 820364991 820365001
    0x807050c070602010617120a0e132406020a1106130e04051b03070e010b1809090114090a230c120102130506030108100b011214152b05010603200108 65
    0x5d003d80800320880d400d039042c5044503c0a427281c1035014611a0410409805c0446103640d03440303507142c641c10070b206910454110404c003030701181d045e40180d800c0d948055140008074004400144010004440700d59860328615404102d46206501c10800e003202003003840200100416610042c0b03507607044210100704100c04141e9941c24a1041d02121054080144000790140c2c00410318031042c210884007001c241030116035900c000f1640400c00c4d9540300440404011041c044642208903000100300e00c91460703c2e51440402c002d100600b040342c507a0501009001f003030041000842c40200102c91030388a015103d4084c0d8007582040032810141280802c20386800d1301600d0503656400700074a11496040748000062040440b124103002100120a11440c40c03030081c4404000c1a203919219420500d084681c0ba44a14545030b21030310090002030668481d1505100030480300c100780c0e410b08104da050150045c0380503000905203040c003004202c1080c04807042d14007071072003c3c0e07241c800039912 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 820367491 1250 820366241 820366243
    0xa1a1c050d091a0c0a081b01150b090d020f03070806070306050604031716081c0f05040305160c09020a0306050f041b030b010311031312020114070807050c070602010617 74
    0xd01d00070440e10f041c40208001c0300b041d50001a1030310682000403580b2041180e1580710309034000a0003030203000291400300d20004002e000310b051200703a000c0d061076158141480481e460081000c03036070281002031207203029941e40d080311000030003016055031031090b00c0340d80c1c076a02c2d554212054404a4108000003402382851001c07107040f241c0085481050510b507262410386a8080c1094180c20a070300e2240001040000c4001c1159180300c3c0456842c42540c075042c2410b641c0040d01e20303071045252504100101e07070420304464000440029008500240785002c00c8001203580044001a20106801100c3c0760107500080076500102d92040100c450300e000c0200380c540505ca250484550200144c000c24040e4200d02c2d09044141408600c00340d614074100760a810132103440141003003c0fa500340500200014002c3c00e051281300a01c40e10405020f40703007c090001d400c990400808400140055114600750b0b0000300503181503490050b51468028081e01c1349000719020102002d41607111448 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 820368741 1250 820367491 820367507
    0xf040c171302060a033803010c050f0906030c040803131d07121109130b040c0801030f0f02010c0204020714250e040c0b030403030f110a080a1a1c050d 66
    0x25000785960b282c403010a4040b006440f914143c2e030311b080404c46030b0362038000c0d10300030080c9448201c48500450120400425003540c0200840e2801d2010401c5005414100d41c0700300c4401120960f2440da80380c4403140560050320130359202c8506408041041c2000c00024003400c01244e05011860049004034140c04203805000c0e181c0001180064403400f092030a80d4010000751780d5100c038014140358200d0041b031081030180c440c43e110f166940400c440c0d00c2c54184220b04110850780b074070000d00d605540e20103e88100c0400081d2a0940000100b0b0440e071080c9811542a80d0142c000d5440700d081d0316104025507181007103481032703000b9003040c01e2454403000b01081c0040c0c0581443d0444901d070040d03003812514050303c1614400d8001c00d02080400c00c103401940201e200f0b42c0c0020700c94072410840b030100e54500d5985003400d04200b040400381a1711245480e00000e2520380011601c44807489900622044450f15400001d624507111808040d4541e26004c680283c09031070030143d004a08441c500 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 820369991 1250 820368741 820368743
    0x20f1c1719030b01090f1805070e0a0311030109060603081908060325052205091b040c031e06090b04090b070f090f0e01140904120e0f040c1713 63
    0x4000d520705030081d074400e40002000c0030042c1440800a44c60380fa40e0300d0401d145811800d150603110b424040c0f049958030030281e100d14246849000308402200050105025201c081c003000c0b007521028446540030741c09208510703482f68082003401d40d2031800150301c0c0c028200301030355401c1c8181c0011300c640c058012580b140a0060190181c500c9502c01602110180e10761600c28080002c008107985d140c00071081d10803010b4400072135100040002038400d8400080c0b100185802c1500070710405d401c885890806850100c402040140790755030101c2c021300b004001c100c00ca014908504000454a60144044d0b4050540502040e119139050000343c0b40000e02c010002c4215a000500042c800d040c040c69107999481c0540b032103641c49184803104c91642d000951030800c1ca00041084062001c85072903200001c0c8c07071681451a194076012240150745018200380041050052000c1c0d40b83c110f030900c6104014010401c0c0240c0c8070004002600b01c83c003003c0031202c1840840c1c1822040d01078611a2 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 820371241 1250 820369991 820370017
    0xe01030f06030308011806080a030e0307060905091b0c1f200d0e0a0807110a090c090b0a0201020c100204170f19020402070f150c11100207020f1c17 65
    0xa41d20b008104c1da0070b01b0341210511001d0f540c036200403548040901c011640c0c28043d503585480040b02100700750a2401a80c080000c1c8510f001042110740c868030100360344034a04034044501d082c03440780110018400d00c24403002c6030044010045010b1081080151030800348042044040d90f140a000304100014082410024051000340d05500781c580000c0000200030303080e201c201c082c1d42e90f0391350030740c00c420703800c030f5140c4031500701c400c90340c1481103181c0300400301c0d4107050115204120b009005800f0a000b0605000c0c40001d460405900075011210318052a03000c80c3d1100700e414000800075005406881d41042c0000035507150803070001103090b0619002800780c01c1401c045c2c041c0c020b00250010049801c035402340409000316003e50107a07817003a030107040070142803524103160b039044503c1f9113102c5051100185050381d1002000407210800445c0c1040140d0b540d8040c000500c0c4458044e170303007652080c032010748150042d08180c284a00b291050366101c07906d11129011407244d008280200c9a5 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 820372491 1250 820371241 820371257
    0x3f03070302030702090709180501050f060f0a18050a090b0301050c090303041e0b042c010f031e0b01060c0c06090506070f0c050907020102092403010e091504030e01030f060303 77
    0x4d031030a84083e54100080c0e0070300300030036680d403601c20b444101410003e01c501651180108100d04020704c06444500c000c80b421850b040ea4001200343c6809052207039070401c0008081a14509140d024500142a0046c510610f0319921852007002d014a0205507020b542840003140907846610103540ba85080100a1810700f400e080780101c808841031f00c0698402c10103400001e8205000b401000a041585003001d5000c1d031f9101440740e0010111000b15911280780010402c071400c000c42a07043da540040489903403011004034103c542c400a40240030910381d407000194080d0440d00044040348a08803508000c0d40d94003064612000d5481219000013041010000086440c100491001c2c03050045210040c0c65101240380d40104444c1c00c0090307903000402620501d000f600340b1121210f140d004014070342c0503c2d508400c500040c4281c00c200c200490200754240c1c400d10880480001c1101c0032503052034603003401403502d008910051b000c203250000c44143c0340e080c1d0040c0420789405031180c5030 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 820373741 1250 820372491 820372493
    0xc06250501360f1707060614010215090304170102120901090314070b010e0415050a020418050402030a0308180a03170f060a1403100f0b0301140f040609023f030703020307 75
    0x12903000d9007402070310140b03800c00000d40051001d12070400902800c000c00b2181d048d1640c006032900c01140d08944000407040c0030131046110020844061328200c07a0051203500314888054060700507550740c0c04d000d16128080201d918815030008140d113000e07646009502210310542141031150713641c0a000d0240c100018004400341851040c0c019108180c043d00c83c540c82180b500c225401914501521a00010700b04008005c6054040b00504421001c01803805c2560010303940f2043d031400101070109420004a281c14001d4a910b00000c00500f60f0751078280c2482c005061701c0d450307640452400e1a03040032440c40002061420302c1850080c2ca503400d154200914028441e83c0c07003a00c154148030b100302c01c5920340c5d4240545000306400a00103e05072101004150135a222040d40b40280903035001009517481900d50516005600302c40c1c0000d00003c01e00210b1940056090f019220ba800d0f44a51150842c481c00001d408480080c0404609541d140d00151644260b0002070010ba1017486040 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 820374991 1250 820373741 820373753
    0x10110310050d03210e0c0105040501080109270501051b070b071103040b0a0504050a06021c080a02090d0506040204060e010807381206030c06250501360f 67
    0xc100316000742071034800603001500501d00f000c85000079a03c1192240c444504105e02000170703a20403202401d02c40e080030700303082c0001c0000c3c0051041c1490b040e118640851140f07400c0001c4940c00101403c1c1c10705064030b41c2015406800c0640b014212040b0344180707805003041d82000d940c01c2660000d205500e540381e8040c00c0341d482e04a4004541d0b5400204000540a9800030040c0f1001586443ea06d031985c2c5008100110810594804000c0d07400c200e40300307441c182088a041442c0105400c0c07850180c0c482840083c02801502c1c03090350071000c1680301005011b8002041c1d84624401c680a121850f1580c0206290080038444d0b90910380c00960148a40c003c0030002c5051012a102006840388144002c110f4404440c1a5004004800a801580200c0c2112229030098054005041703166540d00800c0d010b104525418489148a41440d8400c0a03440e0700a400141c002001b8049415000d106800034802d10408110140c0440300b000140c4030912266042680c10132714012280f441500c0d02 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 820376241 1250 820374991 820375009
    0xa03151e020409060602060603010c020303010b0f0405030607090e10050f120a02100c030f0509030601050f120d030e160b0a05032203020709050c090312090d0804081011031005 77
    0x11001a400010038620203000d101602c002c0c842103201107401460858007034102580504040e029906184120700e0306134001007100c1c11a0052a0250755a400001c95410b0501450b00308030307450b00030013041c03058060384803000e0010744480c03006400a030784035a401d41c4041002e600c60b184c2c01c2890300d1880a59464000b00c00f45034000010190384200350300364009518074509401540120b20305402500c01d00d070b8002c4040c035442403d41895450041600c00007035072240140310312441864422081c82880d1192503802c104041c040741214040605480050040c10300030000c2001441860690180c41484400650456812106091030301501c0c0307608071416800200811984403a8003080060031600b031508100190007079002e0310f0340504204481060300c202814610004074244048016580c020450701684400d10051590b0b90354654082001d000c117615024201101c00701c2e0000340624040742c1000c01c003001a030200024a400301120a40340030554020440c075004003c240401d050007400c03 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 820377491 1250 820376241 820376261
    0xe0105010c020102280f08041a03093c010c0f030c05040317090901080c040b0904021c05071e05090a060b0f0a172409310f0803150a0315 60
    0x3146170505210307110344c12441d49250040344d01b60301c002002c0080c032004c451480b02c1550200d00c914030b107050880d0341c1640e6035020300a1a1407400395580c0d5034504002c164410340c07031000b8440d007121030440101d285402402185041c0340418130820b1040c10180c03103441014034444498403518101429601c0300d41d42c0c40b000348584c24030300a041010200c1580d5919001e802030000b04010300d0b142078150140020b440e244a001c500601000045c03000503138802c3d032403100c452001e0210301c0d400007150418500d0b0003210f9219182812001c088013010080100052050b240140d8002c0c25a440d0710341200100e41052203110030020b41803214500003102c00c8014440002c0b203160020718460404420803441d84250b40c94000711072038030040f080004d25003500384e11151007100e000320745282c81d40074948000600081c007001d01c1940d0503800a952800e55034052400d40060807141188400d10703100d6a658010b03954405c40d0b00c1c0075910481141f0309038410300f09030f0781d01480005900c122208070700007a20f08801 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 820378741 1250 820377491 820377553
    0xc1202090612090d11010b01050919050a060c03091401050f071704090501090e0604050c010c06060b1b190519020402091806012303010302150705010e0303010e0105010c020102 77
    0x80b0842645001d40020301514000700504020f5032604c41c0a00021014488032600c0e074109140c00205a81100981d0501201624001d000018403030920070f180c042504120303441100000007240140d4840200c41400340320340c0f03986003d1500d07440b4031031110725415185400160200480005014001c015100300c61164980c1400040c00c4a200384064000f03070820700c8402c0c0e076240100030615143c000c120180c20b0840103040d081c10261169611501000d100341e0610540650030b0301080040d900003401404541e82c05030315030710139110040c0d010001c0000010140700e44242d180124079001d0720b43c107a880d0701000409500f1111100c60071105d0502e0001da038880d44c00e01031108292107050754001c00706508040d011451500100140070b07841040c03e14454111101115403e02203080103c82c1580d404071a01c1c6100d002c0a1042d60061042c9800244694244038007019001c0001000d141a1181c007051402c56a80b100b00459500c0040c80c1e01a0043e48049041241d40004542518000803081 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 820379991 1250 820378741 820378747
    0x19110f060c010c1d090708010b0306030c030f0d030608070b0301061d130903081e0a050606160b070e0d02180a020c01020708211902030703140a150501030c12020906 72
    0x60759a41c02c44042052140c08500480303002c02c808000e4000d052881a01220307401e07800d01345000000c1c20303500140a000c0c640800080801c2d49554104048980c403440101210501c48a00d983d10f519046425984e9001c6400c2c11804038a020000c00c559054403080e080c07840c110f80c41e2400407901e074528107207071405851543d038981940c6c0d06c80e4041c00c11a141c0c40c0101090024461600502c004c600030044502a41e0004040500f8400f000340203410840221010a43d9103071400090709030f205031200952646007881c0041c040144003502d052013003901da03d5900d01c01c2411001c3c041242d0181400a6101d0702c3c54200c820f0710356101c1000b5402048203140181031000d0313504d43c2c0b03089a00180054580140100ea000e41c0500406801d002c04258402081007508000308543c100722500d000c13580b0f50980100000c2c00039840b0f0341c000504403c0705180c02d103150034401440001402a50510000303c954000042a01d50181c0a4000c00004950350300c0d001e1500054440020b40003404e80940c800d200f0 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 820381241 1250 820379991 820380007
    0x907020a030f033e090d140c10090f060302122e0f0f083906030109050108150c190c0501060b091f0e0103020918010f0819110f06 57
    0x80648440c000500c1a07556280d0512848070105a01c04c0300c15110b1688401c00184041d91100140303484003560000d175090244501e46452803e20501d42c01c40c43e00301e4118104410381a0703000111400700c4142403c8040750584500044040e4800d58450300d021400c1600402e100b110b41e210001c480000c1c0c1c5400004001c065840722105402c00d500003901d0381200b440501c0070044401d880802860550000c00c07529140519003a01d0400c44c403074406610f4103100348e40000340e141c45901382103440000c1aa03641c2c1e686030020080100420300a51805100d103191400c0c00000f400c40d918040c11481d40c8031070a00c030080c6030005060049410b01420840c0b03046420700090402d00800c406045c010410341c0d169010b11040c400b580000124484110f00c10003030b0004095000050b0800a00003840e0141c3d8601c442d0b004103070b005120034105499a040b1000016131420303c100c0e1001901d81140079561684911450903950400740440a80020311100781c121b0f0074505100e9007013a400c0090a0b840c02c1c0520 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 820382491 1250 820381241 820381271
    0x31005040b06031009050c150d0f140703090c140109090e01050f060604030321020403050a030c051011040b0a02150708190603080a1d131a0907020a030f03 68
    0x4265800c448064409042c40118035040c03011000c0e8507200350701008004e4590b11001d40d40d85404902a01804603c00e00203071070000d0b017040702c03400c4ca10014140400100b08070824000c241038652048160003002c0402c0351140b00e8087c005480c0c0e000700b10f203410300e0304064440d100501090300440c14000e8800d03001a50913110300809012000b074000000300c85c0381005000c1c1c401034004001c18842e0100708030600010350410100c3c0d08082018071942c0e00541e1f2030546100070310271608007a00c648070300c6801000b0141e0080c6e002c014a88640f0a6922042c9154001403e940c8811a0074021000920062040808907000b420940400d8810ce50021980c0403081e920040186d80d8040001d811b5030030400003842c1e101d0340740300c43c183c101801c1000340c2c6942c42d40d500e103001d90b0450030f04000411841560030140081008456079000f040c1d600807204502b04003008004604e4414502c66400300d8142c0781e443c1412229100d08650340142c00d095134603507001c9492509103409541410743d502001800c10f20303 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 820383741 1250 820382491 820382501
    0x10e2a0a14092e021908030601020c0607080a03110a05091507082a060f42010e060c0a030c06020d05070302040503013905211807080703110310 63
    0x40f0014002800da10141100c240460320580101d0a56100408200300c020841d510302c800660800842034aa4454100403800c155046a400d0350142d000704120342442407182c002c07c5196101c2d2000c0059a07500c140b2202135020300c00c4058003150041c8031a051a003065904500081c0d424041940b4108903540ca0f030940390460110880e0003051050001d0045c1c0740321000c01d80f0304001c0d000a00c8e01d0320b0700200041007007000038640182d004211100903401520702070a2040002103205860040c81c14441c4801c0306500c0c0b00703c0303500003240c41c03d07641220b089c00d40c216011302c2040b501400031744030b060310b0594501c0d0426030112003e6908005103010f1400c7c1e44542405800307559000b5a855140c8030815094425040c401080a005200c2d0100c03600009107080c1c0d50390303a01402110303260705034540a803424095035070b1500e200c0340100c04c2400c421041042d000d202c1d4004d1564070031918200c504080d66581140a02401303640314003810b20205600c81040841c01100030304039041e0000030305459082e50 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 820384991 1250 820383741 820383769
    0x90a022a0102120703140103060b0111100e01060608010e04030e2206091103150f040b131b140d05180d020105220507030209060612010e2a0a1409 64
    0x295003c103440980d64681c205507074215089103000e101400e817004543c0034404040c0300c010486a80e805952540d6402080c0205848005a003514821080c18031800040c0c41d800d2100302003546418000307e03000b401803142c2d50580c0c83c0203480490703540d541d58090303075503c1543c0030044d48045075007031000c0395124000b80188010680f500101e489450596807109445030003181f05c2606506000b04a600004150b511a4500c81184c2070300b102d01107400814020a002e051180c0c000b0f00a85081040d0341d01a004844070480842c0301003e5054220f2040350704001590020090580810003910f040394140c118603007001c10321409120420621641e9864144201d81d4800542d44590401c501c1541c0079a03000c0b40b54810004440c40811030713944841c0ca41c0038a010080c401d0000b000405c1d203035200d84041d900c22410038210282e09503165215244001011101e030b0105055041485241d10f9480d03c0d440301c104114a022802c100030190207492404204152001c0c3d000180f1000d6416991948400020703 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 820386241 1250 820384991 820384993
    0xf03071b080f0a120806010c030309031202210109020a1205101d0f0a0b100c060e030403050a05190b060d1a0106050403140115050918010207120806030a02090a022a 72
    0x40e0403903180c04e00d660516031140300107000c0701204004c441d0342c119199802c560352514002641148178a01038621075984071403001c0161002c9000c068000c0c154100d0480e151040c0d12826880ea6038601142c03c0c1d20903020348200090b9041503182c2c07a4903090b040150800f103180c21020710340d500d41c40650104114180403540d1071070401c0611054440080c503030b41d000441c1040c18007a502c0c1c444082001d00c086a03e4490401c94070080c05824050150b03c08098000c0751006e40b5a00c40d901c0c10519500d40d01c020301910300340100345603a4401e0700110f81000650342d2041700366485598020401020b04402c04040c2e801081c00c00d6144d10040c280c050203070203001d0b2500d03007076215401d505000c01d01090f082c688500b56803501a010b00e0f500d0b035210300c4008441044409070b40c259075030005803d0303075104090003420560001c14224200401e10544a0388040c107030b80c5e111069034032502090790381c140b003081c00b940120782e400100392020507540040013401a1a001504101178800c13010507403001c0e200c00392110f = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 820387491 1250 820386241 820386253
    0x213150908011a0f0109060203220f0f0303080133030902121f02070c0506031009060b031803071a09030c0714030105091203060609151b01050106020f03071b080f 71
    0x5500e460040101c4c00003080ca00420b8003818494040e541c1d1140d09103d003114a40d01542010717a10500400c0c0340a005003800d60680315641e00e0841b410b00c805800100d000c64021400421850f005a504200f03c84442c2d10401c03000a40c80806844412401074010406485264910150700c0b8220b4410300c50010800526403605182303100c05002013416a03100680d4010800d030400b042e000000c1e4019500e048409035a41e441c0c90707039510302022050b071100901c0340c104400003542452075000b030740c8100e83c4c000d40c05000003421030b440d030346074401c0780f0005080c984007107201100000f0b00d6102690048005044a00d050701c8070483e580740071800e40c40f0240716221490103000c03508003800b070b481e0000e1207080140604002610300070f00f0360200602490140101017803140569580350440f454125590060542e12100842c2559100400c10350341803040d03017004000138401c0c0c4001011004807004c00041c40c14000035903207040b80040403401c01034055041100101d80110f003813110b201428410001040 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 820388741 1250 820387491 820387541
    0x405060d090b1014040b06031503160806010e01061e0c111207080c010e031e030d0f051e090705060c01090209090a30050c01060e09010c0210021315090801 68
    0xc1c0c00d02c4c02c0f0807540c0c011030070688034800c1c070707200e460039130350040341c003841c9880d52804c11000300749007241106031403482d5000724200064071320021a125041c1c90081c041100d0603a02c0d918166a06030f003130b00382000c003a0702003416000b042e407148200c0641b640c425641140c0340f41d00e00001850303805030903013a90820740103124100714181d410014550f00e0882030900d00b610140c1c1000007900c03010200000441d90b1b03501c0d501c04145200a00840d03541c581d40410400507050742101c0c0710000c000c1144c8250607505000a00d140303003490550403500c2119194001d091060404007071141e02d80201c1c117220034944d00c4490000043c0d4031405464800c8010703c000701404115818050071101c0c00b00c0040c1c01003001e0880344005480c4c02e00000000081e5800c1081ea10700c00b00d03980d1401003050340d0000c9049403054091245500064211980e40c148076800c4a443d5800b40c1d030100c00702d10481460300c040304540c11042004c010407040c241e500044504002407019920b04e599420b480c15001000861917804000d04 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 820389991 1250 820388741 820388759
    0x6040f110a180503060105060a03180303051909110d030504080d3501050f03031207110709110703320909070c02012a05030f0d1d030405060d090b10 65
    0x40c2c003905002140c0c18502008292140018040e060152000180844caa02c0c029088030104404180ca03660081686003002030041c2010340f502100802c00020070720030742406000394041160024044800202c0040410075040300d0075604905110060200140302c484c2817016404c50041d07526a0284036602c112019580c012460041211001e00350403412000e41302c800040c10340d0003d071100c01041c085440082d281d0300810000541d41110007003000b058643c05000029080c15000032640c45503100c2600b00180c80751914141000301003032060202081c070404894840b6010704049805686400401c02c034005181189040511400919a00d072402e01070041079100d840303881d01d4840c0800c5940000c002007000041e00c2110a043e05132070100c00c00b400d01140b801584242126074441d08001490055000801c0e1401028a02030002000303604a000d1b0f4100c500b0f6a83c0a145440e092030b04129480e00b2220703090301c030786a032078200c0c1c40055040c4104600903007421041c3c049207440c100c601d03 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 820391241 1250 820389991 820390007
    0x1f14031f050d0308190204030206071101030c0f02120d06150e010f05031608042d110d0b04080711040e0a0210320d18141609020306040f110a 62
    0x440c02040b0305015074012aa000b40440e03084520007004030400d480e00e4005001a000365007001c2d520260000308582041818034210007000c0e0203072414041c034a040c04050b00c000341400100c60140e0020102d000301500104002c240e040c0d821a0f00058032522861400d42051030151400042080d6002c0c0038400c2d038218011944c2c00c602840d10a00d10302c1c0850075070403201e5000022905002d10003000c202040209590603a6410243c800c242c0d0b1540c9110300729001d55111001521420a98861220316040c0b0842d440c0566030060701c1e03030a0030344840d5110f05095100b1101070701c28a010b255032040315520b90140700000c000c024020401c00019004001180d0240502c000610550084102a407000702d11440c8500c0001441411541d82c0101403030024400d200502c2d86803403404a0322080340090f441c8186a0364001d107000c882c1603280301b0010f40d07254401e00c3c900341c410042c0c5408006052494000710340c0004090310129241c880c2402c0001030f1440c0c1158113803000008a0803100040c1e03c4411 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 820392491 1250 820391241 820391249
    0xc06110c06030709170a06111b0c010228060513060c020d0f0f02010b090705070515010506031302030a021f02010f020310030f02010207030f0812010506091f14031f 72
    0x1e01451402c1400002c1e0070354406200c0d4030320001460060446011051009240032070b04608140b01800e50007003000e0540e4400d0b81c0c1d650700c0c0041c940c0b05a0100b00700041d4543d91482c1a00200040718002242d855400549541d0100300c0248a99070070014100c2c0c000e050080d0f01c0e1070f611907032040041c80e1680545045000c00c4085508c4413003a2040683d2003940ea80c0d420b1075604004915000c030b20000c81c05070011340885c0b80c109404e4418001e02c01d50010040c51042d0080041d03660964480c0460b2079051020705c14154400000d1010841c00c06405210141d002c2c401800c94410301d07003550128481d1007800c92000c2d04442000800400b1940a0080c405040c445d24021441c40ca801e00d240c03d0070021600000e090180f071500d11000b164004c0020a020f0b541094822803012031614226449500a80e0150a0044c2ca44000152030034920b068038030081c0300404180914100d14079a60484c01c000926404224018400c0010004044000d41c00f0748005540c2d83c9001c03110281190107a107031a44 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 820393741 1250 820392491 820392499
    0x40b060102062e0915030314071a06131802030601080f031e0919050f04051519050607051612020a0605180604081b0405090a080d090c06110c 62
    0x2044402d900307a59080c00c03441a00700d0380a085407407a1001e00c3c1c8404070394000c2509186400440d0144451442482046070b02c84e84e0f50341500329005603d40b869020307070355000300f81030142d402400c42d1040343ca94940d805080980200010b1400c3d045a5050700c10036aa4a40c103010048180415828107105035809000010300405c0c0076040d000480e9564813503900e100c4cc01c1c411400640100c2c05103581220b1081600401c184401c200c41d0b1448104103c6a1007940c1c4101050011760030541414000d5510600701d00c205003006081c0310090008a10b5620420911315110f610302143e19541c01c000340504500800040010f81100b804401c844036103500103410b030341c082d0604c000c0140d071154080d40c00da50040c6049a01e074201403c0d403080b443c00f000f0000364800d0001c90042000130000a00c1045410300040c407201d5500601d041c4400c40d402503c07e8244c0d0b800801c0c0583c0455540c000500294182c0800007402d124a0303210b03200c6421281c0c10200005e1510001041c0c0200100b20705224010304603 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 820394991 1250 820393741 820393753
    0x15090825150c200a030507060603021009230603010b0702150307030204090629130506040902120f240d0c03080a020708031204060504320706031112220803040b060102 73
    0x24009039904e0340341500050411200050b034508110140c0c11040042da4041c0000381c40d45181a0080d01c070142d20f01582080004060341010b0817803032900307078440000000d442a49540d081c142440c00c140d10009080c3e0f000304104402100300c15903e00214441c004035030300182ca9904100c07101c400c0d0f50305540044080782c682a88044800800700c08003a0044030400320a5981d1f80c481503031940640c00385d21980d403008010130001070f0145941c004050800c1c2c060214801c4ea039452100302000e0400740c0e004407075540c01c94501004010961403129061000030895810a401d50344c0320010140c1941003103610304030201c0e081880300c0e0100718880c054041c88014604104807100e0544140b8001080a0f203c6130f1141c0114083c41542c0c0c0000d00c14141f6110752030170700c0502c00d40080f8003c40689040140c4d00c109100068128460712500f5a6100840c10a516160001c04601850180580400052201e00603000e2a841c404801c8481aa1240000b540c0364174050400c162040c0c8010200e0381550009 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 820396241 1250 820394991 820395047
    0x806030f0f0c0420180f010c1110030209120706020f211b01020d150614182e080106090b0304060509030c1915090825150c 54
    0x82462007518600b0b41c0c001841413084028000c0c1c444440307910580c0c95500258096a1405550380300c0340000d000c2d112011032030509001100d4201101d24064204520505006100c1c03a1481c520502e00e6072a00e8094100100c0743e0000e441c0c00140c1d080364407503511030481005030b150140440022104520054042181c018158001c007280e401903909081c00c0014041d4007a05a00340071030b961006c844021921413000883c0d00d1300814000b40c550f24204100030000412074070030b040390318145030407030303951307410310310600c030b600b107510f60014071a0380e119100414001c0c80c0c04c104200390b05080d0f01c0705100d030480c0c9640e0002801175101a082103042010300901031101d0003ca50843e500a0740c231080018066549510700750950140201703d018601a04e5103000c403001c82e505002c12001d0080d070419201d8200c00c10725504076050f00b0070041a184060250107240c1008601310060540460384000d0100d445039220344000141d03c40440b0940da882d540d81d141550b001a51000c3c00801c812420440410 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 820397491 1250 820396241 820396243
    0x9070803030a0b1c1109090316111f0f08101a0a02070b13050310090b2403061008100c021c03090b070806031002070f150e0d0806030f0f 60
    0xb8080500715440318032000c4951111190704001c104450281140c3c10702d035180110550b0703840545140309080307100214501807400f108070f03410300081c400c4450b04111150345108140220a07442c5510002012194548017039000210711603444030341d03502008041c804d002401781500074012044002c200401030244506000528825401d0f0480440d03d0f00303081c40040789403168a4000c03200500d004501c108003070482c1c0803101c09494085050f07410b607504421441040314441d000246c00202c803c0e000c9214110364241c3c05440c800900d550301518040311000c280340240c01c0e11418802c444c5880104910030041c0041680a00b45d104203001551862070b0080d80c508007040a295490419559003c1c1d0a001e0390051009039804007003001203151140380501110b000715899802030081042001c0f5070341038ae00c00ca5407416400724004805031000c0e00c900703803c0f52201410201d40c6a859200410500741007058982d40c40755a074448445291a07018142007820b841104074003684080300441d070a80e0 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 820398741 1250 820397491 820397497
    0xd02031f0b0409020318101a0f090c0c1903120606080907030816020a09200712051e13140105070c0e06040b090106030b0108150904020d1118090609070803 68
    0x1c0c1e0f0440c0507803261241c10f42800180780c05c0840040314401d5205c110400c1025400441001010107030a03090700da5041e05005070705480e500101d901c6220368002416485408014208020000e4101c503000c1c03032200402140765801031020781c0030800c10340c01e1416a200500445c00608150f10384501035003004800d403a903c460302d00008101319400b1848000100c000000001c41d0780d00204407101080d543c1003160020000300c030400c00301d81c07040c80000c0511091001150411503001060307082c601d0034428104d40079006042c105c0d080a045559181001041030050140b40700c142b6a0314204502d041d90420748143c240031228103004d0140b0100e07001c521008100001c07122a942a2003855550100140080c4000c20f5550750240c140b0700041501d075072551040310740c2d0001b0b0b00c45580544500c510580801c8261340c0d81640203e101001030010300f02004039031551417083c401e40070140001c03400141d00040c080f503c81032510207038040051180301049407940000040e8003411a141c00d014040c0e44900c = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 820399991 1250 820398741 820398749
    0x11030403080411030a0605100803030603070b0904090204110c070608070e19091b02060c0f07030c0c091b0e1c12090305010f050711010c1209050708030d02031f0b04 72
    0x80010400074060025000601c03d45030300060559031100460b10f000c0300145005c0d10303c90228402507101050303201c000003ca0340074400003801008590704e412149181c540c03000c19541c1e0003503242d451650068403039008074481000d061441a031034202888945240c80486d901c11000c22980c1c505101c0080e4002031034585032002a00e89a004500c5035045059000f00c0e6403010108618001c4004851000841c1c14194401c01340d094072100d860b400e10280040c0614005054801810010038000034002d1081d01003d901c940f20004006641707011200850743c5c80d444640309840f041019503015a800b8540e0303c041c0c4c004482c90203242c40c0d5034090300d46902414100a215404005903450654022100180250740c04802030110403c6190348102a0800f540c05d0302c041401541d940d4403010040c0a23900102203d55a800c0102100c1c98407a8050903c0c80410b4078035000f800030108a1440500007090a040078410144c0d5906101c556800034035003000b40403c1d4454a03440500800b00c002c02203804030303 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 820401241 1250 820399991 820399997
    0xf0d0f1b09120501110c0123010f090e0c0310050604321e150a09090b07050a03020403060f0506010806150304033b04050a0204050a150207033311030403 67
    0xc207003843c2c91030041c0581e1075022807100303011a0552000005401806180c00d0320680c040f41c0300441e02070004003020a005600d448001c482d424004041250700140000c0c807800f044414402c0200007090902c6000e00e031002c40130751604100551400c060282000000b02107801d0300c518000f40c0407884d9003841204036850803030a0540415007501c03101d108415a01403008100c500f42c1812107500310022108440503005802c92480081c4c410440c0c03103102c0c00d540e0407042088030341e902c0c0c10084039954805d003503503000d040c0d0900010010075180d100f403842c1c2c1c1e444034600180e2400c241c4c001425809004002c14858048581113111710b0244509481e0040d40c1400c100e00c00e285c4000341400b000801c1400c1c201390b1500c484204a02d800d034101141207440007502c00f0402500c032929401c082e48224021141c12052980b001c11040d800031803c050141003500c107030342c0341686990f00c0c031807146c00c80040504814041080419035207540c0076003154810b1082c03801c01580d03030b00a162882c1c0e800002c0001c1c0034 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 820402491 1250 820401241 820401269
    0x90f04030921171e0301030215390d1709011b0305070c0f05060612010b010212370e010c0f02040e011b0c03020601050306060a1205030f0d0f1b09 64
    0x46842105503591038080060b1301e440d1011000c14550a0341013448203910070640f180e0030f900717018500303011940084003000001d16246c09620151804002c0c4014030549603600380384900c1d089005000c0340c1c0a004465458101102e1044000407901e14041c1800d0010307450b0010001d10034954440b04140b0117180d05020820750f450a409030f40780390031164064003001d80c44285908011001c10044e102302c2040f901202600002007150f07080754403000e06a405a03020041012074181440c0c043c00302e5001032000c0c0c511044529441101c6420303051072a45034001204184c0000307a800011100005000386000300c00c00c20300340c41c0c1502d100503800340030f4015039803490b8040d8907010030340003124146040c1100001c1c290000340000e080f050803500540c0103001d544008202841e01103900307802100000c007509281d0f8242392468080180c0b40317404407944c0c4003c01141300346051320006000001d0b01080c1c00a181d046200d42d481c00e661130713080300340900030907038818481e440d400074416004c0c4c0303202080c9507003 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 820403741 1250 820402491 820402523
    0x60a02030a080c040815011d0c0a120e01020a0206040515041a060d05160906051215101d10080d020a1b030605010f050f030703080720090f04030921 65
    0x2a104d2500315000300e0240c2034080b1040002e811609040300ca00a078009a41e00540880c0303d002c45003658044046c21080004241052141b07480792640c044070b140c0050440c41c24040325089030300c0010b00f400940c0081081109008080c0a40b505001c04c0000303840c140c1c0b4083d600ca5480800040c1d41e500301c1d01100c004110700d911204400404c1c10784c40402c40342072251005411710070b03a05501c95043d8031400c00e44049460306104e422003a154120070014a000d61000d101c1c035502e80401441c1c1e10282c101c0700d0000032403100e141809000003800b43c0444c00a0304011007072207902e1016401000e9150301c00329442561035400a07031241d1060304074484000d0112200200c1c840e80903568800350009080000106e4400b000344943c10848004503004415558844280340c0c54100303c2c03202600c480e10a1040340c0108540c8400040b0b4904800a4010100c0321400000c10b80b82c0e064460880503940b4008105c101600103292601902c41007a5814040301d0041d40d09100108540006009001c8002405 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 820404991 1250 820403741 820403761
    0x30210170703050717090105101e090207030c02180609060a06022e2c060103080406051804020f0c10060b0a052a0a1a0103030504150e060c070e06060a02030a08 70
    0x44100d101c0c5e1034008580c105106090302800090b904c6200f101303001d481c0028641500201120341300c560300c000800302858001850025000000b0540030712890880100041c0d070781d5404a061100c00b00095000340c00c000701402510302000304200d0080c80e8800d01881300c19000217174600351001d0000707000c981c0241c2c03011400c0a100941c405545c01130516450403078000001515940d4807100000d000c108070380d81074569a41e144203200213000a0303800c01042c440a840b46004000c42d031007030200c100502c600d40b0003040891b40300c04100c4a0741400820b400c0b070b09003030900c009480103441e49424482c80e800c13741031941c60710503c200c1d1014010001030340c2c206120800b000954408800c1c84d091030300311008440b01c0c0c841d05044000c07524003d44991540d103080001d0b40c0c160503640c00d40e03921814581492078445482d4a115510b0092007901130780d01d24142d1710710009150f01007400b000f0300029460042d0442070a08050995840b400082c040340b00380d90340c0001520001000b40c0340042e43c5480d00c0880d0 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 820406241 1250 820404991 820405007
    0x4030b0a0605062b090c0f0815070503180118060c081e18100c020a02090108030a142203061508010932030d02120105030105100e060f190302101707030507 68
    0xa041c2c1501080000e500004c07c0f46440c22035050342d040d944080f0300d2002ca40e800e10021501400411401d1012502000001d6900c805680181000040724003449169030f82c104409202150302940394454072034816481292290010480a803041c0115900084407a414170000c10191060300d1001c01d0008035a8208441074021038a100d04002e15000c41c0d02c001d441d00c102d01026801a000c0c60700002d46580008102d400c60700fa00e030795000701c1001d9070301071490707583c00061828403281e0a5000003551b814130746600002148100000074244094058401082a041d40109074992404520701c000c200400301240520120103808500e052210aaa50080c0d81c000b44013225031101003051346413128241d00400d041e21000e0010500390b80e869040500f40ca80c11910385d107001800c4c00040003480c4a08800b17a41065000740303000302e81d07030090b00854641400016512804980c10701e00300305500f800001d283c201016450b03c003030a4401541c50804480018007940c1c05c1540e00c1c800909120310500304 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 820407491 1250 820406241 820406243
    0x7150909021611010c0309050d08070b1602071401090e041707030f0e0a080c1e040c090320060301170c060a0c050c030609100e011104030b0a0605062b09 67
    0xc215214205003403903103240c0c0c1c030a2004494001c0c0b07001c2041403c4d8003070002e50400c40d90503a00e484490b400d10050100c40103144500b101c540d80c0c06c0c05640c00084e10011103511541d90b2139290b0349414000c00e0001e1501140b9889900394422240c03048240740d0f880b0a00c0810f03968540e41100c04c3e074585240080d158801090b224070800780124400c0304066100f2024100c51040d50340c2d00c110300241c2010007111813190310440f071966006044054050800d803090341801c0c510141c0b03400b4085811808034050301c20309070300c81000030818072741882000380040700b991a448142135014480c0301c040e0049071091006000f03041c42501c0900784071382e1400b41003040210700640581050740780d10408401a148540d0001d0441e0633024801c0400b6050400240451260303040400402ea6010f00d84925002004140030007200c654031103c44c880425031140080c0f000303510521030814103140414a00045400a4012074400c140c01c10100150640661044c1130b400640b40000c0301704440e01c5844ca0003040000c00c = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 820408741 1250 820407491 820407509
    0x1150e180c0315031903110c09070e0a09060605040515040302030a0b0610020f030a0e0d050610080d090501050a08060316170f030f030109050916080d090512071509 72
    0x20402441d1190300025600904100e40041c2c81044403604060b12440f074030000b110002d0080210102191142400620303040762081070352002ca90345400310712404801c880c0c402c08a07492114030115400e101910310020100708000304925814100010000c2c4a14411540704c0c0072003d0070824034442550440e0000c660060031100c580102d840d000c0d554100031242c603031140c5400c0902802d11360001c01e0108102c48281c000c6c61030304810000a03500d581032007101d5a0810001c030f0101000a904100090041038680c1c5020140d526081c06a49040200d25000303080110765007040269036000416584c1c030900c1c90402c40310507501c041c0460700d03080351500868907a0a05030030020758a1501401d6103070f0102c03d4004e031200c5110302c07282d07242e0342d224600d044000c84c54104010451890181d205941190009050740c820071801300d00c507054101e00c0d0b081043c0a4101400f2200d191b5004030a000050a043c1c59808440c0383d21640c072901c0301498802d040d0020681040400403621809007000a460a80 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 820409991 1250 820408741 820408789
    0x405030d0e100605100801061107030b090a060c0c030507061d011d06010902040302091b0c0d020c04050f06060d11090d030801051008090703030c052404020907030501150e 75
    0x40394180d4a50042c41001141460b04101141030309100d400885441c00949660081da46000030803100035101c10307100b03041405881004070026210b402c03a80c0c0500104002803580c41030344d0411600710f4109800178000c0c400c0b440488c800280d040310aa68407103800c17400c00104080da0000f5180d503c1240c5512a1141d4a070904c540c90074241c2ca20070702c0103050017204a844507a2100b900c0c1c4201d21450001944c0101510006200b00540c000071301c0c0c2141c40b00660750b09140003801304920b8001c50712501405170300603d41d6858141068070a1603400030300300c0c00389074050070b140010407810720a401d02c0346030f099203a02c09021082c0043e011544a01d4010b000481c0b01031003420b000b03041440c28040d41d881004900c0b1008565441054540d006081c06805409070510b10b58045ea0307c400003240c12200c90058200c80c8419000003805c01c2050108620300e41b0a9140500c1002800d01c0004c200310b0616281070010f100485004c1030800711081320307081092040303101d1000580b0310401f914030500810940 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 820411241 1250 820409991 820410011
    0x50405090a14150105040e0f070206010f0f030f02040605210d050307120203100312030e01110702010516050a060f020304030314240f0301060303021608010207081213020306070504051005070b040201080405030d 92
    0x46410307031107007408ad42034841d5030f601e441081c16403580c1c0d4402d511f841d0188507014808074008010321040e070303480103000090440da1000455013100700030081c40c43d100540c40c04141e030401d0074859080e010441d03251071859407030300325006801e8007460311003c40526800b000080c2000041e80800004e140c202d0042d42d03c050300342000901500d021308680549508024046092407802c009480801e80c0c145c5540b800c0c80151669580b14203013010080d100e920824101a000c625030748a6100c6010801c6401340c2e40703240a003006015901d4090300a00035031541801c200186021481340c02e00c0314020b4002e046601c424400085d9038078001d8001d26419482c100c0000b040507000611006c856104000c403124481d0783d0781c079107400c03401040780c0944a92400c01c840c0382132442000105a00540c086425400751101d5008603140060403101000401c0b8009814030aa20703160081d6142243c40e407500c180380c821030b96281c0403a404e02800007814002e2440110381040310501c21348240403c00402080b01c9481 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 820412491 1250 820411241 820411261
    0xc150f09080307020708161a0d18020901050609011d1201022d0f0a0305060111030703080403020613170c0a120c020f01050f090f03010f0903050405090a14150105040e 73
    0x70954070040135100d5660b00207105a0701044002c04081c8000204840d2460000c803104020315001c0140b00c2c4031000c1089001c00d0546100788800001c023013400c0c0d182030041b03106120b81040181c00c49485401306000318041c503a8081481c0c2004401803000c0a80c03a40c1800200e10702242e010a800815400030a070700d0b034014840021031004807441c1e030400d1a58a4503042c03021203171044c21003900020108020b80403561b4000e40145401210626000300340609006105082d40c01c0300c40100c000030064000e11041c103030704102164105003045000d070184a8140c1c2e4888841503282c0c144c1d15a110046a07000b4110001e00800c8281a04000d0140c0d1490003440000e11b052450841284074440790184048036512074810b851420340450190323450460315400b008010360072042415490341d00c4005c580400600c9000e8407040c2c0c0c0c844e448d51070b1114100030801c1054600104080e503280c2ca0481d00b0181a01c0d29810315800c0b0340a02d83c43c03a08c05d0803242c0100c0b03c43c4526040040d00d220000244200504 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 820413741 1250 820412491 820412497
    0xb0903030d0e19030e0f24031506030a021207110a1106090604080d0f030b10200d0306060806040924090b190b0a05030627150612010902010c150f0908 66
    0x8003200c2c2602e03006e0140c8200001501d21302e081c08001c07109440d10381180d0016000864119808805075441c42d009640002c074640c0c0102c903019200358002c60b100b01c6020410204a81001d1581401d0200f07440d4a8202c554542494a01528040c000324070380c0c3c01501c40900700c680703000000c0c00880c0e480341c032000025500c105e039005080028044088010200b0300c28441d29000a00007894003500f600c01c0c42d411642044035030001d951000008108004048041058200c12030345624081400c614260010302240310081100d0b000c2c40c1450414400150020016500c8403111980221400c0191b200c210080440481c010800c10f2020144020017506040b05060504a10350a001d180c5401c1c0601804500c148a426050350015000c034069801e03e5000003080c0140d0000805140c80c1d40350380390301d052081300951411000038002e101650400e1009490300d0101d10000703001175070b100d0780020140e656101003d070007280340b215040201881c0c5d1700043c0301c940c20490140600b00c00d5041c40d4407164 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 820414991 1250 820413741 820413767
    0x5030c0d062c010602210d021c0b010f0801030203030f0c1c080118180204020d0b0406090c1e020d0c020f0603340c0b071803080703090b0903030d0e1903 67
    0x10201d0b000008040c1e100280c0d8203804480a1003442011505440e0401590000344080040580070700540c0e07042c0e414525041e444001444020402400180000d050440108045410010b48100510241c0c5000007210004158000c6069031111a8402541440c40c80781c050b8110380d509040b4540035130f038040a0a4140c0b045072900060401c070701d090383e00c1191903607084c0c0188510303481018005071809074040c0c10034441088012860718000c1d00003e00b00c488076000455503684e00c0302100003ca80c00b029114590400e204856401c03050454081d50303810600350800d0400c07440541132011900c0e4484000c10007130000d844140c0302d00b05140c031101d11849c44c4210b42d10303011a840411542803200345c08407c89900d503071120f450b925815114100c89140003800441070141a601c00803900a50703604503030085006203012510740c1030741d1400038101450b03680054104101801031710a6aa408021a8400034080b280010f5003410380901c2b900f0700503c2d42d9507852503440080c444c0c05054005a90030024 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 820416241 1250 820414991 820415069
    0x130506090a060b0906030c0112020d0603060e010e010b01050409090203190803090f031603080c0f030c041403060f01120309090e0d141305010c0807170702030d02070605030c0d06 78
    0x41c240202c144491314204580156140d48400200420b65002d510b00440411044001628124862101d4020303940c4641c4201c803040c4d66a400f22101580c2803282103072840841000b0300c0116040c10001b0500d0146000c1c400c40359541d140030f070301196420021103841010303006600b00003510f81c0c00d0849440d0030417103003030900c0d020b103003015683e80e28040112031a02504841321085625140c40031603a48400070070104000b04200004503440b42c42c10b0245201b140d102d0300c4d60b13955500341141031200103030b03d00c001d60203580500144041c51080710303c22410348541c4040022202240c2c181110001001d13401060103074a00180000300d20000300f9a424a00303010345441c8100f1a40c0000c941182c400e401c648944150800d105010640c0b00d086200b140c94001c105c1c90742000c0b05521444120719501d444602d40b4180054840c085040c1440541804100360001d800086c0c0781880c0908944001069490398060000f10006e6104069000c20090072002c1183c680c6c20712050198140c880c4400d000c1002c03 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 820417491 1250 820416241 820416251
    0xb1321110c010504290403080720092815050111030c0705040c05041a030103060501050315150307030b0c0d1d0d0c03030623040608030c0a0b130506090a06 68
    0x35200000034409004101030792428a0036103005030b0004a542c503649400900004aa00400412203541c00342003d5805545001e64031125460046480f40d950301b400c155212288903841445d60304c0301301240d40001178003411000e50400001001c0c0c24035540b400050074600d89410310385100d039101c4803c02944da0a0720307032141003855000420f559000c0e040e15000a079200d02001e00860825401c41700e051b038168180310381026240c2c66031215001000b026610f2081001c0010800c0c801d003402003a00504060b8090a40c100d40300080000d00d07240107244813030041040300003003442d440402c0801c00075500140d60401d28103106038600301c2580018103086955081250140e11050a40c8440000c5d1800c5401061101649234064440c4801c1c010141c1c10f0582d1a00e00040c81d00100c0170550040d1030020502c141043c0c55410072044405941121481e0b41c010301c15010020382c0003605030091a00211b4190b250342c0c4502200c59400c504001c020000e000d07060034044001700c0000c0d1115030318130500d01448 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 820418741 1250 820417491 820417517
    0x30e220f0b0934020d0905180703110d0e070311040e061b120c0d0606050a0e0f06040306061d09010c0503180f011d0c0a030b040b1321 59
    0x7692000700c0801d902800d58804500c541006100c0b0032500d0030340b00074480c82ca005004076010100c400c00000340250f001540240c09540e40608858094001107405102c00030711030400c003048210050807042815a0781d08082000030341d40c010f0342d02c81116003605000d0441e410032140d446100e28171044501d40000f2405040c2d61426001340310140d035250b4014241c40e507038039105020300210401d0305451820104030000e04c070002005650300c540c1c181c01c6132554a5055000c03002c11610154042c1e0104502449120080ba03032100d407191800d001240d8801c111070032000086d41c2da208030f41c8010305842ca0300100240c200002d1030414181002c41d020313000580c0d03c0d40d202030b00740e402c0e02d81040c0020380b0070000503041e03542449981d0020582281203480c1103071214010342c2104e200c068842010300c100c0b40d0658004408001819201000707407905203206142d42c0d16042c1c0c0000240c4000c080da180040061162072400b45480e118580122110510710035000180812003140102800090b0307003800914 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 820419991 1250 820418741 820418771
    0x6030222150305370e0303041a09060907060c0c360203011503020a021015091d06271209040e010b01141818090d0807021009030e22 58
    0x840b120003e002c9083d004e407030140035044042e00303111440e40240e580e040d150892813810000f45101c2c910170994107a42c141000746415207440c0007020a00c4540c014020407030800000b03c3da05003212418104080701c0c4d030359450700e4824015260010b80c1420100d0503180740c01c000303462242c5401c1e0801c000e41c09070301c40e00c030380020280c1c44240900728a000480c1c40c4480c606210341d004240e4800107206940c0c0c6104100900c200b80c540d000384140070003000d02001e0048600078880c042c1e401900500102007420385c2890181c4901d402880c100f50a9103085540c01000c00340c40c02150350b01d5032101500c01c0e403400c0102d050480c4c2c011058581c05607103080408403c2c00c205200f03425003407005840b064000c0902c2d4185a43d540c1c072081c2281540f50501d814804140c40c0c0b8503120083c1c1c801c00840d80210302d00f00020500e00208840c1c070004010640c1c06001140b50003281c1c0d0500840360401c0840e8104080c142500c122004121650b00142901820f0300e0000e08005003e001000d603007010300140103040206 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 820421241 1250 820419991 820420021
    0x30c0901091d040f060b09090705010f03090b0c032a19111e010605060f12060301050c0706090501060b0c01021309020a09051e150408070f0f06030222150305 69
    0x8184803100b01d400705011800115018080511824000c540f540f4444049100d040e025503581e09540e02040c03042c0000c3d0303008500c040003082e1a00d400c00c2852001d4440030817074070707002c1c2000950850000220340040381075070503120590080d001103469440803403140d500c0381d800a0700c90203c0048101d10510010b04c03442a4002d10b002880003042151040142c0c60070b000410440041159a103078000200d41e00c0d420b02415000348042201c40d100c00640c155440034140082905200e40d14200402190b85911000d0b40c03e016044003000030b01000ca89812401400580c00c10075803084007044c0c82d4400c520540090801520f0b1b40205032040b40e40c2c881c050142d0094036802000f280303800b90180b00710b0801200a03071208079500039075203845800c81c0c0032400d0f140c1e8031603d8001c0c2c214001002e12900004102e04001050303070011401b091803030000111447c1880b0301982c810190001a8085086130703900390b215002e05500f050049036642c070100c812a4102c0c00b4201e9005c24100000210310025103042 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 820422491 1250 820421241 820421279
    0x303031501031e060807140f010203040b070618080d0f0e030301061202120c0403020a080d0509010c1a070201020c072705090703061a1f022a0402030c090109 69
    0x40c0035815485200540140c40030700c004810030804500559a11050303805480003e082d50b501a261aa06000030b400c11020020400350145000b00d5080d1202d1740e0000403101220341e5015480e0315078102d450180044d04081d150148800c07040c1c88070005102c507413002482c0c513260f220000c124051010600505403031080c1d25075801c6400600c0100312003802251004c01c8600000001441d11036030045001d0350110a0b61068103844000c60b01340214102110300e8006030000500414400580e18401001445602c550904000c0d41a50b04810003000e01e03000301d0f43d001d14000309551482c203240002e00139007007950704600500c075156002070500801c10142c1c0d00c0c0e4050b54504010204680403101c080e2a01a180414a01c5007030f8001000c07503200e11a50212450758030380e43e800c0c3e10211080006880c0c0342102c00442d034541010010890382c0005103141d1304c031115040302c10b24080794000c40542d8004031070b400340c2003400001001a180c182c2b20003481d02000c241c0740c82c3d01241d115458060180c03e1481 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 820423741 1250 820422491 820422511
    0x2a0201022104120e010201020c030d09050736180f03030c0f0203070b1f0311090f011d0601120207030206010f06080f07081b0a05070203070b13031e0c1e05030303 71
    0x300000f024841c0002c8445204180009403400d040c00c008149150300c01030030203644540d0307030300c0c42c0080203418816400201022104001da012030780d504154612080c216642d00c1860240ca0a114903656410004110b03900706000400c11245003400640c0500100044001070700c0d0441a40c0285d0090151b030001503071300d0340258240a1240e0301c2c011201c0c00500300f40718140300d10180c100707815459072045001d580718103096180b0f03100400900000f4070000d02401a20100030340140100d4a40310b07041d01c020345c403d0791048a103407a00301c0181c1c0c1d081242d601c0ca13869a40005440c03402d01d41c002501504030760092015289036580c03403d00712070321401a00c40c00c800034041c00c0456203a5110382e40c1e0035000582300701c550307021190703208022240e54880e0320250080340300419083e003035103000d010042c000d10840c561146402251295209850040e0200501e51800944030b15500b100d0101c0d000000c0364040300b1000c005450321280c07191440351682000f401c03021100b021496041c0030054902500c00e1034 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 820424991 1250 820423741 820423763
    0x8160605280f0f031e090212030307031d07030512030714120103110a151b02090a020318120406110a0b2403030403152a0201022104 58
    0x11421202a40720060910512075040000050030364000d440d014154816202c185158050384409015185120030840c1410f1502d1542c64000c2035032144180c1c0380342c0c0308000180c9081d031840003a85041e40300004a5080c40040100500c01e505540f0000304204d03580c0c050010408201c40171950340125001c0102283c0101000c0028140031324003840d0800d82508054901c65200c507501c03d001c0c4c0182101c440302c3d404120040060103166000f00b9400031060f12811055400e020203142e000c0c59980c01e140c00c00046042c1304102118008030b40c0c5200d640200f0001580c20402425406508140c41034801c3d251030160000c0d0701c401c0041e1111404048005041c10030b46014800c2d1580b41d90081248401e000368801140021170a580561103034040c84000c084416141030504080c0c2913482c1924060760040006001144410914040ca2021200d012500c0c0341401d0780c203c071503004408a02c00ea00840040398200380d4041d00074040229000000400c140c0e004003081400003810798000d4903041c0c0700 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 820426241 1250 820424991 820424999
    0x2041415040501050f1903020307091211150408010513060b18241f141315020a050307030f2303040b0a0e070f050a06080903270a080d03060816 63
    0x1510151005c410301110440c24a1440090804003000c000d00c1100000d50020403c461190800c2a031005800b125500046020b0f042e070320029017034203100c00c2c0751144c8a01c400c10710240d41403c00320340241081c136000380503a082c00010451b0000100c00301300c0350141843c05099072400c00d080d1032030491000d0380385186c060b214804400781d12201b0600c2d144402c1444440c0d500a5110f09041134064020040000716901c03c60300e0042803d141d040c920b40c1c1c4d80e1000c1000444c0313462001d2428060798480d56640c0d00d20f1006000607480c0c088002401401404007258030410f058022450800d0000980c481c0d10440031030040001d044800010f6000c01c4500a02c007150105404501c2e29500803121038001400403c20a03a0901c0c0441985c0002010081e9802c21b024901340026484024034980c100301503242404103490b500c80c080d452043c1e00b01c0009220707007402d13140401080030486c03001034940d04941d0344031030440e41c07034604046a4002003420702d040003603902400620740242c4102c2400c00105030b410 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 820427491 1250 820426241 820426247
    0x16090c020f1b0102070b0a050711040608030702090915041a0c030106140c1213050102070b030f0612120a030e0c0109031205130914040314120414030d0c0302041415040501 75
    0x8081c0d02c0604602c1840000700c3e0302450000285501d44081d21040d4940c0d03418a4040341c640d1385508058021810b000040241140020a4506141d4100c440802c140d80e4080350364a070610b1011031444040c0540d0030320040c003540c015407141c0a1525981d240240d0b4819005a481d8482807141e0780001e034001c4000b0b0804400c2c3c0f0003a01100015505a81e4034068200c0c0610707441c2c00ca0804084a408203c608001560f0100104002060020708040c298a001d400242c18101c0040480b405000042c0b00c0004500061144201280080c2c113143d07120b00d0b5106c4d009004095081c0c014146210360600d1009075030252400d5005c0302d500c4141c2070030112a0010444240d006680c481c0300301c05000c01c000c44c003038100d8090f400b8041c1040d0041e0b04240343c1428014502100764041c02483c2404004070400740c03207803165083d4803507007054460b00082410b0b5611481c621071040180340c010300c0e040740100c803954160002c10888403840a1300081d003064030100000c01d082030361440e200c440b08000030425540 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 820428741 1250 820427491 820427533
    0x120f010e06130f240602190b0403171302040e210f0c030c0c0a06050f0d180501050f010302120318040f0b09090d090b04050918070816090c020f 63
    0x1450034004100d6003080824a000c0d030b00710000c03041007035035940340824013120001071020040c091840100300c0c01050f00d1f81c4112001103500302421665191000030103140c025014821203ca8900c40008989011440448070a0303540030124421400d0501c0d0040420000801801114445010075601c03001c085808506901ca90300044003080306108030040c100061016210b0600070001400000600b0020020784071050b400c808140035041c0701403143c8180f41c0303081d9035491214540020b040090744402030340104d807802c0700900da5030a0070f041191001044a096040360b200780e6606c0c00301204010303055182e0245106040d1032502c2078900074140c0c5440d8214803030000313280400241102c4100c0201e00300c00700032101d40b22541e02c050082d004082e44500440c00420030680c042d400c182c20400050b500000140002e041c040c4100850b1388092028080c40300284007071006c40b1643e506103402d503d11414184240910180f40984a8900b1400854882465030f4500701403d5165001084400300a03 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 820429991 1250 820428741 820428769
    0x50a1d01022805060108070f0e100f0b210c160213050405070602100207020114070c05041803020c100e091f06081f0e07030906150308120f010e06 64
    0x2100e10000c1c51074030351801c00480c040d0708181c250070b861030601d802c04515243c410b03401641c040d401004100a8030040070303058000e90303000c007501500640700d01062014006c9140c010407210b104100d0b0001c0e04160310002807464241650a44091540d0b0383d10410f110300b0112a21160100100803072400c43c0000461140041d20003000c0ba034680c8501c10004049850071a4200c4155000d16400c0c0003054040160650000e1240b1080d4584003072075000070a004080c21211810303400209030301041010914004d4041c01000e0410000308004460665100c400083d00740c0c00350003841243c800500701202820000ac2054540c0075100c02c841c41071080f0711a008200b02c441c6d03038448000c031401d840d005000c00005d1559940715030941c10440070328000c409422544030380c40180c084041103640c10340e100302d0781d200389642000141581c9a09051002e018082c440c2a0044030018010042180d201d0150130324507641b000b00c440e55920300c072040004203800e0040710709002004000440c01d1400c40d040300035003 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 820431241 1250 820429991 820429993
    0x61803030c0f0a14060613050a0b04090303020414061624061e0503033c1207081305060a0903090509100303031a060409020d021207030e01050106050a1d0102 69
    0x518040050505680da40910100d410043d0b6a40c24049110103411004032120301512403030411900061070840344600701e0b110541c0341d0340040d1012502e54440c6031a020054002d0061078050714004000b5806401080083d94451501c142c075410440240c411218103a0001e150180351034450443c240044174032a0006010440031210090340c034020040207108045c00000702d1502c00c445000701300d030141c000b1800b030b034000d010b0141c100070b80c01003105030001100c1c120b22a00d0204d4602c1802880c10414004003900e00061100c1c0000c1c400040c5440b400ba1961004550346a80060302d0441c13810303000c00390590f8481404a580701805521021442c2e11a05007080c4035540c42002c190004000c954400e02c407200c9150030000d142e018003c244601181c20308190030540000d000a84600880c0a007040c06603000c1100c002c2c0c10444c4d811105505007072460039030b0038585070300024013808407181400c181c0c0d401c010000466600502c141c602001058442070282030750010180c4041e000c1158042c11 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 820432491 1250 820431241 820431247
    0x607060e0c0d0b06090105010807080f18010c120501060507080712090f0602060702100203060102070308070c0905090d17070f083102040605030601060e011121090414010506180303 79
    0x706980e814200016144900061180780c5061001c001000a0581c4480c0c180040e01041010881e800003500c3e90128406405403255101c004030700840382c883d050150545d40c0382440380315200ba00031801103c502c0140350280544e03a00c0d6042140d0328096840001e00c4100140584000101041410441031b0100c0c82c10501c241c0d510000c3b44641d0140c7d501ca2405078000741c00b80150b150f41400100031510030303d80103504d58104200001d644002510018250800114010040062001380749005001d141020b01440c1400480c07182c1383d001201051010924150442e042504c01521062207059a5210009151201e003015106004024560b2419181043c44c40c003c2001d40070784803010075800c1d4407001e514541d9105000485480d50041d510a901c448010000564407401e1007541c45001c2c41c21035081c40202c04c0213880c14580514240c1c1e810001c1d041c1072000000701001d800c038000d0441d028488099040d40f6040f0141307080c055035030410b0007006a144030550246069a40e40409002c40e0300d = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 820433741 1250 820432491 820432513
    0xa050d0c03050601031503020a1205031614070801090b0601050306030109240e060f1803120106170c0c0c041109090c03060405091f0b0d080c0604150b0607060e 70
    0x42110805031020011a40d60030074000070356814445d980c0d03204182d00582041d0350664000504130b84481c0b0031510201c1030124a0800c0080a0003a9514848003c60b0390442e00c1a81c0f401d50300b00702d4207102c003803100d200340200050248014000c03150029003002c6201c00c180c0311000111400c1c2c0c0000d00740e5070107649820300000040c03030301d1480e0720526603020300c0000380402c110681002e85d0382c00c03004268030303920031420302c66244500e94001f50403040114a480340c01800c181c0c00c41c2107014070403080c0f400b5116080001072aa400c029124506020094030a0f03003a5070b240840300f03c174080c0282c0d003883d5910030314101d0000e003003c1d071182843d4540c072440c0302c0c144172100000135050b10080f1000c648101010040c048141401d0080b01e0300181769401628030003107070b0380160001d8001141410442c03610b03840c0f074040540700d48414003055500501141d9a8512544090356946011796003243c01c606041c10460b0740c1c1c080b510072401c102e40300402c40340c0b9203541500e804020b00301804900e8041c0c09081d00ba20 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 820434991 1250 820433741 820433767
    0x4120e0d060605010f0c02151608040e09011103090a240c03200408031c15090b0108010806062419020a0309060201050709050d0606031b0504150501140a05 68
    0x5102103101c0c103004540203042030001007800d004a054003050010058040e80180e40d69001c6200e1001c9031321215403501400c0d10810902c50311a540904a40c4000501088088100841521440054000f403000142c1d886220035a8801240d0b9881c0d5a009141000d0000f6900b540d4050038441103030005079420b040340f4000040304c0c400c81403038011030307550840b03410f101700d07044a040304210305407003c03a0a107490034548649900c550400b0322640c103c4d10800c0d0b010b80069a000e07135640f401410301c406085445c0c0d0416070007031000101440c04203098000002e2186000200b0b18805d08000e400c2165042c5056211440301c2000e08010811100074031040020b036000c503203002d4107803c0e00e500422554001d030a0280030303034106800000459040204003e9840d8115007010221642074410562032142424040010445a00300411419901c00400940e4618220306020348000300d03400c00c000d50407000c0c040148182403040601107181e030b800c01d600054010010307008a400605003140b800c18441409 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 820436241 1250 820434991 820435009
    0x7030e06180f211b120322030506040b041e05030a0c050c191a120c0703020f01090b060307091404020d0321020d110307090b0d060906030c050315070804120e 69
    0x441940c0180d2440c184e81500b103680e903524100c03d8422801e40c0d035448095a03200d200b030121f0107801e0401d4a2005008a1000c450840210707001020385410b400d2502d00040d9024040d101034866400e2000e40c4980d41c589040302c0181f059000c40103516220041c001600c9020629000b5101c0b0f00411240403ca0746422010080f0610741c2c88000c80d072541800092221512240500c5840304428084072000554035101290480724081c103254941581d03160481c94030708440e590b0480c40d420041203108019407107403281d01402c001c87c03c0e10340c01500d034154002110112580d100c3c03800700b040082800f500b041c10b51052424003d1406510003c0303070104e071950403010b15003005031340341d03001454460303070710340e9201e117800000080360305a19500b000c0c580240084254020980213400014046200c0405580000028841d0307500501ca040d549040103078100e9a140b1410307000e805004000d0b5404619050b00c0b0340b007180c0e20380328004651240d0320381c01416100071208509100d112208080b04d503603101c0003 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 820437491 1250 820436241 820436299
    0xe1f0c0218040308160c081b0d020109111806040b031204031208130f062a020a0b06010c0f060c090905131a091e010209060f07030e06180f 61
    0x4078440341498a0010001e8030020700041d102c0d1800105a070042da031045016642c103411003540390700d84280000c50f00c22003800c5003403000307140306802440800c40c0d019045010384030b0281a40300300d081000f5050100080546c0800d148807644803000501c5441c2070b81c0544584100507048809040441304654a90390040c5c0050720a60101d820201c411940207118075880a003086402001340c48a6440c141e0860b074598006090a40f0b17520b9120604442e82c024140304045d40f03410300078002d03042070b019440c1c07070001d030069588807030040008010b540140c60709400b0f503502c940302282091660b19030100030401d02c1c1020307082041c00d0800144a01e81d03802004c0c01450b4150003031500c048035103000f0103900e040d0304c400040070010001704507070444003081c0440007100c030313540c01840890707448000c50080c400c00046c6580042e01148160b250001680644013a921075107a2002c0c0c401c0316810490f060040700000d11030600d80e851070300c0e406c1c100040c2041080402800702c820050352a21410703012081042 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 820438741 1250 820437491 820437529
    0x40503061f050418032001060b070209010b0a050a0c080409110c010507020f1f0e0a030507050709150302060f0d0e0d1d1e0307080d080601030c0e1f0c02 67
    0x8980445450440750316002403000b1541004107014603c0180c0418000c0c0c1406170611800c0034509460f1560400c0180d800c50749000200203590320b507042c0070700c640c00c011001ea0003441050008140d034441e02080f50503014207912000d0500c0403e820888003400700c90307421201c1d01d00034000090322214074040c44140c00c0d2080c3e80303d130f01c03251300000300d50860301c00030105411940004a41400c2c03420105440070741140f05d000354583c0d41009021403018000e4243c281c0403610030b4400e800c05040e4450007a180e5284550300307403080c1d2540c540c0c66030155581c50440201d10300d1480810001071030030100070905001b58042c60703824a104400480e045515500e291505604484605100c865101d000c801d58014000710050072459010049804001c80d4510315084400c1c605030381200d44d07004c00140000b054003500310740f281c0510b0b0070001e1506405440060210341040d401501c128028000c0c074181c4200036000641c210300301405031901200754060b01c010320411072120005620741c03003505900408855 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 820439991 1250 820438741 820438771
    0xf0f051c0c0608060312030a0510060807080a2304030908070504140a0203060f0306090c04050c0703050307080a110c0312060d0b0a050718170d020706170c04050306 72
    0x8400d00500309442284409a4250888080c001030803444445080c0c07401d80c034003e04550307214404a40341080403c880b09819001000300010b4000c980c1129201e400e0b0381400c1c0300c160756111007d68240030165001da006c204400009401c0d11440c5e40221455029525038030001b1030140307a0b5504c20740040c0c0e01500041e0000d041401119010030000e0000c2205079400c0050194010100c9042c100c0139103004c00d001c1d00000407070700650f1062405500c0040050a540f07450901a44a954405210351090f01643c141070004c1d06150510f07003610300e5203030103484140c40c1d503540312002c56982c6001030482045a41e113103288905100c400018000c0e1031080c10045a0343c011040e010b02010740d0040a591141c050800c4000000f48440d120541014a01c0c01c0820f282e00d07015429580d604107448170070766032242c084000400c0115003d41502224003441512071200c40350742d00b244c9410450040c040401c01501c0840b1001658100d100e5109003800080c90610303444100181c1000380941c0c0f00b0800960312 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 820441241 1250 820439991 820439999
    0x1422082a0105040303030b0f041112092103071709070e060316050108072606011e1d0609130204052107031e0b04030306180203010f0e100f0f 62
    0x404811240040c40ca00100100c032038550000b003240c826030000404042d00c400e030b03ca1041d00c6c0d1054140c403180c001072050181100e1010b001c07445030444106e080c140341412011860324080455915044140c2c40d0718503254030308040c03010351140c1c00682100c0030050303011408075403030189644050060401d000649050b900e040c40452036054060911846034002020a014280c01c41101307200f10ba2081c2018111a500c884081c1d0341b003c1c200c12005107146900145820303002d82019882d22404090325031000810148a0381c070441c40c000702c0c0071800f240180806000288500658000481004240d2454146441d0100c0c072540c2091140c0b14116801203010b00c91807a00031408075100700030072080d0f80c0340950303810030310303900c1c0810301c40945003942000d004442d50400c45820104650403a41c0b41049050078500180108490704c2544000071402003140350940c440d000301c03412156074442030040325080501d50300316034501520b45848d4001c4003100103500303c404100c0f14018040307001120505454 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 820442491 1250 820441241 820441273
    0xa05010221010b0405190902030405070302090c03060d020402030604020903030706091202030a0f14040815040b011a19110613150603080d0506030c0604090209130507142208 76
    0x803500030440780e50707520700040c00094007103000d81d01200e40c112507503001084104030000441000e6009904094000400c01041c010700041e604101d031b100340c64481040d9a06c6198249901082c0d40503903010a44001080c050301c0c00c0d40255400c0311005100510b001d005200280c60f40e0322601c41110110f4407500550b0038000f410410f02d0190616002851418091200c010907609000314242c041c00800800682c034001c252040d13401400c10074089400d250b901e00d81d0347c0800c0200300c0f030845048100768004a144002041044654004e580c0e4050805c240d0030717001045012000000c10422041c2400c100001d03408020b41070140300701042c1d00300c1c220002c0c100003041d8102c68205003181d40c07c091081000500341c03030403512600e0058034001501d8549400081c04c10402d0b00c0d0240c1c1c00030000c50f0228200005600401c40901c0c221507030050800c1200c0d041d42552001c450400200d00c011184005603862f410061103104038604050070041300d203222842607480c0d182c2101c10282d2010340500a9200 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 820443741 1250 820442491 820442527
    0x20120010f230601050d020c01090b01080313050301020c100e0118080403030f0c11010f022d06240d030306090204140913170d14280903080f04140a050102 68
    0x2c01010189510702000060200d02c5040301d010141070780040c00540b403200a41c8140106680120343c1c0b0340b156985c00c01ca0b07660707400400409198005440f8002000d2805100700c440340e00008000d0b000d00a60403002c02c00825655889405554076868036180303c4a86800719000c4511441045848134194100100308152007071006003400614445540410030901c510061903500f4a40079800b01ca40c3c100072030a0043c525107004c0e114103551540380200c00c003080308003205c0e02664203c1d5030503a640b1043d03540300280591045482a048507210040d820700c3c0c0004003c06001c0d04000c1441c41e522452241240d10662246031042d103541b50b91010741c500090f40d00c0d00b00202c1e1700307440e0f4070076401e86441d040f03012003031041c85100130000359440c1c9181407070700311031000006044091070520f4242c4c04071004d0802120000504101611405440501c030301c111808107070941d03510382c015500d0f07039090540d0040c05001070b903d120f4014400c101c500010014140c0c1184114005603c40060702d8101c16520 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 820444991 1250 820443741 820443791
    0xc130f0f02120a05060904060509031c0c02010c1701030b180d0513060815060919030c081624120203070309020a0515071209030203070e070f03020a0c020120010f 71
    0x3d4201018048a07031390b00c00f071094016820100018040e1203c1c401c0300d1444c42a08110600c203032a8101c41a801c03c0c45500c8118000260340003400032012a1004442c2c0314403240e050248071240302c0040c0045507a402c0d005508c84040b441400c2c2c0311030105d10740c0b40390020483c04000001d0000400340355210b411303804040103100d10b00b051003081c10a10b4058035000a0b14081d02d00505c0d0200d058440c5a6070401c159203203d1f80c4079009041c498807030800703a500c5d2040e4000c00229118604d400300540ad40c5055190444002904030714550350100c03035032002e1b083c0d5580002c0c100484462184456001c9100641c014510303034400044048561050000c41040c0368040751250702c14240c01d0344507444036000c50300b06070ba0041001c05285e151401c15224000039404c007079003500c22801d0105003d03000c012054001c1e8643e41303980c218200c030204110140d01c284104480003402d4189204015409051021a50034441100c565000f0040c0003c40c21641d00e07481a454650312268820026507448121464903 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 820446241 1250 820444991 820445011
    0x91101050c0c0d11060d0905120a02032223090603010b061e12190e06010f0501050703030603060c200c4905011505030c130f0f0212 58
    0x44141c03440a900c0b0071015804900404912003558104001d41a1640c1e651400501d00c64603241c0e00003080740103042c0d40c10100d8030340c4190444031511700c1864003954166203480c1d001b94603100129204140d04c620031203150104002d03000010440000a40000c034841151440441c1c408503601d041090200c0090700b601c1c023903450f10801011548a0714110703081c0300d030f00d11103a46500d6071074401172110f840360701c04070021007003800140070080c412001502c1c1c40014280d41071209080a040302512040c00b03210b00301c04800242010442d550050016150107402400c0020f10329540c1c2d241c1c2c02c01d8649814100002512001082d54503061038a00c0d60f051003050740040c01c1942d202400b00c5c07010361012032501c800d1200d0020f41454408900354030404e940c0c0300400300d00714030907842d2a040c040301c0d544030445640d400c151035000f80c512421000f2080b05c10040080007050244ca00b8841c500c902c46440048058588009000d102410b02070180c0c0010704c1329005968110800760f078084030030f026100303a00b1 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 820447491 1250 820446241 820446247
    0x40c0816080720070302040e0a121806260403080601090f08150c160b0609090607020705060309070f0b0921030301090216020423010b070305190e0a030609110105 71
    0x2c40e48107844003500c0066060004a412584055030f10381011684000e6200d030078640b00100c581d0001c42d020f00201e104551490060100603001d80e031458a0384c103100d01901a070001001241d1051070901c54042240e04041e035440f101d040c400c0582070b0221401e40c00f10766440e05100309035030f00c030085070001c0030003e00c502451418912500e4407194401e98035140e81c0030300408034030700d907411004460942064024468100c0303481d242003502b109049036458403c1d80c01e40009030403c5000f09035240700d043c0b10340c040e001407420402045103542003e08032400398407403e000444c07240e4080e02082d0250510038002a1241442c104005070043c007048600d21144444911003e1b5540000a5078151011300002580350080550480000891444040e5116050210070140480c44401c21328580801d401581c405a0302d41c000307880c0c54400c0c0040240003800811a218401c0800c03110040020864507042c0f0080298900140760310310550003e03201c155468410008120b51820b4078250b8290a00b01282 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 820448741 1250 820447491 820447501
    0xc09120c0503101e1505060309010e0705042307050f0706050609060d0b040f0303020f040605090315010503030418020405030303010e1501090f0902031e0c040614040e06100905040c081608 82
    0x759583d60341c3c0d10700036085d85480e00c900c2e020b105508014050900075001a48030716002a449018140100014545000d0180b000c101c6080900410080a00380c0d45840c0c010903400c1108004142c0040ca4401006010321404a01800711401060800d004442c0860103061140402900400140c92540f252401101480000b2480b0b07000c1c41d44a82c202c00100144003180c201540648076003100c0d03504410001802041590708403001d0300c4e0514054040f100c004412140000503440207010386640b603842440300b008030265080481100914a2602504140d5203401181c610b410030707004111100403580401c00c001c50035030b018103000102440c0c00d890452a088012107001d00d24026182d260750004001002428681100300ca0710102c07080500309031030f08a0180100740c0180c0034010000341d800001c1d803d090070302002e80b030503100e800c0160001521004104140342840c2d031221070602171807410003d0203039154481d81440d82c405440d155101c1c0303030a900c5641c11198640307112080c80a5103003440 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 820449991 1250 820448741 820448771
    0x60c03090703030c11031c02060702010c0504050607020d050d02010504140706090608150306010f150503010b160c0305060a02040f05040c080613110d020d0518100c09120c050310 78
    0x20880f030309400c04c4900040b05081201e00e507902542c1321501131040c207000000d4980c54040c00712461245500381c03441070726441412400e032000610a8000a42c0a110601180c83c015004268807840100540c1c4141d006a5525042c856031124190146c0d544030304000c1805440340c098a000b42c1c0c0c4201400700d003070030002c0160120300140030354402c00c41c08800043e040460403074100d00c0d09a008040b1401507960381007050443c60117000f043c0307050840541400c102806082564141c1d4841da00d6070703050550a903941c0c4400c45641c0400d50711050880d20010116405103c80c5001c1c07803810b207003d81e95500302012010250201c2e409640914034103529413031030b580e0001d0a00e030480c04c125503030903a6041c64091203005c0c2265100950752428000f46001d0007008942c02003480540d841400c0c80b00e9600e50420a8034009081d801440c80d40180c04049504507040d80440c1051b41c9505103190100d49515140110004441c006c83c0d080313030312901c1803215140412072111208240c0d8000c0c0a0744240010709 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 820451241 1250 820449991 820450003
    0x10170c0a230307030f06091407030b010201180209040302160b0904150302030606040b03120d091104061d0c040b030112140c240c011104092301030b0601120609020c060c0309 76
    0x80c0003055500d6080b00c84185c80c0e500000014002d8510500c035090013440d6402e0905000d03034a090109181292400065006001d01c1800058400e51982d0240b000c2d0203000d0f501034000c104504600442000c2c84034030140e18284009807659650700394a680301c0401344001c030340c40f1044414503403e0350941000141c0e0300140c0f85a0068042d5004160000c0c2500070918205d28195450029000444c0101d00e00c8607946c801200c0c90b001d65503c0c030100f180001848200d40c142d002e004d80b5039a440501c60446003041c80700741e810141c51300615103003070368651007107040340c10030707041158141c0e164024803090012990b68881c03a1102e0001038081c04803001d0014050940d05028030003161418200b0b00702011420041e55110750850000f03010041d0350204500d03040d40140a120ac81c0b42c604400841f400008480380610503621100b0104143d08588403040413903402031419041014444111020070340d00d00841000305100f00e405a10707054114a4141010307070052081d46031060510130084503500003c0e00d = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 820452491 1250 820451241 820451251
    0xc150105030114150f120d14070507120804030615030614010f06110106120b090f1b0607140d03051b090a0909021302120709050f01090510170c0a2303 66
    0x440c11244c600c0d5001c1050740c0200d03800c41d54845071464000320400030115400b926020b0076901e030b011250b440c03540052640500c102c043c1040c0d00c002424800310a2440c240b58606005111180c2003039502d40d034504c161200340c0082c603000509078000700100601030007150300a040282c2e0100141d03040103100001900e40e8402c5c05d0800c0480c585640090703001b9440500501150001710020841c103081000c05900b003a50301c94480d00c101c0c000114001404151a10510249510740c0405010202041003d0b08141c0c000c0e640307105850207078401c00341c040200300c20480003030b1404a01d07440c0102034800481081c04402e42c203003e04000010301940c2d80d40a1405540074100002030403c8140080350b03000c10054103400c1e000384002030a480d1006107041052050740140d03101240c2580340c80a208e500c03c18515414007040650381c06106038585140f01198054244c6001000301c3c2c0342006011840c00700f44d5020142c4c000010744141d0b901d81c410b40d504000c45c4da0381c030041c0f03174400360b2501500f01e4480205 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 820453741 1250 820452491 820452511
    0x302040f0c0206070e210c150f040302010c020a12050a030e010f0210021305030a2a0509160e0409081b031603050a0507081c060e0114011d060c150105030114 69
    0x8130009040d40d52000a151180d15140100c0c45140306c9640c459031142001001440388440d001003103c80b120100403110070812091401e42000d00e943d005503483c03140001c0032640b0a00701d40d000318110b040b01c2c69241015010703200601d9201c449050244c50f040d00068580e04210b00c0114540d4259000100b20070b80360303081800140e81d00556401c1d0800641039811095041c020344032810b060140e0303001040c9400040480f10168841c01d80c083d16030418484c40b80c545c10112940002c0c04507103c8044c0c0c06030a007950300b041c18100f60204006811901308220444284201040101007061004080701c5880083d50003546001c2c078980b500307441c20420260007030811a0004250300301c24461001e64100c0c5502c40d84241d201c50341448287c03240001c84040c074540710f00c1c1590005a0081c00808603040764202a0141c268079605401110f6031100c046428100c402100e5101c00c0b00e40b0b69030002e162040b001030140c4030507074031440c641c0780310801070380003621a81c18004080958031080141c1a08045829 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 820454991 1250 820453741 820453757
    0x90103050f070c0f1509051f05160c020a09060f1d0403020a0b13050d030606020c0a1802090301021c052203090e061212030907210605040f0b040602040302040f0c020607 74
    0x1280030002d032003003211071000050501c0500810800700140604424552340c01c01c000381d81c0c070386040f001240d2049070001c0760712120940030340807039025480c006d0b1b2190010b8807103441d0340d842d403e260041d01c04a0340318840301940381c40c003080554024003501041d41003480c81000142081d85009640c0c44842e40044d103524103280c0030501c0240d403c100c2520341941305060b641d1341c821440002d0b005140a1040314058000c030264a59146441d04881081e900d504011030385814805405000039084100c0c080c3d015035003000b083d0400c1c01e1b0600740c1c98080d421001c01040c18030b058002c0040c0301c01111070301283d5540c504d000703000094012000c072003130752070b80d80c0c06050302c1d0389000c006441d03004840d1a42c0c015001e540407907004032041d840294419401c00c4101c17018260380b00b10940d031a071060051030a0030000340d200704002600075042a50014041c4858107000d00d45a02c4a90300d14000340d90440c1c6907030f80040d0800460405010354090340c0c01c403220401848078204800b94036080008d141c88100a044 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 820456241 1250 820454991 820454993
    0x60a0b1206011b17071101021f0e010b030307140c090408040302041104150906030b0604051e04020f0406090311060c0c040902030f030a1d06070302030d02070501020d02030705090103050f070c0f 85
    0x34512120305a08001c0b401c03031300840c5403002500c075030041c2e10a40700b10034200844510b40d40002415807000c4144007449201c0381490f46004010b00448035069660b54840340c1c01e07036141d5020800342903114091911030b20700c034480310a010f1038660f0480420340554038400800021851100c00d0f6422241c041c0d5000c18400300c5c2c0313180040c440c0328540042c1100314446e0300c40c01a1700e0340000390000790b400756241000315804560801a440c0030702e108465000783c00c4810000700c0b05c035001c1c4007a41000040c001501300140c0010400d11500650000c80000b24a40010010b00c80480c60034180c0240955042d850f0295020304030340c60725406409240259101c8200b401103450421484e40c00c8e80351b03074041c0e0341c8840d41010010044c0250b4480d0140960140c08018801d00d0710008403580e0603071540085140682d0764245602231340018005540e070303560034000f2425420440c00214480d00d01eaa44690381c40c115580050211540078013100f603403524a03401c10002d01d401600b02c03441150000310501030400e003 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 820457491 1250 820456241 820456277
    0x6050717030414300d15060f03060e0124020c0909030901030f0c02210f0a030e0f120f0f070c17060901090201021b0103091a060a0b120601 61
    0x82411510400c40000304100c02d12104441c07030000c0031075600989074030b0610b1824181c00c030350200c000c0480108000a10900003940c440051250000d0400c022441c0c02645c1028031004a4a50009020070039a45e14156603581c5446468080c2201c54001d468550400403411201c4511442d0400c2100c8280310f0024200e0080014800d480c0009090b030b240c610b80a0986a105d0704004c00403400310b170400e8040011681c207400381554504881e80201800e02200b15000011000c0343d646030018003040050b100c2040800d4020004280c940d04d01148450020100307503d0650070303e46440040c0c200031101c0c20b5904102c02100e5110050303120660f1500b012402c450102d1082120003054140d00071000100c00d12400b448001c0320280001303850040d516000c80600782c4241e180028010380007a006811418020190023940c80d9061500090308015075850607020349540e02105400300d0844101301d014038258074400d010b800d041ea299810a550300c0e45030b071522080988034a041c801110401442054 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 820458741 1250 820457491 820457513
    0x31d0703051c0210050c0a0207060207031502030403050c01050a27020d120306050a0e010503120c030304060c052106120f070905090a20010311040305030d240806160207050901060507 80
    0x5513088041040741400038140c0c8075584890f01000c05402650000a40e41780041140c1003100d030041050800d110000625000a6100030021400d1100c10f02c80d41d41000000d20a01c0d2140e00030300000281d850408108842e2000200b140c800280303440700160740140c031102800b001840e884000404841c0407113006034080c148940155410040503203000400801444456048880039000c1d128000e1282001c0c01c02c80c4030320340d26160b60750300030004070780010041d0340492900c030200e240c81424288244911554401c0c0300f01104e038548034010900505250044103400000e200c2c00040511152581e01c0c551102c01910400c01d00d0741d5190b0005240300e1050101d2480b00c0d6026040c841c014555240f1191065181601180064540504082505181c904079020381c0d1f01f00c4c2c019403c000103a100e2401038588032001811800420085500e0005504020ba0150000c000503041c0e0740b6120150040390082034070030a0455016807020040f6880365010241515040e1070171669422460a100b40441 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 820459991 1250 820458741 820458763
    0xa0603150f0612051e0715050903070905160807021c0305180f030301060909060b071203090b0a020702041103060a0b070503210405010b04090b0604020705010b10031d0703051c02 78
    0x410303800f03141e42c10420041380d0302d000f0b421259884082002d84440d4540c0c2e8800c0c80c013400e1046007180562181a6004501804603064028115440c0039107415800c02691002d031800801074645101504070316401001450f400714191005144148240000b12042440041c0c8002403654a802141c941800604071010305c6111804851200d0010340365a5036950003440ba00e400160101c201140c1c103559405050200c5200d28007140c106040394031021020b5080d206500141542e441e41500052100c51580d449803014103401615841540148001d4031742170080035401d0741c400c008211840e9205101001991501c4144c281c407a034251401d18a03611440300441c101c000740703041c1c0d50500000a6400340c42188520002e1000285010a20040e40c4920000908100c2454002031150505501a040c0107001d8000802c03101d9003507002c6030082110741301c0e0000007501c3c1c400240f2801c01e80b801d0054800072500081c0100c51842d203c4039140ca0210034440c0301403024801d207548461003082440c41c04 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 820461241 1250 820459991 820460009
    0x109020f1603050c0d09030506070809010e151911040603020a05121f080303090c060a020a1a0708100602190204020714060415020f041205010204080303011d0a0603150f06 75
    0xa0381903814003030f10366042640e41045910645084e9060548200b00103001c5135031190081006858054081e20560001080000c83c0d650310014400114402c001194244c480f089001400d41441e01c0310946403180c90313200030b00c0c05040c04226405003000004a50841e1614500117031680f8912780216090301c2041024903001206409000340c2d80815466040c2c5c11a1040c1c00440544c1d84410154503800212503000303441e00700d481107600c02d00b00200181452400c0b44191888a09943c0e501d41c50100310720a046040c43c404070811070607503013005c60603801c54000501054040e00d400b500030b613649152001c4490380c0401c040c0307020854442e034056800c01c5500001a0041c00c3e0b0807034241d9034903141124150b889945d030108130340c0100301340c0c402c4506080340422168545420410788180b50b0f41900f1007120959030030040051120030920165020f001c0c90003141c45100c00c0706054500000300644425907852401c101080020388006843c20840389440000c9200002c21204800405407036104c0800 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 820462491 1250 820461241 820461277
    0xa02070b030a050a0b2b02031c02010f240605070f0605010608040b0a060518100b13060e01180504230c0c06092103040c091802031b06030109020f 64
    0xb00322941e004548581c10030392081100840b50300820400d90030740c2c982e0f041c90f01d0100d1480740680352829400100720340007a003100c04040e0000c2d482201c810701240c001005035514541c0c00701d48031807130041c0c892000310300c916a03829200480c26032540c5021031254030180000000c0c00030800912035294940c042d00701404010540c0d5600c001b600b4408122800c0702e0701060340c8006603502040e48125010344602402c240144001d0800d900544040a48010340c200154a0002041c2d101e4070010203445800309441c6008a16109001d000101e404085038107000368044980240d00c80d841d190780031540122004a0800c50311340981070b40704001300c201103035481c0308020060b410f1038140040c170540c1003020495410f0740e21401100d4642800c010140c0740e0201e090300581250881001950b0414001c03240c020300c0940c3c3c2d000302401c8421700145020400030700b15000d020f501e800d1000c14822540030b8070007071401080400040e220303c41406901c880a901003801401d050a400070b44048050799006201 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 820463741 1250 820462491 820462501
    0xe0c0a1811121e0412120908160212030301440607140405060301030204090804090509060f0c090906130902060714120c0a060209010c0b07080907290a02070b03 70
    0x8001411500c60345a49428180700040f030101000092003036801c90b410345c0c8414105c1908617003000000880900e402d44406030840420607000c0101421144017000e030003404085d02c140039417140c05608140b25038005000400103021041d00c6841507106151f22006400303156180203900c40e180d810003000030112000301100c52140061020302450b1240c88611141040c1c0c0300d0035032248aa800b40980095040c0b00400050030117400c000599403140014600b060748481e0300d00c0450744212050900e6612030010b1120110b403001c04107802c510700c030100c50b29110404021502144000d400107000d10141070515200e1403481d030085d81c919600802c1c1302d6031100c0c2400d1182e544010b040324000c0070701030030241245c0341400c03100b11501090032401900c1c14840503110a0020b40200cac440e03d06200b40103040c1000500303100c031003600c40c20090312911002c0c103002c24900d2070f02000740c00c000c505407400d0075802e44420348004100c00c00101c20007010b55420741400200d0420a683d88104800540882804 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 820464991 1250 820463741 820463767
    0xc0b010e1b0d060609080f030702040f24050135190e0c10170a0510032301050a060b04030803090c0303070503180303182116090e0c0a1811 61
    0x1800ca44c0f145da10f000341262074015454907440380c82c08034481c0f40c3c03040184400504081c2c21480c41132201130400154421100925002900000507a9070101030a1800f48100d42e080751020b03114a000c613200b90042425142c800d90110040940c281c80702c80c00c200054440220b0b2855901800a03000b8280409290415031036600c05012840c580300c2c880302d40032030000034850808500031101039085400640c4030720480b0740040001404000c0c0400b08040c000c000310b8100d807a00306040e05000c1000082c14001600d483c21070340080c241c20b0b21b49051140801010994500381c41c103980c1c0140301996030751110b0804c3c502d001c030f003202040d815000108006041c018044007400000180c2c440c109819680207040640b40d11409840d98592040c0308608009410400d416840081d428041d051140c1d560b40c0c103280c9000c0380c0400d0840d151b40030440c2446001950300607484000c0d8910020302200038014005400c0082c140500e2000c00d0b0403107410902040d1682006034011003402a160351a05500e04030 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 820466241 1250 820464991 820465001
    0x609050c13060602061e010501180b040e040204150312030f061d0601110c1302070303020d111c0b0d0212250611061b03090307021215070c0b010e1b0d 66
    0x1341c0101000555426080c1500c0f038065812942c400440b40e0030140103513460600c00d0000c14114168160100300c200030b83c8020030150481c40c1090505162030310410003504d5807120502c40280030524100b00140d10ba20394048400c082d42408140c03502c2405110000701103d500c080030801c00509a0b4100381d1404a055000d00300c04c0c0e90780c0440382060340314283e40300215600a60420064000005420702540c00341085038030130b10307015103042408481c0d1000d44600741d0200c09e811781c000039180d90340d01c110045030104500e015000c2c8004045140014098450305001030701a41800015110300d030720600c804441400f046d00040c89a10a481034460742a01500a0201081d070b040c40b1007050901c0080c2c040d100c0c0041c101042109001481c1a10b0107401c060719591903444140400e80060380c0780c51005c55071011301d8008200c00100e1540009100c28081c010100707001c1405032120220751107895940c10b6484020070307649551601c04495100e40740c0c1d0004803403904804100022003121a07005 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 820467491 1250 820466241 820466249
    0xb0a0b0702040b010816200610050301060504060825241209080304060f060b0f1c06061707020307020405070c060506090603100509070f030c09150b070609050c1306 72
    0x10800800f280c540040d6a0004207460511860386d80321040404284151440c40c2001e000125070b015045c105c110843c5402e03010780b55920611341c0c0c15030a0040d400c0034820800201400c880a1150a24121003152251030030041e0054010f070030384649910000448419004001041801c0200c078020a40c400c4c0a008011003100061201c0c0700c0465214601c2c0500851540c101314014030f0b4ae151540c0d0036000f40744000c130b032480c52500e0341c80c009103001149000d03040344010003400984d81d0107901c2d1001c1852650320003c6000604d0240148211a80020b07a420400806003107103015485100e130036072079400307458402980182418104080c00364091100800075110748024003c54503188108010002c007240c000c1c1d0117a100c0e003003001e603079a610b81100f5042110310040ea10026102c0c0e82002c01d1500319082554210a03042e810802c9d281c0510503600054a0800d40d840d0075410031403501c0307044c422640064500c60f1521068020300005210134080f400c0020454101011107068000c040c041030701c5 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 820468741 1250 820467491 820467499
    0xd0f0b06040501030c0b090301060905100806100e0402060a031b051801030e33040b010807090b060909280f0c0201020c03220f06080a050105060c0c090a0b0a0b0702 72
    0x100c0c00c80d003480d0269a050f250311219800c9510b0514031089055005041c00b07540c559207400b00050128021701c00c00b40111140e52007442e085040400d0140b802c80041c06480d824258640d0400900305000455078000760b04541107542c030b8800c034908070040c0015405080a101c076824242c0d0140b504200103000022000401c100482146001541283e86522061100381c010100c4142c241002140c144890000030030709000010500d1101380740c84008450440e400b0003035500500031150202701480c0142481181441081c1842010640e280107500c01507000e480d003980810b900040c00c2c0b9019080c010200c41306184000002c9441c03000c2e292501004c0c5a091501070071582451041c021030700040d032002c000b140b42020140195403020126008a070300901140004695621094035140040c5866520340c6002d080500b400340c01c44106a00c0188142e00c10000a04503290125a68100060844211400380c2c0c60400c2e07400a8208548100e9001c000741001207030380c6604d2400381100d640252 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 820469991 1250 820468741 820468763
    0x80c0f01020406030c031803050f0c1b030106080f12070c0905040609020a050102070b16031103070f0308071b03120219030f150b031302030309120d17070e01030e0a020d0f 75
    0x40f005800307c542600c580020079400c404104003007805a030003007003040040c0340103d16105030703000b0986c01c11084040b1035154100720720101101e03103000d004100c0503254401c0541a4002140c1d8669507440b010383e4020070b80036002c80c050041c404000040c1c0e000b4000703060f061005140601d0a10020310304102d040b8070032116404045915440001c80c08242c40c0c0c1810124903081d85c8036800501e04190306403c070100310949050701d10500050000d005c034203114001206440f01207140191070300d10000c2001c02009403a01010800661140801c83c140e505410004565411860040c1c003920520041c501c920b400c50031003080442d433544c4190108114072004010720038550003044220400b510074224000e805102140034507495000c980002032005003240d01d000c038040301080002d84007e001007403a8001c64404141d00d034000c202c010002d40ca01c84540c0191400c3c0e803011340380c100008005030405a6032200030510000400560f2126a0001d04c0c3d240301c0c508502e0507034080d01d03600c101120668148 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 820471241 1250 820469991 820470011
    0x20a120216090231031707050c09070e0918030a1805042a0203040e0103080304060c0804200d06060b37300e0c010c020306070c080c0f0102040603 64
    0x64400d9a0041c0d40c00702c1c1d0310038078440e070f0981c91800c0104800014101140e2031000000680034121b01c448543c1c1002d04c0503110081424164148100c8c031031101d0040d030441081090301a40411a10a0f40c0b80407100600940c9134080c03480c040501c4000c00401c2c6100004640350815000b00c0c8441c0740654800d14041f40f551224240000d032800c1005104144502186481140720107c1451224508a104880c1041d0351030782d00031121f0402f1390003581c0b6524008288000e10031603005082d1007800d5070a00740154241640c0b031421026000c2040c0d401c0140740c81c0342e2003035640d03042640b0000c2c507000801480100e446181d80ca14a60100741d41040142c21400500b0080004a5020170714103419503650b401400302202c1906c01240601404654000e148200c080c80210078482413041e005000c000500011025080d40c40c066281151605204440c5507110040c1e0b000261264481064a00b58151181501c0d040401d4043c0b036840c504075014810095010003015409001158525a400d200d00000 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 820472491 1250 820471241 820471259
    0x30f10180b06040c0513090912030203040b0606130308030408040906060908030a0e04110a0807180b03060607290f0c18010e0111160f08030307021903020a120216 71
    0x2452400901d016890000100c040c9015030001d82c8681c1d0b20b04009240800c074081100854000b500302940c0b950f904e17504142885110141c07112181c50a0804503d1400c013500c81d034298100c01010a442142d0000303200962444000304500110381c81780a1585a003060700d491203d581103400f41009076842c06000003410761184c5050b0088900c0c0c40d014600d81400440101c0355072205000c802c1d00643c0700c400c00780000e12007500400203080d40b40c0d110101c82c201003900520800d243d610490701040021014003002c000d503001c07690082070441c1c1c2030340c1d904607628000c59901c80c085c50707207a16003005910407550408040030307581c85210b0400d1310b903101e90303100201c60540e4020305000003400d803002c481c48603681d4020311040440c100141030005600c0c41d0380c0405d0f45080c0c144506000c240740d13800420443e2012014107180a408100040d50552402160007541c0e41c0300c2c520015551700512020030140b50003071003c40d103c3d50300b00c05207001004c074541c0f029685082c0300a912130b00c0740c1c00030000110144 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 820473741 1250 820472491 820472531
    0x424080f122514010917031b180924010c0c140d08040f08101802010c06023709030b06060d020c030406081008030708031306020702030f10 61
    0x1529440315030801c07042d02646410300c50b01c8034054001d08030b00c60000020030030281e200f0200110311000800c600c04186400600d80255004500303481c2e0050007070040c0031460382e240c152403400001d602c94540c003003484160301d081c02d03d2000da40c0103240801885401e4816000801103440065000d0701c0d442032030001115200c0c00744070060059000c500c810300c9888110003500580303900041540c00c003203401c2c1d25006010b600039841100300441500c02042080e4050111400c0d045404a0821070010310b020195001700c11908005e042180f101040c0341004041e605460700d00450400c82e228404108150001600100143c01030741c801c0c001c400c4856034880d60703099042d29444078610216454403014054960829000c00b01c08507024003040301c0440d0204040e0004081c036079a64041c9040a460f4080516801c1c0c100e80c42980040141001107800b0700100e0344c20001014547d030a032685401c125000307005800c0d000f54580503002410702e00030380c0040c1c01000d50300c04440402244241a04401d4494 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 820474991 1250 820473741 820473763
    0x20601060801030209060f041a0109050919020901110304030609060f150b030702190507170307050d1805031b0405090a03090909030509030609070e0f240424080f 71
    0x1d034400010302c018101055103030340050000c1c02c4410705802d50400103003903402c42c45070b000074030722081d0408090350b81c0240600000c000a40b407029450901040198000c00c3e41560140b5041c2c00280e01c18150344a0344400b41e0201c4c824041e41c0e00e4139100d10307240001d00b030303018000e07900f080c00c0a140c854825401c4c820000c82140030115001e0080c46c0070318140468200034000c60950007485c200540300c1a5007000c07100140e1103200927140c07079810521010106072070080000c0c0039910900806000402c00036185c5001d00c002e0500b0b0121480c2851100d0380800a5000250035014004001810202c094054844000c00300c90510580d95a8000c00380d4071394081402800040a4940c100b10000a550100318201e020340b0f0040d1800c404180420300d46041170750b40210a42c001d40c020003515501034031250300458400780081041c108180c400d1540c580041031084580020b0401c1c181650781c982c049000b992581120994021400c00d4407410070b80e0901c5400c09078001c041118040407c08180d0741000 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 820476241 1250 820474991 820474997
    0x70303060f0e070c02090907180510120c031121010506010f0201020f070f1104020c0a050610030b060613090507180e1b031518061c0b07050f19021c02060106 69
    0xc00540d02000610030000d4448050f45c0194080803501d1404c085003075080c071074820300128007804d001d0403090310b4bc00c06611016014010036001800a00c148200d0011250060a80c10b8088003540020300352882c000001c0e8600100840b50140f40e0360190010751044900741c950f140f41d0404003100780e080c1e1264840c3c0114402c0108400400500707a08071245480780994030170544c1782d10b0b80c00843c0403680010100c00b03860380804119020071500700941d590110f40e048201c0e04092440e95442500300300079042a10440003c031341c0107040064140e007070005082c045030900441c103159101404442c003890881d086504c00741701c04108107a4852045014044240e07403640f140b601ca94081c84150000f4018000403144d454458400c2c0e40c2d4004000d0b03642c00c202c556103200d420060200b000704500144000aa0b0303440720384400105012048150f0f2000c101e042c116030782d10241d114210070f44030700f000384400641e180404840460f0300065101d200c40b049140c1c14408840c011080c0c1e03844000b440b4140c00 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 820477491 1250 820476241 820476257
    0x70c1e03120c0e060c0c09102102040b040f0b0a050102061012020102120703090e0108010b030a02060a0201020c1207050f06010b19030212070e03012d0b15070303060f0e07 75
    0x100154a920600e1003100901e056102c100e00ca01c0001c4c502c2d8000550a60181d0111010400300c0c940190400d0300081d4550484003100d00d00b0422103070390207071807850b036450045448480c4190346690b04100c802c0040208100140c2d206440703030740c00034104054158003c0c3c101100200d81540000340c0c40b03003d0000440340a041d2440c180c60000d00140742034080313045005850299080b40c144801518002c2c0c42a1503c08030a41002d048140c1c01354141d100e0080e583c1480e00010301c170303103002c1401e200d02ca805445144c2d0340c820003801039000e03114144141da4544154a400545d0701c0303084e0050f100c0c0f04e1140f01529200b80710a200265141003e000e8414044420048080d0b08002c080c0001c01c00011400d0150800e4511540d490106500b00c0f041c00210300070140d5212030340350038421a0b2030ba205c080003c4411071441406005c020a4084240f05407640c0c80a400421f603449130200c00206000c0d90815a0381d040c0c030f240007001303021288100c1c4031034102c140700070500c1c50111120900c110190794410b8030b = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 820478741 1250 820477491 820477517
    0xa08060f06040f0b042c040b0711032a01060302011d040f0203250203030907060c060e06070c120e10032c0304060908030a0509060703090905070c1e03 66
    0x12032909141502584110100800a0746a0458400301c0040c03440d01d0089449500e4001400c21000320000445105190301c9054480c0498503005283c115422500700001035032080010340340201a2800f4120512011441d00c81109440e04d8412030300e141401d09501c040e5100b90414240c460b61b02009010540261071801c07000f02140d111200f0100080c07012610018480403401280e0094400000528040c0f51900c1c00407820f00624110180a100079481e40ca0441c2d41a0307103921850050200304101c0c04080c00c180542a0451264441c9840983e10f51741004407004d0006103044004503482a0402e000c0c0110a000d5920b001d0388600142c19080404802c1504070001c0210b82005480c01d1590312070154134420517080529620f0207140210b0f03441e4100302018025119aa0080556038010400302507040d41c0700782515803d090640319030383c4904403854286c5509829801030b0076040d10b04070410040d2a0310641001c1503d000c1e00404078203110700f00b04404000a03640740540412140c0c14485 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 820479991 1250 820478741 820478749
    0x126151210141b0d0f05010f1e030b010b0f0d020408060403140a0206060f0d050d0f0314011a07021503040804090501140f1003150305030c071226040b1c110a0806 71
    0x46401000c140000601704010030b03600b01150001c0c0c0081c1680400c019003841035540100008002546100141c032905207540e503441c80d481e1050198803441c400100300b80c01010340e0700003541ca8486202600359102e54880d0045a611101110160005950400303181c5048040c1d03802c0725480b160590242406584020a01c050344412840e40c0c0d4001c0740e00083c900205100740544000c0641e50750360b1059003420300c1e000a00f5502d2141d03084400028540042048024450340469000003d00c8020344a1016000003401030f42e01d106005d40d40c2030000704100402c61032200410a440e00843c0030003080e62200d1091202d03008030502d0f1508440300c98110340803440c0400008426a01510300490034216a0101603c01c6500d64421140355101245c1e000601d6418000c040180405e1045111024615215090b0076040390400c500b04440c00810000c900d518082150702400001e11015600c40d0010140a41c8591010110313040c80c0c9000f034541e18191406080b6503020a085e44c4044054442030100 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 820481241 1250 820479991 820479997
    0xa270603020f0408031306020d02010209030a02100c080a030b100e2211160c090e150403090b0415080601080c1b19030503010305010b0126151210141b 66
    0xc41100c2d0001c0c0000202c8050410091614a150300c0d80441d00a140500280c1b5203040a0b40f100c003907900512444480d51000142c05c99010703011981008082441282079035944814403026201e008001116203407141c1580002245550a84100c12009480c100c1203c02420441c0015400580e40c0003141d84500d144045210755050500700085060b03900b000d0783d60540c0710002d007070118460642c0305400c0c0050140903c000f0024003a090007000c0c10010003544035485240041c00454904c0049000e040c8203c6c040c4d0054003030405903590312a210141c20855200303e8540b0400502900d00141a5512034500b0070b015101200f11b40341080b0108040f400244038880480d5014428030a19030030480400200c2a0840e000791038496480d41541011820f40300a03503041e1707040c002242241114881c2c40c202c001c512399410f8104d070396291900e001e05171803071024140309680032034080b4620000140205040c00c070b2450fa07007402c1042407904c18514510441c03c48071040c180c00700b00c1c5401c003081013100c02 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 820482491 1250 820481241 820481257
    0x30806030a0312020c0f0f1f05040f03140c0d05040524190e0d0308061008010e0c030a150803180d0203030a0c0305071e031b200d170a27060302 63
    0xc0c1c46c2c2410242031468a0f01c10301c501450040c3d072100c2c608c01c01054221000c201d2041444030180018905501e85101d0304411420060400001c041c1202075035110109990000b60400140d07244004600401006a0002e000d640d00c240d4090034092030f41d980140304ea13007d050510701c0090601c50702c0e490034859520104c003420306021200d0a19121a640d0341c500c414902c3c46a01c514603141010f400340800d20700028a01414050b000340180410307406441442c1c2d11000c85142c0c1543c2c0d90ba01c00000001d0450080206010810080c010071a60004000b07070161180390070901117680941d0f02040305007282d020000c0e425810400ca54152203100b550804501400fa040c440e19080030342e514201036440180c0300d0064807031a0300d0700301d0815902645912042c21804030304818088a9101c20a00301006a45c40041d6185142c0c2e52013903894549030408100c1d08080090406c2100c05603500301075028050f80d00006038241c0c41c0c4403100740094a03403d42c81d450007c0c082c0d030880c01c10b4002d03802903100c020 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 820483741 1250 820482491 820482493
    0x60e0108060d021f02150109020a02010605100c0b15060a080a150e01050603040525030201020c0103020304030e040c1209031d01050307020303010e09030912030a020106050f0d06020d1413030806030a0312020c 91
    0xa000f041d241b0720f15082d0007810034a0006964000d5200d0007030031900580c0000d0310513850100c40c419220341c000416042140c00030003019041d200c05840700b005034a003000254200401103039114042c0e030440d00e1540306400c800700c02c0c040010385c281e6518061120f40112102c0110600041c0031707504250015660051003182201c1c1904407600546104001000b5044000c5402100500840d40d06020000010400b030030194114202564054440c401200f001e0307000e950b036189802c02491080c441c8500c51141e0240402082c1c020341401480d03d800001034a4042c2060030041c1c85c01c1d482070048070b1080060b40d001d14216405d0048640d11454094001000b61000f809040b103e540c0b1341aa80000d9820600219640c101c4040043d003521140c1c0d110314800d2152003010240c1e511029040e580095000200581e54035403450b0000042030102d10500300c02c4203000800c144140100300d0400c40705d01a8882441540c4c4d5141016900d01c042c2c08001c1c0010f4a250041c100f00034680c01801d0011001e01c = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 820484991 1250 820483741 820483753
    0x301020706110304031d100c0f0c0f03110d020904020d140d0c1202070b1c020d0509030c1c021903050c0f0610050301090f0228060e0108060d021f02 65
    0xd00c0716425565141072080305204000144010150441d02c1c2400181c0100403181a0300c3c440c40006418800302c0500c85d050100040d00c40040200c810b084c0100c05621250304400d950304d40055030001442400304652291a5802011031880c0011030092156401040f018465450341c0c00e0007111031850394101c40001c00e80c0700480207071006002c0c114000b8483d0b60b465407901c40034140742c0303848001d403c0d1074030640d000000300b40300124004045034100c03004814120a01c0301480000700c000d10a044164007168038103401e2007410031001c0020458061208200d8602c0344c8404074070418030075088550005640482c0300c0f0f40603403007080910a000c81c0682016800c01c0402117880e4103142c130340e0070705c20a950030510401075228031500e018006000c06030300800c0700c0070294ac0c540b4264401703060040e100f0a00340360790184000c0050041151400e0034446a80d801e540c40c07030054079800251145601096180c0e000440d141002c0040a29180e00240030111401d043c1501d440e030300484101000440c0200303 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 820486241 1250 820484991 820484993
    0x140a030b0619210c060f02060f101802090907050a170601050408030304061d15010b1308070305010b0a090b0d200316030215120705281211090d03030b03010207 70
    0x1010808a030f0040030000a14040b44510700b901140342260003580600814100c49180242c3c002202d0f42c0c85440107410f0702e116210002400d4a645840c1c0c4075183c4100318540001602c0040d401411004c52b0607114200151038140e0181d8030303401900c0c11200040c610680703041f184e91b902644941c00c02c506051141ca46074861003083c0c1075038003c5405035502901c030100054194462a02c0905080402d000741103e49600914100401c2061147e4040c69201041cdc4103005c001805440c8020b00e2000100d590380342e030300e01d015406820304031502c0b40700362200c100c00a00740d00b242c020a5114140204055030242140d81c4075008240b1140000066411401c100a0551002c011015030780b0080041c4941041c51072040003400d440b0140d0f550054842800191004406440d1068000000f800d25a4035200282e40600b1488c1d410044c1080c91500c41c2d0080358440d4000e848401c40345003040082c400e8003452441100d15115054256810080b035510a5020a120360321038040e071180100058034200c8a = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 820487491 1250 820486241 820486259
    0xf101406031213030c0608190c050a05072102160510120e10111b0d0905120a0c0603060e07180b090607050d0f0206070237120207140a030b0619 63
    0x2540003030010540b420140500c1d940e0388c181181001c0c4058409016501c51010b00400c180a00e1030b0b4103080c007a020410500300703c090089010b90030244585180c42031890000259510031505d400314804102c01c80120306805c00f804944000c0d41151070f00100d030f0300d1004000000304050b0b882e54403e070040748003140d407000c205e00681080c000d080c0c040940b03e0481500346504d05180c0e42d1f00380c0a03a80b003801d88080c6150840507802c112141160712150a8203003841c00c5007024648040108001c503001c0001c02c880b5010703808038064404d03038080645156100d03401914415401c2d01140030100e03440c04104480790401c0001c040c03004c03025043d1400c2150a641e15450030b808803d031a0041000300c5001c51585904100707040d448103480c4018406082c02000c0208000e8094846a49e01040d4a4005220b540b0030298401c0c0607900c00d240c031402c1800d43e140291141c0b1180185041d108445c88094281c2c50154240c0d020340b90086240301c1142c4402c010041c1400400024500410403500c0000714408 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 820488741 1250 820487491 820487513
    0x160507030e22060b040e0a020a093519060b0f04020c03040920031501050c06040302010b190b09090601170109060e0f0c030a0509030405030f10140603121303 69
    0x482d072180440d5002d881c100c810560b0500e030452118180d041c801040010030b20301c9030315001009600c0059441070103c0048420000c1504145000905074240044c1510b10003080104000020081b900318010100c4080c0c84c3e4800850b0012026a0740403c2404207055511602401d0341c01088144003407568004074003640c02040c560050b580000c2800c21408070f250040c80c04100d03038401c02240442c0040c007010020700014004500019170804000904d9000f4021140394003900400c6406030306d050319000340600010030115001c0d0181104025020310007950f14016104141c58641c20040c2324014400c00800040c2880d0401c1150307600d98030400d80b00c40d40c0c0c0380038050812000c0f49880c10018044842d41d4058207500e00310040d2020845120081015650042c00c0f00c18040380c15141e4028a034990300960300720701e40c10300030280464170200c0300082d1144480361032101440141031498044000b00302c2200c2041c0c068000d802c7c200c480310074000003031559041e9034280b100060707203075195444010 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 820489991 1250 820488741 820488769
    0x2130216031805121c0c05070b031f080606030d14121003020405090313060527010c02040509210304050d08130816021806011b020d050f0303100806160507030e 70
    0x1812510346243d014028580c802030b209211b04203441c441000355201903a45489200e1450420b82c0400480e002d010810148a43e50f40b86600c868411070700d4159194890354141c5185103c0e205144017a03241d0340c080d0808041440c800820a03040043d00b00036915510002801141c1c101e8a4100c04401a070310343c81079074055502c00c0300440d00d4003c0d0306400900480070b5044482442030511048800b00010580c1c1c0011403400420210341e0809140180d490041c2072030001d5002c0c0c1010100301001c3c1d8001100d03208511a14202c5c81c1d0303c41001e441003007610080d90040c01c0c42d0800340d6041c6007075001c1e4581a4001d600c2c8040d003a40800c0301d440303107079054100f50415604055004441c1d03081d4030380404000c000140c40c0184550703a0500c84000781c030040c1b18801c00440002d40c48126400d55585440d000b88080c1c0181c262141000e90303845060b1294400c4614550101c501031001c507914070002440f505c04c404001030816080c1813501c0c143c400f60000c103401ca00300b0140746845862600d4400c031582c4c0381 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 820491241 1250 820489991 820489993
    0x16020d02031c02060c030906180a0c0608150105031504020702060d0606020d090b0c0c01141e130812120606070219030203211e0909040c030213021603180512 69
    0x2a40442c000a091240152500f0710740c0c401401401000d0310081203150304058000444078000a450540c181040e07210000500340c4159100e001580603000181c052065000c603403903c103490b0515005440302c0c00b003510021482c0301c418540d00100d050075802015003a0000300301c542084030500b140d2060b80e03115000340e0016007003801c07406101d51304002c2c24406001c0182e142c40c20505650106c0f85c4e9200440e00d124104510a8400400d04528000f101c514543c01c03d2a550380100300000c3d044540d00c914400c807240381081e2070001d451400841d008000e8680035403858909614002c0340e0120b2913004d484c07103520510402082005940e03c145400d41d2170005260740581c1491801010308011040c42041d9600005954180d10070b0180d004a070190b00e01d07400c0108460f44003001280c294020720000b245c1042242d0103000a10000907442c030b084a10845100390040b01c04e03900002607000b402c268000e01c07100a601500020f0160800b00e81005001e1400c04c2680e56a400041501603520810806 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 820492491 1250 820491241 820491283
    0x90a0b0a030b01080603250506070302031801030e06040b10090504050619020c0d4b030b220e030a0c1b030b1306020d020417010b0406050616020d0203 66
    0x4225054000c2c51204002402d00c100a40303400c1c00881e80361071254280c40c5620240529904107001c09645140c05000003901442d00c0d0030b554507019507641d03c01e2084401c0d1034180c0c070440750b2541c840e00400940101c50805400191101c0c0e03180d0040210213016a0f142c10381d0070001007140780140c0b007404d02c07817070044c40105002e0802c0010036101b00c0041080000b1a80108a020800c00c1c0014500c905480070b80307484116042d807050300c4100440038100703501b82c0641c00c06080e40401c1c0c0c03940350b10000e0000580301c40d083c040740c040140c041719502116aa0420001d40340c8400d150b90070003030070706400c0d007840000c00d10424015031079007140c0c4004a80320224a000340c1c0b500c180646402c0340c03040f89864800c9950054119156081e03030003c002e103440140d14004000108201d6140c040c0e070072aa406030001d42d00d4907204c0700c03103025100324481a000a5032a044100f0181c1c546030040d001103a501900291a0035400d91085005a06214007a60040305841c10000181c030b040100e4400c909000c01c080c42 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 820493741 1250 820492491 820492507
    0x11041d07090302150901180b0a0c0f0c06030506100c1a1f060503070e03010902090417220e0f060a0504330e0903040e0609040606050306040b0411011412070302090a0b 73
    0x580d521f01031002242490f1140c06000d481c0750002203030030040e26810030705039852407450a0441050000c03402080307542048030010b201501a08840c0c060441107a4544003203003001800c07592040703400e10192119582c407010b461055600032019411140600c6070303450400c02004d91040e8480b841d071200300000c00010030404c102d90b00c11404108038000710020f00c41c400c0c15400081e1048406407018110440c0300c40c4d0722842c0d828850807034690382441c88400d142c803400301100708403007544c40c4101d641c9141400000350070824024010f501c5240000c118020103800c200030310004040500317070211500310b46002d401104003000491003111103c001100302ca1030402d8a10f688890f03000e00f940149038030034002801030644038100140e1044e001e44000d100e594950400d00060003441d44603542500a00013408140300d0f40c1c3d01d0080c4524010702420001c0070b212401190311244854144900580601c0042201940c0d070407582d4021055182c058200004e44001a003107034659441089264000a0004 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 820494991 1250 820493741 820493747
    0x50c0d0f09090606230c0a0c090f230402060409020f130e0c040308130506030c07020a0509070905040905010b06031602010e0c060f160611040911041d07090302150901 73
    0x74002d0000c429081c03080901d04a00600215043c1c4000800703c00810700d1180d10321000002d0710a9840a2011500c5802c481d00b025425010300c0d0240703242c45820050b203440c2480050150580b0306003852a002c84481c14481c09080c011400342040ba0721181c104400030b90104180050b017460001404103d980c1c15076151001d0f40000240c0c442440ea43c102c40420201040034001d6500712900805029035504240c0c915404505094010591203c804028064010040c1c000361404078800d80b0080380f141d40f50400c10448010455000c030000740c100d1414055400d00d9081540d017544180000b080c0308441500248440d00201d45c0f0804d1180c2d88040c407150b06609000c0c040101a01d48007410145500e8404120b09114500c0808103240001a442040040c0300448018068202d007042203080540201c2d00075940c1701c0e216031400c440c1003500c000e1340441d5642c1201c0454013030178901d145c10226180d00740d0078903500528000034850361940000160720b40c1d00030044c8525203c030740c0e036944140200000d = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 820496241 1250 820494991 820495007
    0x3011407111905060c0304030e030d0c2f040f0b0406121a0105010c0206091801030b2706130c080d050310060206090c1c061b1b0c0312050c0d0f 63
    0x58442c2c00c000d007000001040000c130340b00750400d5a40712030564a031303164101a11805100076607030303800d40f141d84104080650302c0190500c50a202d4150700101d40750410240c100d4452142d20035424201c40640e058031494075034001c08242d80c0d007280100b06044080001411110194808550410311400e040f040082c0035650314038034425072801130801d504140c0028888800e41000900807000020102c00342d0307460341803100981050418181c102d6840c0c0c9050159204140d5040c03440402d43e1400c030003210384001c001861200300f030005042540c0e44009070000d082810b64280d44200c61080003086a030018454038081c1659178a605070340781000384a01465040c240d1044003190000d00610a124802103031554900c2012140c4420700a507003144104010080720000302660702d000c01202d561000c2d440c0142d024003440e00e5032a4011010300d035600012212440040860b196050300b031000400d041c006040185180c40c02a0811040261980c6000c01492001c008a5080b01842c400355502c1562 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 820497491 1250 820496241 820496263
    0x8030603250e1003050d030e0d0908060f0a15090c0f09061e030f06120b0a05070909090501020421111c030e0324090d08060d020f0301140711 62
    0x8a14040910456841c501c0d20302e00408000c0849040414500020400b00002954000080d103a504101c414045c00400746140c0c500040d00400e01d810b07003514010310b8804c003120a414080e1070255683c261100720040000c1580381d40030303568015020750f000b400701590090242c2c0ba6002600300a40304019004200c0005c907901007210005051001030390183e0b003042c05168501c5140c0122046003805d401070300c0c03013a00401e529031814100186c0f0000440e02c0e10141c90003004850300c41c0d100d030600e000030358000302e0b41c0c000820602803040000d0345141d0311186849001d40300040c101070300c4101081d18600d803100c80b0045c941d62400c2c20b00a01013900c200b0b0f0305000c000c644000100342c40e4107109110504010001d8240004801d5851003620b0a12050302d10019030032400c800b003643c00024480524040e226039085202d503034070429400d40503040903801030704c008103d804e81034134540c00c114811110403510b0b5015500c0e40303601c3d0f007824401c10361103000c1c0c3c1498491142503249030585901e00307416016 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 820498741 1250 820497491 820497523
    0xf0603050f1e01090c0312110118060e01060608040305130302060a080a0b03060403020c01030f060b0304080a090902130b0a0e04090501050106172a0c0307060c0e030102180108130f08030603 83
    0x1060000060f84110f1000c02c40f0350011010a810a0000c1c0236200c1d0002002e0105071542000e04808071103040c0030000c030000340700320320401441e548407114034201e502c10b0142001050144001c540882d0060019020802a280311480784a07169800300d01103400000781074011550000504c4a62003040c0560500c445e825801420b10307244c42e4800a540d00d0315800c032581810390750082d00307201c001590081030240400e89151562070038646040e80041c6e10070b11032100012000c0c040401c840545008403a107a10a4008549003982060946046503003c03103298024445a03158840c410745890162403103081c0500d000084d075601d0444060b0582510f000380c0c201c001c02c9081001030304201c41d0348405071603030030600200c031a241c1407041d802c2510400341c0e9007034284808104413041003070907007021900c2240c0d03560740b0307125810103002d1500b40d009042032071103100003242c0d02c1c52580d403264180c00d070300c0b00350951b043c038442e05640c569010108207075409480c3d1300d2002041001905040290002405c0911 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 820499991 1250 820498741 820498751
    0x601090e06090a0b090114180f060709180b090702011b0c02090c0315090c07060b0604181a1305150a080709020d09060c0c03020c0301020a120f0603050f1e01 69
    0xc92003d03140d401e2420000c002658207404604541c01c00d50008001180043d5101340d10308003007440001080d0403801c2c1164512803084802403208020803418007480e00350301c1c0c2c8003a242c104070362040c401c03001c0c4100e0540143d0fa4562403403166140320b10036000d12800d27000010010a10641e000507000b100340326030180300850319078a0050302c0e000c0d00702e07034403101c0c07013251a840e5140c8120342104010850310403540010010180002901c0c0007008003140c078842c00e8200040da501005001042c003440c440c3e070144640041c0c481d0803d28561f0440c0c950a014050b0140013444190006004208101360031710681e5940c201308444003480000c1480300100c00c0380d150200c0c0f441d201440c1d50b0744205019408410781c020480461240b0103030880402c1950040d403d001c0b00740141002408c02c075400c4002d800502c500c0140c0e0010341018800c98860b002c881d6200c0f03e910310001101405032510702945442c0c0c5903141400400700700248142050251b40101a00d070700070381080c0c80c40b140e0452124286603a4904 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 820501241 1250 820499991 820500001
    0xa1205070b0c0a0509060c0102070609080d0b011b0308040f12020d030e0c030a0f05070506070809041a03060619090f0e07210b0a0b09070908010c0908150405030f04080601090e06 78
    0x4c00380c50741184200c48403595140038000650290094420040c4500e040105120400559001902c005a00e885040128401801c01110b4030429104030340140703c021000d035030119218110250380540900f00829585c041c40d03981ea87c1da03106890a480050304841001400c196041c0515810780c0180c074018514840920002902c0d58500076004010b21221513030b030342c01c1090074407a0702d008180042c0080d882c4c80060a065100d070f400004010302c103c1c5000c4803454450701884901c41600380240007841e007039540a062001c0d030140400c614102000000c000144115107000d40d941e42c071100f000100d036081041c0b80c03451402c51190004111031603e80d081c80384000e03212001c4c80d11070303801450301401a00c070804060002e201f0401900c1e00300515038100404140c000c0e045c07100b00c035000c0008100c00b1200d45c0f070031900c05005005200c3e4980040845503020000d0001c11500300b07010300b0642c0e10b082031080c03c1030081d40c000c0d40000c059402500041050301c0d0140b244009040300c15020b8581440e00e = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 820502491 1250 820501241 820501247
    0xc09020d1a0a0e19110403030311032806170c01090602060f0f0a06051c0309120b011703120f09061b0a08100f06020a0c121509050a1205070b0c0a 64
    0x3590150442c0c3d25034403400641402a0003a02c00c2c4a0240a0350822130070038031108200a6500901003600460305107424501091802ca0803a441035560821000c00013090b40008000c070180c0c5c000002050342c0794800416448891104403a803210032a004041d82c501010000d007401409503c04002d5405c05001c00207154507000019a00003041401039185e42d0302c082d00c000050035a0707003041c0e03002040e02440e000c1421090782c9518030b89009480d00403680ea540e4440c4440101041c4009091211a2004103c1c05107101281e413910f5400714240c90509400402070700d260702c0c040b120b1120001c0c144090203042d00040c0505178004503002c011002e110480d05951406108440640041110340000680004000d01d8110060a141e0408810065035000020350310044105e06946c46040b14000255900082c1d44034070b4500d60203400040007030740c100c1c0103000900081505440340c1c000d04d203201c0005005010004c4003100c1a880b5540c40b84000d042035864003000030005140c4d0101081000351880e0 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 820503597 1106 820502491 820502509
    0x414010602030a02120a020a140a02040e0a033b0d08030a0b0a090603020f0603130b0c0a030b030106031e0201091d01051306210f0c09020d1a 62
    0x480105000170320300c5110940005079010001800000d012040742d180600c000005607800118590041000d9070600e1030369600755086114407804040e045029140700d10207400d050b50703001c507420b4841c10a041041060444000d407a410841003130b0344a04490f07496650282c0d006480f414100c000c6409008070485003481001e4195012480000c1441035204030707138005100000f0b102007a0184034650388058040c2800c1000190003a000c9100045020300034007920860580d90031110900400309c40564800c0e48c483d07410814204040350703004046000c00301c1d0a0030308590351026440143c84200c1154810504040b50600704921802d60301d1f0118125201500d0703000034000e081c0f0b0300c40304450041c0035035014030300d08501c84920340342003142c1403e100f48204040d00308000c054940e044154415409415400d800040f40c81d03159007940115206140d030301541580303660140c400a03035405 = true := by decide +kernel

theorem cover : BRFrame.Cov 820323741 820503597 := by
  have h0 := BRFrame.cov_init 820323741
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820323741 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820323741 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820323741 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820323741 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820323741 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820323741 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820323741 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820323741 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820323741 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820323741 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820323741 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820323741 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820323741 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820323741 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820323741 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820323741 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820323741 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820323741 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820323741 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820323741 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820323741 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820323741 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820323741 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820323741 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820323741 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820323741 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820323741 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820323741 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820323741 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820323741 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820323741 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820323741 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820323741 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820323741 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820323741 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820323741 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820323741 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820323741 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820323741 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820323741 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820323741 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820323741 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820323741 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820323741 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820323741 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820323741 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820323741 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820323741 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820323741 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820323741 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820323741 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820323741 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820323741 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820323741 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820323741 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820323741 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820323741 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820323741 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820323741 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820323741 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820323741 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820323741 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820323741 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820323741 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820323741 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820323741 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820323741 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820323741 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820323741 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820323741 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820323741 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820323741 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820323741 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820323741 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820323741 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820323741 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820323741 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820323741 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820323741 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820323741 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820323741 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820323741 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820323741 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820323741 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820323741 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820323741 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820323741 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820323741 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820323741 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820323741 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820323741 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820323741 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820323741 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820323741 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820323741 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820323741 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820323741 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820323741 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820323741 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820323741 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820323741 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820323741 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820323741 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820323741 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820323741 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820323741 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820323741 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820323741 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820323741 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820323741 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820323741 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820323741 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820323741 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820323741 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820323741 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820323741 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820323741 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820323741 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820323741 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820323741 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820323741 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820323741 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820323741 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820323741 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820323741 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820323741 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820323741 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820323741 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820323741 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820323741 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820323741 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820323741 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820323741 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820323741 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820323741 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820323741 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820323741 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820323741 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820323741 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820323741 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820323741 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820323741 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820323741 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820323741 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 820323741 ≤ n) (h2 : n < 820503597) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
