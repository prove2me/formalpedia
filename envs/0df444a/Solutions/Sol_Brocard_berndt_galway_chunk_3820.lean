-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3820
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T10:46:34.92139+00:00
-- url     : https://prove2.me/submissions/26d38584-3a1f-4d52-9a07-cdbe34400199

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 686870503 ≤ n < 687050359 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 686871753 1250 686870503 686870521
    0x9180d1e11060106180f060201060e0c031b0c010f14070f0804420b2716050f030906041a150105032e1a070506060f03032b05 55
    0x407001d0031046800030807069003019030607585401200c200c1804820610740c041004451803044c403005050580010901506000081c41c10007001441a00c1842c0248204403058045401054407031191400c4941c0c1c0d907214615140c0905006456090100c0c00d00181042e80701e82c1c80001c0e0304c00c01250360b40d21103ca040d498125186035003601c2c043c0511f071b0110900c1e0080992030007400312a03540344411080c0d900001c0030741c02c05658070401201c0040e07564007441c0440d00384502040b402c074241249070300c05c00003000b452205404000d0100d05d84408000c6407215014080d030125400c2d0b042c844542626032400c041e040759075100c226021290108481801013000002404d2a8022181c02040000450140004491540009100e01852a0412070030106441500302c40ca41404e0645500c0c1216400c3c910000b600e499a0200340440e0102004090301081c00410421307000b010890340c404030000a100001c4c0b81d409000d01055280c105030850419008400c0300b03c84180c0100300301800a96240111 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 686873003 1250 686871753 686871767
    0x30209010c061d07122001020a06090203160e150612150105090d03230f04030807150e06040515070c0201110106030b010605041406070201050909180d1e 67
    0x9a4081408240c1034000240d450b0021100310300d00d4511880140c4442c0c01c40ca180140a9100003102240e0310f0840c814440c011030003e0b514001ca8540c1c038015401c03440001c3d6103001120010b01403030713a22040d844c115503017401f000d840c1c0112015211141d50302c0c2d0a2190b090b0b101902e02a0400b00b030b0320400921424450301f96103061114000b00f036265900c0307031a42c09150604044103070420404024100301381e92954104240309010b070361210803102000e09850500314481070070340d034080385c20b10010b0f04070340042c0103c2d01641d034055040e68440ea080d15112000c2d40c1121a100041c03824400740d401480d41c00507840344290700500c11110070502c1d42c1c041054409060300c2040000300400c0d03840000d54013511042540742d0440c40006a17541da40d0300c802c0000301083c0c01030320002e24002410402c84100c0380880400d5041180d046252054a0b800a010741c41003401e42c600810704100041d40c544501c00e480032042e5005015540344502103035004002d821140f00d00348800b81e031160110055481151 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 686874253 1250 686873003 686873017
    0x90c05030423030f09180603071403031308061b074805120303011401030b1504090603152309190b091e03030106050d0212040b09010605010302 63
    0x681500d540c44946460382020840780050101c01e55a0000c4141d0303240420003040b00300410540d260311203018104001040702d00c0402540b90b420504140210717990046141c000311040d00110398050383c2503001003400c601803185072020030004c40c0d0002980c01c40110f00c07107110b2504241c005444520804c0c000c4124040c481000e08100e2010046080c1140340081b00010002c070501c010503640070068901f42500c4500d503000c1541c8c4000034003003103941004104c6401102c0f1f00b0020f54190f41c1801052690301d607103194900d04141d105c081c5054261a81961740421004142100303550b1074403034504201a02c40e5103c01c0f511902e4014812100c81038a100c0e1141c03c0707403015036250b14030288524480a00f8005000d07104a40a801c1868071091806d9640c800c080e4800c690802040c500208140d0070503450f21a0903005503803011082d410524080300700c038191a0b960602c982c40e4a44a08000000d000303030401100291240c0060000b4070031a0900301c4d10908085000740602c68840c0011400e0f800f0b0b00e1 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 686875503 1250 686874253 686874257
    0x1200c1e0d030510120204020d110d090b01090e0303161e0207050f010507050a320106050301050709060f050a1229010e0303270d150e0a0308010e15040e0d020106090c 73
    0x305d5040145000e4004019490480d0008a00800c4450354601d80e0743c40f061140074110380d281544810000b014403158010408102d00f0400e118444002984a00c0002c100b0210070104110150351306020781c6181d100382c142c001080c0114800300402070740d40d1006000300e9214a40d1201c0c05046903209034100c400c020303400b6000d0511400e0543c0e683c9081d05601550541c1085811481681c0c05071071208180d22415550000c1580c6150a051500f1503001078680c0c400c00c9014601407215a400c50404003400c4d01c10f02c2c14a6648903020f0088a68020403c501d040c0e0310f05007041d40450200400300c0c542c0180300390f00740d00a0751001c0401034407000c0c01103d48981540040c048145408032422003000703000703000544980310151810004100342a084411265500d290b413407041500c0f200d2207804041c0013102c0080c0350380707183c60f10003400308001441100702c00c0b1005000944000006612103629010182040c0900002e451080303803281001d03292040158a80040084c82c1d108034000c00010364055 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 686876753 1250 686875503 686875529
    0x801230a0603020c21070308060d080a3b01080603070e1812070501020301030b090c0604030f020f0a032915040c02240f070201200c1e0d030510 63
    0x80c4203801035040204e41020301d0040c0d100c0b81c1e0f0180320100030342d031021074100029903071801070f0b26014001610182580340100046940e41e00050459021198106c4841c10301840361608000000c80180b0511103056042c02007240030f04841d5541c000160342c200d001d1f00c851000da905d40d414941c0e110340c24402c80900ca5000f1000c104210058a0300459030f00c600703010303a00c1c0104036070310070100e980c440c420490715a9400401002880b01d844100c42d0050f540c4c50240940d40381d903a0001c2c0250080707000141c00042002c1800c021550313010700008103424080c0444031004d40e03e0400740b1810184442500c8214585e9160304d4003840c0740e4000501c5614a4070440c1409440c24040c0002043c2a008100c154410304686240c03400c0140c2d0503111309c60140460300c4240c41c1c154540404194054215019a81454022440c51425000c4007610100a040300c540b24014460341a141c280e00c03a03c4c4440417000001000781d02c110208180d0301e507088540303044c06251501364200405581a00c2451080301107 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 686878003 1250 686876753 686876759
    0x2e0518091c02071d010f1d04060c09180506130903020a0f080c060f041203020415030902150705030c0c09040506180c060301090207020315060d1b03120801230a 70
    0x1000307440300d60884003403046402c090780716010040ca1401490641c0c00f68800e0200401484600360710182c0904122200d40550007101c0910138907540001d8802031103e43c848180c01202d900c1120071800901d40c103240b40321810740160281000340402d03205030b80604c118070801540c601302401010400c903410341c01030825141e26150402c05e108140130465000350104105204c40100700003080c010008448000300d28141445c20000c83c2c2c810924031014113006001c10001304650419001c010303859410085146031a5100203541e66900ca11041c00f030410100d8020140840000600074405690003210b4200400300d08000a0b04000c6a0062456000400050310402110040c88030740c00310404650f0303d54008400102c068100344c0001d60341c140e01150700790035481d042040d0009401501c01103002c50810308041401c54240c03001c0500102c6070084156190603c3c20140001507400481c3c0400032102d640004114407001e107e02048041c40d1003c00c2c06d840301c420041081c0300001007208007410b07d = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 686879253 1250 686878003 686878033
    0x6010e180a02090a0f0611011112190f090c0f2d0302030a1103011b02120703090306020708270603060f0409050d0818242e051809 57
    0x2030010110044282c090091420648a1502401c05490340c140c240309140e0412000502c0704404a040040c1c80e07050003001c041c4480f40000710f64200840c80341407030160b0780e0a4003584540b401c0c04400e00c145841e003c0b031040d442443d6130052400c1442500855403407644c80c0780d260300840d120301803114546071247c41071800c0c1a40e9441550041603060104400c280e40350002400e103084510161080428002d418820345420f02c02e4942908042c0421842803100e440c001b55103030340041c8501003102000880c2c03000d00d07000e042098001d59200d0700640da101014640300300182c002000e40c5146e440b80c1484003c0c00c1c18080d410120001c406480c03d400d55440d1000c21100c801581816600907a482c11801f0110380140450032400625480e081c0640c2001701c1d00250718070035030701885420340020031000c004e21800c1c0d030030315a100007040c001c8249850b0400810103000300780320039900c200c0406030111a140030b080e8a4004481045a200d2a114180c0c00503c01400d401c90303030004160400d40c0b000000030 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 686880503 1250 686879253 686879299
    0x40e0a02090a080607170c130b16051207030e0619080402060912150907080a262d03190903050c1f0c022a012109060506010e 55
    0x500002e2241c0c50056440503807500384181914003400089130a060301c030604088140c45604103035180007061030024026014880380702076010302002c00b900016010b140000f183c503c41c03940c0c0c3c1c11a0648008010300300801c4075a1340504011808152041140a031a243c084190740141c000200c05a0b40040210421201c02c040200201da00450030300c40307040c95841301842c03841c00307501d041c00078001101040c0348141b080304020101c2b500380d440404148000750012030386460070f81d4041c580c000c044e0000e8111031050008021156070242003c85c1d80340c1070f8050300340802c186011a0444a805521881c022929440216600032918504405145101842c1d90024448c40d00a00d0010b081c01c0c445c02d1428104144a00c0d00700066002501c540640c031814032484500d05040d000520903850b0301080c80075a405081781440c0d403880c2801c42040c2c030364020313060710b81c01d91225004d080195200b440244001c1100300000e03100a0724007800603a6550144c408508418170041010b0070f501109140c150f050 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 686881753 1250 686880503 686880517
    0xb0304023003041215150e04150c020c0f03030316050c072403060b2809030501020d06170606100c0c0e0106051b0105092503080f03040506090105130308040f050601030c090c05040e0a02 81
    0x404110700018001d03c00902c01c01441242b240c0c098410400c4c0d030010840c0b0b005c100031085110380c1040091116055412036030218540981c1011a1503140440711a410000c0030b0340b00e203200601c10700800c024054178290310544c0c040c860720108220f0340c90700491181402460100d01c0403036040031038100c00404030b030f950b41d1a40700d1074a440c4500b03580b60b40c0c4081c00d980220001014444c1c03500c40a01130309204054540302c0e101d10320001c1c0010310300840024481c80c4005803010030300009e0712040c424840c101e6085000350950310180e044950396190300401503402403031035807200e12200c40c1c0084040f2041c05010302402142009012089404040048030500054a607514000d503090010008804201401c440e001c0d05442d503450340b80c03d041003410440001e00c1003c1d540d242004101c240e0901114039001d0f990546000d18071030740c4520304034100421000c005095481a0400001004000d0700e403141911803d1505000303010180b0401c0d18a40264000c0c6000a15204000398812031254041c1c851 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 686883003 1250 686881753 686881763
    0x2090402030f0f06091218040e07031e15090506010302040203180601080307111804060f0b04020c010603111005040920180a0b0304023003041215150e04 67
    0x444030422000034074006442080014903041201001401441480081c45075004011450310b4102c864000000380111081814865031340c6110340c041d0b14000f0043d290186a014480c00c0d0085601c03d10200e5332079080c1c104a66110390041d140444442030b000c1e08007855404002441c00c0d909503400c01011703410050038440084282d120021a1000401c074460003407142802450703031707141107081010500c181100c0c001e00034078102c441c0030141e040c1400a15441a0003040000e07030030281e40d5036580589840403015502c030340041100d08030104194040c40c100d900c102462070140135880d090166961000981e0b00100760144000c0042200e26007180101d0040c80804400c0100d003c11301000c207400010840c1602c1c00000428680c50070146008d101502d403500c0700505515190740000e05d10030500780c0c410813642c1507080603006105c0354100041080c0e4024140c90f11036480e010502e21650301c0420668071071660a941010780301c814403480450140c1c810345894054104081140103940c040e1048039 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 686884253 1250 686883003 686883013
    0x5063106020304151b0804062c0f0c010203040303030213351b040e0c06030c070b0703150504020706141602070509090705091801060b03070815060a0f0507140a02090a0c0c0209040203 80
    0xb01d0f2814007403900814641b0100455271241244186d0310b00f500e6100d615070a40c0c40781e000c1840c241c2e0004140d50440c4e074103113005070340d9980b0708008109800541d804802400f404640551020300020240520200c00400b201407800e40c01e01e00507518002041314074001c00d440c11085050703042c1500507441c18440704d0111449401400c0218903135610072210924070400109540301006104a1030700d401c03000900d018031403140001240b44088a0f10711619124a0740041c3c460200140303a042000303c02050217040d90b1034034016034643c14055010010b100103002e0100702140300e1030705106590003245210001c200d414105020b03c81c03214009071585600c16098141c912210b0424090708000d440f0188001e034590030704440140030104003915001c0c41c0e8581744558500341d02d601064070926095841e11040c01a080301058038a440740d0180036100c40c421903451500b00320006142002c403842130700e142d603007030f42c07541c140c8001c80e1880c0303803c00b001801c048000805468003130403990f001400101034032 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 686885503 1250 686884253 686884271
    0xa0605160c0e070f0905060409091104051005011206030b060d080d0908180102030c0d120b13150f080a061e050a050708060402040305063106020304151b080406 70
    0x8401c041e4507511150442d00d40c8010451000c0e401140c001c072202840c10b101146a00301130000c1c3c200d000c0c0c1d008220286564810700d0003802010104c4102001c3c01a01c20040340c00d0044c09804500c02ca4003032280414600340300c02c2004c8041d817003100212a042030740c03007913103868100c01c100c0c0f8040065000d55101c18207000d204402c11051081e09405441a002103603a40030300107082c11080c0c55041e005040d9002881100010031000c28816942c052602d440c01c41982a80702c4c1200409100588940044000400481d411541d0b80550360407503e0030301c5610510790702c448031002d180e143d00071040180c021041c1c01e000a0020f812035403012003681080301c0300441c801c21034000c07520201c0308605407030303143d200740448242c100c100c1a800c000d0a503002d519060540d07c8155982034040c0082d040350455120030240b610410114003851403004020284480440c00c212019410030f560986403d6180150170b5103103512403141d10301044060310503074030040702e845050700d0410380200700340c0394540ca034803100c = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 686886753 1250 686885503 686885513
    0x13050f12070f0305060a0c02030307270603050a05060607024b0a080c06071e0b040c140d0b070e0d06020c030d1401060c080c1218130b0a060516 63
    0xd06120740101490741d1450078928074040c001b82001102518140414074001c0d030110840c0c1d071007041410300c2c1306210021031100341d40400b4a6090307003035a008640b0116085602d500424016101d810302171080d40c882204100f100e205400c4000e510169003503075194031040070303100d07500040c00200c41d66000b006078150450000044050b80c440106001000b02003038074100300004080c2004100900725803034494007240b01849044d00240c43e01d031850105140c07000e030340800311131021f40c010102003c40c1860304e05080b04103035502401401c01c08000145d001801c008460450194018696881035102e51905907441500c0c00324041e0410748440461000c0f031124001020ba09000800440d0748022001c180c80807183e19101080140d10301130300400505902038441c2c20070b070341c200c006a9900d03102c0e681100d140540d01d99020202c217a01164040d81c45015014110041c581503411000c508944903801c8100c817a200c040a0340072007002400c0c01a248250084c00b050540204035000090040d211 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 686888003 1250 686886753 686886763
    0x9050601052b050a0b0111013b120702010f140307080a09022e050903060604020a27030209010e1b090312030c03150603040b04030804030c021009170313050f12 70
    0x6484d812030302c1d010311038a1968802100ca40d00c0c52a0030003080300002080001341226101c0e00d2803000e8241484031000d440f030950075250708a00c184c0c0b08682800c0050140c3c10403a400c02d840c140d02040c50b011440400350f00459030b05440900c000009841e5580c3c0d41c0c8285c1e078507800a0080502c17070360341d0f4941800580b140c400001c01c080e1020b40d013100b41460644070f0b40c02d1900c6c480d818810090305001e022540d840c00a5001d4000700f0445001d6294805401c04550001c5401501c6040386034111807507201c0b410a65586080e2402501c10022581c0c0b11042001110403d541c3c42d090301e030218000c503c40c10441400341641c158018180e400400010107000c503103401c181c07038100050a000040c0217120000c0c0420905843c400d4130380f80e045241603100d00e01c0300c1c04024030103018043c01d50300150426108a03420300200e80d000303100e0f0f070300c145450340e0040c038034202402032141e010181e0100c1c00b0307225800010f4540c10414491030301400e605003418842070440302c04926400c100b8a0004c0150440f090207 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 686889253 1250 686888003 686888011
    0x70f181203020f070b07030c112d04060608190506120a140f07050a06211805010b010518010509030709060e042906041d01061e09050601052b05 63
    0x1c010190300c500c10758098213045042e440403181d00002c004640000307030014107201c0751680101c9110441031100020543c21286d41c00b40300410032081c07405d5007004052811600350014103075820041945c5070202510065819500c580d6030548150340e84086c600641c20603540302c003019041c802c0300c26000c0c0485150500c0280f044400b018411106094003c0030404d03d88040d40c468020001d05d4505800700d261480c13603008506c10414001134034a0015200103003181d00156410742040200000c481c4010780c0154284225421f50a1070f200302241c2d0301c02c509490314000c6d4031000c5445003049900540b0b80d9880802c00d141c0500070141c00007020595441034400826080e6182c4e401e0f0b03d07051a01d40c00e035035241901c400700d4038103c80e0103041c20500403203080d41c010400d403000078120780da030404401c0001d810010202c0e00e40c2050790100d840702042e4143c10030381c0d802403a0800b0080d02c911000301034900841d00303240090818091307100324202c00d101030b0302c4004500c0f5803120007100e231501400070344000b21 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 686890503 1250 686889253 686889257
    0x90311030a0b13140d080c03091606030b01020c041b0302090d06090515070804050c090402030316080a1206030b04060209060c010e0309120f0d050912060117060f070f181203 76
    0x26001820300c6030782004d00d0300c2071407450084c0801069040025007070f5403024210160900b000700c0024042e02040000c00450a000b8034a41800d03a0345480060143c00d04210700e5005000d2858400d419080c540605506500c0ba0b001449d0b08621b42c00e0110300a410030301d601c075486243d45407240c0200b007061049110060180d4060810503d003401c84d0b00751810054500800c014641d000c1001180c1d01254a00072034404a60412964030340340006803440c092410448100c881c078100c4501009506001440c011105d900c07503410980c0500688011038156100103441036008000160002d611136009092440004000d07504100300350a201c2d085078280400494154400189180d0515080200701c0719404450010300c1792000c1d42c10a1138403114040065010301c5400301d0702544581e240356020180445c52411070302c01c3d40e0354401c42c0c5024014218003c2243c065a00400d04020b00064607a10512580e1078040a101681d54100c030548501c00e04108182100c48010501650690507449505c0c0a6 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 686891753 1250 686890503 686890531
    0x20408010603111005041509151e0e03030904050a02040b0a03060504140108150402060f0d05060406300507090207032d020a0803100b0403150e030406090311030a0b 72
    0x5403601c0711010b140c00120394841c4413015190030031107078824100c9096820305031300300c20301c0503207102d040c0d861540c2c3e40c01118000b910440e50b000380c0e0b540242d01d10400000c00c4510782c0c00d80801076080c1c0d07032074007880151074041d00700f00400852801c20341c1019805c0210004018034180d912404124242c100b00c40b0301c400a904c69030b04028520306401000c100c49003504a998041d45445c0c0b06642c1c034000887c1204c07207052044000385c2035581d0241541c00c5880041c1b08241e03240c26542e04007000b413204035021407260b45811400700c3c15240e03407201101640072030200343e9040b10b203034500d50f442250912411580b074440d80c030001c1607141c031034005004001d02c40d0b11880d81c2c14070003a4400048103001c0c03000f104480c81d250050111140d0000d08040309580054555030b8903241e08042c214020b400e134100e03200108000500004015441c140c0380204844007070100801c802c0c22515645074880d42c42900c00113607600c0010320104134807001d21081c601d00101146d60130030040e5111718080f041151913942e000b841c = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 686893003 1250 686891753 686891759
    0xd1805030d09030510110702010c03030905071d01080a2d0204090828050d020702010c05010603030203130e01051f12240f0503030a050702030a080f04091406130c0507060204080106 79
    0x2c00c0001045d4145106400d10600986201c05c0303000780580c04004c6e04004144a020042c54001e602503e10b09400500340c40c1295160404040c0b450380c50200156003c184800000b0300080116403101215400200c0d520341070f8455500b0301071a44182000e051524881c2e4074000140e896202e00b19860303200f022621f4072000b14008080136000c0c803485a070b00300c40038643c074045d640d41d10000711201581c9440b00143c1380c141500040b20381c0c101203400141650720f4910b003c000d154000014140381110070303150740030843d00d80050f84659002881010b4010b0708065040d16145003081e86001400c2e640d1070441e88011044444c0015a5403043d10200020100c88900030342664810b000c80c06001c80300c080000c0c20b840d010100b56a8070519644000b0864003140000440da4140460700b420b94102c102d00e5281c0b02c02803d01c03041da81c0a40700381c0400b5443c00e43d98629a116620302d003881048000d05102c601030382800c0c01805881d12014003c108401041010001060380c030140000d06400e40001803c182 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 686894253 1250 686893003 686893013
    0x11030a02010c140a08040b070c0506100503240105010c171b0f01060e01140a0f09020309190b06090406060f0611160b0d0c090b030408090901170d1805030d0903 70
    0x1458101e020f10386020820300f8443c1e80c1040103584c00c19409801d1048558032104129a24607806400405600804044c089894a40f02c291015507800724140c0716041c0c04241e00d1940014504150481340e0302d400010481503000300d103984406405080c0a407241c3c690950001141e5100b00407440c4800e0800d03988003080c21003000078400b18403065008001d807508100c02c0355400e440501c205800c841e8210f0b2009899104ca403564801020083c0c22a80156211120480079410440b0303c0d0b141441000e0000c16800d00810800c1a80390b001424440b542d1a04824000c10120051040d40d80c03a841d2400004e03440300c848003540c02006280e907107058550804003e5401c01c281d480042c11243d0125206000c528211003c031035041c00080000501c190132a0001d940c081036071340c0304c581c01c070401000308012b11440000408080d9001c9a41e000103a032100790480c90050302d224401c4440e805800d04541c96400340c0d041820082000c2d500c2088690f0300c00c0080c4c946281e0480745000500100f2042003045 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 686895503 1250 686894253 686894267
    0x40e041101022d07030611030118181118090a1a010803030c0c01110310090e010507020325080703030603170c100c050715050106201c11030a02010c 65
    0xa000d2018024003d543d984008261040a2201124600c00465038580c24810440d450003580d00a000f880007041e0381032048101e800921406070a0804400320307040240d214410242c40d50740810801846c145291204070416020303884030703508040a20400d500302d807103882c1440e2140001e42d0040008030207a240540c88820300140c1584c03c10748420050060303042c0801943e51000d4032691440c0c95800d440f2419002d85004200e45010107c00804c0c820712034002c03d940700c1580d0b2070010074803041070034a0317200b8200c4404580880043e0404c2c03080c842ca660560f03860700c4141403c5024070100c0102c584680303105030300080e0100c0100350394070410010005402140961480100c40007420501220500e0381c90307050b0f81d505941c240d90380b0b00f44c038101c0038041c209440c407103504007440c2090284d02c02503660084c4028000e1001242c2000380445818800c4400300c41d44541c11000703400110300d4029980a101080010603040c0400c84041020315102040a01132052440d40003080703417601103030301421403 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 686896753 1250 686895503 686895533
    0x17100c170c0a1115010b130306020313021e010e01050319140601110604030903022b030e0a08010b060405060702061204030302040614030103240e011e0507030203010e0c07080708040e04 81
    0x5030048108101c201362450b09150456801003220f0307035030b4040781180d0418480c454000030451352011050115a031071410500803001d1080e1400c49180141102400c0350902c03000d80140000c0048413601e134a540b088003c1c58001800c0d10802d00c41c003c0341d440810590700d41490100e0628843c600308002980d014940c1400090888058441d906003a100205031404500002c1d00800703840304c42d080c242c41510f2980c900205034000004420089150050800c155161140c2c031816180030081045007041c0b044160304100101554607040c40c0501f4001181c003c12416a400f000070321624407071a00e00110305100390700c80e560050b5914104080a460030800d00c0c1c146030124000c0c001440000d031001c800e000092207940451b000d00c5c1040d2124400307450b40040b9004154240403000c075107865080403035140c0d4584a6028411a41c0300c0c0c02c00c4007280800d200f004040c4400c1d01c04140e0401d05180107020080c05102094900741013901d50a14561080c0e0160280000350800c00041c022011010505 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 686898003 1250 686896753 686896787
    0x207080d06050d1a0606040f03050c0405090304050f12100606170a0515010c05010b1f0806060a052205040603080306030105090d020607180905040b060102060117100c170c0a 76
    0x80801d01d4480b244a04c803881d01d50f0402100742000700300303030343e60780c40c192070040c10009402403103a5140d00c1c16a071207a40901d0003c0c0a00e0a05011520118004c400e031000d07940054003003100d501c031000130002c03020369101d4200c0e601d003d400300150081c40b071409032401074440da0302c80c01003000079103075140210070004040e41116890001408040640ca003500c5503106030034a0410068102070405e603004010740f24049611204c08a0410b034144c20342c41881d18040c54603100e01c0825035540c401e100311403045043c0040051006c12694080002a400d04902070058a0300b500101e0f0b2600b010a04440c0c141d0001d03115148040304005651800f4014150b02034050005070012800418001c0d41e1042c02403e240248040c80c961208400e030b801800000800b00c00c08280843d0600e41440c0701d6446040d180d603401070040000219100c1d404888c80c05010b0605030040000c10700f818035070380c000c2103005c5581007000206000908416140b42c5103d00405048207d1079440d400842c000d030400500e03c120b04d02d = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 686899253 1250 686898003 686898019
    0x1a0108070602121b031201080607030c0305090d111e010f06050409110f04090b0f0f100b07060203060d560c070203030304060b0120030d09020f03010207080d0605 71
    0xc10f0162030010341d91405500c0144800703600c1d40301215401c40c0142c0c0a42c0c4204100034000094081c800200140070f180c00b600c0812940c16035000c200e054440c02c80f440c0405501404c00001e07000e2156802d01418082c1c0401e450005100c0603464030460035503104611180c1d12080424a0351071144603100080c907088804105071003090751080b40c02403064002612a080c9401c07081460b031600e411162017030b80e0201100080c0d1610030406858041c042e078111311401598030010f0700c8115050600426035441040b22400c148082d41d9190296000030311250304041d85054000c006680b98401c41c140001c2c01882a410041c175081d84080450f0000010300e2911041403840c0815030b4512040c00c14800411048206a660f001810140d00c12520001d403d131000000f00424030800394001e4240010981e100b100b05041e405a020b0990340094076110503400400015034032000b40ea0021200740c0c406420030380c403411380000103422038000c80b4007500c021900040030000040684510780c041c08088134018 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 686900503 1250 686899253 686899273
    0xa03050a0605030607031113090e060f0c190309080d023a0218270109090b010e040f02121b1509060703030e030703050a020c030a111009031a0108070602 67
    0x20b0351131001034070305000e0550700c020b07080310700d5911011111103243d52010304102170340c3d408421004004900402030180119404a950004092042c074050840c07414414141404002c0030303508402c079903071140107155035a001000013030440d6000d8070710402150700046c0c45400e04410240c0b0a044449410300b01c181d650390080d04c0c000c005840d100609184080140c40e85003820304042c0c02e072001d00c60207078091441580c1018440c00c01c8081d154400c580a40d070031980e42d80d44400e07420394030800c4d002018403903803000500001c130b0782d441c00740e41c01801001ea20300c082440d034021070091540c00c0c9500c40141c000d40c08130881c6040060018401600c203503516160130032020040920707400f80164072441414001030300024103110360031801c46640190296661002c1d02e01d0054819031102440d030016002d002014491450003241100da83c0b40c000615016042a0f80208a04250460200804c0c0085100003101080e92540c0d02c1c8200441001d0b68041541010345403071034070700241e104100f1076110007006 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 686901753 1250 686900503 686900509
    0x30b0310020705190c060207121110022b0207171e2e14060f060a140d050403020f030a05040e06130f0c030e070e0402062d0a03050a0605 60
    0x1000c5240426240141c80302c0c0c0b9403800c0d0341440b040c400c501201d10001200e0109200410081404440d140c0d000c90350901e681d240c6000f02005092004ac0020341c00d031004415a040c00e11072110100702c0d5106845610021b080640c002503410301007a40c0b82c1503140c01e00050702c3d404000c243c01800401e581a20000030031801c540d40d810345840c41c1602c0c44042e241c220118402009040c000c82e003410744040605180104002050700240c6c880c080c42070410201d01184c1c420b1003d00d60041801800320054001280144503a13540702540e68403c000901d007a000b04041d0800c0a40b10a01d920480480d03113081c1410000d14101031100c00e4103a6800403c81e1001c1c035500001200d040395003a81405120742e8a81002030f8807c6101100381d20f0440c10100421140d041a80c0444001700c0180c03410040c10401c03980180c1d580106000e070859242041d0003040252a180014011420a803c02810070140c000c0441c1c072447c0c1110b01210300d1440104050660390340600525a101c40d0142c0100f007103510301000 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 686903003 1250 686901753 686901763
    0x308060a171c0e330405130b030304120606031205090a120302030f0c010e010c02030922020409090c08010e190b0703060308160c09020c031213050607080601030c030b03 74
    0xb0542c00b401d400c48101605000c0d0182c01107144009100600310041e20249504051260f03031100080c21128440d0500d4400d060300340c03029504054141c543d60014903000354000d048001e01542e151005001c0091b81411000121598034030913040428034524516108090515840601040c81f00c00c0c42991b485440b40c02000c1e08954420341040c2241120307003000da0452040035002001580c1c00550325900007015001100310588480003000345244180c022a00da004180203964421444601a82810b2030402124030007003106100501d0296541031480860306034140031a1500156181000350f040700f03200d525010501032011381443d1b035041038482002c800e1003c0c01841088c055003c00c1a0f41e2195014130302441d40300e11360b01d5480030110740950070203a0209007180c2c0305030780c413202060440b458000d54034a0044040118100840a941d08290b0035004000b0f400f903286024400020030810441d00d4058401500c91220354200580010700783c90315990f00d0024541000c403080050303100056 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 686904253 1250 686903003 686903023
    0x9160b2b1109040f020f22050409062715150b0403051c030e0d080915041b0b0408060a0908071a0105150309060c0a0e511809040308060a17 61
    0x20344440000c0102c2c2d1f004081d0f503426001075411614041c0c500003000311356440900d404650702800311403d8109420707110042c0280c480145010101d10754001c001c0c0f015002505100920305c03e02e20390545a400110301074005600540760755000340185d00100078802c1d480000d04082d0719052120360408450f040d42c40003800461010480c405001450512040c010084111407440340440300e81404d09218180c0520001d051094a500c1840010710011034801c580031074a01c24081d1003103503941c10100c402402e221100b07988003481000700100003000009041091128054010255410f02003400300134242e1007071004da108010018000b00e0180001c0ac1e41c2e002407130700c4080303076105d15540080f01c1d0f00b1f9141d0011508106902407071141c0300c5980e2255500c00041ca1080b00001d0402d8400158046950f048201a1140b52490b00e045a02070301c01440c000305414800301680e410303040451701c03140044038164005076022042c04403c0ca0100800380040a81e011a040402042400d468440c0c03003402c = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 686905503 1250 686904253 686904277
    0x40e090601120b07050f030a0e070501030c08010e04051c110c0a050102031603030e01090302030405030d0206070906141e090a080105060a050d060e031209160b2b1109040f020f 77
    0x7100007004c89100d50b046400103920070101a0302c0c0d0510700740d040007810138075080d480a80504c65001c516940f0038455540711141d10340d16941c3e56464110810905c0c5400341042e5803d000ea1070039a505803440e42c44020700d0081d203650703103545620214411814620024103982c13081c003825104000f20b81c1d000042c4c81121484006241124519207001d0700105035a60401050394200b0358440709041d00840580f04458058056032039009007681c04985407401101d040c00444d40a00c014490580305200d03420110540f001c00b81d03d8000130984030309032040302c001e1200d0310003c001200d0b00c0034180b590400000300503d0700244400d0030b20341c3c00605408042e0107614012104d240b401340c244010394014003000300323806003620741c6c0d20350008200484c28401c40300040a1302c42c0078034228a4890703100142d421114000c4030300c1d04008803403003201340c0508403801d0715040c2460840064000740d680d100e0011000d41c0444035503a00c806000034002550b0b01e00141040c02351042c00f140c200c0c0c06d80c9030b04481101c0695 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 686906753 1250 686905503 686905523
    0x50721060c2703031209021f03090f0b0103120f080604020c03120405071a030c040504020a02010e0d0504090f05010803090d08040801090317090a0f080901110f03040e09060112 77
    0x8081151000e01c03402e007801c1c0d5200c4010041c02d107086685109410340e40a5960380764040000600d04060b504007200003504080810b00c06180000009040b00c080702286c03402180c0000c03d515070040f0b04421650585c0d01c1e01c513a5004108104e00a45095035200190400d8681110f03d41c1000c2c1c8601401060346d401030390006511007020405108450028041200840c5542041d0608d1070744c40768039016104140e103014400c401500800401d40307100d111000d1503140340a0815003404040e4003c145500195920f440100011383c000b800207542020b6503548072074a070303071070056030b48103035001d0255061070140f504005101c0180c02100700e0f1258001540c564151211a2501103001d2242d903020704910f502e840502001c03d40e000940750600501c040e040e0780b180c0c49102d03449440301c07541040109000849043c0302c00081500d40070713004030001418852502c0c0c560050032801c00e02c20040e000b03a26040024144900e80001440c580c100015030b000300b08960409201107001042c080c80a4808100 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 686908003 1250 686906753 686906771
    0xf051801030b06030a0c03060f1508030313021c030f0813020901031202030f0d0c02101406090603281e0305030703050c19030c0f020d0c261605072106 66
    0x10010824170079032041c1d04084081d07a90030104014003200b030030000120706042036401150101c170701ea8030559510101861135500e85a0500020030000101240c0004403541c100380500080b10035011094000d0301c136050a00c840c0100100124002020107420305a2040782002607151184890b0540341d000c82d1056112408101c01d0740382d4040c1402d59143c4a0300094190508403c0740c01680034180c654080310125403800f080035055038030781d08008008460401c00100a40340024401c0e400078001350a560b140d001107841105003d5282030003d1984680070743c80b404000070183c03c4100203001c0307240343c3c418580584d0000c00c548005400c04c2c5c10151600e0102d01e4110620b81201c24003001c2e042c1e07502c0f8038550708078080d002d00b80c25056003000c140503408540c021400070450958048079540c5d9000c05412542d04c0d035007401c542c80110040d6104020b221600418600003e003002e07901c12915140c1c0c1e00113072501d14030744101034001c10110024101d0304200a219011011041c039405000807413443d0f4 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 686909253 1250 686908003 686908009
    0xa12030804080903011d0708060f2e1415130b0d0e2b03060b04050105070809031e1b030c0f010314010e090c0306040f03050a050f0706060f051801030b06 67
    0x540d6800c950551070310b000302031928481c1c401d45415000c82001d03100110f0b0f5034004107440d881c00301e40d00b10102b041030000482880c00302c4203420741855405010140e01c20680c1c2a00c00070b1620787c0104904280903010390415151416401c1151292506810f180c40442000b01a010030244a040c840e29001b0907440c0000e0015008204d40d804200110351f010649502c408202d20401c4d2229030710b0031014010810420700c41d0240c0303801e0751641c000302d41c0740903d0480111002e511954003076541c020140700e9050305644c03d001104e40200c500e00c462001c0700c2d44103580c40c1801403a81c00440801031605c0e4620090320082210303440d030b450448107850301150500c0140c0c003810950142880c411000800800e60812841c0801d0151428104a518184014051540d07070a82034901030140c139521201c80c00043d03c503800800707085190b85045801c150403000d41d001d80703800c44e08003154110f850303150034070488002078000002018102c03103100c20103540042200342540b0600010304040824000510720751 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 686910503 1250 686909253 686909257
    0x30a050304170307020d0e03030702010e1012110c071d0a1503050a12020601090c1b1a040f170301030b19020417010213050a230319150b0a1203080408 66
    0x2d0800c1c12625501e180100b002922100f200f04c001c00400c29082e107815150500000341e42c04103506841c0c0c401142c05500400446040320301c5200c00b00442c11130144d8400f6087c3c010043c1c2d00384112440ca0b00c404039014034030b050662503003001c2a80305541c1010b81509250170710560308003603036501c005040c00d61042d030321041504c140c002500602c15824900b08010910865510700141c607400c1c0d50140c0d8035400c204c4265903070030a0035000039051812030313402025607100c041c4100703120b0b125410401707070008030359048040100c4082c0c60390f0b41e500c1d0b0502c0610003401e031103810449641180038595070440e69007000c0585e005c0c1c84c51b000e490380300160601d00c0056504a5005d0060f00d4158a56003101c00c0406020303500041e000607800ca2843e01c005240d041c81101c1009a901040f092000300014071811121034074544132099240c802c0c095002d1025210000f10b81c003007801022406400100d400c0e403102510700c3c540e941d034024010a00e08200701c142c0190a0200070382e061078201050380301e50815900038 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 686911753 1250 686910503 686910533
    0x1140a021c09051612060605100903030302030c0c0f03030417120112050a0209010f090e0705031e011107060603140601140f0d1502190e0a03120c05070602010b030f01020903030a050304 81
    0x1607126150046111000a905e01d070402d03118010074440303551038800b07010328040d0b40c1101c0380202d0744001c0c0c10310009002c0d030051540079081c00e40a0742007420107c6058a09107d980b000320550b007000050000b4840c00e10160034100d501514001d14210038036980740c442c41d80c148560780c5100b1030070000c00708009040c4036075404031ba00104001d5071540c4410011549601d5407240f1482c0300d281000030040040042050000c8604c004c0103003464001c0162603840407911040b000e8961356031840c81e4019640c0840c0605410742c018480010505d0440c9400b010700340c08206004215402800100004015440600311700b0300103881000c07600490401081d100181c034a80201304c0084080c4604600c0542c0c0d014041c03000440180b0f00402204a000380c0320003c0c03c400141e001040001c060000c9410300c040307040c407200030780f900d903c1041c010345034641421410381003080140d44a885ca40042d203410801c140700102c040008516144076100000e80d07e1140b120f4180500c80c011000a081c043c0c841003132251 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 686913003 1250 686911753 686911783
    0x6170601080412210c030612020d0807021206010b0702131e0f1e0911011d09070e040f090201020601150512090c03160501090b04052413030501140a021c0905 69
    0x80d13000518030303201c05008420700000001b440e0000000d8240e415000d11980d698000d8107503040320256448264443e400030f441a83c10100709891900c10201c200450381c001d002c10f18156403100400c0c410480030490303940b1681c22450402074103131a10390803807802980184c0030304000140e820541d100f5001801301e40f40d06800c540d40100314105580140d030441e5429901c95a04d9003440c0340c1d82401581c141401501070081001e02c41d0b800452070601c01111904540c03582008082950020009002d89401040c0700700b070346403036101010465030100100c601500000d0b400321055605854028402c0c040c2c44440c80000c3c2c40f54021800214007072014483c20318001d42a540c1410451184510b058058810341c1d002442c0d05030002042040b45007075906942000b0400d24502c07011a12100c48407443c446410500c860030004190180f04845034400158820303000804c3c4a4281d9000901a5070001e042a0185004101d401c41c2c0000e80030510000d007100c0345000484c00c169082c610714200c510030315405 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 686914253 1250 686913003 686913047
    0xc28050309040b010207150e041b020303130f06050411040b090910020915040e04120e0f0607050c060c0705031b0120070914010509060a1505090607080d0606170601080412 75
    0x112103032340484094000241a40c0a000c000c070810400044600003501c040b0040e04144003040020201880c2d4062050041c17001c402041da860312014220748064408540c5e003440785818a00034242801032403441c440c00c5581e4142c520f0a1900251903800804114440f95400030302c04109981d601c1b805103050b041c0c03204094440d13485402c04201d403441900d040e110711604040070f490540c80341c000404400d00240c04101020419030500c5240e4100c0d1314200d0322070007015045840307030321160007800044441300e009100e0039240109050400e900f28040c001c14848c001c0c5184200e0342c0101842100d0010840d004001c0300c00901811b040100319005060b0f183e0400101042c0101c1072642507041c0c0758106c4456007252a500104940c52800d40b06000b6118030750001ea4203840c0c05030001d0a44400050030103854210a9607841d52254060110340240d1591401d05101c0103501074245a006c680e0300300d000400c3c0c24400006018128002d000811403090f61044041c41c0344103859a004400d65114084 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 686915503 1250 686914253 686914289
    0xf0206070210090614091515060904022b0605120111070206030709120308040611070c2114010e01051018020313060504030206180706140309010207080c28050309040b010207 76
    0x2034485015400004008401c0004500c48007499060232851030402040e9a02d400c00860500c4069041040c450301d450028801c00540209800c9158030b0001c2c1d0003100080150600040000711035071601c00402c245e01d420780342e040c0c10b28503030200d5000980440703074540c407a0789242085a0354170240d04554a0703118660629003c043e000b0490394040c62013070000b03225040960400e4161801051409402a00507103002c0100c0805020907800001403050003160308070f003917122407a1040b035030b44022015a5503070800c00c940c0c100030b11413590080c040f030704801107085ca00001c0c4200d064142c000703c003503141e001002c9050400101c1e03500d11101da10030070601c4a80f60904004c1c0d1146812241c40004070540484030b4400d010101c0c00f0410b0310104d0326100d04c0d60031400e248000e9600010000402590f00300445004104c100019101702072089000f00151909018040c41d404442c0221054003406e03009040e0020b031021007910100751081c0c40010362004038400403072030f020389540422041280c2d0300b450 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 686916753 1250 686915503 686915521
    0x6050a090f050c0703020604031211070b0a06050a0f15200a0201030b03011104090e03040b1207020d030c0c0803041703180c0a051809011407050a0f0206070210090614 73
    0x100030201d41c0c944040019503110021000030788152400280180c00800000300024003c03010302d0b035804800000021340030041e40740c04003290701050b81a500c9140c440100200c0c8a020300603840038100c03d43d01070407071620b05010380d0031907410f500900315129013a1282c3e081d070b03600c181341c102000701c003010b034030380359140d6640780b03592941c0340400c051380040c0c00c02150bc01d150905000780e0511603440c40c2c0180c42c244c94008038a0080081114181517800100300009141607203501500e0351902800789140b60303003030442020340b0b40050845000181400c01c0203245c4c1c881e4002911f0071460790000781c0d456407552a4544884000b0300002c4040c4070304004014060340c26800205845600a5101118003041d500703010800220b03c0c0f0b10560f41e00c400c08052101070483d400c6880c0d40c01002100c000f0603174810042d01d220b880081255080e00060001c942c940c0701c0f6030300c6070502c88845881d0001c0c00850806040003901e40640380701641a550300d40c1c6426081010b5a031000c03400c1c05000c80c1c41e02c1b440c10b15041c9 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 686918003 1250 686916753 686916761
    0xf0c011e150f360207080702031618020c1011030108070f05031506040b0310050604060b04081b01051c1b0f0f110a060504050a061b020d030c200604021e0102060a020d06050a09 77
    0x1a400ac1c46040c10316951000d41d219040d065520f482003c000b07d4944101002c003a41c41101024140d0040800003a2980c405d401141c54409201c1280c40c0c89604004440e1318040701d990010443e403025130b804108944011580190315210b403c603072401540e800d8040f80207442c00018940d054450f10861404a40c0c06510550007444111020700405d0758841180c0a14000c50240d001c0070b0300605120480c801401c1028200030006040080c10059a01050103c00290110080c999500c40184082540305042c04950812081c2004041c0940010b802411281031041207401e208007002542080c040070891070107191b0340310078240701520301071400130740340d0b0f401c91800c40705030703041c8044d80c840c20040700d00718541c0303041583c003c2a50306c0090608802904a24402c02c0c14440a03000303104200815003c0038400c924140c008040320704051051180452148184150024980d40c1f00616a0b80c0030458681001c29140c01603141c8011182d800003d21040d0700c09035204c05a60b400160611032a00 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 686919253 1250 686918003 686918017
    0x807030f03110a02160f141003090b0a06210b0f15040f0b0f010f0522051008060102060a0b0109170111031303020f120f0c011e150f36020708 62
    0x1039104103585202c500d01c001114040d4a503031181e4943d0711f03402e40c10900c08103480c4500616002c180c2e00c20f03d403201c810607002540d04042141e29420b05018024500303544100d296440034880c0c03012240b50700c510500c0c0c000900298140c3d600c103000302c3c1090403002c00030181c03904002c1c000c2005028481d84040208200c008072800f42242c410144050342c00f40f81b81c06e5509650380c0341c05103403c440d6010390510129220124000d03c5090718003240d16200e030707182c0109041a0791207152090030558006454100010401c2541505284002c540c0c0c0e41d020301403200f03c4003500e144004a102e180c0105001d0314250079240b243c01c0c0301004120303548180710790303401880780a50207680b41148058442c5413501c4101920406800f4100000d002451f1030000a100a444101c000a104491503c01c17038900881c41c0900c40f185a05da40d104281c11140e282c0074802007a07845152a800c4c1d15000d18000c0c25a0828a01b1100f00503c0307003014214500510450149030509000319581d100310b00e030076101c03038201c80 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 686920503 1250 686919253 686919283
    0x319050108070501050a12060f06030203070e040b0f010c02030a050d0e0111010504050607140c0a2612150607051903030507030203060f040e011118040506010c0807030f03110a02 78
    0x400018422004140350b002c1d10700680d202443d203d051802070381c0040340b0055852480796101e40008140364410994409000595409644c80c00c1111004040070050300c1c2c428852490001500d2180c3d4944030140385c600340a00381821411200d00000e07090036043c02d070103001c1740500d214807801d1540c0086080380003003090701d0b078680d054000030090b801c0741d00840c4d001f082d0341e0020300407502650003420301c941e01440c6407150501d40164500d0b02410400300c041d04458885840320501c1c01011191181d03102c014400200c00e090018040c1032080000f4060300070030091a81881a58050700d07410201c1c0e602a0300941124207070200ba0303014103280130f00000c0139070003c1c2c40c04c8045801c4502c81d00071030b4007603a00140007064141010041000034001d91020319000e669070010301903240b80b107002401d48080010703c0e00e0141203112081c003050b9000105101d040040a030003240018124005640c40389070507180c1450b61035010513040c2c00400c600084141d94900208420f420785500040c06101caa03518 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 686921753 1250 686920503 686920511
    0x15030f050703050f0f03030a150801021209060c0a1706060403020a060801061b052e061403120c030301031b0e0108010516080c090603190203090304060807020613260319 74
    0x800e40058450088510444046c0c000b0000703d51592420341140050000c9911558005036841c5000344c00c83e40056030b0000740e18480f608000107003100780000e5601a00d24940c070b41c40c15a603110018001264212103074088124000421503944840056030050344d80504500421a04d5200103000801c003485507000041a42000803662841c0c002c0010700300d6400801480078a40d81d98400310000031003401a8400c10300204038011100803405084003e01e8482c10b442c41080c50b1034241810441c2001c0e0400b2000030030041641d1090000044074112908036185181c440034000014101c04595401360300c0000107071002207a91001903001901030740b0000b413405043e03400400180c809503002c44801d00403a005204107030883c24a41c000f17541c0402c0f01540021a0150b28102500300d0700250f4500380aa07101103030034082160881c3d15980c01922a000504d014a042c89103400c40c1f241d820802004444800c0d280b50400452000b00702040441144843e200d18018200c0e00346e40150030f092400311402c1c = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 686923003 1250 686921753 686921773
    0x8010e100b0403030815041a0306010f06020718090203030715050a2007020103180b01410f030d1e0302090306040308041e0b04061a0f0415030f05070305 67
    0x1040360803000300c0c0c0c1c0d000d5403141424a580c5069807103000c01080d1400200c07211042010b9543c40c1d206091110741030f03036414003100c2030311000c0c94507040d4141c01025241c400c10809001d00b0350001102d10440f0b9449445030381201504000002515a0146c002e4052202003040d00400c8801266146141c110010421150b91009071404c240c51035000074156400741c015510400614200007019268010306000c2038028142d078040c5c3c080d2081002c16104e0394058030050140000d112440360301541010122070036004403002e002414003041000b000a10500030f61000c068455101003541004010281e03424200c6641c005411403c9251201c481c010072059502e505600901c2598121640038009180342c1c0c0e16550180c92904000e4020344200000f40c01140321401101c0d040590355101e08003000840c00d06150150590700c0c9500c1601c5840b064182c4010310351101580915280401c840100c1d841c0e01c402070303103c00350a03907130005072400f22101410030522000007a01c8044920a100b00e54403008 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 686924253 1250 686923003 686923021
    0x81605190b221a06040603080c1b030f0d1b140d03110a081b2515140601031505060a03060e0f0f0a05090c060307020d0f0f0f1202041508010e 62
    0xc41c46a00400d0034260108196407440060038880e84071340082e00015038240c8a4840d04c0c079130f4201084ca00c3c45079100d880f000c501034907903600304411500241c00800c0e10490384103070749803101000c40c00d40e42004402408001d45c005100c21800706142c000094944585119140b00c0e10340c0070400300400400d04141103072001044860840d40081084d60746c0001e035455600b40c1802800714561040c018550038050302d81c102541502052045e451444082580601441c2402161682c000c2246929141880041d810400c0002c050b07070059091800140700ca00602c804081c41c0402d80115400c000c01082100001e50582e002e50140c1c1c8003428844996906c550348166000310403901a4044c2a6410219035884400d8220039000014801134412035408400072035156003086900e4401640210089041a90080019543e4010f1441d01500584006c2c05c00f91400e41d2105510003003004400c0241280004c0b40d042d1806003250826030240401e204c5802004071400b030154003c860b40c1e050108a10f01 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 686925503 1250 686924253 686924311
    0x607120f080c0c12030c0408190c14010801090222060507050105010f0605070213060e1e330a050604061e0f140319060e1012081605190b 60
    0x1a280794001c0013005040038030b040b26600301510103090b040e414040401c0d0010240611211030382d03002c0000d80900e00504000e4501642ca60141c1d4028a9011035107815036442000a0705650554001507902e404030395041000700c18410850042e99014080800e40660102c028524540580000e125690b21001005681c1d0381c5403080341c1c040b8008011410050800c08038140a01100e1035000441039568049255241c408440745c90b10000d16003095082140c0300f0803440c2c0c101c0b03204d6614054014100103203035501102d4030600c44c080040804510019554421140060b0034094000d503100d80d079410001e442d815954070799001490250034429101b6209044076a0882201d175102c11100d2980c600240a40d480039042e030300850480d8440c860030074614010a030080c142c0351a078a040d8941071201c2d0420140c150403039101d2a8050303442001040072603050711a400780543c0381c2000c510842c94810302d4035004d440558108903c003c451010b0019880c540ca00c24807514450069508e40118500c00310 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 686926753 1250 686925503 686925517
    0x100b060c0c0108180303100603141302040510050d0602130519180b060a120605041a06030604060302150a0e100f0e0102210d140402031009020607120f080c 68
    0x41d0300032a0144100c1d03200710f01079504249500f11031444590782418150850780b00303c42d0b21a04103000380003001202d605200d64012882c20141600040c1480c500b06a101c1e9001c1c00040d1007140c44a0202c3da80c0701d0400010360007040300500d4013065130414980075002c0d401000f400c01a007801d1190008050502881c4065403911842c41c2603241414441e8200c002510040e840b0b42c2035560380e6a9190585410000f0164842c5a880c1c0450510003000340314107036185170f04024012406c0c000345661001e29048240d403103040440e0016101d940710008180241103542c0040e511628054078245944c1013076001b0901c1c0140350341c801e002040c052042c043c041000011132000103404290740e2032058410108074001c024148161046045140040320a112642c00f0201820301d00240582c1e0071101880380c44c40580c120782108116142c03c1e00000c0e140e10f804d040081300c807512511024115514401118222030703018502c001c580c8103105000340031440441410001c18404008101000003d005480d12 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 686928003 1250 686926753 686926777
    0x41104060809010b1012050121030e031006030f1104060302090402060d0b130c0801092a050403080f031e151c080712120204081507110708100b06 64
    0x601450894101c0d0600d800504181065680b4007400420b90f54816100c85580400c0ea5005a407003441b0380c400301280d5040c3e000901c1d2407a0b00940f007220072140c42441c0b21442d058100307142c12925030302c0841c1c208103030210803585440c034101c00407040100e4a0071600d4003501a01c0c00700200b005500c24401203825a000c00381d4000c032010006001403074a03030b009201c0d081c401d1302c000c5404400700020407199a18440c1e00d800c00ea841d50942d001c200e600006950051a40d1801480340c00403001c42216140590001140b04629005401000030300580483e00159484841c0071741d120000513046040d500305898402a80d00c80b211881e410030290b120550040140c0030b040040c540c83c081c100408080c40c09125038181c00d0045110010450720805420114010404050380d14850300008242c51781d608074510a0a10501040c40322440000308014000d04506c0d800d00f0703a4072200420303500c18240002d801e440e842140f00210794220b010600b61f101094114046c4590018070b0304000090085500c4190 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 686929253 1250 686928003 686928007
    0x6060f05030702060a241502010b0d08070320070801140f06090c03130f0812070c0c0b0a030e0f011e090816031107060e090106050f032a040303020a020a050411 70
    0x11844406900c160000e01e8a4400a0111b412072421010303603510070b9020030f500a01c06c1881d0101d10350203010782405000100d41c1940c0454982e40d80784801d0040785c0000e001c0044030010385140350241800307000901400c3c0110740101c1c4d600d480090182030180400900c148516002c115004100001c0c1401030a004008090765a0381032004015a0001000881c41e900305000400114030f000201850050103802034a903601c00e045400e55120700060480010000f5450f0301707601040505a800c410344e22a040c10640d540454a411000b82c80304807903904250180800b651a240c0d8154040c8c803000c4110b9550982c110b900802031001c50798030321806001c0f138030200101302c12810400d03400001c0358070904040403044801e9524a1424002d44c00840100703140d05981c0c2000d2a20b800e0b00741c0140301c5460f00601d0020486130303580d120b000103418a4441480565050180044042040002100341540e1629165a410020f5890f241d602013079000352038801c0045030a00b0305004030074101c030201d0500c40c = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 686930503 1250 686929253 686929261
    0x10507030c050c0d0b01031205030603060c030a1b0f030609020412030c0510020313111c0609050a0b0c180a24030902060a05190201060806161206060306060f0503070206 74
    0x965a0072140000b00d61a0040b6400c90125664541010b84114000d5003c60029811454414008154141d140050080500401c43c41d039078002401c60b802007103c0310f11500c0740c444500d540040c00c4811800c015101c80c5049010340d55a000600300c1c2d542d01a960240a01661240d20740101d20640c05035580d10700c0008040d10119010b100e04c0c280c1d245c0325104954914003200301200498000755444c940c00a81d08070203505000c28041c1800340208120348403c154600c4040303402c210a042c61008100c0d90301c400030345052150900214200e1500510030254a01c0c0620201500c1e520561054041509a900000980c18a0500403060300c540c3c1c07248420201001841181510010542c041091b03181e0140c3c030010b8030740d00f024041c0e61400f0f0b180c0545036000d04502880091a00712104116807402100b041020700000380035810900ca03406425455004040c12500c3c0002144025116030512000064456141d8000d800b00c41c550b5440c000703200c400300011a8148400d54681c4010b0b80f1140110f = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 686931753 1250 686930503 686930507
    0xf110c010b013e0f030406091a091203120414070e06030a062f0d050a1e020a0e061204030206060312040515071209030b060319080c0a050712060f0203010501050703 72
    0x40c00620840040900c081801c1c3d842440c54440019600105500f01007820404150020211005050402000b0481100c64441c0921074000d0400e40c4d03105010b10a0340000449003403080f40c50508401000b0100780c901410212a486807001c50741015100e031010000310041a480a00d014001c01005080524035544031440500112400071518038000702e00035000e0b2058034240500405c00400c2191100c02600c200c90071510010145001242000d00000c0350004451074800d581003a41001170300c80840780021640c040701c1e042c80942050f80040d481d0003071503d4542c500d200310f1281d42240c0c0f03160b03500303011b00d038a502c120310a2040760b09080c4000d0025240c4801155114080e56001509205107925001070480840c0000000b14440000920900681040045cad002c0002e070010f101c400924802c00d00a0002c461016103841e50100352201c1c03051b41844510f41464004c4112140591291800b8001d0503034900200e030700b0b901e001c031230810944c070301c1c02035074100c40058580909050880d201 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 686933003 1250 686931753 686931827
    0x20d14340e03070e0103030806270411060d050402090a09050d260c0912011a04020706021209030309010c0306030201090b09040905070f0f08060412050705010f110c010b01 75
    0xa00001d012510381c902009440030406200209190308019400c1c1d403640c14044c01c800d90203801c00d80144030940b00c242e12115400c490701024820166a260f0075501c07414140303a0094180d06103075202c480050880059405904070500490003144e05c445592a1032900390100e03031031036100814070b401c48c20000c50094092400e0340c5000320040d04040c2d00035401c002d12200100708032584400d410006c1221100740c10101c04114120390075000810200c003c0540340c4c0c0c070203c00203a0051046030005500000c219161701075900300342a0501618060405e0500c0e19140d400860320300000350710304052200194440d010302e40072a60181c499000c0035050810a42c0940d020b0590181c10944030036071240000d00400c0a00000c18090320758400c00f0742800b0404108000582c0b00c81404d03440442444045881c44c1d800900d00405410441ea4843c03440c0340540c0945488449072100900e02250304032005070070710048c03500013208002041030410800054800140c480400702e00640c0b601c4011003200c40c40a0b0f = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 686934253 1250 686933003 686933101
    0x11090a180f020a030903020c03120d0c210c0807050304080f0304021903261312210206011406070b01231c14060f040809060409020d14 59
    0x3034003284098580800d401070780e21003030156002035a07601003078040c198140b044031a441000c034080e0494410443c0d047c20940110b03100c501f0000c0c0c0d40c40e6440750f079901600e41245001000c00e05041d0b801003440701139005020070103262000c50f060400144c030061080c1c040340d2041d43d0020701142000c071000d041c1440c5420041c402c903004580780c4402205401d124804074011489a40d024028444109072800707072880c0e031070194886100c103005034981c11a0f4502c2a2081e54002806044001c0b001d0034031158941d912002d951601e22105010706400c1e44c0403615605880344040c2102c0d03400c0320304081c0140340c442c00c50081c284044400050041000140c0851010500c001401c03030382041500014211a14018210240b002e18140c2e00e020081c40d1804042c500320610094030991625800d0300c2446080100020b0850341b0015140d80f096540c2c10641d409003134079060440d1a041540b00080041c02481c6000c10944c0c4d6410002d1019140302400c048400c00712040504001000b139517200014182c45 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 686935503 1250 686934253 686934299
    0xa060b0f1207091503080f1e03090a060c1b0209041a01060509011b0201170c09180405060603070602060c09030115180614010c020f0a090c0c030f0207030b06010c0c15020106080111090a 81
    0x45a05d080d404232580c00303113018032411310180403540103e140200c01c69003c41410424024071080f800400403990f01807440c03150f0160356407080c1e0354507803901309072144044c130a10464446220000c44c11503032101c040c001c4050203803503c510348090b510180070002980d10000780011410444105910900e0f41000d40000441e0415410094603c0002d001c51102c40190202002d0810400045c05010000d1a400a00c290090402d45050038030003519214010078a200424001400c1102c40e1000d610046842040e944801c00c01c5d80c40d444680c00d0010f84c0c01090880302d0500001180b44074032400d0b2404c92110503150300c10030368800d600f4000310803999086503903c02c41c0d8040010f1814468020b10403058100d95644100c107605d440c010744040c2851900070219030001e4000e0001034000260706070014000d007800024a802c40c50101c0000c50035402c0240302d000350034141302e03819805420100c00c3d40c00f020020302018003d00d0344520180988814503500a403411010049101d420613400da41c200c1c08 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 686936753 1250 686935503 686935537
    0x1150305071a07080912010e03090103050c0708030103030809031c09020127091e0e1f020901051c18050f0d020c060409200310090c110a060b0f1207091503080f 70
    0x3034440c1c07800c42d034414801e14025000003903004ad05603414490300394070031100130f1058240002c07500e032030070b55000500004091050305008110542c0d000c0054036868030062030b0604018914000c07140c003400348914100e021420803000c00440e604071a429640440000142c00d60041c9420300e104083d05010070310761940745000440691105042c050408004041340c01011864502e243c41e9548035285401d211480b4814401c0482c580c1c0e01c40100c03151045042c42d100344211a5000400c020a00a140c103960207641c034001c601008404102c100c1d8030040030701034900e0030301c4212003661a08040314031a60b2020040100f0710001000e68040c40655006541c2012842c00342002800180e00c19190b1440c89210b40c5010420b099160040c103416041d03074075100450320301c515036440d526444250010512910380003054441c0d1a40a4810484a070050200f603020181ca040c06072607250318001c522a2900f00184104020301d1500c0c1076080b65403091442d4584018082c40b022140c0017942028091040 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 686938003 1250 686936753 686936779
    0x9150f040504060b15040f05090403090902031003060507050909010b07030c080d1b03090f02040e030d0606080603100915021c05152d040b0f0301150305071a070809 72
    0x158814688030b5880744000060400a9030200000516048150301503600d00f0030042c49501c0c0060701e03203811903009450041203904e445ca015104150640c006040e0a0b06c04010821a1030100d0b1804086034010b00c0200201d48a0360300850f007074818032039825080108080100002c80c1c00d074004004450082c58a06002103e99641054561102d80c46440300e0340c44030741400e548071126403140318218031400c04010805103650340c02c035241c4201c40301a10032a501d4400c5040c0bc0300610490b140740c15145810000c45841e400003902d4084240e4419000703120310009400600740600c83d8440c0240c009082c450240502c013240c0e00654407041c91120300e038104414400c0a81e4143c016035016500c900340b04641c558280040c030440c81d47d01180c00000260311080d40d11060651030304101d400c04d050310045040101d00b0302103080302d840f4805a40e0158600b00441c0c3c81d40c001480d100c0285c0b031142040c2d84442d80d994441e80030341d02c4160401d02c801c00e0200075040005070100d005000211001d4110b44900e90 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 686939253 1250 686938003 686938009
    0x10b07140a1b1502062401090b030108030a030e0f031e070203010c2006060109060f030204120f230d1b02030a0b0a0b150f07081b070303031a09150f 65
    0x21004400550301c41c411802405490fa040354000c801040e14030007419a840d00c42d10962500108550030181c004103c0039004c0180d2144110034050044990391950300d50350317600c40d0342e40c9902c1400b284002030b20307114144030440350208a141343d038100900118200614400162181c07040740c84940021501040a40c005131000e010304d01001145445018140100708003030603841e20b00003003802541c1c00400800c109a0381210f034210a403181880d03c2640790b480707540203038028404c0b03030000e005050f503180811040015450749407850341e10441c0384c40d1050700c0843c0c500400030820303041c0000139003040c80c9044540744611401018000c10340465100c480030364000c2400c0000340541a2000c0240c01308100002d40c60340a41005000140d4070200e01d20507140600b6002e000358401c01a05c6a40003076a07005021003441a1815602c8003c0d005110740c80340c407001680c5042d03510003100441d08120b40103070b01d20887c40c401458070101910700304040e13980001c440d06c4034020400869010f0b01c03008405d00d2540f = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 686940503 1250 686939253 686939273
    0x80a0b040b06060721140744030402013915050403030504030f020a020303040320120f0105160815010323060a080601050a09110f0d090c06030203010b07140a 69
    0xd00c1c0e80c09802e17011030111170020800f0b8032201e540318800030200f0104001800d0403a91040141450b22042120420815400920100841090b049000d080290454004040e00a5005234803d881c0d440070380000e4400b00c0000701e10709008070313041c807100040c500c0d010b000360b202e00c250144100f0103803074400c42c036a04660480e04140e4040c1d00180e500d9040204064100b00d4040f80d000c0280002d0100300c0107640007d0f0380344120700008100f41c0c12071450b4610451303c1e0b904800e0035100180a182d250750700c543d01d60f94400722000c44d541e556081c40301241100d88110721096403620603960b003202e03940d2046080e19010140705d010b941010b58038117084500e81181246200075080303140780c0c081d59003005400c00c400044c0503002000c0940040004200741c0e66002c0e1100100c80e905503011420042c0c8807110181e0b400b42106c0c1d0b151200000900303600010003580714281c81c43c030841400840503203400007101203020901a1180c0f41400f0004030021415a079426048100000100c901c1d16901d47d5400d08a0 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 686941753 1250 686940503 686940533
    0x504061b0804180b0301110403060b04020702040c050c100b0a0b070212011a030105010512060f150d031205090f030a0c080405180f01090b030a020f1804030f09080a0b040b060607 78
    0x40324041c07580c884000b03c3c07070050b5054110118000d2124680c0c2e9a400310881c455480002e010560700c40780e481207512076030141d0303548940080080040414000014107aa40202c01550030b50160048850181c60b541c4507128035811302501e00740245040442c045455401000240e9100c008800030005460090080a0042107036441040140d8290400e1500303466042c3c00c21413260080946900807568000740080e801600030240c10416201c180120b01c83c130340305401680e00009920f075404103040d04030b40c01a041040036081040550303149401151a0361800c56121f0244d00b0401c09d150509115130041c01c10390780215803141c07409070344000084882129001152150001c4070401c10035000700c80006005250b084010300c95240600e00180d21598058002032007010a204d0154594583d010360715010190710f030851035181000d0501814041044800e1800103d030841c02081d0344101007411980d240d80010b4420303490f210750380c503140e0300c2c407000f003a85400400a02600000c2002c4203018200 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 686943003 1250 686941753 686941769
    0xe0d0b090c0a1a0a0813050106030b0610081303050a02121803011503150c0302091c060c020d080c0d090507030b0402030c0a24030e1515010f0504061b0804 68
    0x900c5105105200c640035240d800425440f00002d440030302400154219005039100d45401c81e0269105403162844038000c1201601070740c42c0ca01e0200c100001d03d00214001c1404827030307000a100007844201c0e64081d04840f11841d1b0060b10b800940006d0142015041c2d0341d65900680e0311039801c1c10116030254104180c0403000b00d58458401109050a1007030041050021091010080c1076031141c0e0100d0349010a100c003015a60007c800c201c6200c0c0d4142c4180800c020040306000d907511700148028965200250b074401d180c40c6401e0851070000560b02013404a0f6220340100e03507501c40d4403401e50340207000030f95041901d4061500000e4410300c5102c0c0a544600d0802c821030500d03006041ca0b0002c081c20319400388c4c5e000e620510802da44080c1869900041c9060741b0021040c800003203001c3d005403204001d0310700c900701c0070b20100210b0202c16442283c04c4012912007000e050011242c0c07003207817072024021400400050120030b208903040c00781030360f044103840410341c030030707910a115540194881b8030 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 686944253 1250 686943003 686943013
    0x10020c041103042904030e03030d0f09052a040e07080d0f020606150d0c020a0605010b04031505070e01080c090a140102060603010b03030f0a030f0606020a02012d0e0d0b09 75
    0x30054140d0b05420000048189131400b0f80c0f00e0a40c96003084005800503042c0300c000b0748130005a950800440304248488501481084847c00c05400542580c002c2110240103000040007034119144884550892440f5024490b03946001400020030407085640700340c1c050342201040300d003000c101c0c80d8540c1207191344402203d445c1280003410114094186032150110030388a10701d0407000c03000c1c4c410300d00910f8400540600346041c00d0741b420503011401800c0a007408000200087c10002400c1107034010040c0d0340741881070290a00858004031151300101d424002c40c888594815010194018208500c0714900314880d4009181001c19500c503c59515103d0100d1481d0351f818030130741e900a0800c1d1b00030703c1418048400240c40303000d1107249526410f000304621a42d41e101790001410206204010041203486410003902c8508090047c0d020400d41c0c2c01d8050401d50100d8607074a882e180c81702c03000c041048a4012038185c2c0000c10079642c055a05070180000c60801c1c01114041c204800040c9 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 686945503 1250 686944253 686944261
    0x1030e0c061e19111501171f0c03141e343e010b0402040f091410030303050703021209061614040911040f0b09150403020f10020c041103 60
    0x100352980f55042c03002c4da030b000102101c40036221164450f06480141c0700c48025118201400c502c2c2c070908201038000504c1c00e81103402003049603444000009a550b81c18048800c0040754801000e8041c2c80000c00c504060040300802e0031140320443d0826242d070034400595140c8401c50761f4000b512405111074000c0e44010f501c1068004c2d84692028150240d10307800c0b15000320f003a0403c0078900e941c083e400c0135554150380c40203400b98014442c0a60040045440c1d584800e60300029010300d0040000044c170704403050302d02e10045004a4414920405010300d102d00b5940d04402801000d81403c050603024030903640080303580c8034414862111032006090f1860f20740041c1445200c04241c42040c4484841d026034a224040f08036400e0b2400000045408484101041460300c11540804542e030450071011503004458001000000e00803511200c00d0a0000c0150030584542e00c4000d50045102c4003482003400c02200d645510940307401035070400421240424103489020701c1c1031960a20000c100 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 686946753 1250 686945503 686945507
    0x60915030e1219030903050d0506010e03070602150a0204120f020d060204030b0a110f0a08190204060f031505010e040906110c01020702150a0905090406020403080a090503010b01030e0c061e19 84
    0x8805042511307041c41601060348014200e03114040f00d901149403640c2c000f0300d03164020302d03265a820314094202e0b1082503450f00c0081d100c000141050799402040c4021450b10421030003920180d40200d9444010031503560ba4441c880010501c0482c0c10a2544083c0e03004035840b480584000e5010350340445040c039061510400701e82c03001d0381320840c03603c05002c609020754020064420312803440c14043d0158403010200ca56900389420008202800010042082c6d680b2007031014a00740c0d241c40c28481c004607014411b01941140c0501030000780105600d0f0007500d46500310b90030050240c0400038035191403401c0c009095010020220480c7e400180f40d5045042159400f601601a51250745c01c20941e84801420800180b040d54807420545003c42c05101c0107074119002150322401c0795560f200c4400c0301400c40030340740c07254034801d500e002d18140541d4044d00034042901550000b0b0002e04900004112094014150361484440310b98000d4550390a404020407004030b070310132010502c40700c003200 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 686948003 1250 686946753 686946787
    0xc07051921020105010609052202030a060503070b0301080d1409190f091104031205160b0601080604052505130806220308071b0204050f011707060915030e12 69
    0x207400116031624004009aa0740450319105a801c101c54000c2c0c0c9031861800518181840e11651903810310000c2403080c2500340c2c0c0c2c0184100c2d1419010b503680203644640050381800244569116600010b01d4030071800d1288185181d9000b100011303500302164900070902c0d440d80280740355245c0120207014400c0740c240e541d0040c000c0c40c81d0002841505265004401540034a11006107120003007008001400c0c091825682c0080141011010110541c100310880c40419640c0602149a100200d600e41c2414011a032181e41c28416000c4084a111004451408101410320804c0401c2c000030314401c0c00641024001e004440040c40b0904144075990085480d01d40e000b101c0c1c00e00310b90307801d0000c0d4100c25130700c5d4800a9400c040d128901241110704c0c80000f8010001c1d40145468200603101541409550603175001c03600c1820171103400180c040e5289a94090500480c5505004200101c00050251046004d41c50041010282600d60714503007905c641480505100c0440c40f154180796941d1 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 686949253 1250 686948003 686948063
    0x60b0a09030606080c1f0203040302120102031e04030f0c020a0f08071701140403140904050c030a05070e03190606030507080304171f021b07090f05090a0b0c070519 72
    0x80500390301c0540c0c0000451240b443c4443c0666040c0f281c1c0c06da800c0303070700910076200299006001890303107036041182c01d4000d41c4203c6480c007400400d8030540300b4025914070558815a0301d615400b1000b140440d042c0c901015035001241d004040d1b08020401140f508603081c01030101e4002440c141e401c00c5e03000003800701c801a6180c4168508642503003803100c4a0b0340c17541c000c0c0d01401d1024100d03a4a40c40400719100c0d2810345a0444d007080284803004107d4002140f080038105020440e58450072402c50703c81500c40c000c0c0d070341580050605ca8198a10040c201d1034039100d1900005c0c1ca43d03699581074100319441d80284030035003012904100420403404107240d503028000203409102140c0e0550070820302030b003840a080030350119602d41c6034024882c1c0c030590600c01c80c04942400741d40340b4180000d800845d0075880395a0511021482488002400040041d0720102409043d42c600d19480ca10760407803d0261000d05c9844000d50000786024810000710740506500d00071442c41d6440c10b0031982000e0 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 686950503 1250 686949253 686949269
    0x40216060b240c0307170403050613020a05150d060305010917043b04291003080a41030f04080a05072a0b0c0606040f060b0a09030606 59
    0x2c0007005500c0c10811084071914240841501c5000c091119841e600484030001c0c20141d410130780c00444280c072005042220700c120101e40e182c0e0f580601945400703882c4e500080d080784a00b90240040d140019107540080180151a41031002203a10315096403001d90043d141c6941d191414014021044582c400682d44090034a2801f0f181c20401031017008481c0c1c0076080d207405032140d00b034440c4c900f41d8010065040c4c07540d0380345541450306280d10480882d540c143c1c88203803500560100500d07440c2101d48101d2a00d920300c0c0d4854916100c02d135444c1d12543c600130400c041c2d100e0004528000150b0a200884c1c190310500d20601c5940201200803051462491041c0c004d000f006410031801e456180c1c032940c85452540c8a81e030001e415901e9000c1c1d44002059030111401004003040c040b0400c0162280d110681c404031990f0350590003442c412032101c00d100781c000c1c0740001d500e4101900a41d102e502c1440300010450350310090601d00360000810580001d00fa80c0040060000318080c002c06003001c4 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 686951753 1250 686950503 686950519
    0xd09030305180c150d02031f05030703020604090c11030f0a080c04050906010f020f010c02061509010302010c11030a1e060b010305070207051e101e0503040812090705040216060b 78
    0x81038440c1da18400701440794851084a010f02421381c100e08240d61080348450019074490424034103400001424048118044100d40d00c0060b061030001401e004494024080300d2400303080101e0240a0442c1c04011020b0003800d80300700880050410041c564500c6028400c1c0d154604414018180c1c60080d00050f000001400140160f40c2d422041641100e0b090030200740700750a80e40264206034900c40d40845552a051100855903004101c03540300c0ca040c21400d5290105820401046c071000f030101071700203414041d40c034000851904000c000c1c41c0008040350118002940d403881c448008000c4210390310a0400a94204111030050410380c54090805100d40d01d001200203603104020301c02c4521030303a604a82c545c01d040c518400c4400d0383c07a0103080d46000090304e41c0c0c003407d02e0012030307500030700610940e030304010740da2061043d42d002c1d5038400c41c0075181c40260180d2121490000c3c0c02c0744c0c0d9500403050006443e5407503100a0100d52141d01100c02d140714941004009c03074941400fa01c0c00b42c070704 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 686953003 1250 686951753 686951791
    0x1609050115030f0b030d0207050f03030309030f0d0b0901090c1706030c06070309091b08010f0806010512010b0d03030e010c03021204030302031e0c07120201020a091701110d09030305 80
    0x1100c03220194440031840c0000c1c4108050342c8000c0613144048980c3e070140101c540c3c0c465800d13800302c0c80c001603540039640518900402024113903644030440c2c5042181d00140040341d011b41079540100303420010004040360940f1050000780c6041d600380d00c040131441d03640a104401c1074204d0f03a143c051007a40300030303c4e106d842e0404c0482e8840341040076040c4103100005482c000c05019148040141c901c480c0c0c01c100e4010203400c285e290410340e04a44000c540864000110807007104001e4064550060240409900c4c1c40300f07101e03000c1612800c0200782d5484146c012610340f240400300311618003903070700441d5080703d4003811401c54078960701039400c140c010840c0c14a90311103005e10a42141d07140c500160b0302e030350320390384650702c01282481d0202c982091310601c040510004050400e1034091b83d907540610010020590807440f643d050000890300d0580104422841098035052201d005400881e43d9540841e541c021584074016009007160b03961010410300d5030500c43c0355032010443c100b841240310 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 686954253 1250 686953003 686953019
    0xc12090a0308010513060909050601081e0d0f030608010213050a1703090d050f1e07090618050709050d0c0f0b03010e0115091206050601030b2202031008070816090501 73
    0x50305000300344c0601d01582c003585004445a2001b0000c19064104026044072860a81d0301c810081c0308d4031b8210320422007941c0500c7d0140400c410f07038844c848001d10b21030ae0008000e07908403100c3c0030501c040c15901c03800098112020700041090016140c1c1030762025003044200228041d09400140a054001d08a03101d290000812a68203050455600b0381107491898030f0381c503064850103441c15600400f110f15004040080200b02484030102c19142d1260311340269408660b414401c0505880301001402d581d920603501c4181c010240d4038012020f10b8861000c80c8609014442c101e074008403c1030100960f5180407821809031400030945031855143c02c851000c9440e043c001c04000b180c1485010b13400d14003c00000c0000e10603c3d403010104116030411800800089032403601182c00d00c0c0b95030500345440400c2072000d000032141c0248912903052070000941000740403a03c8140c800c2d001150309007082001100a0512000400703540c2016004c454a01d241035109410300da080c42c0061125038 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 686955503 1250 686954253 686954267
    0xd090c090c02030a03091403070506010f300204061e0e0a05160f020709060f0e070903171806030a2003040309140319121115060405090a0501050c12090a03 68
    0x800d1490701180c13900041c10325143e409441f9419070300c244400200c2c0800c00c40040395403812038542c0b500c03413900c142d03680b084800715010034003204108102d0030741c0e1501d401002400650102e0b00141000501031303110b03100c1c2003030f42d1940c2040040f1900600c00401401c0f001c044031031703480b144003001800607051034006088201d4290306000244004000211192413007004103900a100c40344081c0030084d0b90342a8001c0038071960280c240040040c4001602c0280200d008074220782d880007468a001c2e00401847e006a0400d0040c8401405649900041c0355101805180a10504500080e800319204207101d031808007171070142d01d100401d00410012a4104a0b02011904014030b011380c0f442c50f0000090900410301002141c1c1c250310502a024040d104240c0841c0d400552150103c4041c8440256a42d00c00030901c120a18000c4000450303509050b00038a40241000e03040300c01e04000b0f690303000e00b540c0d0203d85074507150001181d800001e200300802c40c2d801c8032200019100f43c4003941c030010111 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 686956753 1250 686955503 686955517
    0x11e0905070e0402060c07090603030f03050402010f050d150b0c013606020405130c090b16020d02061b1c08010b1812030f040e0f06090a0e120d090c090c0203 69
    0x859510b0000909544070203080704d210640f030340207403031605880d1881c060081c0614001900000c1030f04012601240c0a803142901580d0141c443c034900903a403503000c0b2010f0340168480341045880c2c40d0115140407a0740c03103490140031421061a25807184101541c06c440130003034140907810040019091003a0034503846080c02c0039442c60140c00e1100c070f042c5030001e44a941d101581003072134442c6d00840440698440480c3c03110350b0b40c80c41e26617031390741d81003070140c0c0070f907013080301c12188c2c00708904005150405020705103a102808450800c096402800011544003e0441e9560800345282031586844e00d148031280c295802d28001e194100180210280500341e00c0c0c0c1c50010b040e21103242c0c00d82e0358801c0a07840310801f08c2200e03074801d1400c01d4108280c010b07100744c503072055551000c01c0113006100300300c6100d4100588079041c141e43e0303403414038060305c500150b107196070041030b00c1188904100c00040805680c8020003040400d864903094550409541c0620380843c5003000d0444026400310481d03c5c0c0c = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 686958003 1250 686956753 686956769
    0x180a0b030703050915070507030818070902160611030109110f03041506081c1119030c030c02210c1504120201090824090d05030606180a08011e090507 66
    0x41d81d075a00031380c1c4c5c5003100312103060004081c040200044694840001c1c1101403080c0e035030b440c0c00c1d01e4090307250040040b00781d0f4410301d81c0c1054400b030100c4560350340074009000136040a24000d4178140c5501080700c0200118140d1560000014000395616000784072000340c50b004418a00710003068221100d01010700000c20b00c1c0402d260f90b0780c58a00a4110074090060501aa08111500e0741401e902d0614101140086002901d034021441c00114135862000003590304582000101c1d5400c40b01c01e485c4441c00c50500504210b240702617260304001c01c4900c01580e126201148120740e0991034140101c21840c481c020003001804541403c000703446c21108100e500320035034030b002c1c80180c941514503041780113148600c0350320200d072000c00d0483c284880c2040c0c48041180e2210902c9541b03448a6414290228400300003082c11030522400402c2c41000c801c425801400c881c0e03000420700245984004500d0303450b1028042d407800b461a9008100c42400000c01104000b550380a44440e40d510480070 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 686959253 1250 686958003 686958011
    0x80912030408040e04140d020102091305010b0307030507020312100f0806070c1731051915030b0402070b06040b06070b04080a0c0203070e041e0305090906010504080f03180a0b030703 80
    0x704001a5013146c001d440780d48000c0e14100b10407031000074001e42203503081920610440c0c5000f4414072a91207194140e0314100c00305407860b80c030204160f015050141003131007180300030880082c041c12289845c900690340c101384c410649181c5206143c010b0896002140310790809030500800c60303046a110b40032158482c90540304500c0407100b0402600034001c030080f030204100300f522a0310321300c5511412843c49007100c0c0c1d64603945807414030803443c0040900800d0810125020f001c502154036007131020355840d00d40407506444910110302070741c001d05003c80b000d0798484213004a41c41c1c180540c2d5250784c415164141801c000b0744035512400b10180000e401582d00144000c9000d100c3c401b816051a005400c99801595032140c201d80c071102205d044d84c958441c85124402c4041e0103401c4404290966030341401e10320200204001e0220241c03c46050200403c00050380e80781c10b0200b00f00903c58003001d907490711550144030103110121412544500d84850042c0624140d01042d6600705020349000a = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 686960503 1250 686959253 686959261
    0x6030c020331240c03050d02090d0c03030201020c0f0615061c0e030c0f12030402041e050108030d050105030703031e120f0f0c0f09060c060603080a080912030408040e 73
    0x4044054418012441c40010840128144242c10b85024a01069000300750840f41c8881c02180c201da00303180014002441001002c0b040d20854004e405002401000c00d01168095902c00c0c0350043c09030300850150f500403594002c600b0080c410b10391160803030b0380a84054a0603113100a840900c04481921500011454000655010b04010000000300e98204048002004010340e07d8110b0185890704d88034003000ba040301100401c41c420400d030b030003240c50300b90f844603402c00024025403c184106150300035401400c00a0078010580206507644c091665a084a1a07600070b0360016080207005c0d51103100700b0800030394021040c1e0305480d0503000340064a680894115881e0750000007444241c0d0400710403803111291a40401171550000071304100200f191a016102e441c0040483d5001c40c040c10341c20007085004102c9520f50b507101d81c40004a0f251207540c0e00000b90020162030002603004010001085000c100ca09901e04d1405001c606600c0d1a0341e603140288a20b00510b030b02c181001d0045 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 686961753 1250 686960503 686960557
    0x307030f060812120109021e0702010203070f23070503060f06060403060213140103140115110610051801030c0501050706020d0f0902090a0b06030402040203150a0f0f06030c0203 78
    0x1c0c402511421090b01d101d0300702c21100788415041420301c00d0201c50f0b15000041c07070b04031a10845018185100e481e10000310341c070080c0e04994004d0042030717040d03004c200700317440000d8051411001401d10500011803e03040c02250b414094401001c2081150b11270a410b0041c0e40c0d0004035141c3c0043d140c5c41f20b000b2540e070400442d060b8002c550008043d2400032464211155005c072003501524407a901d060b0180b12040011801d0ba00c000003a8910f4210150041c807803000d0003891020030b662242040c41d4980003500a00d840c240c2e0840300c0244042210704107014500e00b1355003440fa90703c01e1009081c115410340d103900f422482e262044030f040c440002120030400c511074060fa200508248820000c03070211100d14006005100701c2248030b4a18840090f4000d8054880c0419080c070252405095940d01e90a00c4001e6001405001c1359181400c1482b1050345c0d108840402351280c10481b0009500d44070024121a0700c83d00207400303060500d481c0e0001164000140c0c1c0c0f03a401e10348890f006c020000c0080c = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 686963003 1250 686961753 686961761
    0x201170405070302100203040303030506060f0a1101020912010f06050411040e1003141b0312180a030605040317070206010510050d110a0e1f080c072d0b0610050307030f 74
    0x80250803817600c200c0319101e00d030080043c1c0226800b0b918188040d540b400c0030422a0f110310301c025407400b0003c0c009240c0c241e125401d0342c41d9685803080014a801000000100c03040641105481203a4445140e5006900c0c00e0152000920050302c040c8041c5031303001c5480b080d60065004841102c0751480c00101400f102410007001190414a081d0075403020a1060b5103403000c00c8130000c00241484242031300341c100000c440302d10809200308076082400c40c0d644030941d02d10480340641c2c000038131100400810a00e1042d9130281d8401e813511401212080490504024020700c0da80540d0410801001942c4800c20814001c1c0c00a16220b980e88281c04040d41c010141e0901204400c14081548294160400300403190031500b210f4001f40f26100d44289010111650b414600180307940010400c8490403202400400d842080b4030903e11080071081c240c01e20442410380d2070f142607541f81c0300501c0001d18806800c030b0380a07101070003111400c4401422500c0090800001c040d5604003c150f8600c583d44 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 686964253 1250 686963003 686963009
    0x929090901060e070f02062a0c010609020a03150b090603012106050a240332030307050406171302061b0a0f02012d051602030d03090c080109020117040507 68
    0x402440f41c140a5001000c3c8440f00d15030360090310590011a0f00450310b91158003142c640b4507007204a560300004280900d8020b4100c0f00e8142d921841c0210f045011400600000d0556980000d40714034005440d10344650560302c40622500e04000d010201c0d00da5104172810b680701c0e058015494050344540145140c641d800184c1950700e444240202540a90041c40701c1c58103048030307903640c1c091340c0c0b030162908036030752000614860308142d171064584400d42c000d00e0344101c641c41030460000b10744002da045a0046418000080001a0501296407c15402060b400d070710006880780380350900441d41c58260b9144068403c4001040080d514145506045070b004140740603a01100c401d443e0980414010920480c0464040300c0d80070880300b44541000e95024410b42900e400400404050b10306920802c1d9818200d0514252000543c90030420281c1c41202c0740d0f00003c600c0901d01344100e00742e603250480041e86c0d05080143c00540c4c1d100715074107101c000035202200c1a860320310b400c0d4a40b41e410f40c = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 686965503 1250 686964253 686964269
    0x1b030405190f14010e011b080a050402060408120d05180d03050414010c02030403060b0d24060b16120302090a05090a18140d0201090b01060f0e0603010b04092909090106 74
    0x107220a01da0f070f4040d003000c41000c46090090201426000d03640740d00c03a1181c0780303400002c1c2c110341c00228540c000e60403658200740060800c5240c00c0e00c0300081420301e103c45070114070380f420010783c00351100c0051040c2d42d4414222a00f51a000011142007522481012444001c15446502280c1403100280d46141104040c4000708550503c051020391030b034201d8801902d04c42d02c4c0c62110902c6092100d610140a41d10002c0c5900604207141c45101034401786007504001a07869801188017440f143c018044070300c7d41e40d8014100d6203249402c0b81107234407a219000806005012924032034031002480d0f4213840b8103d03610340055031040c0c003100045c4a103c100d1988004224503507400e1080b00c4100f00c1c4003c642c1d4068903001120034200fa826207541080c001c200e000c10f0001042040d10409602c60b2010052408410340040400000c1e082d42003a0082c41848800140070000302c80c0e148100804041440d840301c00014105401d850b80c038000d8000c26005609180010303138001390a5200310050907002e = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 686966753 1250 686965503 686965523
    0xa114309061d0c09011d0301231024050c010c05070c2103050c0f060114040f050f0601360e070c11040c02070f0e1b030405190f 56
    0xe0a5100140c14288602407800e02460b0300309500002c100710303441c89001d00e488140c0c60540314400455011841040140b841441088240c041c1e40e002c0c0600640000e00b0132034900158001c050440c100c5201800d4804220402c03041003240074800b14454072102200402e4443d01d101240d4103891900c504250451254a4030a04020b120b4201014110003401844a118280d4403054841801c2c02481ca414805449008412001030300c128000e200320300c441c0054403140021640c9407403800d0000c2e0491034141c1403844284646050038421007442140c1c0c60010f0040b41842081d55101540c0542000d040112000403a401c8402c0c0003150181c14840301001ca03844600780c01841488100750094002021444001c9103401344101380400720141c00c03103035075080c46030b00c28100030042c01030032996815400350101c001000313400c0d8400c040041c0700809440c000c505e40403280401e4040071410300c544041051051001140002401542009002c405a25064060b060800800b028103400800148107 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 686968003 1250 686966753 686966759
    0x60307170f06070f0507060209040e0a1101020d020309011b1a0903030406060f1409220605060f01020a080f0703030605061602010206070f0c0f02180c0a1143 69
    0x200041d04941500c181c0e081034680316811034003210804030400001d0014090750740070a03015401803100c0e0300004c20000f0790201d05039a90342009810f1400781c8007810000b90105140d6010322141550b1401c6101175850000c580001800c10176800c40c0106107001414000410019420310000824112400c01d0405207880701c806903480c0c4c001c5030100d51a60a000000462450181d0a80281c1e00207081d0500912401e0090054856004001c080c0b6101201d80c4a41c3e0241805409404c00e030003400042460700d8100c09002103000c220828a046500c54503480b00410640c80c196440f20b43c88d060610b80d901181d0030110090052900580d900503400541d07002005414094074a80724801e800392400d59a50080503101283d02c62480000311382034558007400500707498090804548000d050f10746c5802d0320f260b500c004280c01c0f1030180405d4000034030340e0206a0001c0340074440561600040a4025140725040720042403040340b580740541855542201442200a1000c0e807002c0c0500305603000e80d = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 686969253 1250 686968003 686968049
    0x31005150901260703030f0804050c0907020106060e030705090601050d150b0433200604030c021e0634050106090b06070c270504050303160c0b0f060307 67
    0x107618411074031410541c0e49262483d00100d2101c0849801d5104c44007224031418054a0018004200302d0b6280034003007002115a807030191803401858141c0c00001d440341045000f4101c00300880c61a0300c030740d0008204102036512200010f40c003050030310f031080c0c40e5481510920013a0154000d080c0f50000e102001084440e0060007500480d0b05140d9106c2c0c0101001416101001c0340d4800700d00c0101020062106450242c3c0c4880c026040b40400d110780f5584c0c0400c4d141c282482540e040380000c180c0c1141070154681100c0b044e44032030300410350b1200c8055038000100148501c906021801400c4c0301c0260841c402c404080c03d0241c01000600061081e034949075000340450b020704041c3d42c0c6010115421403c00c00706031000198400381d11203c1d1810810f00000701014074007080070105030350700d0300d024210b01401441d0080b03114000450301c03400c0c40b000d5940c0340315844d03c40404005084500740e0204040c05012a0010302d03070260801c503500d50310301081c1401c135240c004005501101009202c259 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 686970503 1250 686969253 686969279
    0x216080313200306040201050c07090608061602190b04060603050109050105061216050909210a0e090621030f0a020a050c1002100c0203070c03030302090102120405031005150901 78
    0xd80701d03606641c180e079180c40c03500744042d00d0446160b80540c4503a0014006500400003400c8940b9580c0c1280d44440e41e402091048c1c9403940c0290465400040c1400204650784800d11041032076070010f03042030000e89a103941004451240601910364440106050100c030340d02500185070401e0091010481c80d08109019000c20b4030014020000300101c400923400108108111050414040f140c5a00e40010810295400342402c00b060144ca0140d6908002c203120002d1410749500d14261074000004014100313120340c41c40280038210040801210380d640520f51800e503103500303040001c1c0e41035410300a484c60080c101c3e56540f414000075800300583e000103400300d00902c2403080700c08120a5009100601003090310036409039005001d07030929501d4540110152070305a03c1160308251071a22040c032072582c2540164042980000c3c01c0e692540e05112010383c0c940d09005c2c5500c0c15242002107035450301010252091199500049901843c1c4529032005000008004451558451103403003041c3c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 686971753 1250 686970503 686970541
    0x52a010903090f06230d05010e0103150213090903030b0a0906170304081c030b06030f0414010b1e0a030b270a0302060714070605040302030301090b031f02160803 71
    0x400e10541c2c1c006094555014480c0c15a8180d03580e401e00c44180c40c5050290480380340162203011001d000c45084140613116803030090500c04c845076442c2d407540c14041c00034020180c2180b000ba00402c00d00209a5044807880704884427a1000140303001c3d41d007012170080080016140d44204c640300e0005081d40e0540290080c4d03152288800003100720400c1e5150742e44180d101b000240c0d0049041d0081030f644001000400807058107010800030400d40015a5991084620002c00c4c030024040c030040c1702203292400c08a002e408001c011400e8a500083e0320a02801c900b800f506003406a844020386940384441e0003107078064164001d0781001c0084545460302078403502d241e01100e44d0307000384030040014034002c03061305900640b580f521080000c43e22000712b044800d8008608201d4500041c66521a05201d54080e5014540365410040c0e5001912040740c4c0c2c0c540b10ba03000c0552200f0380c072501c0c9804d600c00700580d5001a40c410001000c00c0f0080e00c03598000e0071700300c004002c003d0710300d024025100700 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 686973003 1250 686971753 686971757
    0x81021144905210709170105040507090b0307080d031a09090703061d1e0f06040f060902040905150906090d08010e13051c0f050304112202040f030210090602030a052a010903 76
    0x321b0310700d20380c3c0f0f1030032920100c81c003820541c0b00300b0007001840150307401010041c1c80601503c0480b0f03103e100d0303035241288200c12030300040c0c2d40b814400208a10a200d0a420780c0044031408980c1c100390102d10344e00c4200e80006401640e44034074100c0f2a117816588179560303440400996011410300000a0b141340d00403101e0101070700a0764211034900c41c02241caa44100d81c02101c0c40c03010030480c1c6070000105201c2c40c0481c0c00560303c00f41e0001107001080220003041c40a10440300c0303842e24003503081c10800040c0400d540c0307034001c402d40b60b089508141014151808070051414035910041c0c1d03900324200c1d400007d40b09010703248a08800d1401e00307040701b4400b900341d11410340408107503a0490361444100d07005420002e030018501543d00d005038040034035030000c0780001600302006503c002241e01c164071003802c2c004100810801c505046e001542c0042e500d050440910345464800307903c901c81d003900c40040220010350070003000b0380103074081200042000f15042e505c1401c80018000c00340c02500f900 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 686974253 1250 686973003 686973029
    0x1d070308120c12161b0609150c02030d0e0a141506010503070c03080613241d01051002070321081021144905210709 51
    0x140c40b03282200b194244032910040d80d4140c0d136071600102c04078051200603000c100c038410034004000c1c101e0b0300c5d44030003501a07000054102264071b0131241200205003c0001d42c0d081040d0903d0070350300032003680d80091209101181d544030100c43e050515a011100400030b03904202a5080040c0010358032300310303504050321402135031210401580e050000b1075001c000107100100c1900080d105081e074603001903010701401c0d09d0380601c8041c0025900121813455001c1202120a0074002c900f100c42c20007003808210800e000105464104120307901401400e015600c40c600d000e900030300c200000d200841c0c001c184503012802100084601c10203c0c0007000c001800c48010502d14454100d02c070b0b0440d000d4841d070100280d002c000403d50380c0c04c05142034694101d00d0b00c0d04441c40c2014044108429003c03800340d480c000030400000340c02032281c4486950500c08110900c0d000b003895203c241007002c03508005403a50f040e01c520201c8148a42c02d0700e104029150705020070b8982141c80311047d2400440400 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 686975503 1250 686974253 686974261
    0xf10020a02090702071428031209050108010308042c0c090405010e061809010209040608010203070201240b16021c020307060c0819050403020303040e0a0f0204080c01031d07030812 79
    0x280d54203011b014040f001c804d100d1601c10743d81703404d03400302d6086182c034082c02c0d4840f8249020555240d405130304c2902c186041d81d1202c12030550045445010380001d081c0b0042c40c1d410f544519541c1e00440c0296a04001d03400380d40c4280c10350104c401c5070400c4020070010320516280e002d60300b09402684416008508090020131980703144000e1a04c140c1c0f020780340b08030452031021200c0c002440036100e411195800c00c6100b40c691111b0042201410480700050b9590400400007800c40b0203c41c1c524903100d0584001144500030038011408840e40c00300280e888666021b824a00400803060081d802554801012552401c0c94102c0c0500e034000c4054520540c1c1d01d0701d0648043c1c03006413008000e08803c111428074260255a000160030700b51038240c1c01c0030348a40c003082c42d5a105412262070450050b00b001751609982c000d08404100c00c02003075061600e005148e640d6102d02c1e04181e4185902d50f03411030044d8103696500090f41c100b460444002a59034140781c101a480440301d030b110220090005 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 686976753 1250 686975503 686975507
    0x3060b03010609050a0b09063103061d010204050604060804030e09011202040b10020c010c23061801140a021605030a030603050610260703050607050901030e0f0607030b0f10020a020907 81
    0x2d103148000140010749008800c240130342e0f0702744001e1070f42245201d64030040003030400240800405144169030025945a00506120017000011036500e403903030040200340929290300c0300740c50850302d160500d0400d9440b2490169800050015241e4101c00e180c0c0001410020545610340030764025582004101500c0080c824009281940303000540d004101401c501e500c40c0a07003c400c075000311424a95121208000d02c500350710301040c0e0185134000028450030034404d4684c1c06028001c5c100801414440d1640308400c0507004100710b85041e40820500b0400181102100303031240c1c460152661444045400740042c401400140c030382d4803440e80003c03a524481d0003000305075280c1c0900007030700107941e44403003043c0604981d541c11580140c0c00001f002138000c02c485030117140181c0300c960729180108001821030f060702c142000164804000f1901180012800307030380081c124940400d0041c0c01c1c501003602e400701250201d4002600407141515564081041e00c90544200c480310750a0300d0752181 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 686978003 1250 686976753 686976757
    0x60e03010b06030c0703120905071a03011a0306010c17041a095b0804111306030510020711060f0d0203040c170a02090a060e0c090103060b03010609050a0b 68
    0x90b0070000400c0880c2c0d40d1807582c0007415480744280340900b200d41c030454410042c1d941c0c111f01124258421041808154050f0100351748401c80440c080c0c0c219850f10203062503815003144c8980310400300001003001c60344502a100742103604001c0003100b00010302c400c07441303943c86803091090003010f101000c7d111203603040455003540d50040071a0070760301c0d00025000c801010b50390701c0c2c03840c41082481c00010100c80b03046494404d039603400e0381c2c0e460b495030b81782650415106070b8400c0c2003000c00410400000c440e110030340403034401595200c0c008070700d40b07200000410407504054642d01c94140f507409469083e40003000290f00c500c038000d00100b0f20b40107004041c0035003039400382d20b140207020b12460142e2903800303598007500400f1007030300059844001079045d200d981c40742040c5030032140c1b0800550030452487c0390420981c1c03404000492819030030131010613020300190098640041c80e03a08c1030703110390443d1014002a19106a481d40e5400002e0684104c07445024062181000002807000440d02 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 686979253 1250 686978003 686978021
    0x1150302071502030901061d060102010b011e080705040b0705010209030c030f030f07060902060d0b03120c070302091806090601090e030301030f080d1409030d06050d0f0b070e04090c060e0301 84
    0xd2071698624180c020300c2c01030b402c0144103241c60b41d652075002842115a03d03090490413509039a0003403904004000a0940f00a0009503042c0505c514040c20f4680301d5605400040e03615141109443d01c03449021256442150f002c42143c200100e00a400d0005c107500610048808404484040e030a0105141d02c44150000b1081c0c83e8000b03200041c0141108001090000d01c984c000040f030200c907900083c00c5070044030766221890755038043c05805040030004050130102c0400e00c1420b01d119011980d5903070351701d400024010000080070680c145203040b001d000034008401a90000d180c5111034590300d00d4240718840c2410f0900c1d000000d82e84006c41102e042e00d41112518101134015120101542d01510310030390459034440010f0951940302400f42d010754014000340d5682c1042284d01c000740e40d1182c0025100c3c010a0300c08100141140c4d4902d0795040e0b001181400d980d403020010b6401c1900050555005402c1240207020003c02d030011400383c9200b074841d00c0790f03521030409040c00c070341601c1c4c = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 686980503 1250 686979253 686979263
    0xe150405011d310f060c170a091406040b071707091517010602070501090e160e060c01050709182c030c01090803060a08031602041d150115030207 64
    0x8000c5011600041d1204981040c50b0410420107003800081e1a4192602c010a0704c2d100002c0351207000f0404603006242e81c02c5405e180038070a0210301d42954155281c050b1640d01d03041da46005d03007003c00c80c0003a41d60700c0411141080d48e580b803034213040c00102c0f40e9048648900080c680743d0f0038030762407088100f024055542ca42e80e030050142004011450f03403482003500c030706020b504543c001d2036040c0c2446540c0070300099400b606a10f03107004005082c90602d5004500300b40b400d1410400d262400f55000c0c0741c0b050325841c2041075100d088000c10414402d0454001007542030100f0000c0b8550480002d0702100c1703008800000008070b07210752404036040c001d51180e80a00e00d0300e06050040381203a0320302e0340390821000d070785c60039074000a900d084581c1c1c40d0381210698400300412440c2d1404c0b4080c0d070020705248000d54602045001c2560501c0e1126030003c0c4219501c070a091545d903584082010214203213000c540c01c11800d902d01c0c40c110071007407080480e8514403240101c4460700c240241c4d04110703801 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 686981753 1250 686980503 686980559
    0x60a05030a180605150f10120906061208120a0501060f080901060f0e01050a0504020702012c060f1315020d11190804060212120103080901090e15040501 67
    0x760309100080d10505025107502c121204078903000c941c8a218050240100c414070b04101402403040c80034040215040c2441100c00141d200300c000d82100111340409516480000c9040f02450603030002c1c4429002080d00200200c012020401040000c00604500006030300c883c1d91501301403810780310240661400500c03d002c42d2001c00d4080d511443c3c00c040740800104841c0d4031a042943c410403da80140314030801040104500c0c20001e141d20301a1006403410342c600607040e00040d103034061400644084070910600c0d100600e403d08040c100301c3d0030050020f0307179030044070084450640150000d030961050f010b1000845c18410b411462102c44150040c0000c81d0f0720800940f085030001c0a5034009008081107004552140094510124803a003203541e1100c0c1095002032902ca00d29147d00c081d000e080001c444414011042103044903404091956a464082d004a070f400da482d5001c242a4015842480120f19039071808118540c001d031402c010f281e0381c0d0045020818260550304801c4540 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 686983003 1250 686981753 686981761
    0x150603050a050408090d030c061802090f04080a260406020403110a080d1209050106271107020d020d060501090203150d0206030406050601020a0f080a1710050919090501020d0605060a0503 82
    0x42011403400c1e074000d02342440401d0854540c2000c0c2c5541070140006000f41d41140c0046142c03201c41e0541001c80100051220b10b856a01e2417039903c50100a101404040810200b0183c140c11071060f41502204036401542000d19110020307400500003150403401d40f150401c0541020103600c0b007254800401803005503d1034206464294080014800d010749a503030140103e6000d0107150014100072402d841d20180d99000305000008442e074a540613400e2030321071105080000c0544200303503011113440308501e600b440014413800c03040c0801802142040c00018101100354080e501c2491101c44440761000e1550420030200d07403455000354800002c0c0042408180a43c0c029948002c040c0101d411602e050b4035800303c51400703803070100c0b846a030000320314000b59803024240a04a03c00340d81b03d02070f400c04c0040b00003150407034001c40303001c0c03608000000e8440c82810441500c6020a10b010404c41080d41801c0e8041d52291020503031583c10103e00103428140382c4200c500b500f40c980d541c4d5007183c031 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 686984253 1250 686983003 686983009
    0x9050c13020c24061c0b06010519030501060e0102190602030a06030b0c070c0e01030302031b030d0603030215100501080a051302060c030d0b2202030603030c01150603050a05040809 79
    0x2144680300595080c48007410700c400411003140c1084440414580c1c141e604400c1404141c80100102d002e140400035104801c101390b80e01e2511103500543c503607680d50340d005c01281c0c1d901503140080e003000290000240e60380d0301a48414160f031965600c2200040c0040700690351904510b00304841c04242608060200c0d05a2703000d90f80040002d031000c201f459498031500011101610a4040308000103805030400070b800c0c4914000f800a050841a550b00d1030310003a4903801100c034500440102c0021400400710103100f158101d60341004208403c036180e0a00a543c1c0601c6010201017440303e0003c20a418420343d05481101d1050355038090703a42c2c45405c100d01501002e0014034407152480a031600594900e8050006007445000454039098560009015103803400e1070a4054450807011000c0c800b040341c005204600843c902503aa034440d940481e2a5200c1c00b80e041880394a400c07807034161071341403003080310886000d40d030207114985941001004440d425140140020010080902030341 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 686985503 1250 686984253 686984269
    0xf12020d080403230601051503040c0906060918060f1208090a0308030a0b0406030201050307111203090114251407021201151a030a0504021215010509060409050c 71
    0x244050911a0005116652840c2580080c0c00c1121001520f080600007600003028018440848900600d0654980000b090b401036168a609520b03002c000000740c03d0100f4403001c2402808015030400c802590380800524001c0c05000d240030602c44001421849440382c043c000c296901401c080304c000d490240704a0450002c0a800c46078520240804012641d4054901c0d00450040030181d07501e192445801c8103e9040f1041c7d2846145080320520251b68018180c81e40a541810501c60080700e04403003c2c600868a000711001c03e10000800c905d0000c19080104180f40c5042210b1981d01c480250081d030f00303d20400c002090441156210301a8810020701c1d40f86682d0382c030707203030715001c0c440e004540e6406000c40072441980d1a0208001c0040300d502c0c060b0010b0030310319080c4a0030307200c100c000e180c148405031010f400e0a0302c40d40444c066542d0405a2000555078070121a0b01c5c0b40c0400104d03155030001d1103018840c002d040002522410907001d41755a02d64014060300403444100200300d03401d = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 686986753 1250 686985503 686985539
    0x4120c0c081501030606090e0705040e0f070311090f0108030a081b0a0c050601080a080304060b03010e100501080d0f05031f080a0309030c06090e04030c17031e09070f 73
    0x32200480c000256400140911101ca4900d00b442565070360660070000180c0341280c0c4418411072510841109211001c40c585040d80c6080300c000c40c1c0e8004c00114546070030070040344079586004c0e4080c000708101023021404008e001c1910612820794440c0510781002c0c8007442032000b030b90010802c5208030340c8584c0c8465031004200c02112058070340c5012b00079031070b0000750116012a002c1c0348568140481007284070b004001c12002071030420b80c4c95641240034007004c0d00041500d5184d8080c0c034941d590a420440d07a04403070008580707c2450501003800500000e11404140f4000c001a00101e18810050b80c17103e0415926283d2864a8203450a000009440c2c0000d902d412a81c4020581d020b003400076402c04da00a564884c0788074154108201950050380c848800d01c00c4403c41040f140003080f402a0b030007030b014208950f110500c5d003800b0880507000120725868280000c10080c4501c1e50020b007412402c101c500b01c504a59480510a5551245015030315030710b182188100000c1103c08250a21 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 686988003 1250 686986753 686986763
    0xa0302130b031509030703080f0121020303120727061d0409150c09150e1002070b040306020d05131e170f0901021618050703090f0b06120604120c 64
    0x81c5014072400700821400d1314410010741000030184149540a00c21b682c00c1925070465542c507503d03017072240d20588110551207a41c8009010010150b507405d009545010b40401410202d603c0d2030b1000808402e1003d0b8071000d00307138041030551602c010035646901078905540700d018035421003140030b022000c030700d420541d881030b150320307200d000030303982c044011074082103044040703085145c2d04000741c0600040e0300300c0144c030b9601c22045007401e94810000860a003041d1688011811064022403c00c0c219412000c10084009400400c104a82d40282040d07505c0100401c00f0343c03a030301e020101e070344010640508050680300003013280742c40b100f8504c02410300c1481c01880b03031480b11108120917086081003400c401c8004c1180c1080356010720040c50404c42080d6001c170f1150815110947c0349480d81d0166011617031f95000280880d000b03500045115801c01300f0b40600403c9460b0100d41c010081b1440d5004039041104401301200c0000c040340540e80c8202e2103c03882681341422103502c0a101d009843c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 686989253 1250 686988003 686988013
    0xf12030801170f0706080a06060c0b0c0703120606020a0b06060315220905010c0e03030708040603021606021b100e0c04050a090b0a091b0b090d0c2c060a0302130b03 72
    0x40c0f4100201301c50310003800035488001507032400b0035181007141c1d0240d01880c148580366055500064441da103856100030903001e503946402160400700c4100690400000d03955141c060040346c40d5070006104903086d4815219168165508000d004a0340410f8910400b1229000d8a080892070100014100c03941c190540c504800c20b510080300c00c0e211900c00656090755074500101c10b040c1c4c0040c981034070500035402036161480950710040356104601c50001059800306072000180351003c0d2500d9031580000055480700114606050351700d0740300046000c070703104840d03030010850940d020f20182c108040c0c001d0300300650200b046c440944001004000c105a0307e8800b07100042c0440207203030085d40c40c1000042ca140280c90030040c24081c0c0c080c6400c4451072942c080154005500441d02064002e40380700113880002d20b044402e0103e150003aa01c1d1031941100104070020018841c507007696034001291807611502c0c28080240d040d4003010790040442d5801210411080c0c00c410082e05014084038 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 686990503 1250 686989253 686989273
    0x30e01030b060a03050105120316061a0a09020a0206090601061b0c051f0e01140a03090c0302040515010e060405010c0b070c061d1005311203060f1203080117 69
    0x60000c0e40180c02a03c0480d545500500982c10040780e89043c1d0f11822004500c2c01d17008441c0c101680c4800240142195182c483c0d5140344c81d03ca11410103c83e10140c10845d10316182d0507000042d4001e600000c00510a01d40000e60300340001460354101c031032645420007440000c403900740b025000a00165001e40d40c10701d0001e04c584a290303e99070098451025000007000518000b0418030150042c0d0b81002000a006501d0000f5402151034210345401d00280d8071000e8500003105031034961004c5c0d4454548000c01150b031420f045003028010099840c8021401e00d0700030000f071400340d4024540043d19250358000020000e0701c1450300500c15040601a6450f29903907002a551004408850150440e24202611204000f071030150230f401b003010300c8280351104000ca00a08c03c5080d9420140d41c0c07494100c500e0f078100e02c003001104c1e00b1181e81420104000400b50150249201d41030002d19004800200340b54660aa01c00855051707641e44640c0e440c01000140e01e005480d940d48460181441f40 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 686991753 1250 686990503 686990509
    0x80601121103100609080303010302010503010e07230901030e060c12070912030c020a05090610050901140414010801080d0f030228080f010b07030516060e16080d0516030e01030b 78
    0x780d03203d9184000800720440c24804018403100c11035000c040d0a510500045c40103170303005030503a81034401d5451103080130b503101c460850b00000c450480580c0401ca28001c54a1510b428000b04036140080e2424040e0021150090b581c1da10b04550035816070000340301124188803a6544190402c1c00c81c43d00744459a00c44400c041d002d80801c030214045004011400c0850034070440038002040101c03401c044902e0030201203143d071002c0c2da1505041040000d5020000d038011001e41950404040300d80c2d40340d0f5212540844594031101031140440d081200001d0003420004804e400403840765500142c0c3d040c42c2c0c44c250701941000051301d015450244d0055030080702c2d031568011907c80c07552080030314241800031192418040c0c111080c0c0c2c0404000040129030044219a0700d2855000300302e40101c5c0d103042120040800c0303440701d90140596059600c620340f0381100380c410341e090401a80c1036511840c409503540d2140011591640819002c00d001080c0902d10115001a040c1404201005c0f03035000 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 686993003 1250 686991753 686991757
    0x905071502030403231c031d03090a080c010f0810030204051501030609020a021534030f021206010809010603050f0a030e0607030c0b09161409070f0806011211 70
    0x14200140d20200f401c00a000e00c5111880b20b082c011180f0580545c0816002a1185001403200f1300890040d40c810500a10a60001008180015031016181e000c038170120745130f5020175100b51007011166004603c8200105900031542ca0503102c0100b00780c4004070581e603c105c010084410898860710020158a5501072188a20000c58084140c00010000541103d960b50424230005105002000d00c150f000555001800e0000440300c0c02c41e0b8400303547c0d542e4400c8511840450409420000301c1d001c0041c0c4d107049404503107480500980c070024090000700e00558010710309492900000c03c0080d4001d403a0503401520740800811016166151a480e000c5015840704081c0d00c10803541052690006000b00313103000403254580f40c030000d910010400e24000001804010540010841c03011040040481d000400d071819502a1341e00c1e451010109042155540160300d1724001030403141c4103807071000c00c0c4800c0d515108569151078004403107414011240c50803580e81e50810b0155100c9440c0 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 686994253 1250 686993003 686993039
    0xc080303100303030c0905330a020102040302032521050f0c01020c04021c020a020f0a030e040f0e060f10030c0f1a130308090a1d010e0622090507 64
    0x42060000c519503e0001e0494400003010001c020780032200b402207555441031034005c4102074044407040030180460640c00c804d80f0410751041d180000b00c0d4045030340c041d0003901c1224000c038162122140d5414090310540e1034000044d039001d040038403d0114030480c480480b0710030b41c2d00c1d080f420b00130700c3c5a030f80515041754071002c400c166010700070301c902c150b9040000100c02c5805440175401d200048611580e0007450043c0164010f402040b000c400700d1080100412016080c02190416115400c02901502e004110107014600703000c91044003580d80e0180784010541d0301c00501c919a601a007060009401500807000c1202c1f500c2c0c00804207060300d510030003a103090000300d1601031400340e81464805108035a0200b510b014030140c51502c00e001401c50489070048000d540d02c441c810700250989007150411501c403203030211040300c58142440303024140c4071000011111350f02c5010401074001e22400a4026580412078070006902031a000124528428011a100d50b51a8070410101d03860081e = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 686995503 1250 686994253 686994271
    0x30a0504110102030a0507170909070807090f0803030f07210218010c02090c1e0d0e070918170708031905060f011715030102030106170c03220c080303 66
    0x1014441880079040300540ca12000b40011032030310a43c0b07100917110740034142c2c015000b885ea8041d124000c6031130000b01e9130a03d100070054203051a240b003001d080024155021000261029030115822030700300d0461040d2100c0400441c04e40c4e54440c201444900c00401c0d1004006440c213800c3d03039060865020b50056131000b5009a1910740300d00c0e2174046500100209410030041d041c0355801360300c483c005150405d484940d19540ca0025410a44020360208982c034581040090031300f9260203113a12100144400b4030596025642d2a410030064400c0b00c00c0140c00820a0300ca80380000b041c111a014452061920003030510b2030343e8456614640044400004270108084a803890500170310401c0da00c14011140809803107017040000f02000440144600495421030106e654803002030000404500c00130007d40d602d6131208002003800c4581c4841e000d02421030030104141b500d80c41c080c1e80c400c2c1100310300800840e60743c1c0180c680141d104501620f50f91070a020101c1c80060600085101d00120 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 686996753 1250 686995503 686995511
    0x80901030f0e010e2401030f080c060f041e05060114040905121b010903200a0b0c090a09020412020d02061303060203150306062805191a070510090314030a 68
    0xc82081e00f01170301d101c018100c120f078450792000c48030105409241503a410520704d5603803603c0383c0f820740518424000c20811510a85040020602035003a159210f1407054104c40c421241f0120f010100e0381402c540100160405c1005010503d402d140d1010304510081012641410644030503082251a40d10136500041c001000203070040001c1e040700c9000c101400801c03881869440042640041c041c0c04103405100c180d0460341181c1c10845000201e0304008014400d0070b080502e481541d2000c0060741c043c140800c000107550b0090710a43e421105020f66078408410f041d0b0030058060100441260b10200034044051205807400301000a1481110016a2404d0440c1c120080120342490346109a00410400c6000d4503003210000210820030020362602490b0f190f41c0025448a80080780c04c008544241d0011601e218070b00012120203080c5440c10341c0d403d5245403014400d00f6400b81c055801008a02c510b00350301d40c4140c50080c02440c3c071004d810798000441c5925802604e03a0005070351a = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 686998003 1250 686996753 686996771
    0xc060c180b1902071d0a06150201050403184a07020712021e061902030d05090d020d050a052b0e0c0a0306052208040618050d080901030f0e01 62
    0xd281d07010b2041c1e8280010f1010705e262032990303100b11803010030803806054080301041001c1e4503a0003a00142446a03000e00105418010081c001c01044600ba0006210030b030b005d0348086502c500150075200901404440032626404070300760b1110301c089071144a46810001c455501c65015001e0000000c0c3d01859603e040a410080c640101074125114550920f4180001030340c81c0803140d20406114410004d403596514002041c5000f4010402030705a5000b041100e02580480100001c14022900300050f03200c1e01034469071001814950800759002d0591560100c0c05440600070302016450203602d00320b05442c40342c0d07030040101d509038150300907002070f4600c2090a0068200c20070300d803801031143c1400040081d0070099184409088a070303803800070030041d035402081200302040b180001c0110102625043d41179605c18840c01c4001250181d4403808034111040b00c0e012220000d050080e19130301a150702da002d61144041c02d051581d08e2410300304200c46805050b0458010800008281403 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 686999253 1250 686998003 686998027
    0x90a05030a090e07051908060112020c0102070b090d0e220c0807030c020f19020a050603040c030210050426010b0d060617120d020310030b0103150b0603070c060c180b 73
    0x10090301c140140141805183c0302c40c0c540101b801004082c0f071a20345002c0d113456006803074000c01c9020b0710000c140002000451400c1c1500148280c5200d0700620209030b654444264441c0e2560101a00040d10369004804501e00100241942003c08040000d44004011a08111101c2c80c08400224202208200310643c061185180112542c005068901294452241c036807180e240c1008030701c8185903110056407510340d02c0b4806000b000c0d0010b992424141402080c101c901d1100b24404d54802c1070001c41e00e13114030103a4040b42e00c250700c82884140110708509006203d9282d0480c15035840ca0501c0c0540d4031103a45818039030140300c0000340c803401c1c291107519011138000141d44030b900590a030105070041c58100d03200c0a00040f130058a0b0380700c0c04070500c1c14600039803024050400d002c0004c070a000014211585241407890f080018100101c144401030004541401c08200c00b1003042003c1902c940044072290040d1906c030045050b030700036440406e8039503003150000c07510104004403140 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 687000503 1250 686999253 686999279
    0x5040f02281206170c12030d0b2b060b0f0a090f110a020309100e0f0906121f05070207180f180506041209050303040509090a05030a09 59
    0x245810154508203040108840041d000c1e1400c405002004a608124900c105424401d0740110b0106020066940440c0c610b44002445040003a0103604071596480c0742c0203900401c4058102c020354103100d003a0940c2002866030b000d200d0740100c2d20014541111007104030140d503417200d500161104c0041030400b44120b64124625602403010000c6a00c0b507940c50f14210011503180d01c1000c81c191044002c803901a03c0c90b40b14a0300c1d20341c0c02299200742540c0100140000030010380365509030300300090045441003541444d007500a1000c0050f0481410030740d1384950b010301c0107000c0c071581400c24038031540703094440e05808429418503009007030b070312081d40a0290407008520040250a0910781001100c20022403d07001e00c1c0e60320b155240700c40e80b964010b1450250f400d050100c00d075a2609109403a000d04880c101d601184004140c01018010b890b0201035a4029006508040c01c010501144ac0340c080d101141c02d01c01c101c9442d00060040009140103c459a1814401c2c0d14050200c4100 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 687001753 1250 687000503 687000521
    0x60c080c0a050409090c091b1409010c0204020a0e060d06090506030304050f010507050c09040b0a180c170309040216050709050f24040c02061b090604030209100b0a02070504 76
    0x38610401030109a96031090684080d10f0f4401c000141c030b0342661801d00c03000d06d410b43c4018000350422031214100da420940c01240640c00b511500d000c11a03a0652810030f110319007945000c070340701135a504054102179006e420920524107003c41c11461050008025402000e800b003545078071400b051080a170607005007500300703d007600210300b030a090100041c80d1400c8002c1290400a002c0f640c4014090708210080c00040c0181c420040f42c1405c3c00c0001d01d4500840d11843c0983c2446002e04283c00c001c13218600a80d0040300310b504007404c0445117680000303001b0401d070441c401803200441c030360303584c0c2b0041c9044170240c04200280c858a180190402015900c1200203505d000304004410034419a0264041d003981904040425030040001a40e403d143d81d040e0000d240000000207e2707000600a8003d1132420307a83e034100e0f1078500450000703210381411a50071a40a220400060820f21801c5030444800710a034400213444141074409070b0040c992440069000344c17801c12060610b8401c685c0c003 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 687003003 1250 687001753 687001771
    0x41211150a0c0e0312032d04060501170a0b0a0605040501080109020a0b0336100c021b0a090e01020913020706060e040807020f011413050f06031b0a1b060c08 69
    0x4040030340c400180d250405c0e00ca144003240390010004000400e61048442000b0020b40703400c000310107034461040b01460850342150101c3c0f812001140d00c1101900108000359420001d0550300301c0780c1d540741c2803000068060114243c0b990000b1034655100d016080c003911b0041e00003e0000e1540c010085850619801410b03441010030900504030040c0009a109140400c521a8812102c055031228840c803945d00344190f0080c5807224401c1d0340e16801c0000140380c96400c40b60741440070030391102001c0342225007650180034180104603e00e01ea03042083c540c1c00d4100018100240d4401044a00012180e6003501c154001003003420803400e84541c6c0c01502e0203020b0311456240564403684a03101e0054042c0c89030724201841c80301a8030540483d0710481a101c0c1c25500c414044203004114012801018814103070703010880341a041400c21389103e500105200408108a4403040d0b02640c040e0201c0c108008521900c90314040e129041d0640c1c3c280b040d00001089800110700900750702001e021804 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 687004253 1250 687003003 687003017
    0x60604112706120712060501030c0f0e12030f0a0f18060c2d0b0f04020303030105090403020f0d050301061b0305250c0303030b18010e041211150a0c 65
    0x2103800e1a10010002680d00c480c0c1c000082030080300048241c0038a040c600c400108410400c030340a640481c5100c0202c101d0301081c00410388601c019015607000701c4061000030301c0c080030300318034600c99207201252000c090f0050040080e00f00c501030035a80442e58000b02c064001a26540c05a800551841440702d503103400c007015a00740c3c15075141282c240c4540410003000d45000001d10010381c61440031303040c4074170310aa01e6031210907000da843e40380248180c8a00144130001454034003407100140c03180e54006d001e5807842e82440200500714401500c250300310702c103013084808034a4003046002038001541d1292034803036150490040c41840e0301c544840000500040c154002500807003a61040c01c509a90308100017641146140c07500c100601c09444000701d004004103141e0541e0040803901402e03904071026200700d07140c449040100f1f126070b0048400e110000bc010640785250340d12014024509145c0030001d038580c1618050340340d8400200900d0607810700203003a407e40300f200c0011560b424095 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 687005503 1250 687004253 687004267
    0x150807080c10090803030103150e1f0c0309170a21291302181302070219120305070218040311063d1d0703150e160207050a0806060411 59
    0x2503100c2c041032100804a290360050841103900340e81008680351220811500300502f000640d0310320200c0680440320283c640820355555501c42d00510720b0007604404540b00e00c0422860051460b486000d2031030070000c406880031020b0340190f0001240e0503281c0c2001c5180c04a500d604000ca000000c40c2c1c484495400c0621102d035214018042081421503c00607160f104d0940714900f2801da83e042550700000c2900740d001d015000781d02400d5018006c0e55542c841018201d04504034402a000e10240b8200114025001070320402c0186144e52026041071400c143c0808107610040d420b82e0201d01080032200c0e03a141d050410001d240e030054000c242854100c02500003811941f4078010001c3d00c07a1040035801214400b80b0b8107200042071490540f061054003440d01c580740742003d85400d4006400c1c1521403503403651100c2c9203400e80b590345030070032141e84646c500704030000c8200351b1800a6024107480041c440d80c0d040700c0308008240302800b40c802881e0610401003107407606100b83c00401001d1100b0 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 687006753 1250 687005503 687005519
    0x60c13180f1b2712050609010605010905011e05040b03180d030209010e040b0d05070806100501020304140f0117092d1f0e01020a030f0b010819150807080c1009 70
    0x286511100ea6000f204010034100c10302e400300442908072a6031084005120401c01c82c00003841e511559a480080000c0c549500c011194508a0301c50b0303500268030400f04001014880d02c94000340706040c244285450354515164071560400c59280305140d01480e4451103c4009209419466035986801c524101d4880c0c00a09280300880b00d09014035900d40f400c514a07241e041ca21841181c00c50111200700e6030369200300365119012101c034822000f842400007a194000030680d81541d40c00800c52800c1c40740c48007030000036401d11050504100c3c415150011aa081704250b03801601c00354041c00b0042003414110700c090080b40d461201008081e1441101ea84010403000ca40d65946461200d4a5190000c01d02c05803001e02c04003882c3d54030006000c0d1019230136034000011041079403028400b40810400540f0f06080c00c46401d150107280001c100f03150700310356005601500382c40b0b006400103902c0342c945503d003c40c6078201e150140e0044050120905d8109210031700510103103441d83c0032504000503 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 687008003 1250 687006753 687006767
    0x1021606140702010903150c02150603030301062a11010201150509010512030c010c0e010e0915240309060604110408030702210609060a0c11060c13180f1b 68
    0x30300052801c010440c803086a10440c01000259007041d15000c8419007c90b4403401491201c0c41c9402500c82c0e003a0030690030307802910712442410b00170040c504680c64040c5c159491510b010440303550a08d1031110546035140910100324450041324042040c035903080000e4211440002030440c035502c604810000c2e66140c00459041d110191440406222100e80452035070103420107101040d403c0400840342d650b4403c0450750441000d90f00d89800c00070710300074080fa80c501522028040000750403005074a04000490000150740940390001340000c3c85110150764000780c9001001e07400c0300c802d00c0014642070003100700d903c2901c00101d01d0146820300c10713a50f91040240c0203010b07202d40781e02c0d4000841c907041c0402c1c4000b00c5a0542d001850203415031074030b8207000c80e9075181044c80c213034091039900e114480045940c00c0c050018821a110303008101c120350000354140300c10012440c0082200003c451075183e041d1514034011070202d8401d9286020344581010807000800c0b01d009210180c4c2e800a9 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 687009253 1250 687008003 687008027
    0xc0908070b0d06030b0112120512070806010e030a0308100504290a0e15030f030c0a020105070213150812031b0705010f061d0105040903050913020910030b01021606 72
    0x22455a42c01038030450030041c03c07241d0700143ca089030010002507050b00492100340c01e41d00c1900910500c9030030000075a81401508400c2501d41030320800201c1941c0110307681900101c050410150602546002a2502545000841c000303000102808075181ba07040000c40a00011902880342d001c801854281850011400c0c20010315a05003412054445140c1070f405040c1d02074108400b8a410825860b0541d40001e1550080c410b14481c42c109280220698402d20f00d0032000c2c2040e65000d80044a068020301c4040e40c0c00022008006a01400c030f00c1544110810120080817031031074861040d04000b114118403040003030400c2042400e81522031314040d0356031070f03292898a41d2001d0070414010440c040758074034014074051010030b141242e400c4921844ca4512400c0b262070385c980d07045c8010f5030415200140490300c107000380e0140d482c21000c0e0196810070404018145409440040c2e4805ca54024034070120383e0310404000107503418000710603c20f465448150030146408001444c81d80521 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 687010503 1250 687009253 687009269
    0x50715060801021602090708011809110406060c0309060203070507091a0a1e1406181212070b070305150f060c01110c06070c05100c030908120a0c090807 67
    0x8850592a0140e80c004000350182000841d181e1000e050038032207451000109a00c02c0310064001981d9078424141d06040e1812210703402c070b800d08240ca1131400b506e01444115520a000720345000c0d603803114443c1c8030050000c1d6540b000540440d0602806100654001004540007000b460340411300c0050110100c0c0d006a1000540c8012440581035202d4002311081e40207000110000f188000b4040300541302034840d024841042d692040110321982004046d50482418070802440315580303001204030010207010004003141c0d40d01c5007402c0c01c1d407204401d50f80c0240412801c00340100e6158440d81301140381410411810030700244000d44420384c400c036118114115088285440e41003d8428204520300240103000414410020a8105460012b4144160070002e0001c07031080400d038100b04c0d008406444071440811050028200101c0e8090615484988a03c0007880d048010030003021040e041e86440d00382076007980292504501480300b01700c0b28030414030480300007044580890340c0d41 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 687011753 1250 687010503 687010523
    0x20f180123130c030e03070c030b040f020307060302030a2318071a03060f0105070222020f0c0109030908070510081005060309250e0c0c0f01050a020c120702010507 72
    0x4031a05010020440100d90340215482c0071144074075203107400001481c0e07800c0c2c405118030a00e846846940e07009511010301443c645960030030104d4195a070f440e070013500903180d803e0100e145402092400070070758030610000f07a002082102c400d5892043d15481e0000e222100c0e06094100c2c005d20f405680034100c0d100314525100d80003211403080011000901001440d04a10030306090358115070f42003100e03000c3c051000c2211b440c0e110b6110713400b202e44582d0700810451a0700c400d0032140c0349104024078212203c0d642006450b03a280c16800c042c2c20541c0358503002084803e85450014803469071075010809540c40220180040e5842d1400d590014406180101e0b81d0b6407883d0b04000406d4a552001d600071400009200d20f40c00c002c1582600701c682c3d019480b280c400400c45803503103030031144035541425500b040458901403070117000b000c0c10001c0000312941003030a114620300312601568602c43c641d500188442c0010810300c044107940505034019400c0c00341940019029118401c4020808405 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 687013003 1250 687011753 687011789
    0x1b010b0f0d032006090a0c09020f041206060e01030c180b0108070e010527030706081b0a051c0b0307091a040b01090e0a02030a270605060f1804020f1801 67
    0x8511401d400503100303600b244c640341001c0d0103080c0c0322503014809540d200c4592001040d9949076008440400180780d01e036a00e0280350100481c2071840c541c40403140d4640b28800010003148504006001c3c5018030404c0d03400c240341003c00c100c0000c0208e0110186414544200d00c683c1e0003038103190340003900b400c282d1032142e040c4004844901c00c190401c1134060718101c00404d00c100c407074070304124148160104c0321038a032106400d58045004445c0041c0e07a402d84800d2308140030100c0081c0c030f01d1038000c5c18051b00308240070905020750910b0010003a1540d5984050307400074901004614020441c4481c20010070b410f440c40c014184d8941d1032054003968803015007c2069100324001c100408042c0f6160344c0c60704203c2e04140c0030713503c203460b101c10381403d00d0f0a190b4400d200f1103541000c1d602c4614119010341d500d565a00113004001c24140d44007001d814070121a4840c40c00c00841810b50000c02e100602c0e152040100c8190140c900c60700444000204441b2441382c043d8040c1900e403041c2100c030120366 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 687014253 1250 687013003 687013037
    0x210f020402161b0911031308070231110a12051312080a0b010f0503130309090c0215010e130f0501020417011401080609070b0c030c031b010b0f0d03 65
    0xa03a02c1c4004110400c1448480d182c3d80120010100703440c9180401c1c0151181e0035a0441d050009540c20003481c8080da9030b001c00544200010301c01d051007d8810501c03810240b071507100c40c80704c031a07810b0301040d01501400d03d120082d106455401404204260606231050001801c100d640303075002078950364600c0803501c4801e0a4200c0300c01c59900916000d036a011114004200700c9054803101d0115091120078a519030040c6182514042a03940d120f013141c0c0c4141e8102d0b48032458000039803d2007038080020035850034502548180c1b007800c1c2c0007071003c15580060004d840b00164400544400301900344401580c503e19580d010751740110b041041c1d0912410400d0083c4200e0380303e0002140941e000404c1c100301900201c403580e0f03e01d5151102aa61506910b46a400c101c0300220590005101403020034406000341c585044a01d04603420448034243d22807840e4024100140c245030f1040302000c20610900a1034280304047c0e030019040b005c1000030039041402d0010040c02d121580f1443d504080e = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 687015503 1250 687014253 687014287
    0xf0d180e040f0f050706030b09010e0a09030e0a0b0714030f03060d05070503010f09020f0406080c06160210030e0f0304120206090402160623090c121e0106210f020402 73
    0x143c0154150003a54180c0c1380c280d603100701d14800c84021074280100e55101703107071080c0c01c2412036401028180503a034444000c00028203840720b044040c009088c507a1500c5803038004070b0002400310440d00ca41e0750320213800d00c825412000710ba18506a4000c0002c01e80c3d1200c0001541d0f004002034511b00c0c07980a15180103401c101c41900075035050342c41d03c0c010040794001c0380c004444482c0242c405214401c826001d010940c1c515018103a036a61103681c00c02e00b04d0906a00404c10003200c140d8060450045900054a0311811107110717002036141c08018045000a0003111101c4d815000158030b01468241d40781d003108c41000010b4458040810030784081d4440b60103c82490720510218045a00c5c00d241c40b00040603010700c001d03030240700c2245c0390891181601c05540950b06803401040b40b84a5a02084031611044441c0e00d038038090792040e60001c103980b2003d1203c1060050012030540e05000b00c114061403021054542c00e000c2c1c800c0c1002040d64200a0308103960161000359032070360748084a00141c = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 687016753 1250 687015503 687015533
    0x507050121051f0501020a020d030e06040b0d02070308090f0a020105030415051905090c09010e04020402041503091a190b03010e07090219030506031002070218090f0d180e04 76
    0x280d0b0820081121012030703e4458902089048803000d000b984800049030340b40a0000025080201107107100e000c24002c040c00120010700505480c81c040d110882060741d50801408820f0468010518004054001207681c1e0700c41d0109000745000c900305d000341d0350348110720340004e4184003000000c5814408035101136034441c01d0514083c802402d042c00000e03c17595903041d2150000c0e10f8100072540401c40030640d400d0000c401440b0b04a20790130212220400c09003c0c1003260b016030700300400105101c0c10054800d4001c450748000030200c840d41420301000c003040c4190541d440e030701000c0210711030901110b402c50018041000550b441ba1a000c60300401c4004014900b0340b1580d07200107201c401700c0d001080b1030307a00c040500c050060045c2e070540031344805440e4290305030465107801104102035401341980c10700040541001186440c001c0c4503600c030a8500c916207402c00c1400190412080280c41c1c0c00802c60321b09581d905040c05030640802c4814005c0125942c82c400224042c0107a0700200c1240b = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 687018003 1250 687016753 687016817
    0xf082b0c0303050a3909060e0f04180c1e0b03180f120c100902030c090a0b0d080901110616350702070f05011b0305130b03060f0d05070501 61
    0x626400780c2d41c001c0c00304914050114460700a203005c1d110503105035080380c01c8640c25101c174a155080d00e010841c882c503a18041e00d801942d1040800c0b9070800f0341c0d00108a1500450800070410704003540e0100c4e002a46584002d0035000300c3c410000b61909a08036584460826124041c00444001413802d080c1c500e41418854812140f2600041880d0710060000c4540b440444000420200d01311040d600a000080d505030003a114159a03070500c045525030101d00180000b402c0240c1c2c00010304070010785082a5440807012034089410b582180c0103185141d01d881c010b20702854031141c84e4800701100c202030010068001004582d06910b1469000c100f07100310003810080441c0044440506411170b81240103100f40540007940c7d0b103a6a10141c04d452042c5d40380300844141c10031800429403804007c50800100f005286106103c0411000280c210000440c3d40c07420100c0421410f12084e6007140e10a100b0491030f8400190009803083c1116400c0c00d250080d116045004007100d580d440410b40 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 687019253 1250 687018003 687018041
    0x3120509060d0f181b05090919050f01020d09140a150c0c06020c010b030601050a0b03040b07121d010f0b060d1107120e10050c1509070f082b0c0303050a 67
    0x1004130aa00c109031701089240b40e1600300b0307540e60030424004001d56104815400460741d20103503030880301c1c0782d101c1140107404075240c2042c0d0101450886c0e0002001c1100e40d0fa403107030424200b040031849113103591441001001504040d0b2514990101041210b0105541e10281a400103018200000f461031300315000b191a40030148245001e0102c14840034442e000e01d000201391032409246603804e58180551080c20b65659654041c0084000f034a50001d22100704843c544040c40c501a042c040790504441264007001c04c0c0403903003960300102d802e04445c3d081900300391894032100d0a43c2c0134444000c40100e42000c1c2d0610040c1d9a104403000602208601d81358005c046400001600007008269240ca015080b00f50f42281c2d140a18020b8040c242c101d0380d400f0a022901450030303a0403c0c0900140e880855480d2418260f10702654400780b123a800031038507400740a015110040310310141c2d000c82049442080320007050440c003010000c0626640e03401003940c16841d580084c0b4507540000c10a0 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 687020503 1250 687019253 687019301
    0x16030608070b0d0e0f060c09150301170c060a2106050904051606050324150309070f0b0c0601030b040f0203060415181e061b03020403120509060d0f 65
    0x3410a0340300903021004181407000d214404c500025405610740c00c0300c8080d00544d103030004605a6036000d00351280c1c1c8a100142010050205c2c14000e5000f040c0544000b42d86003400041141804100300c1d60610800d4180030601d00303a134000710310704040f06c1200f010f290001061504a4001c180c40e80040390010300c14001c0004102c1c0c00544001031007400d030025810b00d40ea440382162184006c840b02541c4082d00c04200e6984c078144100e02c0c5038200000d014804006080d01081c10070340040342c14161b594050b80f400c0049500000104018001400100703103031501c9c2d5040305a4890062000400409000b0300040030308c199591104000ea50040541c2c0017400c007820000b80000080143e890790b24038006004040b005509a44148164025011400d4200e00e40a00d40c481d104507209a580035200d695499407820003001d03110042181d51001078a031410340c1030081404003004011810300034204001c014903640ca4041e501d81400741d0700cbc04112280e000741014007808035022998408103204201ca = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 687021753 1250 687020503 687020519
    0xf0f120c0c020a1a070f060e2a01110604110a03061104050108130c05092809140a03140315030102030f0601030e01060303050409090305250201030507030c0203031603060807 76
    0x258030510b0080324540c24103500d13041060502c0645500700714840004115190000e601c1440144c401c5000d600006a40b401701c0c203009080c140320000c03181d1500380820504060071000c0502404803031b400e00e81b40c1403c00743d285150382d40b04c07000360000e407030040740704100b4080c0c1c1e070b038040c00c0000f455000d0014003010304801c52004080d002030080300c2c00b00780c1180000740385003c4000ca6921513030b0170081e00000c10b440e00d4284019068040c00802091081e50045440089010820f8141030394800780043c4c0034440b07050450000b1030190240190b90011800040070a62200c00740c826400300c10802503490712071010040d81725400d401e6580d0954008020001e0402c800c0f00708a114420a880c02d014403507484906030308940d1389000c014003280c0d060106008141d15075000b40041031107818131501d050340e4515440700c400140f0007424010036100e040001156414080c00341c1101d801c3c20240400c204404c800307900c0c0d001c02080303c1a160f2000ca03004030340522a03040500104202c03c01d640d01c154965402c = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 687023003 1250 687021753 687021767
    0x11100801030c14061902070504090507091404050a140a02090a020c06150607030e0613180b0102160e0709090e1b101b110a090509011b0f0f120c 63
    0x949002c20b204000007810104009030010000d80100410b02d4080312000c0a0501d00d000c150410842c482c51101040e2502c1c0d904c9007010340303030190f402042e0082c50003117544292803507980d580140040310700074000052000a21405984e90150155403090103454100e40b400c00000301c0a9446440c02c0e060000d052020740c01002015480400d4849582c0c40e2840280c0da5003400e2003640d0812410806d0001092148682c044a0140140740918003d2407412044640b03490384c00c5913a002c403910308030380b6109265114091a044081c00601000300c07100321119481c3c020752044203042d10070500005e000c1d500c9040e00501a01c00352004020101e91096950799814421441c031041000400201201303291840201c4811102907984600304200700d9450f4103030042100c4100c504c0040c0090204031650345d4417400010f015412400070346407406030708140c00c0d6032401d00c450380d0b0100b0700e000040c2c1803507005e10f441a409c0d5943c241042d80254050044442405800103842640d1420070030540450380408 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 687024253 1250 687023003 687023009
    0x352d03210708070e130c05090a0306140a0b09060d02030f100614040509070501030b0d060c0e0a17060601030c020c091f0b0a0918140703060306050901020903060c0711100801 76
    0x10360903109a80f40007064540c0000c46561039842104007a0000c10400d01e5044035000c070100386003041c2405420000700d443d00c0c1854004403000d503181d000300c0f541255001d042c65800251250117000249034200412030111024003101d018010260603801551401c20282c00c2c02550001103031091051444020000c20b95030007181006074045040c0401440c1074000c02d4041c41420015040741031800d00190014075125108640020f07a040c408000700300140b013000c400c0111500d8641c10709082d81d04111501c5082d821808510b48d002040609450000070010b40c42039003801c00194a00d04084141d250441801c6080da00c09115810000c101400900300b422400110429845054a5604403070450083c1c00d1800001500326008028000708540d0f010215085140005151402030300e031030000990450703c11011a48030300080042141030711820750311840035402141004a040c000070f4561101900c1c500e94008042298400e02411480703e88502c2801402628961100740003d054440c0900c = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 687025503 1250 687024253 687024257
    0x4021b0f010f02070825050304080312010f03030c02010305071b0f050d050c06130201120527070f05241204050c040b061909352d032107 60
    0x1500090002c2c000c0d1018261721420940c10f12100b0341c0b881155a01c080c00302500c0250300480000407076000d1008201070900171020755626201600742c3d00c2d458206a010701155a400c40040000ca44d002c0b041d20081a82443c002c0342644449104642c0741030451071454402e400c1c8101102000014135104499600c2141503d5441c41c00303201c10b9855003c0c0039064030042d00400000741c1240f07440d042d08615148141884120308041c10440d200f10b950882c1c0440811070000d01142c588805030020078519101c450050550a00f441a05400f400541c8a65801500d0030715021242404000f010382e0030125440303016884481c42e8038000301128042c5c800341c50030b01600005240b141018040c1d6400b811006d4510b92400c40c6040d00e048281035505c66241c2040f2007000040b81a560400c0441100c50002c0e007070b40c50085407890030b00c002c101400901d07601a800300340040744030090a90b1501120115010201d00680c910304007900310300c0340c1141c9040e000c1500c551290b400703049609150244200da = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 687026753 1250 687025503 687025511
    0xc011509090b010b0304032a0b0f010b041e0503010c09050117040308010b03091014011e0f0308090303040315020318010e06040605130b04051b060a1b0204021b0f01 72
    0x103244820200c811051010b401800b03080010711031201c4ca01e0056070405d100b0301d080528a11840e103014803500d8807004140301c40180240420921101d0802142c0114000c84c61700c12300c5d40b519044104078801d0784160b407040e854420100e00d4102c9884171807001044068000d1080d82c1107444020300c0d20b00c807801024046004600005c641e103010126007442142d05888000407a401c02c00e0000f42500000c115000c0751080141101c0c50000e54020074008002007912480b055051520075821380a0116511001c511203600c2000034080e0b0b2080c4c001201e400078102a42ea038480400320382548100d400140c58040b0754900506800b00a078025842140c1700b0020105e806e20700d0440d18240c80d503d03540e00c001a8000d0300403c021690b158403903900610740e07038640a149030f400d0307a07000444082128143c1d101d17003014902246c103195407002c100c81220112030075864500c03004005004011056100e408225004221000719110b541c100d0740d00610801013603068801101078295a1020041010199420 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 687028003 1250 687026753 687026759
    0x803093111300c030a23040213020703170901151e0b030106080a240b070c05030a02060a1805150712080c07140102120c04060327080d0b060c0115 64
    0x14440182d41d10b044402e03690b5545410b42c5980c4141c2010b0300030000d5075030311901082294075021881c41740380c5203080c0307181c51840e060041007640c82800720701d0044140108103070300010744d2003c180321103102c0840d01043c031a200c0100040c0100380d10a45004103d82a45001c00e02c0b407418001800b040d0300c0f41c40400c0041c0d0b00ca0582041d513000c03c0c460308010070703d07000200740d4442031504070f00c08030b00400000040307000030f001c0d080100c05c0d071541c001c2e1882e24000540c541070201c0168004040e010035002404005895404030300d031841840610b034204003685140300d040e020225075550050500604103c0c01645110030441d040c2d001c0c8900f00c030790040401c64110314901a5884610520040440500f0b000d050f444000e02d40343c41c0707031004c0303c60756080084041080801c10418000d081c42e14070940c03150700300306024003103030a000e8040341c0c101d280e40d03281c460500f0f02600c1d40c514540d0241c00c44c2d850340e01300010000a806260783d03150f0300400c00b0601841f00501588008155882035006100311aa = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 687029253 1250 687028003 687028057
    0x14010e0610091202040f022b0c020d1404080d082505030a3308060f0c09040902011b12170c0403240204030609020a0803093111 56
    0x481d00c1d012a844a90800265094500000310f260000e880416550704010540d401c0313034040b8100500900303070f05014030f06c000880c0c5495080e49003505d008001c445003401d0081e40d01c40c0019440ca00304040000e1108041c000b06065034014400c00307085400700e001c00800070701034802c11200c58101d10300c204292001c40c0c55101d5a000303c0152512041c2c0b0b951108d4403000043d250300761800d40f494144010102145c111082034a0804004d080003404072402c045038681041cbc0054000c04c520009101405040d05480e01101e1000c0c80860f03001940071024401690903c00711500481c403416408040002e1058445094081c4111650707a02418182a10308600b59581a540000100303414442480080c2242c41080c90020fa20051007146042c002c020310709a9005420071908252900071080c01c508103071007140b0145c9402c00203981011500c601242c0d041d04544e403100034124070604d01114440c001560142080321518060011640300501250b06601111720809118010743c21001448 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 687030503 1250 687029253 687029269
    0x3210203091e040603241407021504110301091b0510020a080a0324030c0605030f1311060a050705070f0302060d020c030d0603110a1710090f0614010e06 67
    0x1107001800e1054001c1032002d00e41c400c03036410321650b0304035981d8140800402c0007090400e0f1207803040798038501d4140300c04969809070740e07010034010365210201c014000c03556008514555665100d403901841c80d84c0d5070070f01d1150345401005032a0903500e0010342c142445403071007814640400988030002413903a11340c188102c1041017400080160171414038000041c00b00c3c030041107950254075002c505100705411a02940700440034040d6420f44803181002003000b40c501d901d009101c0c1e803c02c5415880d0012002038581401040c5803203c1c0080780b04003080108650402001e103002a1442c0d0300c803001d244024103582e00400e000e94040c400c0071000605a46807050382c100f0350303502a040300d082540c14881c02c0003030f410140c004101d502007030241400305000703032040c4c000440c014064040c1084c20343c0140608032110f41c11092508a401c042c440088a0000345128225080c450005411209040078208040403083c010103060406100e036054108120610707042c0e800c0c5071105a40ca4441c0400c102541d = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 687031753 1250 687030503 687030517
    0x604120201080c0a141c3e0313050a0602180a0b0a0f050a02240403030b01110309010e03010b0406091b0f0e0d050a02040f020307260f1306020403210203 67
    0x78444804908032803140740040d02000d0b0300c106201d05044082e1070030f00182d507c02e50b000c00c0051840350490001c8685c40d5850b00740280b807090003201e03044502e0f229007942d2000070450110100c01e440040100402000010410b40d0484c40454032145000e902e8400303614023a500340d105981c02c200101d41e440c03d010440d086000182c45070f50100c40a0081a141074100c05040829405201500c1034145078800c2240c408030b0b0024000c000754585460080e0442d0516851141000041c1d0610084c7d514000f040318145202402c0c01007018940e4000a4050906110f295422034180500090042c4091300320202079035440441011200208004403500c84200a100001482842c0d000e00c1908003900c000f19058000c1c01941d0344880c0c15000b05060356071002d0301440e442d80c0041081303003103540615941d1030885c009103101c0b144201c40e501c1c50035000300942a8a0000b152201281103801620032580f011540014155115940da041180040308046448841c3d40c101011050318188040116110 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 687033003 1250 687031753 687031757
    0xf060215010806010608040212060403020c0111061306020f0426061e0a051801020307110f0703020a0b1605120408010501050402280e0d050115080102072102010b0604120201080c0a 79
    0x4660b1a18030102c0741b00304046d20030780c1c02400c4209881c2c14504244141803040f4041c0d00140701520814000604007031540b07800c1c2c107040e0855001c2c403104914512a0780041c5070460340140e190b10440380e00856610980e40070383c41c4d030450501c010b0424045880002c88656040003610610343da0508000c4620b05203034118207240b0300c15800078520401c903510076500000b2410b40700e12062090045242240d00942c2d03600c000c40e0100c107040844010030040c03e040300c44200064250750749194080b44051020303002e41086c0800c08a440e81c42000d101020901c559044401c03a942c0d10401405c0b409164028044c050555007070100100b90303810207000b201c03144c0c0c071070001c0304003100283c200450440030124490810000710001f03035a20303552010b203081c4805024a000241d5000c07c0c0411500e90300b102c0e40701804a074014010800400d000407098058028401c8416000080c1c080e401c074010804d003a1200d07881240482c1c0820b1005554041c0410a40300b1780391140302e500c604c8404000350141022600c0 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 687034253 1250 687033003 687033013
    0x2190302150a14070f03090606030f05120c03070308060301140f04030e060a0516020a1e21050703020108040c08030414010e01090e060f0609060f120f071b0302160f0602150108 77
    0x10f010301c05c9a1580c1c001c1650320f40020440200c4d81ca41c01902c00940c010f44a850f42070510800b440010b218506c2e1401801040d1407900304084012a164000c503280907060000c900700140c05501c3c21f400804d00440070b0072401501c0d181480806038600c1d0b040d50240c001450460403103680f07040003000c484640c052034039500d003407101010f821a00003941e240100c4e088035451400140500c00c50b002d43d200e00d0742030140b01d41c10701d0507c411103030104440d10003401a140751441907c04030748081120010740b9020f20307190445544a0030445113881a561160710a8800002c0c0001c0d05074101c2c0340c504c0704c3c240c26a5604410039440004490b400642e018026560b1040c001080943ca801c0407240f20030b070005401141072080b0440000d103150440116812030800008500b02183c04102040360320001a18039840a82405c4800a241d03040c143c0013036881702c800214407020325000b080551b89000151211070303e00740d225492f01110105c144500800f46c480e511a01500c0716000d022181660b1030030000302 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 687035503 1250 687034253 687034261
    0x20a05030712200309180f010902030c0f030f0403090506121f09020f070623190b040905011d032d040e0106030618050601020c1002190302150a14 64
    0x10b103007204040707000e0018694421010078490b8030541801c201c0c5502942d1106016001c3c0503060880c00440c42444040303030108044109900c00c0c09054881200006880342d40d01c0c140703a001c0740300e0b515100284400200c1008080d0f056919843e110390701c00c5d6030300165a40d0300e4084c80300c103010b0cc140c0c40115280b441c0020740b040c03a44040601311009290304c2200841e9581815000301ea1210823008007158001401c8424858203000c2e45c40c4101001c05c2040214641346007900340244058005100c0380001110320988003004e402025005000408c02c0040442d1403078114000c1c9902c2d100031000400b0106c0743e5603007a4022081c0c1c1c0300203025804031001180c10a01445840d640400070b07540c01c80d000d11010610802d00a200360203400651800100242024440341904002c11a103a900c0303130500b0108004c40c0d9001ca40c1001c3d241041e00d0400d1000d94a800c05d0b8144900003416980d4040c2590206c4140b41d4000b842c00320145410141d507601d9124030310030030151052540081103c02c2000c01013 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 687036753 1250 687035503 687035513
    0x4060c021f05062b0f0303150f090b0102030c030403030e010521060103140603030d090c09020403050d0207052d040608100b091e040b0c04091103061c020306130c0509160906020a050307 81
    0x20342c1c0313900e2007850300152088000040180c1991140c00100309d0019802c0705100c1003a06101725119507009000035802c140c080e14016581c1d1085010050400c000405901b01990140781070b40d40400702040411160003640507000f90120302201c1890010b420414450840c05110700d0840c0507000140282d1b2820b001c03641420043c0501074812070700800c1c0c0302d400080241c024400760018501c1940a002010710781403000f0301c0d100c900d4000d503204860b803600103110f11401038001e50400036a00c0312072a43c005501c2c0024010400c40e0f2040c00a8048c5c0e02000e0000e66540d4030508042d0710407a60150f603a104c0c0720403960017400118050203202107041c0410085080c10210380e501c081850401440c0680350350b82003044e521000013101d61100c01000b8000d0900d030503d40648220800c50010404040580000c0d650310400b070311000b106000c0da030350103051082201c2d140300580b0b00605020046c0c1410020f40080c003100e0009007000405490001c10040d00c0801c0c03148501c1d0f0468021420070400d9210 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 687038003 1250 687036753 687036773
    0x1d04090201051b0601050a060e0d120c152c070b0304141c0807020a0b010b0a18151134091506080702070e04060c021f05062b 55
    0x826410322000f840001242e0105084926058203100060300700c0f0351625080c00200c0720035420880900c68007951a0005ea1146000d0039109600b05e9030415041040100940b821481800040e1400b42c120403161545001c9170444d0600e02030000c4002039203078240082c0f440740621500a12030940050350308010b90043d20b00070350b8100c3c0c0034042040b030306400583c00030b00d0102e5500071080b03801040c201c02d20034181c0001c50b66910418500252503000311aa4504a102e1014040c40e803004101040d61161644aa9034140071040c01401c0f4842d125114080500c10b084100d146400003062400d00b550598404151064a01c051002e484905003501d440c48070036400716205902501d60b01000041c0180313542c025071024107001030b510403105042020007004448020400300c04d55128030360402c007454010842a03480380c0c01c1a0001400c140e601006c904103040150140d18006400702c45007524086540b0aa0060300112400e00300814501c00c1074000c981c1b0b204420403109215068000400c0b00c100c1 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 687039253 1250 687038003 687038021
    0x50d05070e15060c0715030504122d030b0901090b01120209041503030509030d032708070501020f130e010b072405151305010b0405130209130c030c1d04 67
    0x9000c0d2102d0000d201140f1290072402128031103a000480c100818071a40310110b41d4242c1c685010300ca60714141e164540b0901100325110100031600b00c403030040e46816070b1002c0c44c060100980060155011100802400311503501c5403091701980000201c42c00140b08503000b40300180c482c200c842004032481802500b048251503006602da171460300312400d180007560095071103901c400c3e0704c5641c1c5034181407a018842c1900030503d07140101c0c140841a05041880700480301910310b40c406201894400424029818028000d6002284861400341808090b0801054401031400800ea45542c0018600001c0c8a002200c450820461003c281c040c441184075008240d000c2e204403204061000c1210740444004070b50001e05001c140091609802c5d490b00050480e034144511f5060440b298082d00c5207115541c841c5035607005140b41041e698040d6491070b0340081400000000503404038016000f0340c1661000240b81c004003450160094405e000807600e80d440d02c0960111640034403005145240d = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 687040503 1250 687039253 687039271
    0xf1512032f0709020301031a010e1612020d05010806090a08090409020321030619030c0b1309090302060103020a150f051e03011211010903121b050d18050d05070e 71
    0x900041c0020400300440740c01000c040c18016529851030424040017000700c4400c624000e0f610740100299400c2c180c00c107802000d400620020101c00c14015500201c100b40340b031461a0020400c60017548581c0e001f81d04030340c1508140c581603610810401d0315400b0040c0003e11810b41884140340c10300705075100804d01840581100c02d552071825603220000740c0351f80b41d0784130a84000300300b2401c2d0801010f40b04081d4150765800e58801d003940d4507001414468022a10483c001058084681d12a06804070041602c407100b004042c2e11030500039102e4900f404240e000e1007082000045200c48545649860a01c5645501c11201d2101044820750300803520076a5020609410300201120040214003d00308042840003103d03940c505061440c010300c4656052002d8817008101007400710303030700e000001110315042000a0100340f641d0701800405101402c80c0c1300d0000140b88440e0040020760000300380300c82d140741d455035410030007010400e04a00107105402c1748038104850202501d4a0350045240 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 687041753 1250 687040503 687040577
    0x62903070807030903091d0115321204050a02030d08091903090801020f090f090f04110a0e041407050306090a0803150306100e060402180d0201120f151203 68
    0x25584a07c0c90300780c2c03105800309240c91344010030600c00301c51481c021411207410000100306507110408a40904a01042010703007400c0344802e904180107040b61b0400481403080e203190704041c14510355480c08a80704900030322805440001d114000c0080310311440303c0e0001000100400116500f2404440c0d2044040c4a04400c011071020000c1c005001c40000405456403a240700008104200407010380003801001000309205411181001066105030880300035041250010b000c255124a02d500100c00740d0040000d10080240192046440c808010115009581c0307610805031507480c192190300303042c1c1c050f046050001d1480d501440e40906003420104604481001003414144212070000941030901020b00c83d5840c003800094200b0415074045040030000144880016080b203180707482040e985850504580c85030314081503191403000c0034004120143e007003202520f000b000d00d85810702c1c1c40102041c5c5401406110b181940c065135500e030b603d0480800a4051421060540780c85450 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 687043003 1250 687041753 687041759
    0xc03031b08040b0a1806030e0c090405060c13090f060e0a06140f0d050a0317070914130207151e0504050303070c1403040305060a0e0c010f0509040b0406290307080703090309 76
    0x12456241c0d0046c0050b8802080c03c00001501c141030101040845104003118014031000c0303140000c1076980320740601142540d40b1008400b0310b14580b03030f40e0700049115041c0740c1100c00040305034008008440304412900800e0711100c2c82c1d401522150700558243c24418040c0709503925000020f0060b5410181111101900ca515554100b401141c425408074900320340400090b050a10a00e600c4004e900d05464164180629180b03214264000c4900c641c40c04107011005a80035030483d030364540d01015104c9144e00f07a07840c80c0c0140c81641d50403020100311112041c1007403a907000b8607200e5030307110f005035203150b88610701070342c00140954065882c2d00002100c000215410001030003d58002d900400c0649014207110054401008501900b0b400140042e80c3e1a600810f2100341c1d40036509000b911188a200802c0c018101d011030181c1c1700381001000602c0401d44c1a10241102201c10b032902e40c0d0b1810034080400d03203c20b661010000301140c0001d006a40700351b00521819100f0716081c401c00d95 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 687044253 1250 687043003 687043037
    0xc15060e0405060403270b0a030e010c0f0e0d0b040b040f1203050f01091a21120c060a02211302090703050f061c060203100f030c03031b08040b0a 64
    0x40300312411220790f03100900740028150850b00c001210002e0301035210000401c1010845204103e1148580080002c0340780105103020f5040b09480d100c0322002001610641000109103a11a40ba50004520131030381b6407440b1705040380c40148482c3c00c1410022035440340c1d920140c074070301d0040050725481509580b19002408a415040c288091980c000ca15410003100400e28410180e108149841c070b860000c414ae16440c0501005d01c1c44100c90342940316030760355249081e0b0600c000b140000383c05416084100c0b41002e4003c6c2c01070f07200010890740d8a54030000080204d02c1040f0b2261110303282036400c201484101c0000d20782c000c0b6162812042c3c00d205601141ca00302c42940c0190101e52140c040041801e031000c40c41d170340400102c450b10580312205074545249129448040c1c590b0341c00000003400703060003441040050070f00d49201e000c031950300d04108030004003d0104400255004010540d0900034070016128030307410605c1e451515281031011105c1d03038080402c440501c1190300044640714 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 687045503 1250 687044253 687044279
    0xf020304050a0c0506040e0a090201110706120e0607091203030f050a06090b0409081b0f070906030506090606030d031a0d05010501090f4809050109060c030c1506 71
    0x10744610001c20840c842468001c2c0030750f0395504441d00a6000740410880c02d0119001c0e43d401005074100091900403a000413928084640c019124502c201c100c001940d0764080d00c0540c40a4002d0701c10462030805d00c44450311002c081c1ca84500040b554001400600c0055446044d51480303810001001e550141c40002030b210115044030000350f6920381002103d050f0301800c11250801ca0f000c111000b000e580e9411940603803811a2500c005c80d600008110300e0800150b42404102030803580865951550040901954001211580640c00c0800c1041c440051030701d00800d401000b8101117643c0d108110b0060035070010a00340c6020b0b03454644c201c0d1700c4a4540300100c42c05880003113029030528980384150f4600081e100c0b280d030b00e001c22400c8007140c403e20441d085049040032900303105100d04d12039400c1c801600c507440b2424560325554402da8000b0b0a1600315507007a22030150180d512182a11079000041001e00814045806600019180740d005a440078100ca4000394841e22042e210685c4 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 687046753 1250 687045503 687045511
    0xb0a031112031903060f050111060f0907080f0303100f060c020103150b07050c10090506070b0709170d020c150d1e0c03020403020a0b0f0409051b0a0e18070e01120f0203 74
    0x10a41d2105e0601c1545415608900580300a0038405650101180c00c1560307268018003c1c00c12040d018007046503090144090700041440600b1903c080035440c00c00d540300d40c030a941d48400900100300000d801c45070502c802d800c8940d1a2903040c03490300c2940040d03024040c003030300c9000c0b02c10030240082501440c41b809081c126000704024161489814203110f90030385000b0707405060100030401080703039a0315607007120040c581c861100b090b1921840c070151520606034100705007540e1044842c502e00c490015072100d07051240c0d400c4400482c03250081c0b02182c40f8107565001c104004000d0065022aa138202668101c0c414100307415142810100c1800c0711044203041c1c00003a000101001036207480c03d050400380821075107441c039100e82c4500c1010944240d214006100343c9400001e48241c80c1900481c24020340003030391507941c81405800600540d59101d4031071003040d42c114040d4003071030005c020764400c81050303d03503504e41c800c100c00554070740c2c0e070500b04201d00e2515107010508144560000e903000b = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 687048003 1250 687046753 687046757
    0x42312010b0a330e040f110a03150509180d050a0f0e030a050607030218061614012d051825031220010e060103030e040b0a0f0602010b0a0311120319 65
    0x3110f0180d0b0100002c0d2104506206c4500d0b0408071041d00a1190108407004104070f401c0003d00701c1a141c3d01c2c54003d00c0e82e9840f159101d46143c0805c424151880c402e82400809901590807a01c00c980082e903850145004690000c0c1004104002c1103006403200121814010304485c2d0001c0d03941d540b145031100499065000a4000c5a6404145480c160031750704008100c600d1803c1810880300045403200551010b400c0081c181c10b1007074030003803c1d0722402a842b10407841703041030030080c0d01c0f801800b0a4003072680000c0d481c0c4800601d080401c003007010f8000e0300f1a0081c06031346c040d414080403140318841c08005041c0030210000000340010214610707013149622144c44001c09181d0407201260200b010a58603410312900c0c0d000c01c00d0200d07402d415654142406801840040c022400a01d81101e1860700414001008110000707204070030b4049644d507a0090000e6001c49041c00002c2c0d249200090000c1c181012041441c90078000c1e9199802498003141e0a0016580c01207040307520440e21280 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 687049253 1250 687048003 687048017
    0x40b030a0f0b030f030d0b010201050f13140105131109060a0308131706040302120316230a020616050c0a020603060111030a0c030207060f120908042312010b0a33 71
    0x170000b86c0d180030302c3d6041c00e030900082140e0728080d0700b54000010010611041d60903c1850b180400c000f4043d80a020761030a80200294544807001a55550036014103480007184116000f642d4640b90040c070340700d544050122034040303285658000081c0c0020344d2944a031509240041420000284c40c4588120200d00034541402e080c1070182c00c0c0100c10891651a040c204100300720010000100d6035104214500002c1120f001f03004880d1440800c0902c0544e42000140d1004155000600c9070150600c3c1e4819248a42207100c01c0c3c80502c079810b040101ca0308881d200724054034001c0d001d941e1007681814664940252021181c0c1950300501003070020a0814483c4018180e04010210140c556030070110844032264001420303092041c80d600054689450940080140c0d44040c0c074020802c01c81050201f25203281003d41103080c01201074041c19515241e81d0003004140070382c0010380409040e0b14205410312403c04660390b061128841d0380c010400340b08128407142104520b9010701591400 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 687050359 1106 687049253 687049267
    0x5031b03192a06090501140d0e06090c06070308010e04020a0e0108030c1027030c120f030b120601270e0c011202040b030a0f0b030f03 59
    0x22000619580e1001040129206200c1104032950802c0315030680e80120034140312580714507000904022020005540100d0502c900022864001454002d907160b4030401d4982000c00380e05640d11507400c010035408140900c0343d0000e41198a07515004980e10003c20010060050ba00c0e4440e454000c00c0440d03898598450082944410402d02d941c0e4820120343c8940010300c6c11900c034083d02c1c0141d07080484c51310840c100001e20b0100400c004000d4071140c000400111021400c1c40388031041080460100b0820400802c07003a503811280c1340c2460781c01001c7e51844842107000301c00b40c8118200c000004a034003070641319000300d540404022400300744800e154624810501034034092a03800c0324500452008224002a00ca0b8031101080f030b000c1e2000c85c800c61160030813441052020070f0103c5816040030b40c00ca200203501040502c040d400090601071079032002c03503080e03000152030 = true := by decide +kernel

theorem cover : BRFrame.Cov 686870503 687050359 := by
  have h0 := BRFrame.cov_init 686870503
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686870503 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686870503 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686870503 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686870503 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686870503 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686870503 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686870503 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686870503 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686870503 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686870503 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686870503 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686870503 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686870503 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686870503 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686870503 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686870503 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686870503 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686870503 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686870503 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686870503 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686870503 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686870503 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686870503 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686870503 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686870503 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686870503 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686870503 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686870503 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686870503 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686870503 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686870503 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686870503 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686870503 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686870503 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686870503 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686870503 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686870503 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686870503 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686870503 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686870503 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686870503 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686870503 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686870503 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686870503 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686870503 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686870503 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686870503 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686870503 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686870503 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686870503 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686870503 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686870503 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686870503 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686870503 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686870503 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686870503 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686870503 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686870503 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686870503 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686870503 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686870503 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686870503 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686870503 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686870503 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686870503 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686870503 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686870503 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686870503 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686870503 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686870503 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686870503 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686870503 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686870503 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686870503 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686870503 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686870503 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686870503 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686870503 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686870503 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686870503 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686870503 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686870503 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686870503 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686870503 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686870503 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686870503 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686870503 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686870503 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686870503 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686870503 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686870503 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686870503 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686870503 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686870503 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686870503 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686870503 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686870503 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686870503 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686870503 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686870503 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686870503 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686870503 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686870503 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686870503 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686870503 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686870503 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686870503 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686870503 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686870503 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686870503 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686870503 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686870503 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686870503 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686870503 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686870503 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686870503 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686870503 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686870503 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686870503 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686870503 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686870503 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686870503 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686870503 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686870503 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686870503 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686870503 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686870503 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686870503 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686870503 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686870503 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686870503 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686870503 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686870503 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686870503 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686870503 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686870503 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686870503 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686870503 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686870503 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686870503 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686870503 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686870503 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686870503 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686870503 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 686870503 ≤ n) (h2 : n < 687050359) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
