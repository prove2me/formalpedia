-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3388
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T09:31:04.841094+00:00
-- url     : https://prove2.me/submissions/df382da0-4091-4110-b77b-dea15bf2c80b

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 609172661 ≤ n < 609352517 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 609173911 1250 609172661 609172673
    0xc090c0206070f020f061518150910050f150f12010503100507020706080a0605040507021e06070507030518040905100c05122205031605010b0f09041b12 67
    0x50103444503a440c0d40d150250140101d0340c52800c00308520480d00945e001c1081c07c080c0800d0a00e800c100500035408000040c0c544011a1500b15440c50013200c0c10341c14500e1514064690f01c1c2e21002001d4003031a810305004c08522487c01201c003d074000c0c0000c21000300b044980c941550100600000c109030758514042c00c0381c010200030b2141d1030003481150100880001c8074001c82c1d00c2903007143c0c01840b401d4a440812542100080e01d80944259030702c00c0841c994456004480c420b01140e00200021108004c1022190044907580c1e20160030100c00d000d034031648a02200c19803074141c605541c880c1c0a101104041c540d110b08030552091030181e0b0340c0e040202c040344085040100390820031012901482c00d82d001e100c1c8917a541b940d15031100000345401c48040c407001131100c0e81c00f8208913460003552524030710b601104003019001c02e03e21001c000c00800f40907030303c44500166800c61224254034080740410402410040c9106030103c0340060076004d00e100d07c0c0043c02d0190340f841211007941051 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 609175161 1250 609173911 609173923
    0x612110402210a1505090c0913090503070f03170c030112141c080a0501142b03050319060b0a050c120301030b18010504171c15140907020c010c0c090c02 67
    0x401c48490001600080038942603007110322483c414070b0820325012901c41048050381481a036a001c856843c50ac0c0c2002c0b0358104040c0401c3d034812200b04401d0003003414068a030103404129000c030140030208001021800c0800d990450308201142c42c0c000c1140c5c90302e661008c2c0b00340000c80d4907104030040c003401103810480a2100c40c0ca19129032007651128020b02054940034003840040d88846d41c855400b81c10b240c04402e85030b001207030074184811340200071000b440140c010144c1c00030b00040140040c4150807441100c0c00d90110078100f00440c64000560074902a0f09400d83c240031010139600403800090224400662549205035a2903840c0d00d0b02c45015030043d9415018080c50424402060a0511500e0300481d04490184508242a007410019600620809200c7c0d6a00c6001006800544c02082009408042025145030404610240240801d20618403d06030310b428800c4150700800c602003808400e00c0c0206510001f41424860400950310241d1800d180403d000c80d01940482d0b0 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 609176411 1250 609175161 609175181
    0x41a040213140105040e13080c10050601110703020d110d1202030a08280f1b020a050c0603070c080a0e060304030509010825052a03030a0612110402210a 67
    0x210b8120000c01038011a098000d5010f02c0c01580d1844020503071043c40000d441c1700c800e105600c424030b01b04c1c14442040c2800d04a000441a160311001400080d68212191806c60310070a0001c001d000d155400089501c20410703030140464070086000072064445040031040c080c0c100c1009000b4400c0d0050082d665809a080040040c85038000300340c070f4510035607007010001c40c01081500041405034110f8010000e2241d13810300b05544406119160221070240800c2d012190041c10210301c03e400c00c54100785d4108241e030302ca41000c20400200c82e40003220501d10580040c0c0260310391b04000c9064030744905007028903500170000b104020426a219009060200c000c0c2da9001e102d8072100d0094005000001c900415204400701d900d03070345480780300a85040404240300c04401c03000b0303103069580c1c3d40750450754991540001080050b82100d502420000700b54141c0000b003481d07810f071201001c1445920316540304070b400150880d061000c601c0d15000c42030b041c03516070410742401c0309010014400040d03 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 609177661 1250 609176411 609176429
    0x6040c1416050601181a01090e09070905090c120f0307080705010e070905090f0607320703020715020304050a050103050a090b090607090603050405030a0f0203040e0f071d0a05041a040213 82
    0x18000101d001b601042400b420010b85603c00e680d42004d000c54086000100501954801d12070009407108050240a00550410020b8950700d058141440045141d4001d20071555100041e5a020340d01c001003101d039000d402080840d03c908440c6045409410524010b090920408a0100c1e44c4441544118046d032101421107501814058140d0b4849404440307660101d80c01c030101240546040302c14141c040c800b030b0400e003211002050741518a4200150540059004040900c6008042c0b00c0200203201203000460500d031034440010701b05105806803a0415032a80085070703145c4103581003000302a510005504c070f2450842c0b0016035801c000c8030540006100c0d840d00203101402881400e000d140c010700510b140c2042080141c8500c2c035481100c40452208210000305001c00c4018540100c16090b01d501c001e00b8604001010b1000e100494000c003002c28510340600c0d40d5165140b801c8a0055801040703a612006140400704507584181d60414000607079a81001c0201c040f203019a02408 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 609178911 1250 609177661 609177671
    0x120f01020324100c150f0e0f0c090c07061d0f1011040609170a1209030303150e0f0604061e030203060a090237030b04030806040c141605060118 63
    0x10040141c40e41c07a07142114081141c4a48213404115004110b0291142803500030854448045001c822504150264199500304030b5120002079003e00100204840481c0c01280328100610039070214818040c00822f240d41e0f03148903100b2041d18007880300c0503101c103800365904506000034058882004a94580c0c1d06450221482441104501a642a0b032103503640c011036142825164484d680c0d007090504c0e000c1c41092810380000320840000b07140c0c1000350741c820491758070f545405003d507958151410540c1c0101c01007480380c401e0410180d0b40c0906551040011616040040350041505030046500811340c05070388101414041a001d045030701c00d84c04c44806558050882c400c072200004000e42c0100d0a00c0c0003414460000c02140b050390803908825810002c1c5000c4e00542583c0c0d80c002c80d990318000d0108018550401c070f4030356211000760b4040c40f074520f00c840010a402c0c1c802c0d240144040c000b26040004000c03c55003000025801001c5503450358640354422640c811001880c10018242 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 609180161 1250 609178911 609178981
    0x122d16030c050f0a110703020406170606090c0711120d090807080c060a050d060f1517190905150906010e0a020f090609060d110a020c0102010b0a05120f010203 70
    0x203401100c03403d00718840201d09224000d40c0482d03a001c1808003a00140c40b0301c3d400480941d8032441510f00411036003805030344101d0384c2e01e546401c0480080403d0f1140016a0070402007101007800c4441c0d4550001c0d012401a1000c0009000740400c034065299512442420342202504a40e088003500c20342c4040340c800540e40d641d6565580602c4030159001394052140f40402801071019041d03010403070740c0114246440302030440042d1020381c04950f60b01003403c080000b942d0080e04c0c03440b40b40312007071329480d40c2d2514003006140004190041b0926035a180e584106010080c841000300c8404502041c045051a2520b55a550030a0142204600c9108049038904d101c6100721409686000f0945040114200801c000398010001c5d05401003010801d0307280420052050300464809000c0054407194113440091406980c1f054441c15a0300d0070380e5518565507000404001c40c0c404642410000406006207820b0509041041ca03003036002000340082000901808043c000c0303007000b0f29100c0c1d03c2da = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 609181411 1250 609180161 609180167
    0x1b01201501083706091403030907030c150e10090e0f10060f0f20030a0c06050a140105060a0311070b041104050f06040e01110403031d030102122d16030c 67
    0x43c0c0c24078142d541e0b540f400110010b00c0942140603440c2c000c0d04084034030b0f281c05940c00e0440c2e10844d1444000d03003004070103008200c030300e038003002c0504070b9207040010030307850b0240c0070b0035901c2105642407040c3e0034102100c402600c40c400001c0a07044643c0e1404144c14030032803401500109840c249800e8400840100700c003803203a0f42c074401d041410740c0e82c4200c5003102a02507514403050481d000991090b200440c0e80c01c00700708001e10058229a0f6400981d500d00d04210041742c0703000d80381d100c00c14142148a01949840c3c82d8650640e0300440348a55124210340c400e50040c209000c01400f502c00225160040c8940e608145101d00c3c0100400c9044100e50703c00c0008844080724908119107200010078507c1c10240d1000d40c1d04500f00b0000540c400802c503201603680c005a0044001071162503500b80160b4810a149490b818158000d40c20304400030f07031180420b81c00401a0880c508298903012001113000581c1501d421103a040d003450f410040700f805040722121001d0000309040c0f0341c800850a02c = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 609182661 1250 609181411 609181483
    0x120b09071406031807150c060f0c02030d09020118060206180706120e0c090c030103050601052e20010e16060807050319050a09020f01081b070204060312030902031b0120150108 77
    0x981e40650318100c070033700040000b01124a401e078100030444102401c000003e00c1d4101c0680b00f160018043c5241000104200d24030010f509030b0700703401c00203080010a410810340100040040c10101e011000110340364500302d10b502c0042e0b446120241440f0034110004001d505807406001900d10704e81e210024003118090300c0840d1b040c005440c0200d01d0b29007030805c4856130026505d24256007107031090280b003440e1080720040c180c107031f954920301c040c440300040000040d012060070249400d1864908040c003201d9004064030280700300080000c250001e0071064401d07105015500f0411400d000480c0f000030a07075803104074001c25201210064660085240a1050740c804640f400304501070740b1042840c0e00b0410049811079129140400065441504000551403950340040e00d1009130040514051024003c01000542c0c000c01122a99000040b054142c2410400f0481c036822100f5051406c01d8449a0341008100b52001094046002c80c0042609110002034a4031080c20b25511880d10 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 609183911 1250 609182661 609182681
    0x111010207210302120c0d0c020a0f060c090b0c07061d030a11033f070c051c060504060f060f0e0f040507120b09071406031807150c060f 60
    0x300780145401c0c0b000003901600d030840e0403441e0143c1480303211172446a40d14404d650420461034040b640103070610880c03207100000d00840c4000d114002d03050b02c6d07500c2d802c20b0780e42001e4540740d1039a01d0601c08901442000b00200080c0d070300301d550f600003600c0301510752034140103480001e5061010050100e480412000340038200034080d008803003003035503202d100008215001d50940140001c0a0501600342099075161104030700c1e40081010b00d0840c515040654001c134680c11505101020100c1c00e150701030070030b80c1c0040d10210311503032000d5221030102541010040032141014100401c120a5400100d4003207020007040c003c2c6901e69140c00f200f030510340a406c854403011030024400c07501c41d5a100360414015800e6580841e124141110343d402203003819500b0f103e07a101444001740d030412141c002031601d00790000c075052102000406030311028241e458405c6004071742c0344102c4070500908008040c6910780a416040c1c20307102503c100140101500d200d458520b6210300390344d050007030710404 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 609185161 1250 609183911 609183923
    0x10501091b05090f01030f02040b040302030f0d320d0b040501060504080a020603060a030602190f02030702150d110a210203060d0206030a02040306060b1815030c0715060b07020111010207 82
    0x40083d41070103407011545003c20704050710703221003030703500705075440100302500b03001c000f80d030b0342d00d041d80145442c2c10907029a406003a03000d122580c2da0300e68080c090030707036130014012040c0824103943e10075110081c0c070b012002c96400380080c0500e0315850940c4040e10790f83c402c0d2024400ca82e070345c0009841d1030150b1322400310150094288080180f0b02078005590140c4e00510900c1800d45a4a800381241c01500c0500000c0c19001c4103040c007241c021006880418661000358070308051680450b040310b03c0800b001d0001480032a0054400e05907802c154600c11074114030b26102d0b11a0074000f00040354004000c1350040c013944083c1c641d00c0c0b0078000c882c07140b08041e000010700e0034039609010040d0320007010391080c9542440080009419070084500402c4030164080d2903400303e00940001c100d41609540c4111544211014800910400d5130b900a54080700075484031010b06000c2c0c4400308250605011614250010030826100000352004038000c2e40c0d6909010b501d02051800c030302c903e82014002c = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 609186411 1250 609185161 609185167
    0x10e010504061101020705031b1011120a0e060a0b210615060d0203070804290103080307030605120303040507060503070207031101050412030e10030204180f1d010501091b05 76
    0x91401281003e94072003003800010b142c1001500c0e440d0540c2c20111548402c2c803200310803000010002c01406002046d840004c01c01405500340c021a13a1003002c0400c2014983c010002d00f0b159105d900a40040c1058002e480191801c825500c0c0208002030066104d01c1c1030306420100754210142c816407800c4584001c100701e4a5464100f420045603800071540325804000720454512507002460280d112a11341c2d014605142ca0001c03a000e0b0218100201d031103c001c02c40b01e004403a10001c80c11250400c0504d98bd070381310310401300c015001907044030f5006100c400240d070302604000002d40c49980108280e42d00c00e612034100b1105031105a550a0059000302402d1000c10307003019080b10302e2081410b002d440d00340d40301e010140c02880d07281c040d000300302a000c5015041c101481c81c400b030000c4a140861505052040294010210058690020b50b0f24441400300c41d0b41a0b10425a40030500809801c80e100700083c94080e0100b40240b028140c2400303511850a1010480c1103990100b685a882c1 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 609187661 1250 609186411 609186419
    0x304050d08070c0303090509011406180f03010207380118020417030a0f050f070609020604120f0302070e04170c0709060b0c12130e18060f0106030b010e010504 70
    0x203010310018a007034910078010000040040c40100c0c1100003144692205404140341c070302000000e010507400745400080c008103456003035480f90201d59081504405032f031950313220382001c1039036019580202030305984005000820b0291058045198007801e00c0b01040840100c0c41c80c6100300c00150030314608041441c0148901c030a07101e840c401c030700c01484005080960741c817851907500302c00551031241d5030400290071140399404091424000e8031400c20601d856103050034800030b8401d0140c003808880d901ca081c0748c11961020100c400034007654458400d805d1040c14030340c0182d14140001c501501c6802e030b00040000078200c04621445e04000c101c2d0800300c1c031802da21010b03030044500a0b09030003503000110394000d4900c600000740c42c1c17007020251200d4505042514080d0074660306078a000e414882035004c924a05583d00070b03203845000400d0315848404d103400d50030030310074030702c21060180030104030905540c564040d04991503541d0074022a121400103680b004c1c16500414001402003100380 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 609188911 1250 609187661 609187669
    0x50904020d1a0f2208040b0a0908010507050a080912161401090804090f0b0f060f07050d080a0f020325170c030a05180327060309060720030405 63
    0x80900604074101c44004007244111642400c441d01030f80103886105200c070807154043d0361607514081c0b02140300c0302d00807900c81c003106005174801c1000d1001d0000340e0b00d00d914400c03010180100f00d0380000307000703508110030094003a0300444407a00006141400168000d02c00003401e05108443c2c0941c0703440e00c51040c49074600d0618a20081d58064000954810350810074407078030703510364010340a13251501d091814050580f28039103000c042f00390071304c0680b070902d0f0303500d080c841e00c02201101c185540b18440218401d480c0030748007001d0414007c082c007061545030020310841c8038070051401081a0f08540004d603040340016507030441044614010410000d00740d125070021140ca07410501201c001340204409d11a0003121140307030301100070040c000005202e02886820414003c1c40000800c0c49207181660f9000311533003140c005182840907519144131a034080010003019160f80d0b40c9207007140c2055540d9605980c4680014980400440301400024032450b5950104c005586010320b040100 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 609190161 1250 609188911 609188929
    0x102070f06031808030f0a0f0b1c0f0c15020c0d23120a03090618050a061a0907110f0c211c09030506010e010e0420030706050c011505090402 62
    0x180c10303c0030502d200c04021624502c042c600c00d80410707502c1a4149458881141500c00da245542041e80c00c0503107007512995840c0c4070114001105200c40450f605a003042c24900504200180002048a002240c0141618032080c403207010b5400701c0f2910301c0c00200740010984003036005008a4188020784005d00012200c0c8550b01861400302e41d201101c01c1c2131500799500c90110403000c26a103807082402c00080e800760b250382c1c1090705000c1c00d864000340c56560b00d881114000820345507555049404420b1400f850041d80400507221001a107000b440c0a8000c2e003041c036102c152849460000e0308450b00c000381c1d0107100c0b80c0c05800072035843e8140c4520002528103944180e00c500450450201807240701d48641c415041d295aa02503013440d41c14200e003052010b030040988079480400600c00c5107032010105030055401510680403503900001d00c261420400080c5a2501400d080015440d80c0038002d40707081104500200500c10314180c50080300c03c620b02c5500e030001d81000016001d880d00c6481 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 609191411 1250 609190161 609190181
    0x170a321e0604031b1b080c0a0801060b090d03020f0a0f0516061d0303040305160e07020a0b060607061d0304080d030603050a06090f08030a06090c0e130e0f1c030b0102070f0603 77
    0x4042600b0301d02c4d1541c17903174042c03064011603120391228802e600c0c14a8002c0020700100341d801c00800299003002481e0620707129a018060056410300f102d00f04042c8200010340f10545082e081c1c44241d00c10b850443d01d10880b10906031041c0c4a03008100d12004801898034080700c0d082e485042c40201c0e03550700d100c5071540a4040d0740c1c1c14003050000201040307040c001841c0e0b6400001004100c5401e01d4202d0021600107048407046500a5414000007401440307080c1d0444012505a9102e44030351500034044d1404140c1010140400b0b0480007040d10f000001e801510040710699407000f510660840840300c240c0305c041e1080d400303ca0f2100c086020b581c0113032566030240114841c1403c017900c42d0f00b020784c0103444400307006594407010450b4411502c10016103500d03d1801084c002d45850004042c04540525080d441e5590311844d11181c00c1005110380c20104242541e8030b403051002072400e0006014880b00202e410719800e151340f9880401e0344416144180c00b408203a5050140840c010304007102 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 609192661 1250 609191411 609191423
    0xb061216051b0d02011808031f03060c02011b0c030c0206030703140c0a08060409020d11030c15031f12060b0121050709170a321e0604031b 61
    0x800841c01d82c00ba120b4840c0b900d440d89008080100072030f1002400c60b0720541c00305000182d1028503400007500c04044907001103840391440700a10000340d40300c0325400145d00040c800b07440d11001c6103c45e901900225101060282d09081d4800250001d4844c0c1d2583c200050000d41d042c840200146480c0020b5900608545070014034048003440005152400751011760f602c280120b500c00c1c1c51548a07020380d511880a41d030a00c82c040c2070303601081060b0a440b0004190036503070f904445e11a1405c005540507040000d2603811a403034040401001c6920a6409800017484050b186914010101c0440116060b030715030000d0b8692240c0740d007002042428042410444104040d2000c0c1c81000d8040a4284c4241000507950501407409010050030b940003a64a140c850090000100302040b030340821900103000385290308000b0b9a803004800703805030103800b034194040d0400031040e00082001007070f48140401096121590708a40e503400017250b005002540403c143e002081051116060f03141c0700310 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 609193911 1250 609192661 609192667
    0xa02010503150405100807080d05040b092b0611210a0e0703140c0405090d0c081b03040f060503060a0312020a02030d0206150a0e0610091a09040b06121605 68
    0x5030000f002c2e5107041e101041c0b0050064006d1009030b405110200080405400911030208000fa0190641c041c51141c5a000c92006c200000c05440c2c200704040552041402c1c0e00400350451042d038024081a5000e66a242c40c00708800446661102281c2040c000d401c075000e40c1c4240010030a031000002800d000e44191600e0b514942d0140030051000654441d07640350180d1640000c540380750590040d00380f0f20403414841407219040011408401d408030717514000c2005a400c1c240b010040c030551580c54151082440484401c900c04400f0384240ca45845144007010707520342c812134a40c00140c03440f540c05046d4001c100000b4911007040846040e0900641307c0d554007903000642405620110a40941c0090040040c8404094a0303006540412544110814107201c2e50343c41d501401000380e4015007110210100300b83c00380c50154000c080507040348900b06000313050201f054101050050150303050984000b490b00d004800c7c1d90b4020b9950740404119603503184107041c0440c20003c0e4406001c010 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 609195161 1250 609193911 609193951
    0xf01090e01140c070f0b0a020d0b040b0a1e0e090102070302191106071502130302040e0d120c0c15020d0b0f0f0d21090812040803030703090501110a08040b090c030a02010503 76
    0x510300c16803081c11841c20049c1c84070603000700354050703420b280c141c0c0b84110700d0142040d2455030f40c94542802d0b10181000260380c0d1019842901c036942c115000441100b032100d080144040054000f07241c0c0314460303030940b03010b4043d41c4400500442d0321140100101c044141e0010142481c602611440d801403204540b003101c1c01208400326403100b024030702e06404006090042d42040d0240d200940d030f8040040a00307500c0d00e074004008558811240029903207440c800314001c1e2040c900d01c61030702e8010203c00440c0300d60343d010344e00070b41c0600d60205c3e0507410034011110620700030007800c41244001e411030b203506980d14100503000c2e06ca00300840b189014501582c0488900a40702c182c981c0c002c3d00c401c081d081c1003240d21454020904506064100b08000500030301c0008000d80340c00039424100494000c103189489805441c418850301380380c20002c6441035003a9482105240524025036041006484948105032a58800604540c2541c0000440e200551248000390b5001906c1c02d00c555041d004 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 609196411 1250 609195161 609195173
    0x12040f0f020d0303050610080106020c010c0f05070b0315030105060604030305030402031f020a0905062a07090903030b010f0c0201020627010906230105030a08030910050f01090e01140c070f 83
    0x15100903000656100100900c0c2c1c2000d0701f100781c0099480c14501295031400b50003e580b0001d031002a4104000c0d00d11100c1085020751110007440d510030103481d01030380c0f200e1004040e0741007101d66044804217090049841d003010f101e00c5001d400040d00c281c1c80c1504544043d03910340c4c80a04104d0301403180d010b840e010040543c413181c41c001c040203000360b0b56980d0100024160f8480d030b00441c0c440d50042051400d495000d90100b40004410f0f60409040b4041c0c084c13060908440e580520903442c1403002030b104050f45513119071008082605e071550b440280c000300702d4000b50306d00e00090141c0c0c080c50224841c1d41703103421130882c0f201d884e49082c0140d0b8000c031116425210070290840344107444507007901e00d107805014010606440c90f101756040c1c0d2f140c0380000b03070340f03112015024084060000114248a60502c1903c88110174440180840c0c2060683c05802c80401d22404501c43e280c655001c0f400d241c18007401d04400f2035034088084903120b84402058582c4903641c121101c600c040204000034507 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 609197661 1250 609196411 609196429
    0x9121507020115090209240d0c030b0117190e0a050f01060603060b030c03040b040602090303120907090e0715020c090c0414090112140f0703050a1712040f0f02 70
    0x3106a001080307040d002191402018240c1d04807520007801440000125180d02c018105a40d14822800100c0c03103010b0703d50041480b03030b0282841c205050080030408a50107801c001070440082e82e030800304841190f21803289400039100b64100d000f445c003c1000c1e0420035048140305480040c19903032800031995605141007080a1818110303512254208810783d0180b113100020a40104004e185140070024400e461100a10040c0204141000b250503c040c0b581611160400582202e545810300c000c4103a545400310781030310745485011800b1034489214003170040c41040c004000d041c0c460500c40c15000540341900d01e0030451103032401c004141eaa804201500846607245240c1e9142c1c20b011100b9095400ca07003202d07018038110001040503180d142c003504000c0d40c11000301204151182012800d00201421401c0b06204400001c400d1000115044001a105450041400002c0b54910446000f00c0c0d012412466070200081c01044410007520041807084140c02c100101990008081030 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 609198911 1250 609197661 609197671
    0xe1014090f061507031e0503010f030b0a060306050c07060b0103020901020a202805010309110d1a190e0606030606010f052104030f0206060f1203070b0906190908091215 74
    0x140500f0161000354000c6d440202042e807503150a514542c140f44000203184a14440240000c1ca0480082c190249a6000300040c546c08407040c400303401e0100300c1c0c01260b0000c80341642c406203044444030013903020b80300300c621022040e00540240c1c036407a2144036180940e80103103840000304107580c09640c0e48032a000c030310004903c00c903142e4051042030400300c80c81c03898002c2410f061505862002007506a00c0800803040100c030326010600c17031481d00000d6a03140a140161800c079000a0140300083e1f80311100321411050401c01582c8a441c501c540c2d00c8500b515a50f0305a040540420141d5101e2140c00040c242c5a040007132800d54002c0304010110305510440030074441c200d09010425034002501e61900d00307948020111801c0010025041e4182008281c0c0b29010140002c9815203081c81520280b5030013030170499051074070148076601c40004a610900060b03815100035500d15442c440d0707113184c41d08240500c3c2089200010302100e590480501c10b654420344000c224802090707001c00c2d12130 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 609200161 1250 609198911 609198917
    0x2030703050702060f25121b020c091005011103160f110103020c0d0503220b0103020429040b011b0c031202010c021c030204030c0e1014090f06150703 66
    0x510b00441d0003030401401802e1280034100010500c5074424091911031910b048000782c450b003111190905460b4039002d614030703440071424030701c6584640c08a044c940d00380d811a6025204a8030f203100400207800d41c11508014141941721090219502c100c822400813a05c50049030700d80484044410240002140201c80325600d141024003040a03005582c9500f80c4203090071750600046542068546180c030b010706042000120000b0700409e5016048480070842071075203001100c017800c018540000034002a4019402d00c0c0d00641c140a50003402e8500581240781e03c00306070510340400014016904203e41080b4079203080881c004902c10310880c205100b400d540070741614615120030310510f40d06c40c0c182035900d0003485095075500840e20080028000c14080784000350207a00360000e004039040a405038001441c0440c40080c0e0840c030502038000003440e540400d0381d41c004219044054034a030b50b0051104d1020a580d40d000c0c501407a041307a0014050901600302007800320f081d403c107400c15800 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 609201411 1250 609200161 609200171
    0x1801020f040b090a0b0c0a1a090d2d02070f0b040506070305090604030804080f0d260618330609010e0310020f07030e040903141c0218091005090a1a0402030703 70
    0x800a048d60f208449030b02003402c4080610300400798544400d0141c14070b005000254100e003a000e23854880c6d810a40c11214010200080c40c0c4600960303a104a0103000480c0c0742040700884c400c070000c002d4808403840100114580030185d41d0484294204808998004105010120016680501030300240020720b00400c2d14240a5035041c0c0342c5441100090700b405515080d03428031100102c10b905d00070030110800d80c0591503000110b0140220059500d89408903002032103022841403145050101c0a1220030854428034150440e10700d04004059500ca6401c0041c41d0b0954000e0300e846d038080f070000701030712840040552a00180e80c80382d80b00600000d0009014410190004078000f1841d80a035810801a1000c2e034015003a1007400c44030850b48940818042da843c1020210200b007405000c005544554060000070700e0401484030300c40c032034070f06000020300c00400e51520300211903008101100c107403655003000c00103080714000c4655100851003000d9150310b8a00007140516916600090 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 609202661 1250 609201411 609201413
    0x40303051809010e0109180218010f06080108030a0f170103062003100e040213140a061409160c0218010515040308030411120f061801020f040b090a0b0c0a 68
    0x142081c1045440b03994810018050034105000140c155001000006003035007a4000c40703201300501981c02940070b5119258464017004031560716049a03100020020340f1034481005407180c0c002400b410b1041d510a0240c44501442442c0940b4145260304202c0740076101c0800340000200c0981040c1e94541c6c44900380301842c2120354101c0700c0160503558480c1503042546501901d50345520a221000c030705a404a0250b540f81c2000e20f81440ca00c0070100404860000c0d503403101c0c80700700c4440ca107031860010300142a02052200f119000c5000f840d0000940c0d0f840350120f480326007480503c0410004000150045c0ca886040188101281004102541c03526040046103103103128080400b213014402040018030f6201a40e4020361b000c52201c09260343ca00101782b80b00384150388010144100c10308840041c1003c1003030307401030304503603890010700d00c0a080c043d00340d02c41d25000e1882c00604100801410040c3e06c003030803602c4801002e132280583c1e5007101c10551f400034000c1443d40d030001da2070b0300 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 609203911 1250 609202661 609202687
    0xe15130e09070302032116060b01020606100f140c0f0105040510020c070b090d0b01030b06041a0310020c01021306050d06150503040204020307031d0706090806091e030f04030305 78
    0x2036000400c400200b10340e82c01d42e400b007601e6452000c1840484c116007440c41c000d8500040503104090300ca02d5130340011120506003e4094018444081d015028100c08154541010486406d00c010180c41e0f100d520403448908464040300034616542c82c560030b020f1543ca6103020700400110058100010496081c42d017029400e24614400b0b00d40700901c10001102907000100303804040f505c2035044280c84200c40c1d40440c4504c1a40280107220300301070400401040310541885008034000d0300c0400018000f18078944401510559455142d48881481000e045c5950000c0001da02c070480058201400303548218007004050b02f217280411000b058003003802045200b0345005100c50104400c440e1070f410009001c5110141010b4003991300080003d0045000380c1004c42411790315252081c3c03502401c0081030300c4584600070840014050340c0001103030072000403014040c000712409440d1602c20300c0c02008000202500c0c0c03000740e010038840c115808070080050401540280c032507503030319401041a0 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 609205161 1250 609203911 609203939
    0x120204120308090318010f03020f0a0903151509090201020a050d11160506072a1e0e09060c07020102120c060f06090709050f01050403200109240e1513 66
    0x91541c0c01480010315a80c00205c14490300c441c05c0c01c0c219003468180d03808602a214405445210071800114128100d6010f618001102e00400c2030040c10170100080d038003079546403080ca41000200600901c40350001da400304220610500480e0f070320f200d09a80310f500349124415a10042082810021000300c000d100d0402a6843c407003d03100d01504042c0042c02600490784040c00b03109400c0c000708410001f07c05041e0103903a04021009016503a150340b281004d0081c0b80d480003540809134006031201d12804034900035181c200c080c10301940c4452030740c20540c202c8201a41188515024030030100803010050109034510400b900e140e20302940e4605408001411990050030000c0800c544564855240010f4840449100c07408500090040780e0074051900033400d070142c004041c008031440785240501e11042070300da00800998880c042d48003416400380351240304005010040a1620440e1010f107202402404016500b0242c41c803d055600060000d04150964180a2044038810404 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 609206411 1250 609205161 609205171
    0x1305190e03070b07090812131d090111040f0b030a020906031e070e01051611060a020c1002010908070b060a03060908090a050a0602030a1119290f0408070201120204120308 75
    0x210119040c07521303c49960311007200d4004a061500400c1d284e00c182d044411680c0101002064107592109e03100b0100982a002c0d2000f90481d0b00c0d20f143c0e03128815255054804413807903094100031316450325079075402d243c1c401070030100e00c298204009803d03a0b032000051405081403e442507209203071203080c0000e49101808030b00c01d1001c650007a10643c3c2c0c2c00012034020b411070342061850000326140c46080b00408986c090340c44030000c00c200d4440d03030340011152520700c1e0854444203c1c0c4070344001030b402c03611442c1d80a00142010401000072665181c900c5401c0300010b80200c038081e6694680b0f8007102c0070040111120840098490558903099182002629085641207032091800901075500c0c404c4c9005c800a020303000f0010052840d06210700b40070100b90443c1d04003a010180340c0722300100554081c810301d40c111701e048600801510400d55201d0060400c034000582c6a544403841c4a8000c101c0403410844081190066a80300d400a44001d00e070108030700c0e0000c0b40c2458090441e5400900d = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 609207661 1250 609206411 609206417
    0xc1707030807090e041707020109090606020a021e0904030c03050c01020d06051f120b010e10020a0c080d12023001060e0315060d0203070b0307090e070e1305190e03070b07 75
    0x2041c007000c106180e20b104e5030101b4001c1d806a07100807071b100580e0301401c59030013585a20b2030400b0004001d5000301d41c07100b029100302d170428a41c0b03500300c52252502c034150403000d0700440003000080000340500750391910b06010b4284075042c07124002400703081e64044131948010a849580030082ca0070708460060000c11000d01c07403a10380d24040801000c40a19188180c4815100c1c1c000d20880e034003a0200020114003e000c00494024070040a50390b0400307550120740d007400218002524100101d034000c100c110a075902540488001403240103500007004000507001c2c0d0220f1030401003062a41845100b55031180398000d503242a101610200030041c102e8000d80240c5070100f5620200300340d6550104084a81c0c00e10040c050000c0392504800d078201c0312907204000240103807140c200f40414210f40300e03905e04071210340d80c00500f29048800b2118058000e1950b04583c803048080b60031003540801940c402c242d01c0c580800d00d000c20b451500c54988a1900700241ca075062003504813040e036200040781 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 609208911 1250 609207661 609207689
    0x7020a081908030a18060902180405030d0c032a02010c032f0f0d050609060a12031202090a0b0c060c030c040b0306031e0c0a08010e0309010c170703080709 68
    0xc5058100e00c8249402401c00c03500100042c190001c5034000c80c0c44103440240305e864644107103060350050009801c242c0c403e040b0304c1e4104100040032645503100d50342c071402541c200103080b45614081c000c4243d020301855200d5034401c5500303440c00700c60105074041d603540404190345600080c0c21a509580000300305814401c00008901c09814105a2680e4841d07400c504141041580351517405159040a52020009800030001d41c2ca500440e0044204942e00c4680e86c441c00100101c50a040c41400f00d905c2c4d010181d0000710740100d04044011030300d00805807900f142900040c401c0009500584d203100004600041079500400800390301000d1300c8007540c034500703007611106400e02942c411a0811000000062040c1c0c80c24012005401e07000003500360041c100c40e100c640c54034008199140a42c0010300c000540b240140200f0308001340003c06946421401d400443d28031031500425958820f034241c81d1402004250300601100d4066641c1040c20f0030481d07001000b048041d84807000c010444 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 609210161 1250 609208911 609208933
    0x30b040503090a0b0f09060d0f02040e04290705071b0801090606050a0321020703150b030f0109031d150301062a0803060f01030b03010603080309010b030a050c01080403170c07020a08 80
    0x322040741c402d40022100140c65503803100c9940081c2805095101409e8000b10380001c103034859200d4140540d200d441600e420a035109042e0b847c101c01400d000340c00103007200c0454022401440105001c80c055200158651024000c0303040007611603000c1a590ba40d203184003414420144030364005032034211010b69002e0b16581f120500852a80d07400002008101c0c6411109802000341e4001581e100207151180000d002020004050201d8060b0080c001d22102503000e04e4107204000329161f258466000c2d00e41241603600c96050041c80e01500507480c202d03144403406150001d10300920150703039140000442986044101846098454517030465452004001a5800305495102c801650511844422840124050305010707400d02d0305940f8182c4040b0621a001005500c18442c0c84024800c070b0882c64241542c0d50349002d8060a55008040c0c840b12940c81800095007290180c42c0c180d80c130440004021454900548030201115400180c0300214102440524018104040580082a25 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 609211411 1250 609210161 609210187
    0x1060614040501320405120d17060a0e0f06030d08012702160f1e0b04231608060a090b0a0c021c051803010605100c0c030b040503090a0b 60
    0x41d40100ca06010203c13800343c1c0e5490a07821202091a28400051070f080410a240311007075100e80580d40c02081e01d8458440c8503000005e4a0740da502456442161615203d010407103442c8020340050350100002c400042e500b016141400d0290603040c103210f03c075052038802c040c0b90905050f518400c0c05854401000301c01580864000c02511030409810b12a8020003840000c0c41014524008800588003c03402d01104014101801e48500c150f60f510b20b6556050340c2070032217400001080c060300140090000f4520380035141c48031031000c079541ca20b020080e18103070910f2040c00d0201d40b418520b02080080c50000c0244c1504642044002c000240d0395071145118003000421507001c40c0e0f101d00b00300c0c852510800040c8001841c0c4001090b01040c52a07004003e5442150301c009a03524074941c49429240611980c0c0031200010803100c5001c541080c2551503403880c9000341d402145d40d03880080402d03000000c10303201c2d07485000503643c3c4000140412505000540199216440920012080c842 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 609212661 1250 609211411 609211417
    0x1c060305030f030a0603080f0a030b030303010819020f1f0e06160201030e0703060c050a090f061e05070f0f021206010f0605070804090c09031208090613061506020c0301060614 77
    0x700d0742c10990740e240e484400c02c3c0040e1603164001003020000050b045241d000c1103010b4070011015a0302400700e0040b4800300359030ba02080c000c15070380d5041040d05008403480340388840c881c1c501c082c000c06002c50030140001d50030040d40c0e01a1143ca200f003c03841c141d40390300c801d8102803260211405810002264040840d03a10b169000034180b40d40c0d0206075030802000c20504000703543c04030061007065407050008166070002c2c403607100400ca2120f008034580348440c0e24482514035558450a120303801c0e0315a155508101c001500510804116040200305611540c0e542c19024050800004500784180b0641088503c01016143c00c402c005000d40c030103c01a94085424610305183c1702c01d45410030071200d110711390052002c0340c0f8044030171919581000300d0500b228000d1111003070071240c2c1e00050b070741800201c8819202d5041030001030f040e04200807003080030901903000050000340b031000c1a4030034061504190b000d80d1060100c22032502e000d000e05000f81071940707084c40305009420407007030081c0 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 609213911 1250 609212661 609212677
    0x6070e040b0319110a0f0308031501051b010603021c021f0e090f0f060901080d0309030c02090403023304020d0201170f0403032009041d10021c06030503 67
    0x180c0303411411155a9007044012201c50303c500b07104520441500c0c00e03c154454040c0918082c16210710000b503200e500300c81c2e0744103e03a04541101e01c1c5a40380300400d03007480c5010800c181032145c144124425031603c1c980100d0150b100000015085045004000141000c022a21051800c60010400603141c00e00c541e40c016603500700d14005141c8c0031000307903000303a40e40d86016040400001000001407082c004c01d80122044008041562184014054108400d0107000312a0b40324000e00c900c6107100c0e0340084441030203450070302d900f90810760000303404170011380e03007940143d2002c05460030181d0040b19103034005d0a080c0c1140704c03455176060420100c120041c0301902c104164a0300324207590042c940501448403e2507045a189003800302030380208403e88040c1c1c002807130721080032222010750207800d120041c540120ba0500a110f02004042d10741d03044c801c03030300410071808035081510400104020204074071026807904000340c0107003240c2002502d203e000c01c0c1000000c201103000401110810 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 609215161 1250 609213911 609213919
    0x90b0c0f16061d06060a0905071706031204060f1d0d17040e040507060e010503060f0f1306060507031112040b0f0403120e01030c14090d0c08100207050d0206070e 71
    0x44203090030b040c0c00404440c038100780c42d0400c420342102c215501154103440307500119507460980741c0300d02c081c00c00c480b000c030b80360f10220301b035180d00b0401c60305c40200103030340080300a08882036014541802d809a406c5079101d00040354141c20400e030200d4021800c003025803100342d04c0c888240040000140030003000031010741015188140070400c107900c00300b1034001c0e14496070101c0490401d45820f5036941c02d988200e100007015110340042940c481c6003100e024401c02898040054504402c0140d04020522055480a00d8000c80032085489024000c000c19060311510f0300c520407810007030280043c10241418641100604031044608001900c00341c80c00c0001c0c0a0301c400c58043e40c280c0b41c1c8501d0f0005022071a058662896940d4810815600950280d03003e1004000300803042d58250002044001640002d001e0318489040000111515a010300da0408004e60381d42e02c0e16040002541184500b2500040c494003030040030481c04512041520003000180f410010040c00002800d1941e482 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 609216411 1250 609215161 609215197
    0xa0f0b04030201180b150d050a080301050a0b1305100c1b17010207081b1f020301030312020a080703020901030609150602011112150f21070b0702060f0c0a0c09090b0c0f 74
    0x1082d118091f919100c1c42e4041d0440d00d8052507420f1201150f0001d10500c0d216030300c08100803030882010707016074210300060280c0d805224103210400c24030080e0320f4585800c00c03a419640c500402c040c0b50152441c501d04219401d2a0f60034030030b403104400320001d80d40500368010030051000840580407283c40b50065840c00c1e03106442c030604503080c0800315400c10042043d0658451860519034001c5040b2846602c401008642800c50b45059008000304030020070005000a030340540240c0052061901c140340c0005d403241c486503004201c440714030040700004030210381441800e40920886580c01d24040c3c40701c0c02c042040d6000b04909500901001d004028007001100940301c840c900d420364240280b000410b40d94200104c2085580e01105c2d004520902000050101d900701c100e403040d5801030802464070701c0000580350542d001300b24007074079031094282d0400810380005203c0003401c0c01e0f4070003003602402c6017490080000080c11040d0021020805d888180031001c4c221140701004120000c0 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 609217661 1250 609216411 609216451
    0xe01110909090a0506071e0f0225050a06080414150106051c0e0615010f0e04020919061d010e0907030e0f0105070f03050f041109090a0f0b04030201180b 67
    0x30400c0f455100050440c41400c0501c240c03140c20041c0c501030034072000e496614010411704100c410001d14011031001d40c001c4241000c0707009000f0000e031070f03149036500206022561040420404034103688640006050541400100486000244c502840c418010003c450034150b8100b15001c0600c1a5414000c000800c2d460005880d00c2c14031070b03d040014100710703104840c501c480d11404200c0342c0d80c0700c0541d506513507940356020fa9070400251400d603484403102d01a1400b800001e5011b6141c1680c030480041048900380c02120b0800c02409003550740c101e00c035615507102c02014401301d0394079051049031050180252a4042002c4d8405002d01d00401c4000c01050458180900c01c100030055501300802c00500329004200ea20702c2c103201c0d5400300a030f903030341d012100c8840c0c106540080c510007044c40d6001c000d1a001c080076070414803000946011201d02c1d0368000910f04502d500b290780d0700e03014041006068080c896120009a900301d00d46580c80d041e44c81c26815a40100f1142c80b94400c2a8080 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 609218911 1250 609217661 609217663
    0xa050a02101812180b0f04080d09030b0109141902190e1003020c0706051b160306050114090f18101409120a1d0d0f0302010e0111090909 60
    0xc0072042040004000c41c81401461aa0401480c581a10030404000880c002c1520070160050460141044481100d052001051156204030032241c0030b20380901010810880501040702d901165840704007050b840c618040b0b070005030580c440c1141300e1070710100f0b030644000c02186503800b8545040c20020600356100700070080c019402c441411407c0010b01995107a0406290044580102c600301e9004110100840680c40b40600003041740c0c01c9000b04110f12405030001e0611441c0c0c2c08104449421000a418580201c1001c20601d50301c5010007081400464402c0b02d014000030111aa01c0b5614180419008c0c00c02402d00c518030300310680096030956880c481108900100c0f0140c80c0c0c20f211500ca1003000e00441c140b01e941d50070003d030210710030450005260718100e400c0508070b41040301d0540305842d0200000214040080058070a503aa036540d400d00c3c0160504c1901072400300303415820000d007190403000310070010f03030b01d440d00ca13141816405058503000081241d00c100e0720f0307491307040c01 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 609220161 1250 609218911 609218923
    0x70c0b090a050102040b132c04030c0b07030507020c10020a080702010c080309060703060909241b080a0609050405100c03110c01090c1e171e030a18050604061b021507050c040605060a050a02 83
    0x607080cc0300400600407000e0340340d0042c0d806105507a00b151030103034441c000c000780604140c42039005a4005560300c40040c410a0142042c940141840c039840d0f85592140111a401190388079601e0b0001001c10120b6501442280e0103810008400c010924590751120644003442080c40820b041007854066400700e81d0f000b2100d101c03400ca000414052101c41d01616103801510319019150400380007080c46207040c46880d22854021008140704044191031800910210405900301074503060742c84c111a106500030030540382803034000210103843d400d0034445414660041c078400f48544412020307446040a038003003900d6082110424010041481915141c043d2400d02142d01202812a10000340032002c0d2140c8841501c40c5503c4010100c1e004c0c2020109010f585c0d4040402d0205024a521400c0703000c9882ca60700d4200c8152101540010b016000e00012445071200700040704000c1082c240700030400b00100740c03400e0141c241030000090700d0740283c2c1783d2030342000804646000c895108000d1 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 609221411 1250 609220161 609220163
    0xf0b0915040906141f14090a0e04200108151804080403021306050105120703140a05011806080c1c0b010f0e0c03070c0b090a050102040b132c04030c 65
    0x14a59490b660028600074081d14804d90b030404120300c114070141d0034412800c8040c5828030300c9400b40e4108800082d1440d845499901c02460814018019952101100b00018110200d102c2c012440c1030725105410a1440e10381c003002010301c00c8810b00698000100f2030300107030140348204001220318081021040b03810b0b1265810030075141480140091600148280e0340251440d080329100d4910f00c2c0144da0040c0b00d11400203608000012000100308030715500950103280224440c80e81c0e42804481010549020740380c00e035203900400070880561400105100c0300c0000784050f5291032411034461880d07100c0b03107005081044020410980d0800151411944182404a556150080c1040a68507409801180f040c900041a036200c130020680744580603030b41d14421042000e9a6400031600050f01d50342c054130614402e900011000c1c006807000d4648401c08a07110503950305da001e09000d00e580a04265803c010103c41480d200b00c446105901001003040310326215850216840d0004901c = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 609222661 1250 609221411 609221449
    0x5190c020607080603252c070c17031e1506160302030f1c18020d020409030e031f0501060c1505190f0902031e0705090405010902040203040524010f0b09 67
    0x1c0d107050006444c041b14003d03142180f101e1303183ca00300761040001083c140511114500401c0002a00403480307a000700100a204030910741181400c110700d8a001d0300161060040d81e0300300c0c0b40c014451101c00380c085134050080c8181d400d20b02c8000340407c61511803a0654500308c155075002c41c0606000b00216100e60603c03400440d940c843c40d00c8d00003107646c04241d13800307c014208408114408400315040d03404980040c40c45142c10f0703850782000003c1030406001c900b40100004202c0d81e642d01444442d1284009132003003000a401c0e81c0c007000490720140c0101e0140661a944080460f1042081c01c0c400f124031000000c032605c840c3c244d4031101742d607111280344032410914100b2200040c0c1e000340d05414800d80450b142540c40202035204c4164000701040c1c1e41c2d1006008111503c0c213500ea09401501a0000081140e2940c020a060f40c0c0f00700e81c1030f100c1e07900c51460301e1441c0a0b01c000155035081503400d010806e50422600700d01c1d0441c03d04c9403070719524020031003200a603074400115912455660b = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 609223911 1250 609222661 609222703
    0x90315010f0f0801021207050d0f0617070e09060402101407080c010c081603090305040506030f0f07051c2403051b0406030210032a0305190c020607080603 68
    0x30801e00400025030244818500141c100010310002c14026070305070f541400505084d0b0b0b503400740d0440b125000002079401d8141c46d00c804500411180c420300000e02072006d10340105e41281c40c1c40d0351504405a020440b10085002048400355000c10b440b030f0440c0d41119080c50010002d803088400c6460b50326603a103040781c000344420170028a8070040000c0751541000f4490302c030480f902914550422150480c18840f09192110301c00e109130b20040200d8842d080841c20aa03cad1030200700c454000711200340300d06500d101441207003140b50355882d80c000310901e00240b0b000002d094140076440e54840710002c150f151007400700500c030b81c641220102d58004507850300c82656030624542c0c0d800c880e6110b490034011800044410b0074540aa1010389401814892651342041c40440c014254000d403a8411000e400d406440301c1810100c8900900203690081140c3c00c0c90300400b2000c1d212644031b010380a01d4508140c3c150354010450340c0d8003c405044c051900d40c0d40e5004039080104091990326155500 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 609225161 1250 609223911 609223919
    0x1a030606150c0303271c03151e09061e0902070c030b04030905010816080411030102160c150504080a15020c0703030201140109050103031d0105040302060706140a02030709030809031501 81
    0x781051000740078034040141e1171142004a00d03a142e6100d010741815001000c5212101540681c015910450a007841c030a00141d4413994030306034580039000001d00003140102041007103158040e25010340000c0c3c0c82040c8041d17025540001820311480f5080e80d681d004074090050004912101000315000420100740c1d2a0900d801050110b031409410302181c1540c1c0894003182e000c10300c1d00c9145602d40c0380d50304980c0f180c0e00d90412031300c000d464040d030564003008014030082c880c2040b1041a4441e0050508003820088040706d81c48050075a401000400d220403c414500010596103150704410520340d96a54081100301901c18014440e0407032017510400001c16034154880030695030180082445640c03140d1452041e00c000784409400138000320b941e03010a40301030458540c1480c05042541c44c080d520b034040717403058002c040203640440d42c41880c490101620481c0d2640718102c09400c51540c58091405010b00143d40809040c014010640a14903102000b1118404001e1802040b0b2981c1d1 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 609226411 1250 609225161 609225181
    0x4030e0d0b1e07080c07060e0a020d03110c0603060d0605090c04181103010e1515091504180c1509031a16020a050706050f0d0e0d02011a030606150c0303 67
    0x102c040c00580312101040003d2140380704c0c0001602409000058500d0184140c40d01e4024000610200c20f040c02414076110060343e6012181518610944608030701c10700484403103051440c0e80c502180104001c2041180030703526892440d000c20342c03107400000c1c83e0f2a041503080c6400d81d00e0703031100c3d001480c01c408450040785402c540b0819622601404024618101c2414245c504841200c500d50b400100c1e6440d07240318031400c86601982c007640c4071150181100000c0c0e004141030f50b00021580402d2450541800c2034000e03288032a2820880748105161039039000c54054280c854224494440c4403005240380c415160b004c000e50700403816070b840c01083c11f0001034000058661850090070020419a80c1d03002040703038102103400a000c4c0031660310700007043d1002c2e48126059040b40e14100a0700448400501c01d1400204842d0014840398002180190840c4c0c00c1c140e81440006200c0c416410700e13940026a15803024081c7e41c00d002074041d400650289000d18241981e1500001c000c0004100c8 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 609227661 1250 609226411 609226441
    0x12010902090106051b061008070b090603041e0501020d050a0c1803080a030605061803011d10090204023109140c0c0a050d0203070209130302060604050c09280b03010e04030e0d0b 78
    0x1c909002d071074105036144ac448100344078008849030481c606000150100e4801d92a040452680d040154044d00305a0741d10303402ca900401e01e0564550ba50300500540d0305092081c4200003140f41411048003d25041c1c1104804032840010401c00c0005141c4458902c80c0d0400340042c400600015101d10705401821003150703e50f101c0d1400303986480d20441c44d07071101c50001c0c580c02c603820010f0082d12000c11003a40c090001503005a80041c3c007044402050103401c041402210540524074003502e0403201b100e031103c4101da10031860242800c4010070030394007071110ba40c0c2101c482d07007159079903000360003405040400c40e481c054164041d04400d40b0a894011000b00000b030b100701c400c2d1440f81d0780d2115044e00c0d042c1c0408090010703804240000c09600b86035008a401170405040e180c01d00e070b48170000650340c003000040000e115400507a900320700c1445000302e41c0a4444041403a0840d03050000c01280d200c1d0062000d4100110004450b4254450404081d02e50303400c501c0710070152406445001c8004 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 609228911 1250 609227661 609227669
    0x60e010c1101110d080115020607123b060a29131515020d0504090b0d0221011d0d050f0f0d0207020f01090308031b040f08060612010902090106051b0610 67
    0x10000c8070b03000081e07102041c41481101a030302c60a508110780080c040040c0044ce83d11040019a605120340440c4940400c24000050f00514001d80100c1480c26003406009040000241e040030303240d050705031005c0c4490f410414201b0440e0a400000f1000034020384186a0386000759113400862805414103103081410f44010b0380030401c42c0c800301071082703030b80d1443c040c49000028814042440040116044100711040045ca91510b1010503000550400d804807008205107001c45205640960300307014150742c1d0180282000e42030200480c42c02c0e101c0301c00c800781c80c040103400518408401c0d05a030544d000e000400c0340f2945c0b81d1503421102002503110724001d034800d41125800d17540940c442e8440000740c0354040d8896055031142c00390707441d01c484c1d500000c441c1aa000e000224001c1304070100700d0700a120403002041d090801c1c0060006114130381b82d201100b41d04202c00e000240e103503d41c2250448460303240c030581ea0144494004408550310b80442c5c020f01524060001501d82d18214209403 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 609230161 1250 609228911 609228929
    0x6030406050f09160311040905012d050c19021203040615050301023604020c010914060108070e07030b090709060f030b0904110402040509010303030501090501060e010c1101110d0801 80
    0x507440d043c2d025035a8a0418044814003680154140006048042c0320300f07a11001503c082866003035030383c5041c00e440f08600c1003000a030f0380c1166095164880c680b482c030380d00b0110310b0410050600b86010040c5100d014450f42c80005508919449907100300031001c501000c41c40d80d5500d0f41412305d01320024100250484c428494080c201146514041c421205001c0310310000700040c4c0c0d00e081980e5a4005404d100000301c04880300640d0440d182c3d40010308040f6510000001c21080b18500090300c0c15041003440807079070117040148124400080c1407000c0d99044010001e07032381d94a40c1d044014020000750103030000c03048014840c4494210301041d043da507080d01d4a905420580c107040701110210041285c2c04200c0300041004034541c5005280c900c100540b001d4649911a4041051000281d00890000b6650001048441140d202c0c3d20701501440c039122524000ca980000c00e4100a160702602000c1d100c0f1031080b41da03018003410400a0544c3c0280c0c0c04400d203104010300308a0092041c0c1c449 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 609231411 1250 609230161 609230191
    0x70b0408070b011403032205030708030903011109010207120807020409030302090909160e04231e07050112050a0e0d20010e031209010e0102041511010c05160602090603040605 77
    0x12030000e03c084e481c0608060021424591039034254000240e43d290b204500102000020400341ca052140070087c0c421000190794800e0240c080c513003151109641e4080680c0b060100c990b05a0f80460442c04651030450141c020407414100b80d6161310403010000d60003464041030004054241c2c002e04190f034002c49090400d556160142500c403400d484c0c02c2040c0146141c01407112140e00021030703800c20702032001802c0c00550940301c40e0f09805414850802940706101c1c07140d0400d02c41c038580b0070040000019103041890407001803c03102030740c2507450700140c80f000015406070595202c00600d0019400b2030f40f40d099211009004001c6901010900c1043c54031046203009050003400101c03c09040110f01c0d112011680e40c607001c402605400481d502e84842507802e013801d00180000d00718048110b0b0082200c010301a1600100859035141641060b40e0804201c0c0c00405a41842c0c2c424800504141c0040c604040241f20b201802503100c2004400c0c08107000e0240d1000f80305019009403829 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 609232661 1250 609231411 609231419
    0x7030801062007092408071707030c09021b1510050619050702010c120e01033b0a15091406040b040f060b1215220204050705070b0408070b01 62
    0x80300d50880001940650f0040800700101a483d44c8001c5408000d94021616403403196100120202c50303a0045555520a51040c0402281c2c10025104580044000c050561440d034861082c1841403080f41a42540400c1c0d01c040e95440c15850740c40c074001c80094452000c003104810384444400c0c0c0322784014404200e07003c40c4c503007808c500f200c1c14102c00095261900025020407111a40304c00780480c10400c403c491400043d40104a00c03403806144e40b1821a050b454000040885001d03040401038602c42c0d1808210035031011048001d8450554005400741180c0310001c1d24106684c1c0c00204a9826202d039403030442550303802103140c1c1e40b03c0c0c445010405071a0521a5450b04180c4001d0500c4e1108000708000650402070051894032500c070200e4400c003400009960032440c203190300c4258200310a8680d402003524206075000340e007107488007a0000c0030212900030071440c2c000240565910804212400c0c002e00c240c0d646503030302c849020035600d0981740030a070755001494200e44078100400086 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 609233911 1250 609232661 609232697
    0xf170a1d2a0f03190c030b0a06032108060f061e030a0c030c050409051306050f07020f0609070302012616020c011b08030402040e102f030103150b060703080106 70
    0x3248000005008080503480781400044050081c0c4e0b00715a2500c1c2c0e040000005030350281c0c064403404140f540014464918181a5a1146070b070800580e0600c4100094800d030760400d040a400040999900c0c6150720130001007500c902ca11b003d1030031103030011320000305428070440046208408047d824800320180103815402d45403000b194402040d42440300348110700e5190310940c2d2005118200005a079450345801d42101c100b070710b07098280304c08072041001c92501003045400565140d0010141840e05521403a03c0e443c00340802410021084100b8401d15104240003403100a1202041c10500b4030302c04001281044203100360143c010900b040d01e49600460004003001d40c9061188081d5049a554401039800140f0803a4450303a07552050f000c0321003c006550828034020b02c00281e1301601010307903c0300843c104102e03a00d081c046c801507009550210a60f41125800700150801d030080982c40e0b409882e180e03008580005001c50450107250b0b1010072581210340c991100344c076006503402c0e08c0d = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 609235161 1250 609233911 609233929
    0xe070b070b0712150608041a0c030c0a030603060606082502190203031603180b07021c0f05030c01020a0305090c01090e0a020423010f170a1d2a 63
    0x50160010000001c10791400307000c2100003c4085140002c0c41d004003481c0d0009504c054114100041000b02044204038010079182510113002a82610780d15100c007880c10248030041c0314424020340803a050364581c8c02a0000d04c00746511110a1243ca07031a04001448120100c51012220381500b6580300d0b5801c0c0c00910705036000ca558050540d80d2a80862110500c4032154126054441040551103c1d069480e080c40503038840d135a100031003540030400015001c201e4001c08082c500c10080344005994003100042041400d60030302c9000885d50a020300d0041c442d51000d495804005140081c0910650007400d0a1140e0f48040200352540b40c40f107076461847d00841404107030400c0050014140c5400380c0c0f54005008a0058a400d8441d1302003501c030503180d1035500709202e003803007100402c0d0b82203040c0d002c000c40e02d403a0142d01040c100c0d41905100d94007404410401c3e540302e648c0601c46807a881a402c40f032607600704880014069104816041003001c07005109988110851031b0170b46400112 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 609236411 1250 609235161 609235163
    0x4030201180b04020904170d0b2812110a120b10051c08090a181103190903051b0c0a1e0603020306061303030c0b0a02030f070518090a0e070b07 63
    0x1040681eaa260b00384040301741c01500944488020300d00281041210500410003a140040045071650001c0d09014200415045002d420030071007041d8200b070b4000e85040c000300d0f1b04400002d445e0340d4090515402e10344206410036040342280b040403512844802d0010200c0b442541065800c0d601d54107101d0381d40c0614000c0c50340c0500e185820001401010416983d25806110081d10b4142851300081c0740b54680c1d8449504001c84280d8188460220b03c00d801500c90b410040925500d41000c0b031580d2520803450b0506043d5494648200303252040e0300fa0f50031803000100400c80721990000c40c540c1c3d100380001d1280b0410510b5400703c0c5030303640d02001904004980075405002d0b41001d409501035000140b405800010a0003d61142c1d07410025020081d4041d031602c2e0300307015030b80c101900908001003d00e0104c40c010070510007041e440c5180d10f41d00044c2e6203829031f1030b03d078a400c5081c02c4041c2c0790b0b00c0c0c40e48409103c0034000a15800c0e401001050b2015007250000396a40b046241c0ca40501c0d20 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 609237661 1250 609236411 609236423
    0x15050c09010c05011401060c0605100503030a050f0d020313150e100209030c060406090e010f030302031e12090c0a050906030604020103050709080a11040f0213031205070c08060403020118 82
    0x600c00465028104065505102e5000802d44000c00c440417191200c00740d01400003d01d011520000348500c500c5040c4c2c100070f241c80c00036007040c10308c000b2075580c7c841c031450a410020000340d581d001aa644041e03420000450106554030700f858580c25800c2075840400f500e803000201c2d07000400302c02c0c174480e0714440350b1000701811191034440c07100402904460045078260050b040404d41650ba6030300100301070005a283c4d07500d060704000701c907500c1d254141c121540516800c0070900c0402e4001048d1440da05080035041440540c1c00c035040880d000300d40c440300404a144080c400c40080118142035002400d91f5441e81442e070351420070010890564505070140c200c0c0c004a070155100350030080d030003105c038108800155900c15249161841078201034508240c1032000e0b6115240600031290000d00c44042981400c4059100b2030920095110080c203040361f4020300d640f518004c1c801d0700d02c0503400c401c17504000c556408907242c55a00454007280154646000103030404891000e9440e82da800c10 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 609238911 1250 609237661 609237667
    0x2010b040f0912030f0207080301120308060d0302152203110606010c02061206040216030e1507080d0c020c03070303030b030601090204120b070c151506021f1a0909070315050c 77
    0x443c0590003480b0002e03804402c03913001c02500380450220b100950003410300f070f6003801c5070a0280c2801001654050410391007540d00c40c404801081d400101c0240c45414000e810010742c4480651191080880000c0f405130100f20740001d0505410002f620011449001968043c0d5519001100c0b84005540025840135060088050091059003840d0388400090030040c504217145407400c2100c1e140c20350841c0040c0c0200d03244044c0d800c0000700b030071740c007120015a5070500d6040d65038140c2074000e2042d40000035035a40a040032040c402c104840c00d030f45024080d500700d50340300d00f00140907118070038100b4040c1c0b10b00b17400062030400714422541201c9509e01404e0036810507507240c8c048082c019121104011411440c20f021a44001c10804c2c821840180058040e20725505890200210350148095400804800d40c03050f500c5407005204117080d45000a5155884180040581c00d05602c1500082201c04100d281c04000400710260f031302840d1400d42c03640841c0d12000035501d08a80d118500300e402c0c = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 609240161 1250 609238911 609238943
    0x10b0d060e0705180115030b0108040305070c0b0f0408192307051519110d0f121506020f120d0f09060e07060311041508180d02010b040f09 61
    0x968010414584140255010250307603000003070751300c00100820400409224010030081031403206042d544c01142c10144021003002d000030703180403401000a024480001048420400b00c90003c0024060b0811020740754801c54206074000d4000e4050580710f40b0a244465661035620b48441034440d622404030361a00c403081e10600c0109010804c401180c1c0f003041c4001ca0103079034040b280840c0d400308247d03c98030355082000c001c04680000c48004144100740e000c210819501080c0440c0d4420103040c103103502081034038203e58081c25410303075860003480c02244104c2044a40507201c102c1e02150700322419102c06215064844000100203803042c80c04002c071078101c95090b0064031076015104c1002070200e510b511a0400e82c1e441d004840f5558201c1c0030b0601580f6058405c2d90840400c9640d1941010304141c0380c100d400c110150518117220f08403001804003d100340c8011250464a01a210804130515029000c0c111701813074244600e0030482042c4059030303244501c0103144e4111121b20510316003 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 609241411 1250 609240161 609240173
    0x4150c0c02033a0c120c0b160c020409050f0105010b03071d0d0203031602040f0608031b011b0216060f0806150c0f032a100e01180311010e010b0d 64
    0x21441c000f1010740498842c8500082c50508440324601598035651308130300f2140742c9181c10015039005001030000306008840482e001640c000d51240d6120001c1c92400c404c600c0a0700d04030070301c05000394003604100980b010040301084003904a140b01c0001c1c002030740c880b49074580b940021a410380002e01050304400c04850f4800c40840d410030081c1194103101c40071b4000ca400c551210494500741c100c1d04440030110b080500c207140032800445820060ba41c1411406034827841652810410817449086041d0605000e60000b140944911108401c6510254004c1d495081c02148900d44050020b80020801d01540c4072609407400c681d02d42c3c0c10b66407040100b2102e88841074070300191504c248132480710030740c0030844e18840f104428025a294004000c4140c4c448441a00c80007980c02030208411520748002203101e64298540c10200380504154403190041c103084109070740845111540c082419000303200c034105402a04000e001080d802d40c1041d090350088a00c440c0c106100d601c0a8001c502 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 609242661 1250 609241411 609241453
    0x4050d05210c0a0e040e03070303051f18060909020109030b18060a0209091f260d030204050f0108060f0f03011e020c0f06102c04150c0c0203 62
    0x380001100307103012062040000006044842d11142d03000000c2c0f5250140c0c10030550300d881081240c05209401011138200d8607801040303002018546c0b210302003070480c0c5007240c6a02d00071b41c8006c030083c401a0f80b203400d44003040501c1200d145982c50094081121500c42c017486038980d0301070b15006044c1345950784080450700001e00c103511902c0d200d1611600305405012a03400740034400320150b12041e2900804c155500040d10a07094250840001154200030196280c11619000d50503a0310b2200c401d06000491184100401d141c0600740800b61443c3d01a400b400a584007075515509080e0400e0042d01e003448151417080c1d0008401d01c0340000c0345440c0400e40c041d00c202030004222101540c1c01e400031150101c1108904079004241e0b006400000c10115024401c40c0d8028140750030030f030058441d401039900424025859240d0240c0c10040c40722440d450341c1140c1061440b0510b4681082c215200300203da5014850a280c8040d070014440d2583c2c100e51034000380035090300700090300e1040c0c0100c = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 609243911 1250 609242661 609242677
    0x1050c07080c101b1103040f0b0c070f27141b0d050a0b100c030e01030b010e09040c0303110c1c210503060102120a050d090201050405030a080c120304050d05 69
    0x8843c1e4105185855924000c404900e815040a0340380c403c4201030203080b02400703842903036070340d80240001c010444000c51140308842100b04d0f00c80d0b540442d0701c41242400c415030003105080303458030b20008201207000c510034184010240b82d95000c21a41c0a032030207440c00c4841c6800c01c0481c0c64042100c00d4000f040c1e10707182a01e9484454504202030844030107070303901150500710341c60b5600d40c84001400c056000c01801da0a40c5461552200141d50140c820601c8044030307410155a800170781511b9003d040d03100308540000381710180310b242c5460101c0600d241400201c001035500b21910031074002c0001e013403003503110003026561103e040410000020300d440409550200c42070903445270703015003901c0e810000310461fa03a075581d07490001d0000e46400d00c1090801c103111420805040d80e240e201090f030740903142000011034401d00380d000403a0107004603000b540c0c0c54040d042e541410005101c000b40b00030240303201a26280c5c02c490588044a000454002d0030b903030480c0030078110491040c00203140103 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 609245161 1250 609243911 609243913
    0x60702091906170c180a05060a0302090a15171f0b0402030c0a031404030c08090103060b0c030702150f0717070507060809010e0d0e0111030d020a030b01080901050c07080c 75
    0x29500c2000081c1c0c2c0c101d60090401c0d14201c81c54052000080c880c1c0b803c581400d42d52007904e45c0d10010120031003040100301000040c0d6940120b0125a12582a0402140c00400c15001c5081080d510707001003020307141d01c10304d1003107829000523142007c0829508814002e80500364503020544030400407900c080304081041d075174444801140c0e440303102030740c0104000041161030b12150b81014084980742440350030a4480c0c45c0401001070b0707101003544415a0700c00c00c110303204d144000042e00a407420340c0000c84580d0000c59940016080000074000b014000c0755003034100400441001c040d07209250328420003110802222022405211414a6001c12040c005240085030f4855505140380d0360050310014143d007060209000302409000d06c8045040090310916490100141c2800301200400341070281540c1d0b54101c1d488244140c80001003618015565640c00e600000c000b071626100050103c0c8042e0085025103c052185604c240c51170502c0c0c900d45807050700e07500b09a80140b0f1480e446 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 609246411 1250 609245161 609245191
    0x2010b04020c0309180412031107020a030524040503030a0513120e041a0d1b03060e06010e0106180612020d021b0d050a0e06031803030106210b06070209 67
    0xa4a031440100340103030545001d942c56120034020455019030260031001c1c1201c00c00300740404650003403004030541e0300714200004e41c2c04c4c81c0d000301000d40c0550140070754000c150394000018031002207034110910b07440d05030360b01c003001c003801488010310020348002e0a140e2003800020000d0a03650b100b141c003c20845890902c00e510365440b0240700e07500082c18400103181c0b012007811814640203210302403c0c1e00e80c0c40d0070f5500840c00440c91412100704042c1594001403070b1190030030b446480510103590081c070140700d4012a5008240e0b50a0207114070703408226101d000107401e610408851120000b0306c1c01071101145001340449400028002e900441035080101d011508207070f200a014a03540c04844030880002d6040a5007014030054111050000c1040100350442c1d1020707038440c7c070f09800c49a05440b43c542020300b810f08107400c03508111500c400400442c0703154005d20340e002c2020007900b06410150608110341c1c20703103003003c04040d0400d109200c64070043c502040c1e90743d40494103143d4094 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 609247661 1250 609246411 609246431
    0xf0a0e0f0c101407030210360309051201090b0a0506010c1118150a090b0612130c0e0406050604090309060804170f0c0c0315040f060915020a020609120414010201 71
    0xa0258804c000403409607002d18030b4840d4444840c042e10015208003ca103054083d07403c070791480d408881031540050804208024010140106a41001380c000908420703080321548442c14001c060071701040d606180480b0000716210000d0240c144500e006039a07004075070300541d403003184242418140b503034003528100300c820450340c660090a1117041d10075424650605140706100e5540c005410a141140c1400a200100c0c5c440c03000300c071602740000c103090700d01c4c2d55868003003040060741000050009c40d81040c00600d8000d55500c0f10701542c01120104141c3d221a0704010444003800001804950b0100d0304212090243c0c0e0059400f6010b00000c00c1d0a4100c444000065400130509414002c4042806415410b041104c0201c0c03c9090b00289000b404e625510010030303900078002081006d014005204022880e0001200c441d03102c0170828041e4007800b8030b28065000300c00f40c50018420100099041400040c100300301c1418041c1c2c40f8a05410801c030740e030303003a0407220807641599218060700ca = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 609248911 1250 609247661 609247697
    0x1110a0503070b190501080c010f02010e030f1213240905060907060f02010b090a150f06200615040e01060e040605010e07020a0309060e0a0e0f0a0e0f0c10 68
    0x1090b2481240b5400c034618190070800d50443c80e07080710b911414908401071210010020740700c0e1111509007420390704200c103038400f01d000d40800040d088003400041805070003584254050001085186d42d03120031070392a83c1c91a42c10941c4000d000d0000d564203d881a034041540c40b68201d010714403a408602d190b0991074280c038016060798440455481020100641e40e0b0000c0e41c1c481d0843c840c40240140d23000c55002174800304024041c4042d0b02d5540c400752880100301d4204000030304030540407417132150f0755000182a64520b154544160090001000c403241c60108003184505000c110042c98242c50702d09000040031284000c4819650f1032001042040170b92490ba80711b0b41c07081c00c000c10780350706205c8145120040617010f1b00966118010b84e100090b04032494005481c8540340082030308403500002a403048083e44a11002c00948050090300080358985610616040b0014402d500200c4e003510390f42d032100c10b00c00b18039402007182c109403803038030905d1080d5001041c548030b101e2a045003004 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 609250161 1250 609248911 609248917
    0x6210705070b101703090f1302070c0b03040303200d0504110a03060504121103070f0c2105120f09040e07091d1c080109050a060b0c070801060e0c0901110a0503 70
    0x14880c01081c00b404100115840050300c10090301c4c1800b0b9420015a140401c4805100049003841764139012598202d40c121503050b0340c00250800b007420406a66030004000c20744c4251400d40c002401e018a0b003c0311000141e00c1302100ba1041015840c01c024041e041000b0103018000315001c80d0f03103a0000d0b0a030f6894400f400040c6025002c00203240c2000d140001178148d000c043c0800f884a003101109284c0c2000c0142c4891940042d0344450380100d134a8401000c0d012a0401441c0800150503031200c3c41c401081710070024810400c8800640a208840c0c00502401c0a039004865080051250301e04060304510058500e04089405503a1030b641e5140c1551082034242180750014840e0a0344503400700220584201c1004201d82910314014000b884080305002e040a40b039100d1012450701c5990303a0042c0010b12940c0c41194a5074510700000d40c0700c6089110303c079000d608042d070103d040440000300501600110098a00d002c200b40c0042d112200549a52081e9004482030407000c03a07024030007 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 609251411 1250 609250161 609250171
    0x1020a05120f06090402010819050c0403060c02010b0604063902150a050304080306190806150603060d0222110403120201150603050c0c01020414010e06210705070b 72
    0x11a0344411020300d0464207004010007841608081405000b41131315140c007466040750302880d00540035946d540704980d8440074031681c480120716001c20844001d4a12001e0300a4038490718043c040b00038040400c078240e41340b402005030b101800b00003c00446000e154401c0d00440d11040c2020950030300c0e103d03001d003103150b0b42d048840503200c1d1078080f00b186070580407072004c18401c145440c140480400000c0550100420050234102e00102045d0030b940d41a150407508904d0480030880651140700141d00c480c400d983c0c8100c034103098904c80300146003010580b0b1042c070003d4507160b403151060b004c000702c9030740318402e04884c41d011900e121100c038560b00880710660405240301e9a105d2940c40c00307801903126000c00e8411a454040d0031450740c4900380301c407411241c01d85804203040d281c000b00010548119002c0c443c0e80c0d8070004000441104000d960300441400343c17600040308a1800c00d0013440c1c0b04d044140d17104000d2000a00d21200c6107078100f5500466a885d001d07082414560b642c40d02c218040e10 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 609252661 1250 609251411 609251417
    0x3060e0304030515011a0d1103250903080712110307110f04062d0801020a030f060501021f36020310020f0708090427030906050307050301140d020301020a 68
    0x5014003c2c4001044034140307005041614128544c9003140c13840380c0c202e841c141130100000005169120604942040e44c0c01840da203240c0e662810100b01200380c00d1218158103800d0003004880d1071641c2d0250004500304d94210900c1d900d00540c0d56034201a041c5d416013404144000f41000030360640d03082024086540c42040e55000342d0303620344c04128003a40003480c00340c403481c10003030306001e030f0260700b05a072000402419a9220091420140300440165074104403215880841c0113200240d054000c00c20800300010100300741501e80e0012a204c0b44c071040e20f0b09600000840d2050010322070b5102c0040041144034001080608415203000b084d9011a010b810000d030400800039881c0901400b0b50742a41500c0031440d18840c1d40b0410410b019402d0050030325940854008400d4442e030700300c012503e4a040705012080101c0400300c0c003c00d00800c0c1640080e0321210040f54090052045901130805922424190380c030303100200e659103003110101070b00710070000520401620240040c1c580445c0c281c03 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 609253911 1250 609252661 609252667
    0x2a1b1e0609240309020d060203130605010b04060f0c0302071d01080606030f120f0d060905070f0e03211b062a0304110d170703110c09060f0a03060e03 66
    0x100154100c0d0010503200d82d00e10103052410424020a200700d25a60a0128080c01c4030b00008481c00180c2e0f2014000d24000020025004100d20040701958801e80b0100820b0b601c803108a40a070040740101000b2542c0314101d12441c500401400d007050f4440d01c100c488a0f5121080b443c0c0301d82819a030061040b404000502c003512050044642c41001a002001c041d0061f04015942d9403c80c9000611100001150400c0c4422603041341e04500c00800d091041c65503032103a044c0101005c491582c0050110314060440b01d20901202c0e0040c1c0b80113001341110b400c2e49084491a0f44100282e50705039608220100e2400b500505142c1c1403032000d0064209031034404401e075413102903522440c062100e612060075284c000750b0166070300070350020500c9000007083c0b404604801d00c0c03400042d2464070440380882c900c0060000034520980700f42c2d140c24840418060880c1d8507241a0041c0340d000d4400310019000f801d08002001000324010840b5003450b41e2610703807c044035400707400100190800 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 609255161 1250 609253911 609253919
    0x21903060503010e0c01050d020c060108031b0a0c0e071101150303020606150f0c07051e011404120b09011e06051f0203031305070e0a09032a1b1e 64
    0x26108190041c1000d500a0002550780c092894440c940303e022107050210100d0034580c070000c02d9040d10110305094085440550311407a850382d4a401071960740d12400081c441820140b200401d040c81c00c1548a070301080c900381010200024180002c01f040100071005203a240040340c00d004800c04801c0e00400c2001d40d82c00d50800a0500d00020900c60081c0b050220002440d0700501c02c6aa50092203901c0c1d0b52035040f24400c050818185901071580319481d0040c000c150783e2008503159051200341c03120a002c61881c28261120b004a10482d269540310711900000b140014510607404461b03200006003c00154158003d41c2d074444107a821940e503203950602c0342c2e09003143e001030301c03805c1501403000503900300320020350701c3c80010700d507134444602000c01d14100102080007070054406840c05503154600000c01c0801480100026070000f01c54004406242605440c07a4420074503400500c42c641555440f86042c49256045520401c49a41400640000f1281c0e0000503000300c070302540c2c062864 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 609256411 1250 609255161 609255167
    0x12030908040303170714070206090d1a0907050d0f080d09060614210a030c03110604110108060d0b01051e060301090c0f03050601020d0f05070b010b090a0801021804020f0d0219 77
    0x800803011300203c1c0100b6440e000b100401e0301c0d0840e07811161341c1d6440022b40007103800c203081010000c10140324440c1902440201640306072140c00c1c0030084400c85640c070303410400856035011000c1d005500000b180d20218900d40000e016103a03140c640850441c4a65a50034112204c0782c1c01850001e60030301040d407031450041c81e50b54900041800b01d6055400c1651615220480070303000030309020641c400b1004160103407003680c02c00440740094415600d0315041c0700550385900c60b03600340020701010000b0130500e88004600581600100d00c00f82c40e070f00740001c0c4205002c0214400390b00c04890120044070741d5940c8002e601070010075001180c0c5c000081c2000c0c01c02c6a4001401050508141c100161759034002072848060001d132030240204588000159981d21850401510200001001140080c0e4400003007c1d14842036542004003903850f01c41ca404c0b03001c1c0380c001c11015075152540c066603282c550080c110440c200f1034202c1c640101d640f07085049030f010180c0720360b404074840300c16444603030 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 609257661 1250 609256411 609256457
    0x100501030c021204151407061a09130b070507020d14240f0a09020301020c0607020c060403030516030e090411010e06030106050a121b02030309070f0503070312030908040303 76
    0x3050008000012585000407014002d500400c00c0560440514200d551b02c16200048400c5615003a0f903601c1c001800c1410282034802801c14151085410004050a240074150301c10924202d240300412019501c0d511901c0d806009d000c00c002c014010000580d80b54240401c10510603040000c58442411141d8207180d50a4440c0c80030240710207508080034411041545d1190007003030100c0e99660340b100039030001c114500e40070b90958408600030103c8880091900e001d0039080e000c031003c049a440410515100b9400020300069082c00030044041ca42545911054441d003001d01991078170002294050008031415500c0b10314140b5201210b58002120105004080e0340d09890740d13050090183c03c600c40c2403090740802c140342c130022090480952181c2c032640c503108100d110f1000c078090025520341081c0c0c1d500503180a0300704001041c00c000c1c04030324110b40300a409403400380d146407502c1c48400503050301c40040c1900d407030010000400c02c400420107988070344c68940c0c8904500000680311a = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 609258911 1250 609257661 609257681
    0x4090615120b01060806010c030f03061208070309170a1106120705180d0b010e131b140f030c10110d090326030a0e0a141e011b050708090910050103 65
    0x11400b0b4051111507603208c6480f007100782e01420a1001d000d0703600c1c0c1c120010400c580c460303d130740742801c100f000401c68194001e20303d650107542e4181c812501c1d8881c009a60b003480280030440c0e40000540310025010b804240960400141f149060941c07804002d016940221003880001d030700081e00c02403034581d80b00c0c5201041130555600354490300c541d8443c0701c110010b008031415102d00300002600c030205c00d001c80d0781c0c4540c070144491285100c20459284010f41e400345c2241a04000031030540e0342400101c1c1c20900d40020b005280525240052200c1100c5401081003000008990b44845000800000c000102d15954010105d8954100b0741c0110700300440c074a0f885440018488020180e031416030f6007010100b000084c00141d1400641d15055880c0d0008000c0c1904a0f10022006000300c4e0542001542c0305605034101892150f69080700c091501c81c400c04040d49080c1c00c0481d10420181c00001c0c480c500082c5032518800c00220030080894092040c02c200c5001030043d0359050003110030304 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 609260161 1250 609258911 609258917
    0x1080d020a02010921050706180e0423030706020403380a0b040b0306100f0e0c0406080a06170a1401181205210402030c0f0f04090615120b0106 63
    0x24190582c0001c0511343d46108440400c260500940100c50500c409824003d50000032030b803901c1d6440c44090100503a00f6484e28014110450014020300e1003280d043c4030f940d0103030388400038102c00d40006c4860b16070582e0500e001c4c1300510058000442c40d10040c0041c1d405032142074542014030040e100170107562a440800c50b54a02034500c0382c1c0d0071080100b6005104e0880102c1e0b01107041d80401e0087c200c0625495042c45000f050144124405003040191440b000f0600c0d84c40c3d488500f4008030a60a88805104420800003003001ca445910801c0d001202807074041340440d41d40c034440307a00600d245a0f20704241c00100c40c120030004203181030b94010000000a00c005c441c400030440c1c207042150b01c0030f412205941c5c1581e401c50700c031301308603583e1700c0030100100442a00c212401810040c115022400b81c89040910041403400c01d80105401c0ca0007404821030000110030f100103400c1c98139003150389a8454080c050180ca184001c40c02502040700c84904486041c20004a01e5106074841814 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 609261411 1250 609260161 609260173
    0x6083706060905010b180f0102120a0908060718030303020304170301170c010e030c06070204090501050106091d0121050703080d090213050103030203030105060705070f120204050906190e100207050601080d02 91
    0x8452039001c0b0200c817404101c40d02c2d51902848001030380ae051005c07010469150303001411a140a07044151035068032840000c9802569032450159151015102c03030003000792170300300b08100180c8260001e6034030a120301d110902003003c00b40101c230725170800c0c0c0100c0000d0110748241301580004000440703001c0c00920300780d040e405c04130000c81d4039246020305050058100040b4101075480d2504103848a95110000704091340e07444000030003a00f600d008540e03042450154000f105d00e5400d4009050396000ba500d541071030007070b040103c001d0400322812280c5004150002002c1041c0c1d401070404801158804107094a0f548100200c94940c204000c02e1586800010700100b5800010380e4150b89050390120b03641d601c5410a41d00c0d140459200701441c850601000ca55000040102040d2501c241d070f0030f0000e900d85040e103c4d141c510032290310001a40c0ea500380d03200d0112580024282e00290301c02e5039283c9502c002000183c3c1e10005064945030f00540c0104003070a0100300610010704280f000d413103 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 609262661 1250 609261411 609261427
    0x21216090513110f07050c10020102040311090403020c0a0311210307060c02030417030712022a0d02060d0516020a05060406020a140a0306030b06030106083706060905010b 75
    0x4800c0b40d80350940714690f18048450709180c51411550b41e21552103c190f200c0740c161500a07070354400d10036980e0080800361205100d46005000b0359041e2a40040d006600303003505014094410741c003e0054045224a20a99541c0c1d21802540030166000c0e05040c0e51006e040f00520114024505030100c0c10b600340404000d91603804004d8902403544018042822440c215040f850350103036411011004910030012509800d001004045440c4109801c0b00c8940d1121300a0361181a0307080b06118400040d41c3e121a000300d0b410040b040744000500390f107805600c0b03402066450300455100414503684a00313002580861100340354494031284010440f4610f255103890b201c900c060001040340d034000c0b071355040c664007840040304050710450320180c80d2030f08201d0060140c90244000c0da001034498010440f5402c06010b2000ac1e00c1c461802442c040c3c80036019000710305d24480c800c00c41c41d4074205071413030a8522006000315541c0181c3d8086030b12820700150200319101a80400b0340704c407081100744 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 609263911 1250 609262661 609262669
    0x1080f04030c02131d010c140706050c190c170c06161e030204031a0402010c030302071a0403080a15051008100b040b0406092c040302100c051803030405011e050705010212160905 78
    0x211507950091000c113103601c030003071500003502403141d45200d16007646581400c055802420ec960b010300031003202a0312110380c0a0002c1522440b100250a60489800200000c0007841818410307902454085401d00e00f03968481548003030b071529000000e0700054104140f10b41075004015814a4130b81241c42800c0c00d42c0068188544e13528001c0030302d0740205607001403008640c20040e004c850407403103c41c146010318000708103040440303161444518007036800750301c40a8080e2400c00d03110040c2c110303081e00781144805da0b030100e0000d0410f9881c255148000c6070040281001e4001011030400740c50300c03582805009070090340341d504800910070410300d100b815100051108100800406c0d884042d0340c965040c200d00300b1010041d51560141020120306089a002c4020104050550b05065144038104201a200d124920031103000500c045540d0104c4152258070001e0340c6002e080803860f11300c1300e94485003607810850602c4115034101e020031400d4041d81010050081c03051402000746030403c0001 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 609265161 1250 609263911 609263917
    0x2061324081602120d3e070501061d1b0306031b3c061e0919031a01050621061311090f01080f04030c02131d010c14 51
    0x1551034400424149000a0090000c044e90b510b4400f080ca603681d0215403024064a203400044a01c841c20452805808441c00d034400e55607104000c600d10329842012240c08550014101a1041d540c1d0303170302c002000030040040c20303000504107100503440d1a0030085040c860009600e2800041010802c0080d240e0300403030200c80814442504500800d50000442c084001c94222209503100203e40c407801c5c542c0320450348503820749520421804500c402c00f4403645005020a442280742a04ac454103840d2005000d0210803c001e403031400281004d070440c40c0100c1c402d60054030300d00c0e01c000c0348034543c0c4503180282c0c0c007501003039880c82e01d010b4015010951030040261030090356400d00d0007003501c0c0e555039401585120307400d40b014841120104002035259111060307040c032440c01c0e400083e80c2540603241c0a031280d05029400c030300c81c1e580c2d5201078a1b0900c00150413070303010002c00440d4405542e180700d0390030000c0d10765042074403c0e14644925401c6940d8101110140000c0f5a1a0710300c0b4403481c411 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 609266411 1250 609265161 609265171
    0x6090a091d010506011d0d0609080a0e1c231203010b070506101202010309030201110c03091f050f0a0926071e0303120621060b0d02060f0a0c0206132408 67
    0x141503504440ca041c08e800802008200414184000a03101e905503845944200014400c903490094407110503040b12490203085402021044502d0b07551084407128507645021041d030f00c040d1011441d4081c402c00855100760000039a0070030208081d010701a08001d01d5511111108900555a0030b0170400c002280400c03100034101921150385108042c801c0d0081e1211081c410103003600c40c11a403c9040d201d41003800800e0060464407141000080d6114070445400303001c2d10f60900e004ca8803100c9941c154814505c500c140004008000742003142030b00d00d41c600907102c015010f40100ca030030406d418540e199110b44007400340070340c69000180d1400380000480354107050421407480480480c0019085a51042003101007180717102984a650f028400540380c4511400c220b500b1000080101011040c00043d4010300184109084024401c00500003440b850030909a101070a0b80010030503409411114594514404204140503001c0440c0745a1031704440003102c0402842002441480b00803c = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 609267661 1250 609266411 609266419
    0x608060109050c1602100e190e0c03060a0b0f1c0203190b01021b12030301030b0414010c050d020a050912010e07050f0d0605040c03080f0a081609030206090a091d010506011d 76
    0x6c80c0425481c06a4a4610070610103450002d2800b05006130710482c449070311641280c209010001075842d007064080300d00c0b030382d4010650200b103420480b5254864029488401076150208041d24080f84842d0f80f07017007040700209000d41c0d42d01c0e1440c294807654009044031000c160070103940d03600e245e0b0041035102c1d0744000031012000024104001402c0122a2040100c0c58040080080180025440320f54859401900100001c8207100401800c94401120601c0092001d1000c1c043d103445e00e8000308890502c51402e030f8104014440040c40c074105106d00c40507661f540305051141b1f103505010044c002c080c116039080d20100c084002c212030030074010300200303003079980d40004082018155401d401b8540150302d081c3c5076814000315411036400500381c0d0001c41c0302d8200143c0c40c801810401c1304100115601c0901052560b82030010336000800f006902243c002d00124810f80b0510840041d800c00c00e50140311000b81c10805400c5510107440c0710704000c0c40400792541009055054192281d00780c2d = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 609268911 1250 609267661 609267679
    0x15150e18060f090406021801020f06010e0a270309091a0d05010908120603010b0f0d0b090f0d020114010f0302030a08030403020c0603040b0415060f09020f040305010608060109050c1602 81
    0x4001400940050000c030f52100c40c0d00184400c0c441c86501600d00750542005c00760703804130f0b01c42c010790759030340240035441079a41300d1b40043c040110825146c40d0002101c0d9404903180d1140c1458141c0502107620318510709200d400c0035003d040c3d0214605000b0284014101300071541c4202454241e00746000840c05404549170765810040c007540700004c259000035080f07845e841908508901d00100340e509502c82c3d800c16501b1283e40c500b0280700202c07620010200d00c2c0252a56581c0c03594081d00402d8292140070b2800c140686138003d11880c05000c1c2240d0001801040321407500c0c04003a030603000003900540080090006880020f0000513180c1c0002146403242e0311480c04034585090503c1e01c641068001c0241300070403256207001c1b40114840c82405420303007040c00085040b50310318410b2085021055504010081c6070741d0040c078118000c104c4203440d00d61261192401d50701550310001243d03000e81d004001c600030078460b07550081c07103010211b03203060b9103440f55498071881c0f900041c2c801c0d5812 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 609270161 1250 609268911 609268921
    0x5010507032a260f0702040b040b09090d090f080d081f0308040602011b05090d080904060821071101030b01030207050f0708120c060711070915150e18 66
    0x302000d00009094542c2001008401d45020341ca00c000c442c00c00f200e4078200308450115900b022040d154800c60800c1d84505080c095000c120107408440042600203995142c1c00005444000f0300c04d04c14180c6000070070000444140c024001c0c0c6540d404050b1a003032941e028002d540e0081030416207514180340040080d2105911240b00c04006e501500c009081c4100000c104200000500100d0b02c1d5038000300803d00f0352440030000c0318100f514803c00280d007080100124503010090806e6180604441410400c0e404085812a07903180c009540503030000d01180c03d6502000d4103000ba80380550503050030b11600350343e080c480c099001e000605040d1683c0040d043e691080c0e06030f418040c1c009046135181442c8000700340c1c5420190040e802a4000c0d03001c7e281c007009074501140e01003070503840107209641c0e13003040480b0500c880a45400342c6003e0507800003020f201030b0040844100d0300c501c040700600d00e04080802045900000041402540d18090009981d00340c0c03001010300f0007095a0502d9070311 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 609271411 1250 609270161 609270197
    0x417031009091101030501060815150c011a030d090b1206061c090204061e09020306040e06181e030d0e0325060605040506060307030c1716090b040501050703 69
    0x1600318154680c680550b45040c0086641c042602c0302080e2010040d90343c0b80c0300215a0040210350a05c01c800d0441580351041c2081540b14042c0d00245002038103003c603651080c0c1c252a04000210003241117012418140e1809002c0200d00c41414245042424940804014180030f00c03002c0f030048104000c001241030300c030202140c20403e4100161680d00004240300001080080c005a000c1d6180000228040854407803004481e0022540c040f0000d240010780c3d000396000030111508183c4805907007500c04400c00990f80181503014043c41e07603421101580e40707405001040d012560821103144020080c020048549440a14002245101c44000e0a0785035105d000f185080c16070300702a010078a4009211102805031060400303000300c9640310200003e030f0340c066559079404a010004100030303034040d602c0203034190350904000c040d80080341085052420119a9966000c2c100031445480315031104060f400740c000d101d611414913050200003401805801d40080500204500009160034 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 609272661 1250 609271411 609271441
    0xc070b1b060618061f02010903020d05040819020a0b03090d111612030207050a140a0902120c130302090103080304050c090417070305040801020c03040f0b0a0804030518090c130905041703 82
    0x10102c0741e840104900340b80024002c145108c070079801400342a410a4407148204200c0f0220b86074000100300b003071803a240c2190380080340901240e009080f647e0000d5403510b054061446007010001416098074011005444804c050780040c00c580c210840307207180c1d502d00581400589220070401030601c11a842e040c1e00d000401c3d0400c60344645645030014400c03514406900c1c4000003550792103540780c1e84407908401d078007565036150142c080c0640000c04500405d80034284401c2645818140642da90300030a0910400780c00c1550001400401c10007070003030800010b114100c054900e011240b03456294070070b143c8a40c0600c1d540d401c40008800c3c05040c4240c00751b402130b107107000c001c55a9143e800e801560300d038810700c01e2009551701844001482d41301c940075240344007600c0e1160001c1e1703542c9a808440540c4420020f1802d0304e1004c1c600c0030b09072141c26201d842188201c1c000c40d81c40c035401d545402802081c0d40414480d5081c50308100008031040307580c03102041c4107003010342c4030b4885101040400e0 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 609273911 1250 609272661 609272689
    0x903010509100c1b26040603020a03050106051608030613050a09020a0506034507031407050114090a03050a0b010303030c1d0d02060c070b1b06061806 66
    0x982084148650101c0c049007140103001c4000d020000040ca548064039030a03c0e03242c24074a10940200400081601d4000385407011088808410403d5200460300d4080c1d0801e811100019601160071341c4400d40510886003d0256030a0140c1001002c01182d002005071450003001214044041042074403031103c403001a10004100b40442d00d0030700450002004032250503441480340007000101810468116401280941d00000c0f140403545003440480c81c0300120052144041095071103160041045044c0c00080c403009010154514103003100316500c200c51440f0b01303812a103008c000c1c6070b0f0048012036171b0781d21140031282c03241d8840c00003503d0f05085600290850007964805001c0007825140c0e1410707030307120361020001880c00302811907000748a000001d00201001d082aa440d1804066900300e03c2d1000701000d150401c2a60310b03504044050f1702141c13505070041190841400c2800c400e06a6114040040c01c80c0d2a003540083d17513014400414404601412002c901551100708202201c1 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 609275161 1250 609273911 609273913
    0xe010510140f0c060603010b0f010f030c0207170d02010b0102010c121a100804050f1903110a060c03021305190501080a0e060423010911061b060c0717210a020903 71
    0x3c40c469011980c942404440151185d40303082003007041e615000c4c0054003016810f135282c4600382c22042d4141c00030101d6000a800354030601c140080ca6043d0780320100b07003940b2408050319021500300f501a0035103601e818010f0559051090000500c2c0d40440c00c1156651308074030201d001900360304078542402d910001682c0217810503112101c0240c000d038555014520481c1160000304124080076100d202c5261010700481c114100040800c1c400d403e505000c0c40c1c01c60585410352241e039a039800b141d0428101d00f001caa00855a0310f001428a0b0804004090903a44040e46009020f504454600b6074064a41440340303480c046250700c0f800b40e102d400c01407040d00442d1014141070070300c0d01c40c4400d00320f4001c20020702d095440e14104018007079946042d41c0103003840350b00081402080340c03076000340902c203807503d42d00c4012826a1600300000c50280c0750720b8210654814081c2441403070b000c0415150b40d1640d4042200c0c018914214000d40078180d0b25612344441c41c0c45903c10b03040a885224065545 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 609276411 1250 609275161 609275167
    0x50f0d0f020a0206010323060f0a0b041a0a0f1d07020708030d0902210601030b090309030a11041b0504050613120b090c0411090607020f030d050a090e010510140f 71
    0x4501c1d00041e0485c141d81c010384010b50340c0320780020f0b42c0400e01d00e11040d00e102030300000045460807030421605604480c000c400071942195640214040b244803901d0422000740240b944191810136040e40d4020b0100384410000c003609002c1460420401c034001c64507590894030000342440c2c82401000050200b032001d0342c0d920402a2000400340601d01c400780d1040c00f101401d40c2c0900c4030030200c1484e40200101400c841c1e031031a103440b40501c40050200071540410030540603a5039003403001c00711052152520f0850004082c0500c400c6034020701c46102c048802e405000b05298102c01560200c038070840d2002d03542c41c991720b24034001d0b20555100c075280210703d2405404012102d842036100e00b1084044402245040080009940d02c00c030000440c47d0040040904508004005000c994000751000500d01c6105000ca07151454a0080e003002800200d1050340b9107a00058000c01424500e5100c41d495061000040b0300902200d40d0f0004d005030b0020044641c202e40003940e440305151a00551 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 609277661 1250 609276411 609276427
    0x7020f03071a04080d0c0b040b040309050604090204180203040218090a0602040e090c040b0d080304021912050d1403061003060509181c2106090908040e130201050f0d0f02 75
    0xb550300030340104c00c401d02404881c982d0b03540c400e0b10b048034260781004601810fa02c554072800f80800021704154100204c100b00850642c98070001000186074643e030042e51185042110036080005501101c81280104140170161b9030301d200c0c82c2141b40d5440e040110720380310000c03076a29104190b000109004c1c00414000341c44400c14418610a4403240b01ba181b00e0f2400c001000201c40200d2002d96121141c254010041140440a16071007403001c0c3c40d208800d200d80c103420700202c610368041515020065415010000113000f003d403c60614142008120144441c000c02c0e40002881c69000300e076501036044d0900c2c8241c000034000c0c031018040b1800307070a2200b4920040d2000c180250814400c0d105c0003084d400300780421a9546089903101464240c660850415101c3780c4401003020546070000400c00700c10324400d01c07640314402c85260350390751b1a000d5440c066140c0240142d1510840c0e01001000d0b0341c00c081107510341c0c0f4108020703a5441920201e070000604070800b200381a90b02c0800d07044 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 609278911 1250 609277661 609277709
    0x615150a03380904030807030908070f0507031b03020108010605090d0222062102011b05060c041502030901020c01050c010612051b120a06200d060609090b010507020f0307 75
    0x642c88060310380600c1a0341c50441401601c4105a40050014156a0010b26154440c5e4083da101a2043c4a00d0785400031035200c180e81418070320710070355240c3c00081040003000f007880c2d030351030100303d0010850b001c042c51900080c25400d0305100d0841441000079411900e65590b40704e00c1d15080e401002c0f41040211003100c14640352044144002d440c0c1741040200b4602c60035084c070462000e20320300c4035040c1001a401100c2d40c01180101c2003550040300317149800200140843d030f00c1600001800c0380c80364034103e5200060280c495503c02990410001900a6640802c400039111400c1c00c00c19030f40c600202d8140d0040001d9407044d00007011400c03545007084004100006580300074401100c0080c900d0042010121841035806841e03440008000c00048c4150001034115a100c0c40e0f409903070302810300c1d11038640d101e50410720300b940e41c580087c00b01d2500022241d01a05040303100300500800f050003e820362254000183c4141d610b040d954400750350800911003d043c0010f6480e1703000b002c00d0003a03 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 609280161 1250 609278911 609278981
    0xa020409110d1a0c04050f19080613031202030405061b0405030d182106240305010e07091509050c0702060a020a03140a0c080c10110406020615150a03 66
    0x4001e0b00848800444c0001d031854003030b241618002407449010301c2c40135080040040c501100e1001602a9002c00600c1d09424401c01384501295030b0a00031100302482c00030040103030b4000c0514154414428400810b200260266202c000c503008007407441c1000c11004034601540e400240d040c402c2c8009170001603440441005100600b01d0010502d82d180c42c5121a5286124500e17088040401542c2c0b02007030081d00000d0b003c0030a21141d040222110400d00b1200761942c0007560543e440f14107101c400f0708104004001000308080800c220180a808000c42c2d4135144110719a00ba14cc101241000071400e0843d10a15401040e05913144240034010b9242c176a0000180c0200b51b40001c0c5019030030100c0120f9460760100c0d075941e40c0086003031f50340100c42e0704545420301c46881900405440c400e000d105032072000d502d00c1c90141c1c40f50300c0c00000038a0080020041c40c104829006640781c1a1100072072950745c510a911480e84821031001c0407002081106030140e50100c4441481452198840704 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 609281411 1250 609280161 609280193
    0x40e10030503130e0901231f0311030615030304060c02060c01050a200406050306011b0c0e10060201020c070b161e020a0e040b0a0c02070f08060f0601020a03020a020409110d 76
    0x2130380d0599461210032403c9501d150341c054003c0000d01082c2c50301001d0000e886520a240701d60b044a0388049005090b903401081e00100e803419450783d00262207103420000b01d85d1081c41400b000c3e01e03100008000c0390b00c2e405035100d03400602080c01050b03421965040d0903625407500c075170001c00907498201100d0001d06155510000c110030040084d0140c07a2104c0119002d490280e04d4052442d2540c0f401101d8140c8010108041c400c03034040d01100040421281000414000f00d0034403c83c01c280800311380170903140e48403200b036a01c1049813241840300421010101c4140e406403645440340901460f105001c07400008291608403070305080035481422059031070b03d00941e03205949503212424003040801c1520090f002030741440002d407a856042d089041c40300501d02c141c1e00025920703081c00c0001c03811500000240c2d00040c0401c00381d2170300030541540c030110903c000c00f202e40c0c041c0c4003c0d454403c200ca0190180d03480722107150601405001c0f40040303d10207002208047c200d400c00d0718011070044a = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 609282661 1250 609281411 609281429
    0x908150403110f07030f0c09020a030b01090f06120903021c0314010902030c19051e04030516030b040605150a17010b040605104a01020a0305040e1003050313 69
    0x25406540040065045901c2802d0f10061000030700310344420221200c100c804940b107201510010840c003019001914003090030b9180820004c1240001400e910b0080d0440341c207058017454208940c5500400c55407449150f40800100742c0c4d00d0341000c030709220000038103942d0105040840021254998440007103680b03400c0c0490602c0c0d80359006581a80303c19a0b04200a400920030382e5214551915103126140c0329050652030101c0c0b0b41d02d100c1400e045403d2000c43c101011904001380503052246034074030800700122402c0e45040d135507050250f82028001404542e5030704000340d01102549044d80060740002c10400c000b9645401d028507288450041245c50350816260fa01c0ca0300b031502406050310b200a21002c0c0114031003104650024015143d20f078410070180a10410001070702003280110390301421103900b0300503800390744406016005000d046501010080011175440002d540589185800b4030110340c44814600c11301702c2c07160b0001740586c0070010f40c0041a03242c1448410807150026 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 609283911 1250 609282661 609282677
    0xc010f0b060315010e03011112010905061c051510030618020325090207050601060206010806100302120c12010b0415350a030e13020315060a0908150403 67
    0x1081030300e0010140030340220081c0b010840100002079075900089061506800a1510300002801d60b2240240e010140e00c0c0025413000c0c0d241000060783c0900182c0790184280d0030034a0104031300c50060701c0c00d62840344552400c04100481400480544d500e410400e03405420030f075000280c51600b910080319003e141102c0c404c1c101c05455a0000d40c1500100904803004061114102e10075840a282a8074010100081103001c19172024015850155000300815810400042d1910006800015855108408105400c020302c8440001d5030b6050358042000141d22040300c0c501841070f201d1075841220070034010011a0158800c03c1040011607090010303048039640008503450301d0043d0411614107200d90f03c200400c9642401103e07940380c001c5116844000481c905103015801c0c124001003a00050702a545000a296403070f10182c15421855403d040d902c1c00b038214a120f4000340104c2d00031440501480c040c947d0714000304900c40640d91070080002e0100b5103518122411000300e8600 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 609285161 1250 609283911 609283931
    0x801051801090201080402210a2901030b01290c0a020f0105040f0e15060d050f180307240212040c17071a040902220902031512070504050106050c01 65
    0x50062000d4683c041e1030320354243c1c482c0e4003803111011103424040c102400c0c142000d8070744c4004000c05468035000310b070b001210407008440001e038000c1008074000500c559071b0060011441203400d8504403180c01e000d440b0701040112a00001c0c49030400e000089040c0401c0d0b8048841c00401d000c4a9540b007144c041650b42c03011401910350b4081c6008000c5128500001400350b01d8104440541005602e00d00d014284600f01c006020359000e070450788503041c0c076030041c000c0040c646043d564101071001b10924402550401c42a528028803001610415144400d4283c5a05046020401100d6064155900c9112810054100a0580d82103800c1c031a54030000402d0100041d0600c001e03520350028200c2c1c5072410315054115810400d14042c00c040c10440010080f04910040031000d60103160b40b401103443e1039100d0f00e0722185034884c1100a004108120f40e5080b182d0030b01c41c1c8100121004d41441820039900c1c0d151903201e0700030315045071414001164a90700b141c0604070035400c0c900240400088 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 609286411 1250 609285161 609285163
    0x5060a110f19030815060304150501050303070206070f030e0603090d08130b070c08090a06110c030703150213091d061e0c1605060106091806050f010e180108010518 72
    0xb15044090a0519004608000034491240560132134200c0c040b00d011920480d00185441d4003c2c1c2d02180d04903004a0041c0da25100d50061500504044010314104151a00400c0349403149042c000c200e04c8001200d001010300070a84048448000350050344c0340c1c94101146079850880304840ca01103030301d22000900965259860b00d001c82c0d44a23130745c000e41c1d84130300806850a40081c801151050000d1204a44030341352446184001c0c201a900d2207040212a10024101000070014034000e80001c0c100388007041892401500c000c50240b40140d803900102640b01c950b40560f0805c01c0740c9030508003003501e101001410300c0c0b0184500000d40c2c03070700d40314800075402d2030307090714000214000e00f000050400320082d800f903e0422003e90394810091807595482e1705040b002d8104401240300400140316174116803c0d902c03182003503004100442410705c03001800791840b1144071410002040c044402030f803904c031440d840b464510701d8500101d584840c101030207014215911491502d2a40c1d0701680108 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 609287661 1250 609286411 609286423
    0x109062403020616080d0203070909230f060105040302031f060f08060601030f140a0e07060207030302060105100e0d11010315050d030e01031d0a02210316060605060a110f 75
    0x10b8010441480c0c2515818400901c404043e03058419900a0003030343c0040e449400218400c1c581e5136601c56039a410070801d10101ca0f0002c111440c0c2310001d00141c41901d005070f403144e40011a07a6100e003400e940340340040700c0d58407441e04000d40501990038032980000c0c0c8203500002c20307255242d0a06c18a900c69100000500140c800e031403807540054003143c400c0d4002d038800045040703282c0020035082c1504040c40310b600c5003510b0450800d941c410680d0f0303840c0b000f48010340c09008544040e144c01440c1d520000c0da02c580600495110728900c2c0c600522050003031341340e10002c02010301245907204450030001242a40c402d5054007003401d01320a981200e000b040f160701602d10003400b9030540d01d52030320202d40b000004a00d8a060665565504902000030207000c4a100189070051030f0110282c030500c01000344001c0030191060841e43c0b03030a00c044001c005d480e0602c203020802c1c8002e00c29814918080d0405500c20354000000182000a0992001d904821051103c4c200d5843c1c502e0720444a607144 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 609288911 1250 609287661 609287663
    0xf082406010c08090a0b04030b0601020c060c101e23151804020118180b0901030b040f03090b041815030309120204090203061503150f0a021b0109062403 67
    0x681d6403140c02d0b00092001015001c070341000340084013296140ca20b80002a445a0819a407101c0400200800c0d03680c100060600d1043c00d076241030410720412a45a0b4070008503c00d0b480e840d40b100149980c14134601164140c5440c10b800612002c4010f2410302402a0000600580c1508200020340b00e98004902d42400c01c80140c000300100d61313941c400804803000984100e0401c13240401403424141c40c83c0324200905940c082500b40c0d4002452441c048503441c056490044003100c004102242003408001e40c0103410285610320031000e032408940444040d000350103c03400115010444200400380c5035185480300c10200300441c61000c075002aaa1140300040c0044c62554051000ca9100380f000e4101e14409840031810603101d5000a0426600300c64160801c5618000d035401403408000c030ba0f080c080c8101251440b0700307102c801d07580000c100400721000b00e50005602843c00d01c004c450084540031140080001490615200c00900f1045e511b8050000404403034100e04514400040704403 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 609290161 1250 609288911 609288917
    0x1703220f0b2818170d110d05030c0d0203010e1501021c031a06190305010506160308040320150a060501051c111303021005030405100905070f08240601 66
    0x2400b288829055030b0900c4166410840441d8408142c520f40791005400341c42211401e0700c40ca8001800107141803908801e0078100040034900360002c06e00031600d190b140c41c1a01d442039886d61400f00005003807140384c0301407044502c00000004d04008000301ca5014103190000784181c16190b00c01241d5036140103241d040d400e0b40020300200e801d13004e41d005021940b141c12003820320000c080c2c00504543c11180d4024404603039240708dc4036040c0d2600ca540d0150004171520350070b00490809290b603c0d0f07000580207050000003400b1500340740c09959603454007031035020826000061366020700d0701d5802c9007030450400008107002c00c4101109000f140166881a503545041001c0c180c14030040d8a00c14280440300c0d43c0c0c3c0c210400811403640e00800c002da210902d403420861562050000b21401940018100402401030000090020908030204868504040340d00022400e115003401c04551058200c1c8a00c58000a49030801044940d844c0e5446108050035081018140d206424111012800 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 609291411 1250 609290161 609290197
    0x2010203182106101703031f170c0f10020c0d08130806070e09040309141206090a051005060f0d06020c031305040506010201151703220f0b 61
    0x444000505a5079210310050507003401c442024100c8181200300401828960800d0342002a289500003500c0003c140a0416003055200340441984070302025190410346401d03112420318480400154001401221108500c10800380290341d43c4e480d00c000b8014000c08540119a0072850106100340078214607401500800c0c1c1e9600404c07500805040040b18090018408100990725a9101802030b02500c001001c01d07081904018040604005101f40716032540020070000950028100c000c0315001e808a04805c800c1744005210754002d50004038040c03282e1410840801c7c4002040c000741070082c01a644103480710f0b0f8a003002d840088a080d030300400c40c0580c10600d800d01c00d22601d20303103010303070760041c18083c07145202411a0321400400b04502c815403000d005510701407040c5038010100340001c0008040b2145400300c081b1302c601c80c0320b40300000c1c1c218410b2514130500448050f50708941c1140421400c0b000040072282881c043c9503203400040c10085500c00e0354508442c426603040561480d = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 609292661 1250 609291411 609291427
    0x9050c0a0e130311100b090a2007050102070b16030e15060f0a090e030405121603080a09051804260d02070c0e04050105090f0c0d1101031104080d080a050402010203 72
    0x98a03502042c011020460f01924601003803d041c030000b14081600340000c0f82d000c2a4070308008001c503018103004131a502c0c0c190441c481040010944c40f40641041c0c2c880e4503603d071410300d07500a01078141c014200e0b02140c01088426092a0035502d0b070041e1a480c00c0080c002d411480a40d141030720741d441200300d41c21001041c01c52a2008022014140003400c041000741c541d181601620480381003100ba82e400421f0500092074040010348228400100810500103540346c0030030a010188405040c048001038003000d564850340030900030f414090301c240a0300c02c01c120742040c1da0f08221800d03200349241c2c034101d00401c80e81501600c5074007070810416040884005e6982c0c001d5009000840e43e1101b1010000750000d200145180704a0051000181a1900024040c03c003540070100b031400350001601000165224070f544143d070b580065000301030030b100e0f02c0141c0050214010700780c1a204080383c0092854070004800d01d41109030390720702c030300780d284c0d40400d0080e1407040e90000e01503001481001 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 609293911 1250 609292661 609292681
    0x60207060c171b16180b180408040f0f05040e0d0203030708190609020d0f0c05040e0903040803032a040f0302130b1003320403050307050d0f09050c0a0e 67
    0x43c40070741201c1c000041c000f890500fa46889050041c816044c03200d107404010170a001c4052001c000c040300004d1101150b00c03130004254544e5800e800c014004c02c0000708081c0040300064802403c0341e40401551203850341c1c9030343c17040492803081501c0b590030101f580200000120715000c4034406d0740c00542c00c68441074410b841c1d07400000c000349d00b00c4002c42e407036040d01003007406031000403d000000141c1e102200b2000e802940c0b040400900480e05044c407408034035900c030007103608540982c24082d07090348030701c0a028218810f07940484181d00c0301005001c0107485100400500825900300203000b0b5030048500c031007a014520410101e400b81c09420800750410b007104d82c0f001d0002c01ca001403a508280005410716181e4078000c00003e507240317a06031020f80071150000302c118581501c8154100c01c01551100108002e0005040007030100104082a000c0c3d000e44042e840075000c2407000070746800200c1d008185008040e1a41e00c5030f4032548009080c0119800c05981800f200d0402607907a40c0f03068 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 609295161 1250 609293911 609293917
    0xb040501110f070b03190b060f1803010603050c0102070608071b030e0904080414090105090c071e1a130f020f030c0603010b030a0b01020d05091017040c060207060c17 73
    0x148190b000d0b00c07266010b0b06030140510310280420340c0740203803a0f040415007501d4411448807031940041ca4090b41c041d80b41e40d56815500c580107c111400d0781c910341c80400a20b2412940340d8241c1540c00c0000210070070001203a92144401d0a0303080704d007810380d240c00803900c01401fa40d40b00086441c55000000440218007141c0c02e15029003405034590003498045100004129005e50300074602140901c41e100300d09504103907662086601c80c1481d410000000d1140318081c0184901c00e01c0010b03140300304a104a4402c0c0284610f100c81101c0b8401c0e414003182d40384c0307400d8910a07080300c0d14002a4552101d4140c1803010740e003002d80000c6049a036428001c1c0d0550320a8a161b051082e01c410141c1507594100031806454620041d41d200d0802120380c0b0f00343c40c614181c0d9419900500710561803142c0c410141d81e800c0e41c2c01c6034044206208000250340b10b0a81f400729074082c05484040100703104501c012841121080d90031910381d26130f12541102e543e240282c00801541d205242031002e4170b01c00d00a = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 609296411 1250 609295161 609295187
    0x7050702010323040c0909050303010905130c150f1e122705011104050d0602280f022e11041d0f06091509041b0f08070f0b040501 57
    0x800903034142d1801c214560f455604201c50b00050311076081104008172807038910010308462100b400410a50ba0f94981c40340014015401c40781e0782d4000288003a01000781546886810900e03108420f900d402d011801c0c1c400d44104a80420035490034803d8103441400020904d103145c25100c0e11061a5076030031294800034001c0904c9881e04e403003610444441c000c204840c0c2d055000d01c440c001d0000c0c0d2030101c1c2512000401c9080f09032080c8230801140c0c9540c1c40b8410421b521020059548074110514032000f5440d40c0c3e1030103550600c404071400c90b50401c00c50030700c0201c039408680d20710300705051900e400b00200d01e8085403000f88176032030381040c2c142e500100190396a400e500b40c01c0c15140e4071000c0b81c015104c40c05038414400442032081e00e0506040280c3c00403016036141550340740c503914810074a0381040d00c1c540503401680014041c803649d01103524003030900010740a422540c500b00b0513507030100c6018407200b40c012280001009420590603000b1030f03c180e9051800e15180c4070064509404442e1 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 609297661 1250 609296411 609296417
    0x30c09040212010f05070f030e0316030c08070f030c0209062d1804060920030a0f08130308130b0304020f0d0c080703052a090a02091302070804030b0606030403080705070201 76
    0x105000385411301d01031181726480b03e40e104110307020740c0f40b8000c0c15619540b03240d1590341c00030003a04400c220644d4400003243e801d410040120385040c030b019880c0f0703c00c80c200504400f01e2032928200305584000c0c0e981d041e41c004c031140107070303516528100003540c0ba641c0d00951800540314940320104c082064580502080100304400f8031513500080c912100c030807141210596600c4921104004640101d10070310015500412640000880405d503584010035021700b07022040c615810401c040c52045030090382403509140400c0742d4034a8114901e410081c030013800c03010641008106e4422010503240700d55001018140b01111000a1106c14584e6031800c2d02c450204400205009000b0091303000118429802404042c40c800c40c88262044655080715110101d00301000c00c950311094150b0300140f030b501006a4510400c0005480811480300d0f10350300b2170002c900d100600540ca0302500849000d00b4a440c03041d580c800811005100c105c1d0018007052031f040c0400c50491140010307001862042c1 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 609298911 1250 609297661 609297671
    0x50f0a030605010b030702070e0f131e1a0c1804020f07080309032206021c0320090a050d0b07051806041413050108071403010207080c030a0e030c0904021201 69
    0x922140c0c00d40c0d030b090300030710407400000042c000d00d02d03410000c4200800a07262100d00b2824450200c0051443c003820a040e4030007040422400d1200300d640c1d09200c18000104800a1481c1d032408207008859074103005401c000304000103109103c0c4a0441e901080d0002650b07545100500c1004000c1d000710309040001c8106100b03c50008001500a43c00788401d40000d688500c4168450070359584512800c140898948800708441b90700040e141c06400382603004190308040c1c0603405c500030802060310140c030880880ca50744a00c1421401403080c0107080d144107400c00c1e21501446420504c1e44d100400041005c40020302032841030f405064400c01c90b01140d91143c110000003034060704030383c00002d000400f42100310070918042840c07020300300c070004007884158904001181c54502078400e41d02da0388801d4085041030354084d0b04031000d51307070321000c02e0340c891603a046200e55035085141c0a0380456883d00c481c03032030b900c0c000600d124083e00050041c41666150703070900088405008280c4c0c402d40d20741c = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 609300161 1250 609298911 609298913
    0x206090c150c0115031406060307050d0f0203250f0909050a080f0405180f1308031b0904050c040501021207050a171903020901170114010507020d0605090109020a06030e07050f0a03 79
    0x481c1d4444011401b4000920320941038014280c00e002024000b64403030750002000304140d40760441100c0c0895041640c0003400582400800c1c100b54003500081100c00c6003c1c400c070800182085050145c40044443e580c00c1521606c00900329446130002a011350301c94090300c070018032034200500c84201c804a800c5d06080d501d00201c0c0750103001c01402d0f04100201c600300a4034654007406141d01000a690030041602251200b013020710002c0c26202d90f1034181c070740c2703170700c000740840121808034401402c01c10892604030042c8919401034003a45005014080740044200c4200c02a070321802d400030058000440e590b991801000a032803c070b181d2405090004070b0303400c00555012000240385480160752a510071000401c1200c90f903000d240d0045800006100400301c0100c05500c0040070f0900943c0d422640c00003c20542030110018101411710042000844041d0400b804030380c400e4584a04664445100707034140c41c8268002900d550042000f0032441c90108030107203110001812680200391a = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 609301411 1250 609300161 609300191
    0x111070f05030d0e150a020327010b030f100c090803180a260d1107030f03020c130b03120c0c010c0201090b0d09231b04020d0c0206070206090c150c01 66
    0x351513458480d07044071802c20040b861400416611819106003186189003041455210b5103000d949e0200300065148034240b2010254084041c0460090448003103412580e081170f59601a2180901242d0900d1011a12540203444000640c0c0c44400610f00300400c003003074140c000342550038165104403e0100054184004d140703010030b01c03040c401e0094000007019109450310441d081c580e4200480034038005000c580114542040d030350b010124041030031140c1800c0b464080c2000000da485003094411803a2660301c0d03440703264403000640a441a41a080d215561140076011500b0281c3e00300210700001903100d4030b02140001e00c14106649207644550000029800c1010700c1c5915580d1388141d0028040a000d01c40313038a4003400c07035210f8042e03e041c00c0f80c1c2e15000740d1615919000c0d0081c4001140384c0d1950140c82085440f41030400c0080141c01000f9620003007581c1e90400360054030089240c00c03102140042d00d000c40980300c0c01d40c0c980d212400300242d6110051020441d540c0c0d40481c004c41903 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 609302661 1250 609301411 609301421
    0x621201c020a0f09150623030402060d05011508070e0906123c010204030503070b0c040b0f04090c230a0309080a08040203100509061506070213020307110111070f05030d 74
    0x102d00d20b00011703030498124103440c20701c94603000541400300c060f0200404081c650080743c450500d0300c00d032944036203503032021800303602807250f01816143c14000042403220350400c01072050340c5256a102800e4464407810b40d40a9280044250010420f20004045d810594000f1400381450001c50b1141080c40458410f40d1100c69421910800c4004603041070b1640011000d180c0c41841c0c0085240514550701c80760b4134411418000d20100000b00040c0c1203240e8442694000c1c20101049540c3c4c5044403440043d0364000d024441c1d00720f00d00740e4515091481030303170480d200c100c0e100b5074a16100c000c5503d02c2c801c0d8111400b4401059201c0c6408400a000305c40075080e04891512843c9543c1401d00c109801d201c10b030900c2d4440c4030318210030440080400102c41c0c1c3c008440c06150902c4111600c0411441c0c030078604080e4110b081f4040c0c00c14125915402544202d405076286003000000021480c260313403800d50505c0fa0300d601840f842003c01e6040c210200b850b03100d0400c80341b07080311201112013614 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 609303911 1250 609302661 609302669
    0x203030d05040c050a170a0b071e08071b020a1404021c1505010c0803010e1008061303080c120c030c1e03060a240e040621201c020a0f 59
    0x83c00307609041110f0300b440d0960070043d084604600002000402d5440c7d40c403004408060301000315203000c1106507000f110b0709034a0494080222560400041d00078150360000d071503000015000d015450240302c0301100b80c00c41c80e540244240c90700303494182070480d00c0015100b12a0303c80c0c1d0801460074144d820100520001032050404605241548818a100d07116940700c94180410381c02d04400240301e40d41140c8c1940d11046145525407681001c40e1200081078000020a102d00300501c400c040304004c12a14252196690004680c0c0b268019991400340c8a41d0003c00c080c44404100b4000002002d950f01ca41800305590800b2081070302183c0c0c498a402d010000c0080000501240341480840d600c007500c0d10b00f0051414125a11225200035103002c18401003203082055000103903929041700c4002e041c00b0144134030f035000d1010b0100e2010220201150301c200454080400c41810804245d00d4a0300102102410040c0902e8140b5400006800b241d00659070400803d08400e0300d0150070241c = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 609305161 1250 609303911 609303923
    0x204030b1e10120f0204050702011508190204050c12040f030f030203012103030e01110903100c05041806030803070c05010b030604050705040e1603063e03040203030d0504 75
    0x80c100301e646001a89010100c410030903000008010a032004164080c003210341c10320300d2032003803069030030305212064055400031360050410b024000c4403541500b04444540341043d0510f00d40c4e60310045640c0d0307860b2040c0d42080201d078002c00781003d40b074a94469a40407014604513880c0c070140100f4864100d200301c5084441603203804425003419031004014a08c019030b402c04525550601d042c240481c052407001800104904824608240c46034100c0c80014001c02d0082c003200102c651584d80d5030300400c040500910030054407288500090080000c2080c158071101d1516040445418a14111100000803191103620000020b1030702e60046206211650301c0212209082c94102c0c2514416000c1d81d00ca83d100d4814800490008200340040310012500094040d150300700d0305080060403c0804580d84418100006018080e005140d130406d029681190f000c0100ba40f4000d11a420311184002008c61f5070600032403031000c001150410300042c100c0e410039180201c0312080d40c0c0122812948 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 609306411 1250 609305161 609305183
    0x3030705011503030f14070b0703090f032111190c32030304051b0d0c14190605031b040b03190c1106060d06091b14120a020f13020403 59
    0x13810381c4102d04017016036403458482c280b00d554043c881c545000c0e031140a4949500d050100301c025000c0d6000ea800d140e0b02c404134a44207c29400c018100401807000c800091448020300b440c1c00d80b103407044420300c2810304c48403418101c00035594580aa108081d00042c0103190200b9000304403410000010300710030040d02d08110301c0d0013248921a048070454650a548184140400180003042119502040b0032101605592200000d4850720b4210303001b0381442220340e408201204140c030a103407100c0c002d8a1140110445080701130702c2110714818240041c00600204030342e007070391070b800060501c1080c03a0b4a00705519000d40c1207241e4402d07200c040102944040300c110320f405c980a603c00465541c10051071030400b0b498001d45a01000344650300c02d140111524041200c598050190142c11204c4960000d0228500c00c0b5181d007207002e40c852074500c00282a4051501c80c81b0000f4040c84a8054440190700350f081c0000404d010741980e511000d0120a404201c540f4409000110f000d0700701079403 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 609307661 1250 609306411 609306413
    0x4030507030b0619180c140d05011d04050d05032a070302010e0c06040e18150a0e01060b040b0705100e030703031505090f0a090209041a090d1d03030705011503 70
    0xd4160401324001d03410480f288420061000d9074400c1c0e001040c1c0b03041002c03074008550001205c420082804443d030040020038910400440c940c00345042e1541038150400d0f81104044601d001e5100f00c400030304941c49070480b0408240309074084c0d03030081c0044461082d0088003100c012007854a04800c03459920700499284103040d0f090040e032200d044094050070144007c140800c0c1503101d5800341900604001001c01c4c18500c030701c003146005104007801d0b2a00b4030001d48044440341c40585090b0300d40c1d4100f12080000c020184034030000c4408005409280500d81500904c49030041c081c10703100c0313018009810250203864041d030349800c0c4414020b5a642c40080c45d010b0304071161184c5101140189080a005684a01c1c651941020b02c40305d651259544038440e600242c101e10304000d400903040700600c81006000c5d444d0140420380c80295000c250742d203090459841181c4c210140c0003405480c00040484258480040c0422014040e07d01c1e0452544980d82554803840110040c440e040070104 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 609308911 1250 609307661 609307669
    0x6030c060c2b020c01140a230301080105061206071d0d1208160302031005010c020303040305031201091802090402060a02010908040b0414091603020a0504050d0b090f031315020304030507030b06 85
    0x102020009080010b014246e40042c2c50a5000b006041e005002c1c0380c0c4440150061131461100000550304d6000303540e5030312642514040d280540f030752402201e51500e01c00443c4004680ca81c402c040300d54440030860718407482942082c45200760250414480320500d804120300d442000c146074100c0c0c0340d0880f02e08121418400624405100e40d0406106000b07005c240d01c5031104023421520241f0780403800c1c44003400000c1c02d5204a40c801172075031100003400000b000401041a04844a081c010844589541039900c880d0b20490743c001e60120510000800614004000c1d080e425960f02c00000c50400d036640e00101940701d5000300c20f01180105c4c2c100408184190b030a5803107601602c248016041907000d180b2040c0d85003050109064000c91300003440c52282081c0c0f4000d06000f404c03c0b03280900d50600340e100540175550302019004e501c40700102c284c80042114585283c154000b0f00292802c1a0720190100c1c8002003021400708000c0040480c1d810401c840155010b4055140e40e410001c00300 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 609310161 1250 609308911 609308923
    0xf061c060911030a0b06210d0c0c050f031e070807060201090b070c050a30200106061b1128210618020a090e100506030c060c2b02 57
    0xf031007036001d00c02d284001010808981d0b00080181c0715050707402940b1807a680c1500102010312058410030316030b1408542c0c0040c404031114002e041501a140d00e540c03e000307a400914054a806d58405005d01b48100c90b210b02c1810a6015141641c14080e01d8500030307402c20065500800050b0345488180082c050844200354009c00c0604003540d40309072580d6a50340354030042002030710140e440100c90b100003816004481403929400384d42c20042c1019a00907007003c2c00080c01c286411082d01d1001600c10052041c00c06035120350b101e20345080c000c4039002c600c1c110361100440e0011542c040b54110341d158207105c3c17001c009040c147c8648103461401c1019000d49681c2c003080c0740c0c00c11042c14001c42e001250f850704060703400c4034001c1800d07401c440710302200c4030821400a4001500c020000381c905540da210200c807030283c03004d58410b0b8408e109401c06840040e103100346d00d5008290380c854076141050061000076a21010f44014100390030a0403c1e20680107900700c99001c100d41810412a818029 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 609311411 1250 609310161 609310193
    0x60b190908010203060a2c160818071401030f1103010e090a0b0601050a110607051c020310060c0203120f0306010801090c170907050904050309030105060604030302060f061c0609 78
    0x71401d514041c80000e02c217240520441841d02c90400b000001300784400b409861590464451089604180700380c05184e148c103048810004c2d0012001c241d4400350b0000b50050011090000c100407401c1500f4006049503030740291f41456560200d811051015009e04221a40003000321910f84d03241826040d02101e00900c46240e90f00007101200006008a5241e604150b0070700c2e269445040580e015100042c2e15104800b841c815042081301c0c0943c440000c003068000602e84415481460b03965034181c0c00b0640e150320404601d6001441010300c0f82c04040d00546c0010226108071003a5220541d02e64050a017594080400208000c07003540c0202203240102007040b8208840881210011b00701c20340c41c10005021040a004514140c1003004024064070780107000e00a507060510300259258045d0030424003d50801002034031510341101035900b141e4040c0c003c1d00742640d400c5c00101080c0380083c82181d00000655614190f80d020380070104106210302c00c0043c09c1e0115003813a50300200c100703075 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 609312661 1250 609311411 609311413
    0x50909030a05070f05011a03010c03060317070302032206030c05090603041709130e2b230a0c0302010f1b0806031905070f08070b030c0d060b190908 65
    0x50020045000048640e408900e10307210391103944500c0e049550005200d0701030103960808001d103203480403010b950100501d088000700b0420b0400301d0103805669403031002400e6002c42441011b00e09060200514115100e481600d01d0261a81c03107010700e114003c404400c074600749580c14068181c05100d111450322280c05c246080464481c0010840c0c40014070040c5007880c51284500380d101440207403004d00400402080104003410008001041074a5000255101c0d00900a600000303040340d400450401c500f541d04e50384036421042c0c400c4d408030402040528200c3e8040d180e0a401000034040b00c42c05d0b603582100348400750500a00b500d00c44a0b00e200070510341103500050700394071030060404070a241080e00e640c1d65104006401e10200b50340000340034801000d24000c00c000403030780038107444000802c9220030762203038a9150b4a40060040c2c4000c01d01c100b011685040b8440c02802d5140801d1902007007542d22007001c140c03190801030505690301c00000d15a0019500261104081d141540c = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 609313911 1250 609312661 609312679
    0xc0c0212150f0103051204050a210b0112020f1f0f1b0b090d030c0f0e01031d1507030b10030b030c030d120c051206010e011107034403180709051005 65
    0x230000035000c240c0c0d44101803000c292800700c029114075503442c0c0c040c13190708440001c0c65507035180080c0344e480907900c07002c034494619a0088040b070f14280a000e9100020141202640b0303141e424240c407100b5503d8220401e115201c2418805030b2000c00c030210f2858405c2d02c40240f54101130f04c0740c0b880c0c0300d4a03140032002c0c10705146140f4502a400044103000051600d40000d0010813880141c1c02000001200203185180b440c7c013000500c0700042c0784040200711030240700181d694410480072108120106c0d80d0141242d0800ea000510903001000764407030060580e40a0041000042e01d002401d541c84800300d86035442c0701001010901c9000606070301030034014a085820603e4550700f0303100400c01414890100e0002c0030a92240e83d4040c1c1c41041a8200c0b49255101c1c1131014401d0b83c50344500110081341c50032500b00040c128019040150483d086c5070b400d100c0900144529000141036150b00c1d2186185003040c0307502008074100401c404103001541c2e08045000311103400c05504014000c50b01c0c0 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 609315161 1250 609313911 609313919
    0xe0d02060c030a0e07090603030f020a03050f0714010c030c0201050705040513020d061d09062202120102091320070b0a0c140d0b0a05040c0c0212150f0103051204 71
    0x4202a079001102a506039981e40d5401c0301e00c0c000380f80c0c2c61a0060346100d031090104450355160311007000e4902a0300c810081c40785a441c126030381d6095000080011300c06100c002c481c4c02d096000707883c4240c41040b43c42c034407100c408841421652a4282000001d480e0759004004940a10455400c039030304e03242051505080001051010407640300c1111465400114050600000c0c5e1181010309822001c0d099040303d42d0800300400f02043d510700c2ca890084201081c42c407204440001d4108003061540040a00640c00700718412105800c0004295002c200c0884550340d805d0004900c40240701000502d202440000300003415100c141c003840d603030b00704509000302c1d003e440400d0f409441200081483c0f054104100c4513000c8042925a070b1500100f074202e42150690010804082c0c1640c001d440d03959034108000640382d403040c070340b00412a01410354001d800d0410044158903054000c0300c0c1c00d0700c0184290321000b0310490b104e407801d412007001401040400e00c002d07100d510550075624142810 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 609316411 1250 609315161 609315163
    0x906040209010c0813030f030c0311010b18040501060b040803041a0306090f070e030a0804241d06090a06092d06110f0d180524031009020c0a060e0d02 66
    0x50f01c00203001c10303201058048021218100a0019581c8028112080c182c14500501840c5e0658000c6000c50080801940408014820103016080c0144000160104d1024550000780054000d582c0f075509c540d004a412840c0070b0040c0010050240150344c1c0d00d28020301d01b10014048800e0000d0400c0c100b0600030f03e42c0e2054522034002400c0c0c0c40f0030740140c0b44c1103000d50300030885074074041e09805072080400031701051002a104072520a203100380091400d50300c0200b000039100309000402e040801105144070242428140d154014001d03e18000f252400200d411031030707902c0b45000400d0220203002042c05424840410514000d080003103084c254401042c00403640620030400c48201c08a0035004070401c00006190003003402d64103030420380301c801051501c03200c0400c0c0385c8031119903001234241060030010800074480400700740040b001000010259001910051821100032008200040544028280d24085500600048150346080c400341c07281401c618a150300581c101c1c2440c590 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 609317661 1250 609316411 609316427
    0x10b07021207150201020304020f09040506040809040902060d0e0d2d03140a0603030f020f061b07050607050d05010f060804230f101b05072904060b090604020901 71
    0x25040714120050841a61010700d858010750022002c003440c0214020095019030045014034000d07200813140f0b80022041c442e066105440080c02c661058002801162101700604503100000f00045090f0034181c0015840e600400d8090203002d50340c0c40c22a8942ea41048100c41c40141ca080003c0031418030b50108141a00c107900100744000038100c6152000e02c264448541070303a008044589904220a554004000d18001280401c005280403640c0500000383c001d04104070790018500c40d940c405026200d240b0000b03403450150b1007442058005101803022501c190050356810b03860313030308a01000c402e540041c0c1c0b10034880e0400078801e011860b402400144d00070b402c84072000400074100052941002498070201c7e090058180c8100401000b0840000e840815032082c8800a0b41d2000390107000280307881180410810000c01740014083c000f500c807504009105548559000404580e048130103c404403201c6075903940e180e82a04d0000c1d034164002200396070850400f41d502c400686809 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 609318911 1250 609317661 609317663
    0x90f0902070201051b0102070204050619120c0b031602100b0a03030e0d080406050c10020a0e090c1c0902180702060a1a06040806040c0806040b01030609060f06060f0e0405010b07 78
    0x190009000001d59015104961750342c254591003200200f0004034a500035080f0a03000c030300ca2410040440c8880c540342c66549042801c600320361540f6440c010080070000c403854000c032003442c11440c0c00600055104082d601c102c00f1450000841c04d6910740c024100f40fa4480324024482c50310031080c00945603104844256989824003956000340e9100240140c43d01d288020310148000902180d102c0c1d00902515030903002030708941035150303020401d000764099174000c00e0014008104801051400c0b00e103d5802410001e4090725101281047c00512200c0d409803481d56522403228400314142a0301d080701d4036805012036501401c102d0740007522500045c00451b9071a84481401c0c102a400341540514248000c000035525548e03030708000e88070303201201c0030307203071000714800000e0001c03000b0171400d10959100c00d101d112682140c0e02c8000500c002d84054071515034401d0301029030242c51081001510480d2540449020102d1008000c000c0016066000b907003400b004101d109510300554201d9 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 609320161 1250 609318911 609318929
    0x1080601080a051e100615020d030b090f07110304030b010f0e040b28090c0504061d0402010c150905070e0c09030304050d02060702150c0105010906060507021e13021306090f 76
    0x100107008003c624101740d40464203e1289001c10004519202c030a403542414410780944201c3d070040c0006400722200e00b841075030001846c100280d8000309060a003580084e50307042c0b0a03810303008004079a1071a049900101d0b000001280180041d00803520082d00905080b84c4d40381d072501c0d041d03480f100910b00c00303405105010042c4402d03265150200313001106441c052801040024401e00381501c0304402482480d000d00d1501c00c005c0b0394112002c01c0e030460f184003408003c1940d25280e00441e00b803a1500c5068944d40303924889202c640c4a03a004a01d819170184004003a07541c1002c5040d10f5800000d4448c5000f42c804002e50009a203010003030300d040740c4040780c2820a00f105400030820318410420000e6120414150301e00380c0700603500c05403400001040007008940c0c0c0340d4031801d088812600401c800706a050103d20018a07004100031440e44951140700c251400040c0441c61168084504048460b008901820030242a0b54442c008141900d0070f00c030744518202d589031501c481ea000d0ba0f003203 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 609321411 1250 609320161 609320203
    0x311060703051209070b0a0e1903390e0a0b03011b0e032506020c06040302090103061e05182104060f140a120515090c0c010603051501080601080a05 65
    0x104c1c07007041c0170600043c4150304500340c0e18101c03a00010007406442e038019100300a090809601e000c40340307020506581c0c3c040b480b00e150580084503070b01c03c030b0a020642906103503483c00e124012054500080b004101d801041e145030705158005400361030300ba41d2518066851719014800729842d00b4070440c800601802d0110071018200d0129040020008024a8401071303000b02910601403145c0010860f0001d9094a204107a83e10810100d44654400039620030000030040c4041042c0390b001c012500d11303082000e0841101c00490900b650340403100440f0002c1e80c0c0b0403140b1851002d000310820081000c2040c003440300c200e031000c91035000301d01179101006010940c41f406140980c2442c1c0c004c922010005407618881c0c00020b0041d080040140f0785142040c02061603440f502d080c080b00a00000c0070f901e80c0b55a0300d8138044564000d01e01031000d644d00c515002011071001e000805030841030303140803840c0d58181030342e980c0b0323044042c0c0c4061703030725403103001500003142021415600c14810780303084000d = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 609322661 1250 609321411 609321421
    0x18050d080f030f0f07020105010f09020322230f0a060c020328030c051804020f1c02030906092109040e0607020d030501080718020f070807060603110607030512 70
    0x46280500c5152034810107002080c041621001e80e40b0510403030380f044100c2d5180d035903000128280c820070703c50304100f480e07001018171006146801459004091030310b20500c0100d0a00900c4c0700c411000019280540103040c071a08541d0a0aa00c10f1804c180b40c0003020100c202c0c960096a804003c14094100307550f980c04d61802500c00e00407542d40c0b003403000003170005c1000b0114034032094a64000c43d102180c81e245108888500490a98050f0340801c07499030540d848060611020750b120303080c4a52498000c2201c0300482100840c1c2c4020451350b82030060b142d00d0310708055840d1820140074644603610281080360181c08403081011480403514001c0e4031036188101013070141000b0080051a402080100800b199001500090a00040e9410f004036640c1d1550107440d074102d030003801044184051100c01e0320244d80c00800074000c4c0c02903400c3c40d06407151140703660b642116070300b11a2103032034203002c00520802018001041c030045801c00c1c42c1020301e9401402074403490201da500341d01c45100042d = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 609323911 1250 609322661 609322673
    0x2131d1b0a03080a0e0d0312050a050105010c1103120a0809070b04030c03060908040e07030b01020c0f0312180d0c0315060b030f181c26180f01060e04030f18050d 71
    0x1400000010b45001b201c1c02e910319010300710038048444a10014908000519092181d0140e58100ea1040c1c41742c410001081c1c44102408080d10303c85074151240c001c000034410911030050400e0f6000ba9a0981541400d94010f42004480c2d44081d00300300042c0301c10300210380c5911881044a030b11078800a50b4030b40503e44004035003e983d03c0840075004550800001c40c0d0181c204034000c0c24240c0c00d480420002004024040508504e5650103900103603042001e000218020802c5508400c504003001e19103070000369035003505000c200d4005528a00c20410014071200c8046001c083d11024001c280c00d00e140c61a60307000050040000d245007601240052900900c1d4050184404050b1400e201d81402600f139005145107400002520307660204174862058044540e1000d913400c0111400d40310410301b800290006800301e441c0380500080419081c109201304802090b041405410501d4142000342a4024409640040c0102c0300240481740e1500d42203001912002c40f00046060000c1c1428 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 609325161 1250 609323911 609323927
    0x9060f0c02090a050103141204121b030f170307020c0d2a080d050412030309022e0e060a090603020d2003090705030f070e0402131d1b0a03080a 63
    0x70350080c0d2441c060181c1d40000c0c1e040139050764000e101800b10b001e150301c03503603565403ca20001041641c06001c1070286c0444410345c4081c150040d00c035186100b0f01101840482c96041c1d000720b60103040ba010000402002540e10b03446000782c0390b206421441c0c40c0c5d2002c1d4940c8080e1340000d100d902400d0341041040b00d4a80e1351308601c0c2c3c20b98801141885242000301001d0050300451855205002d412111640b0500840e0207850325104c130303e4000c003440c0d0340c258080e0141c3c020881e801a820a00c0e40d40c24a401c00308610b45440074600c081c1c0b0028900005030080744c1c0003d489000e40b1b0100440702001d41c001d2401c2d07080318410b00d001690f07014508210740040440c011050525a10381000520408a0304003a42c021500700040d6050079545030704156454182408180c85c54015002c208203289001e002c0a40c040d0001e822048504d515540da4000ca9110f020031075041040410f0500c00e500080100d00211555640c0002c1000501000a910841c45100040982c9400180c0c8400c0c98861808 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 609326411 1250 609325161 609325163
    0x8060f0d08271c0609020427030f0e03031c0204050a0915090510030b041a130b0106020d120f020d1d280b070212040914011509060f0c 59
    0x88544400041290500d214010220701004801c00800b41c0018688000304404200c6810000c1c504003c2c0340e40c0e644054003c0c0710080e41e00c82d0b6140118440a8000d941244230b40c504105003201c0380f503861030054001101c0d00150f0041101c0c0780c482d888146c070300200312034907810404158440c0105c0a43d071440a0710036a04003a401c01d0300b032400091619084e4102c4000002c09200c4a4045500d07548114220380d8200e4100602450b01041000410070250210340c00900401100c81c04031030002c4007059200c4180c1e5052407038059606040103020181e03135030902511062018014078202ca050043c00b03003441e5405848229500d003141c052907861075046802450f50818103205148444c0110150601c101c2c0030004a4080c848003003034005860144103110001040c60b02c2c10980094503260343c01c0c13500908000c1503106c3d49208045840511016000814100b007000c544601e4614201042100691142d440b80714260403040406070005c0d055130a84a203442c02d4450700f654424119145940060 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 609327661 1250 609326411 609326423
    0x70f06082707030204050c030708010302121002040e0105040507080903190e0a1e080f12071a090601180209030706080705070606140f010f0f1404030209270601030308060f0d 76
    0x845421840700400c44204a03030085600b0413084c2d4035190713080d070184001c4903500c0008601c00018401840c10f4944207000360000012550f041ea03024413030004030380c015000054201440801004103190500819500075102d1070000000d09200c044075030b41c1e0050022554804400702054803031148140381c0d071840c1d14801051000703d0fa556a123030048110300300301c1d0f14080d05409803000c40c00000000e4094880d40c40300b001014405510349114026030014041110b44003483c090580807140c62000603030003503141c000a0821035140c150301c02001540007a0b0035400b0350040c031105806540208200b070482d0b0190400c80150f58940c80212414418107d0050855181c080003007071414807104040c0b03005000340c85410650801400544118049241c244005443c1000c0021024801c64130250b410490360700f442d041c16143d50003e542d142041764480c0310108948001d824401444481150070000480685110350454034000d0039084000d2a040c081d00e04200400e5554868041201c1003d070890 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 609328911 1250 609327661 609327721
    0x2030703210e150f060307120201030f0b09090c041b0507020402031510050a020d05030c3702061e10090e10091a0c04060207090b0406082508070f0608 66
    0x1a2a80c0e841c1d03009071192211300300700400040c0300d410000b0b112016509080014201c0c43c1c010350045015080104028000ea40c48071800412501d803400054064081000a82042e00c81801030000300c610f0215004c40301505000880d0095030080b0803201c06917011f403405662595820314a400307910070f503420203400400d80440d02c200e040d4404050b010a0a0b00c1e402da07601400300c010120ba10740000c0c0e40c4001d00d020200329880c88400c2010f149103820204100007400004981c2801c038403219140242000342e00310318100218045037806881280007041640416401d04800010b0900464010702038180d60baa0362411000c00f0800600480c154450020701410109140c2003103801c0000c51b0007047d00c01040302103601c0060440c10746007511010341c01481c0c1c50b46090722000c0900300907400c1c5a0444d13520036000c50312610a21602c9004501e441e032084129518595107000c009280d402000141c112490a020024849100d881110350a240c04081c0f922a268a110381041003544540c00e190f10b0 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 609330161 1250 609328911 609328933
    0x180303110903071d0a090327080d030f0b0a030c030f0c052e020a0b060103090206120901060501081f06050d02092d06090a0e0709030501050f0a0c02030703210e 70
    0x8a40100030241c1601c00803610348400c00c801046e5001404002c003c244103c209044078510090180c8480a840300031583d002c0e51005640d040c102c0385c2070301c00002600c2d09950794020340e05009003110014103503280603c0b1495920b41e0303160003100740002030400b100c0c6990801800b03203644130180a04001891070304017400c500b55203500710081b94400742d4982d94004c5240300241c0003284400d0080d80040143c900c0d070381c0d194011801040401c00803030b404101400036a00340c00018826178400d030041c0000080b82070801001510380c07807000340003112012901c1805c000d03c0d4060000030040b00d410b4180b040c0c03940001c2540350081d0041460642d0006100c10102c000c0c803020b1020180445038200d00013203161043c2081c8140c51042c5424540c1007580410104a410342c8002e565030300111500c0c2c9405115140c1e6941d6003924400d6500d580f81143e04400c0c0a810001032041c82c1103d003007800118171f07040141c0e802400e40703031150403e540d640c2800286a000c0c04020340051103044141c0054804141c12 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 609331411 1250 609330161 609330179
    0x1816080123070804020f01030608030304050a06110a02030406031107020324102601090b1f09061d0a0f0c03020403140a0302120d20190318030311090307 67
    0x22064145855580503080d2192039002034280c050b440680d43c08000307503656002c2c420085401c5680c4c60400d50f03500c600280c20344060000d503014600c92000340508400341e04003002624a0304000000c0c1600800c0003280a64000084070111001da040101c3c50090a00c490081800b07003a8001e905070080d1007004590105000114881424a0040300010385480741c00c00c880700400e005030f4031008101c1041000c090003041c401c00740c64200c4c03000424500a030f6a11030407400426200711012901404801900d50240d403010303006010640010040704e031511442404112000c072001688240d1600031070703014600d40c1c02941c0031032007001040c0040180d20000800070360082c0b00a8503d2103801106510741003021480c480c078203805900502c084001d58815181c2070f840032642d10983d0781d55903405903039031900d90004440c900058000f10345a051020240700c019400c6481c0200b054034000c02001e01d21840c4043d644041d82500e03000070780103000c0818180340c0c811940f14940c944500c000001e40100 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 609332661 1250 609331411 609331421
    0x90607120b1c170a05090112061d0f07050313030e012c0a050307030206041a04030210030501060f230a1206090c12050105010c0b060f12010c020c0a0e18160801 70
    0x203c5040b1100b400408052400700314003c0842d6600003075000c02a24602d0b43c42005d600c0c0305030703400b80000200141d80320780d400102c13040c0d1011202d210b072a850811000c298080320f41030303000c081404c00d5481c0d460504000c010308032845400409000c2480d49861a5074460415a194a028100904940112115841c58400034004440e105451101d000328281c14003152503801c80e40c0c041d10070f82c1800d0038551000000a95134a00c014049014000000540e8a464002d60004076603180003030781c0e5041450003401c00c0180501034050001c0206c01c01070440c244400c01c16904001c1181d6600c404450104841c3c0d04003121f400d40500c0d042090100340c44000c0d62241c1d07031100c415114070041810844582d01601d409114507808188140260004205500091b9500003402010700002d8507010001504d004c40c0ca024103195603645c4c1d06200c0a081d010810052021012603d04100500d483d403120942c4c0300080c450301503400c028800c165000f408004200050300501000040f06440c0c2c05010300902e = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 609333911 1250 609332661 609332663
    0xa03020313210b0c0c07120b0a0e0604021e0604080609060108070602071203050c010207050105150301021804110903060411150c100b030309030a030810050603090607120b1c 76
    0x3801c2403200080228100d02c0d040707848400500c22409800841d2165111164020071001034008108464000c51409120a101605004280060600050a010401d0040200ba00e00b81610b03007080c41080e151b0000756142d110350304039221500c468041c82c40c100c84004a18145401580c08100400c0404001c10514403980c2010101c5405031717622420316a13146c68900c56840540c22400c0c9c01d0150382c040d400748100d0a4003130300304030b494245201c0c42d0900b2640891000c1d038990355210240320803201c400c0e280b040c01d0f103000ca00960a10003420f01d950580c45581429902c01c0f07a8503c854031b804424034040e00d5105100400340c4d0744c54034050401503004051403441c244a090a46408018440f054055582c01003a46000f400c0f400480005140148900c10791142d251009000e14901603034200311350050144030350346948003030814844526840d1031642125110b1042802045414600050102e51024440c64041e8280c642d0405800050000c84103494025074008010110010358110121010f = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 609335161 1250 609333911 609333937
    0xd051804050a060f091d1c03180807060c020c010e0a06050310050907110d03140609040312050a0b0a17060c07140a060b12070b1603030f020c0c10230307110a030203 72
    0x2030811224480d4640d4044502c0580003040c2c0c947ca202c60504c030364004403164000c1000391141c040191580c032400e81148400311150f94549004401141d410b020f04c8002400a00b0040ca1100700c1c0400641500c4881c09040100711000c00050000340c84e80724083c0007040050035444c81400c01800003041560f820750001000d100e85500c0002c814800c0c442d40000c1d40d485e09000e035807529214104a1500000b40042d820021001440e00682d42d251054501032002c0010000d40e500d074800c280700750042c01e64400b6514083c500079051241901041d1690300c078421600d1240e4819031440c240d501110514444420361003480c034070000300103c5503c00c462115040ba411000c04014111180d40c610b098000c000c019803040c492403540300382c80412030100c58401e04000c18a05140700104040f030f003141c4030403941341d0b1280c51511980c0c20320544850f84031116240c04400c40100c034510305214146404a241c1d41d030030000000f545144211071401d4150403000548142d29100d040096581c1c03c0b0596141c06 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 609336411 1250 609335161 609335201
    0xe0306010b19080408072f04331502070e011707090b01230403030315060503040807020109080a0c080c060403050a08090f09070c050d051804050a060f09 67
    0x60034070305000b034403200c01e5100c9880318902c4180e4030454034124003034022540003a003400f4940000d040868007105200094091913400642546140032140030720040320300030340c0f07030980803200d0724840d803400e5100c40024a021007101844800000c0100c10640c4542095515914ac0342d41c1540c0c04503502d0200c0300c003e80156040d1340c0701c80503a2408013800903440082e61240c078041040711200c0c0c01446503200141000c40d0340c000e100d01c001800782c069034000c1c6103103c8006001c1c410950180309256071501c008001e403011508280000c0c044d03120141c8041c041344008200d000440e0312504d4808040c09010060b0b81040d071461800ca0f81402450094020302d001e102c2a10340d85003403200964080b6078000f8010000c1c44281e0f01e9010080e40801201c0380c01c080b0800c9070b01100c1d206d580165000f0a100d81e0382c8106440c0904042d800c203807110000104001081052106e2944074001028120908540016082c0ca803526a1002092035901c0300c5d02455030140300290207078140e0f100c0d100c442e50700504281 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 609337661 1250 609336411 609336419
    0xe0316080c011d2404030309090e030717071502040806040c06110a060e0c0a0e090d0f300e0307030201110f0418020d050a0903020f07060504090f1b0e030601 69
    0x40554210b4042e030b00f0840b2003180f4084038903000b03801c031508a94202080000b00c440f40e11001403503109406c1640810070503002001042c4c0d051254840b04440d4101450030049a80d4031071221903505040d0010031507010230740c2010710082c120804440a4207c3d8210b68444d03031281c1641c4c445904032002d0b200404507210000310305010724203010400076524040c0810070130969403080144401c540c890098441c2006550043d140c403a02c000103171940142d012400d240403140c0078909100401038004121031101e07400180d0303070401d54441d241010113445844012100c083c15810803452203819903c1414910621003204010004181c110302071303402070061041039903204801b8400c004c148100e00340100720810403403608003440128803007511000751500158640390026200d094800103c01a610070041042640401504c0c4814101c1000b4002e00b5140c036101074001c2c041d5100b103505c0c154807901001c0d110380701544013031800000f0548140c00d50a100d10001d201e07543c00c400f0b0901a1265070300103d = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 609338911 1250 609337661 609337667
    0x12140910062714011e08030702010c0201110102070605070e011d030d050c160f1d040f1101020a020d08130609210f020612091b030606040c0e0316080c01 67
    0x702980c050b070103010725004800800540144030110354200d903030f40e5a00c15125500b00c4801850007042506665443d09071481d01481011045078403840b0203030700c05c1001d40f00507600b00c0c01d1071364100c1c0c09003890700404080e000007a01a11848000804041c0382c8000c21071302981120a01d0f040e4003003aa6040c0d405840d160380c1c611404500c90030280d142c0d01c92001c0490f40c1f40708100400403444400107440e00281d002c201305180301b5070398101c90500007405500744804002042d400b01c803060b616003110070703d04158070340d08445404018041c2480341c2409141000364020403411103120b9014240280c030407103d060004076904401c50002507001000b80029101d84a44801380039601d1001070303860340080b80346110a1424644908071418100d07400c0e07507400741e520f0f40080d19150940320030180c005c0c9032290286081a18002640500f505603481c10807960300d000171070a0b0300c00d0081d01c3c000350b613503a1000f0641390f039000d2000540d031600c958000740880c2026000c441c001c0710000000c54800d403242c0e030015 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 609340161 1250 609338911 609338921
    0x120705040c17130b0a0c02120307030e070e01091404150902030106050a0e18010912031a060406020c010806190b0f091c030206012909010908010f060602120712080712140910 76
    0x48e842080c5450306820030400564101d8010700f4000344051075140bc0c1401c000c0300750b02c40000c00e103094004020046041c061141500c40c01000701800b0720b45540c2e40d0b5141104104451700040e41d84d01003038110b490962110000d41002401040c0072543c88554540c400d00c1115424003040b206078030301d800e80c401409074221095100d4130303a41c1c00100700407049000705034204601213065030005e0340001d81c0d20b0f5100140050400c2e41c0c064040c0052280004d45804000f0b05164010540c40d2907400c0c9099070103441034280c46600c0704441d59050184040f0170140185c4001c1540201c1c0c521010000908000400b0180c510940039034840383c0ea1458a41111419040300b5901e40d0ba4984100c0c060803e0a4028502c50344141080001c0c1030312910076500b1960b032040c03089034282ea6030301c003840901c1d010840d1423711081e01c0c030494540440d41c0d4030304051a95100708003003445080381c04a0103050207030550383c21500052404100026201c0c500b03a03140202035811455a0295400d0f00051039414000d07 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 609341411 1250 609340161 609340181
    0x5040509060103080a0309020a0b07140c0a170f06130210021f0b19030615050604050a030618061506030c02030a0c14240603010b120705040c17130b0a 66
    0x16003040d82c0f8540b10b18503941c1c4506601401c0550b54002100103960b80c40c9884003800b00d41d1412500c80550f0300e0000300c1441142c001816079888180880c0da6039031800011001e40321200304c0390210382d5815002510745160081141d030385004030381c1046080c54611035030125140c02228448821241060141e03142c0c8594540a40703008595401c0c18200d41079500071407000e14002d00390141011482400d01c03841503060f0011110103442d116520103120b01503950300060442196110b1400b490480007aa94005502c0001d01c2c81c3d881c2e8031640700c000e99205120f15140c0e00020b052150b9a03100080492020182c00742c440030a2411f40740204091001040e15a0200b954840107020000c61b01c3e00804403140e425500c0c007074401c144e0100000c80048103400031051a86000402c0c034105401010709682c0d030040140d005200d40500d220703d80c030b00011f5000440c0c000361130000b11a44010412902c0d02e03000313002c6080f00d402c03040c140500101b01d085a07000090041064584a450301c1c070700720080c1c07440488 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 609342661 1250 609341411 609341413
    0x90c0614070201030911030d02150702010c2102040b0304030201020405091006201e070e07082505040b070807020a05010302090a09050a020706060e09060129030a09171305040509 78
    0x110070043d4000d6010002e5903000e8a0001e500012000c0082d2a07d00440c140d1801a040055178090020400e00ea0942080c81c0c2d000901c10313040261801005501034109291440b441a40080c0e844107880e0b0460700901360134821140c0d40e290905010b4041d600610566001754622300014113006401d05480301030340e0311a0755021b54468072010005400b9402c000504045c080c0303407514a904038001c041103094082d14009094624644004212040c400038104c00900500e24200880c4030724400c1000c009496000d40340242404025040700d00d4061500003040c2500c0002d400420312890344054400ba91003165000181e9441d0301c011001c0c0d010b441d40c05900100e90100038004011385401a13548040700030f50050910b4460b1b15107a0946e80298030074198440c1c0d40e024000284000d02065015003844d80c001f24001c5002e24075248000404010584105004000320703c40d000a03400c18040650400c0160030402c4e043c0e2000003841d80085009035004a1340c420014140c1405d0007024801c4200c9c0c0c0c = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 609343911 1250 609342661 609342667
    0x13080303011503090302070b030112050c0603060105030c0c0a0c0f0e090c060d0b0f280e071b02130608060a230a05130c0f0608060d0c060e040e10090c0614 68
    0x54180c0c064044d00004070154010300d540807401e04110303000b65000b445500342030110303100f02d400c200d402d00420040d00d5018980c00c0003082500d98014007183d80107540d03520486da407a2006e501d503504044075120000d0001800342c00c00a01441c5c000c0c230080545200011102c0f031902c0b44200c080d940e004010304260004002d104201241d902e582c02038900e602e0282c04e407803480001000054542458484611184142483c0c02c9214402c1e0415038025107156140f000c001d090012000d001603e44e489a00340403400ca40e01c03001151079000450140302450041401025160310310940c40c1c0350100c841e660400d01d4510170071b40000001d441d5403030104c440c1406c4030040d11406444800b500c00200310003080d0618031204e00000c0d00c4205640001c0c40d800c81407001d29410403500804c1e10304040e050b1880303442400d43c01300120b07005080103011515141808000883c0141c041809001080e0b042c1c8038a000e51440e540b480100d9401149546100d5a2100c10450700c0e00c60968940c4c00e41c28940307a04407028 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 609345161 1250 609343911 609343949
    0x206040c0e072a261207050405031603062004092c0307062909090c03030d1509020316030902060409110a3009080403060e031308030301 60
    0x20000c03103900180b140c03400c400c0740740001e003152246a00041c1e2100e20140d5608074402441068400d500f90129400459a03030410b0a08001449018480315129200481408519214042c00488008103005820b0702c0044003001440d0002c400c03244010b945a9040402c0c0c80158014040e402400c4281c030525141001e0411610300028000840030041c81c0920b5402401542400b854400b6034078808801183c2d500c600703180490603510b18030882250046500c00d1b01480e01e108804141a106051755440d41681e1a01d820b640b034030b6034001e2800c0d0903001c001200b8203c4c411540198030303100080440d007260981d6460040d000c074442124442a068400440003c01d41d02c0b0f40c000140c0c00b40003c1420713041c943c540b40d800e411035046070116a0300d680300085082025801812a0010000c000c06005104031002c0801c0700c0e40404800030100d82d42ea8034505401c1000c120241d4000d180c10180820000004002c06a80d070b902074958201d10000c1c03002c00013444500041207906858990340c000c8840040 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 609346411 1250 609345161 609345179
    0x8070c0b0328090c0f03060b03120a080613060801060504140f061c1209150e090a150308040e0105011b050d05030c0d11030a0b010516030e030f0303010803090405070206040c 76
    0x1107500200b25242d00c660040001c982d00000000181c11140a101d0203140746160100440309410034860003a0084204a00342c11000011741b040c1c4045070610b840c641ea160b60001d030042805071407610351645000004601e0040550244003070781c0e0141c0742005218014804240c20364011500c4000c0c00d0f0b60742c4001032060802d1030a44040401041501c3c191006c20b42d00c0c000600c000d01180c80010b00d1660313042003c180d010000603082c4915041410fa051040808140d600000410641c1e125840750507044a43c404502518000c54212920a8403a91034203041e542918003803240301d000070002001c940c000d081914035210b51642c0030005000e00300000300b0940e0f0030341008100c1c0d2082503081c020b1100860150254100c0c610f40307908085d80c0c1e46000380c0f045040380c1450f507032507042140034401919001c0744e10080000e00340d0141400017159641c00000b034504040f4a800c3e034007600006c0000124103c000004c1c1802e4074044405207d19035031040102d81d1044103c8000e0405840d4403010021400 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 609347661 1250 609346411 609346471
    0x180801111b070e2d06131a040204090b010f050c03070609030c020d0302010b150a0e060f09310c0e01110c031f0c0509150f1608070c0b03 60
    0x222400507201181e40d640d22405005808440b031030224041c240c43d80c400c103501c500c04e1030851018043d1003403103418004046401c81c412440340c02c007240c1c0c0e1070000c80c02c0c80c01d800e6144d503000704006105654654403500554040d0011203d40c60205441d1900100014001c07410340d2022840c810055040a40c5611004080c051400081d018040100c0f102d002503143c200e80b100615002e60000b24000c1c04900c180710404036a01800d803007100041c001c40d240c40d507200010b0580302c107081300c80316100c1400382c250503050311032001c091b80e2090388082070074503941d0514141608001400040309044040d1007030a001e80300ca080000c0c001880c5100d100d05150700440a2001020140c021111194480000b00b071a1100305103950304040102c0d9410f5256003841d000b02140c040892804a0814103180045900404200c0492000350008201c0c2030345813103560b00342c2d000d040700400c0c590600d246506160b0038a031b200d610103880c1501c045a0200d0344503100d070112400744880e4403407910381050382d039031009a0f01 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 609348911 1250 609347661 609347707
    0x1303021c030b041b0801063608070e09010b06160204020715021b100902010813030c0c0e07020d0804051e011d0102190f09231018080111 60
    0x55861042c1d8840ba1141d1049864550b442e40800c9440c800c004000703008900164000010030035442c03503510b0f031540c10b19115986000110701c0c150014898951040c8031a807190020b285038450000002020a01000f41c103024203140c0000300b020101d07420503c4440e10694000040040c4000d40c0c4070018242640201191070181c40e21050005d58a042c2100345d82c030080c0d02d9081d04440e500301a050940510150b8262802044200083c440076030000e028100c00400148803903035800c1d03030034003030500484401c03e5041e4002c040c0e013802c40c0c940ca2003a54441040d20424018400c10040c50446c9000c2c080c0700d0b0203103070410020061265040d408180b6103d161611070581c0d5201c882c00310060180ca503e2100b44003281c0005030b2615105400c1e0424800315501200400400301900c04680340c000c50410151160007501d075807100c24052905c00c0003880700b086030f80c011441c1c444010110380d0120b07801590308e004422980009560703a80d441e09a40180c03041c2101c0c6030041001c0110307102c0c1c1000b600c7c181 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 609350161 1250 609348911 609348917
    0x915020a06060801060501120204050a060507030225150201021e0c030409060b030a0513080306040506041b02061f0b040512070b07030509130507020a020907021c020a0b1303021c 78
    0x204000e40c1e14001582d10035405807071981e454280a200e50360b005411560b050381e66440031400c10b0b2400d000629511058825001406000030f24041490320038815046035265003051460300d0051180302603030700045403059221144040036102c0e034046c03040c000c6482600940d80c02406200d10104211915803000c521507041d844100000a2083c140d8010305008040d4150032a0b164606407042c08203aa0b4020000c00c0111481c020703080c0010b640e0b405607130700844e040d030703000603207984480104008100706031260708145a00c0004c03c2d941c07540050054070070f03041807480e226030804950350440004905d004d0308a40c20300174803047c88203082c03000600054850320400c881c0c015a0742d01041e40281d02220059000450010b00043c80d420650103100002c101c1d514208498580344030b0094032003100e124024443c142c5c1c4800b180e1000c1c07080101f02a44c085e002543c80381040d108501030364585514104071204501d00317001803d0117a0701000400344a4254001c1d040751540b8401c1189211a001c03000014 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 609351411 1250 609350161 609350173
    0x2030315030f010c030510062105100909210306120305071502040b0406021b010f03050a0e100f05060414040305071703040c030201020c0d110f1c0c24091502 69
    0x1a0b0721090154031164000e94400091504141c1441d008480d0300c4c1c4c000d042441004914005a0400380f001000c40b40e00c3c3c1c0000082c41e480708807698100569652022072300600707140a42d0140881150700111100e0070543d07500f01c20404070310581c02c0c4c2d1503d21690510a89054460022900400007840c861b0300c100356005d0300c00d0100b182070b42240c010341c000b24443c2d100403405002c46034042003001c08403001c1049209462204000080018004000d074900709500c034404212001c0d280d40044021050650076a90320043c030200280003000f0200c0744030661070906010a210b420940304e41260500c3c9041032100300e607619202a1031a034040801250805003403415100312071078000286000303a22848140400b1480d41c000240340c01d090b40191840361805090800000d00361409900742d44809648a034103225050700000c002a9001d03e18040d0424614043e40030131040100c000182e40d007081c42c21083c04044d1140d40540710054034010041040824240310041140080c0d030031f00302d204d00c11100703 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 609352517 1106 609351411 609351433
    0x61506050408070b1c09030302030a150503070302010f0216150306170601090c090f0e010f080d020c06070f0206190e030f15060a1a030604050c0304030203031503 71
    0x105402001848084840d603502c0e80030300d17500030180204401c141138100580a98400c4079074080b89440c003100c225403296005100815200050001d20300c1c98255401591031441e445d007000b065100c1c9440180c520300840070644082d00c4015105481c0c05140700002d820340c5d0458002c02d20344451090204144400000c040d030440b841d11201040041044100b80c03123a15250f0014210700503907441c007107002c1c01000f012034100ea4410113031204a0b6590901903868118040d664030042e04400d08148091500750040c01d08580105003064044001c1c2d8005000303030340a13544613551032100c070405440d083d40146804c80b600c50306601510501d020341444548440201600e00344800440d00414556240d14001401528107407202050388a000e880c1c50025400882d80300d44074504060000b0a40c40d15002501e010759803640056003103840fa0304546400384c03d0940c0094043c881c0d0b0003024 = true := by decide +kernel

theorem cover : BRFrame.Cov 609172661 609352517 := by
  have h0 := BRFrame.cov_init 609172661
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609172661 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609172661 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609172661 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609172661 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609172661 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609172661 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609172661 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609172661 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609172661 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609172661 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609172661 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609172661 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609172661 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609172661 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609172661 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609172661 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609172661 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609172661 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609172661 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609172661 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609172661 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609172661 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609172661 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609172661 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609172661 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609172661 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609172661 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609172661 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609172661 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609172661 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609172661 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609172661 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609172661 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609172661 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609172661 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609172661 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609172661 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609172661 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609172661 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609172661 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609172661 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609172661 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609172661 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609172661 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609172661 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609172661 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609172661 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609172661 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609172661 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609172661 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609172661 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609172661 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609172661 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609172661 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609172661 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609172661 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609172661 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609172661 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609172661 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609172661 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609172661 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609172661 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609172661 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609172661 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609172661 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609172661 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609172661 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609172661 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609172661 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609172661 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609172661 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609172661 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609172661 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609172661 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609172661 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609172661 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609172661 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609172661 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609172661 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609172661 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609172661 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609172661 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609172661 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609172661 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609172661 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609172661 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609172661 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609172661 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609172661 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609172661 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609172661 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609172661 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609172661 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609172661 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609172661 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609172661 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609172661 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609172661 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609172661 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609172661 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609172661 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609172661 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609172661 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609172661 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609172661 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609172661 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609172661 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609172661 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609172661 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609172661 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609172661 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609172661 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609172661 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609172661 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609172661 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609172661 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609172661 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609172661 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609172661 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609172661 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609172661 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609172661 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609172661 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609172661 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609172661 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609172661 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609172661 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609172661 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609172661 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609172661 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609172661 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609172661 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609172661 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609172661 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609172661 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609172661 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609172661 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609172661 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609172661 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609172661 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609172661 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609172661 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609172661 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609172661 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 609172661 ≤ n) (h2 : n < 609352517) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
