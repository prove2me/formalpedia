-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3821
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T10:46:35.841079+00:00
-- url     : https://prove2.me/submissions/8e66de66-9df9-43b3-9de4-17d5539db515

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 687050359 ≤ n < 687230215 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 687051609 1250 687050359 687050383
    0x14040b0316080f0624061b0610120b040204021812012315040f09050f0604030305090f0606040c090f15080a0c051e0f0f040e07050405031b03 62
    0x8030421a94101c210411611038050b019060248162610144000148850248070125100381c1c0fa060103251035070418040c1c00074103601c4a010440107410314000140b40c00002682c8000d07050781d0603d20102015031880f075000041c01d5001491b40000304024250700b50740141c06850150761b42d00d15482c10018507069900c2207900c9003860000341034010f8154040000140da200345501c5900b00203213440b6000908988807803d102004038440d40900700354128403000c1000790004500d030000c40d9901030030001003d02080c0c080d8010820082455898041c0641205047d0301070041c00030303010782c966100c9100a1030700f80115210300c540c07842a441060040c000b800c0d00c0d14090200750311030300c10038804803c82c540c04001800030344c085580803590348104e0144002d41d46404e45050036050003140046541401009000c03014054000000d500c2d0000b80882100c4480b450364590405042d0042d10501038004020894213000900654070b0000d04c058a006406400050382100c0d600040c1ca464400c000d5 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 687052859 1250 687051609 687051613
    0x604060f020706090b0a030e031e03090105060d0206190207121101091406180a0801020f0d05070503060d120201140c07050f07030b0c0d0204030501090311010b0108060109060c0311030403030e090106020307030914040b03 96
    0x2456015402b44401307507020f40c606000921190b19800108181054406006984003074204441380ca41c115003040b1151900c1c150041e295680e940326959110000c0030041034036040c02d001e008103110741e4032800e0032001d00014600b00d1410080440800c1041c01034402c2c02c03007101c40480c3c50761202c0c0c0d42c210b040801032144400940d61520802041ca0780c40d0401c041ba044a40c3c1024007160710240a90162481901c02a1107009000006d481d1851484000004142555a05c5410f42d62080d4401040745c4169900284965074400c2c5107442c51410054803410489034100300c1e0300307000254103c1c4500b60813800c1105482c0d1190a803080a00081c804c5c1c0d40010055032074481c40f08101900100310780309440f0444003c03c0b4200c0980c00540b240c4004881990024000b10700902074180641c42c20f0345120300a240001004104442c01481d5034403d40040c0c000c2054644410610b1802100d218090b1486d031001c1c50401e84950341c00b600c51105409441d50200c8107e01168907034807035500c080c94501008007 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 687054109 1250 687052859 687052897
    0xe0d210207022710050306070806060d062c0906010504090302070e04050604021309051213080105010f050a1a031501120903031d070e0a020306010e0604060f020706090b0a030e03 78
    0x102d0159903030030007079198002d00003000004030240c0407413822008139600a00a80302c1175a0b000c40448054500a120950084040c40f64200040180c0300c0c4a000d4003454204000220802c15a0300e40001044c420000da22102000c008140d00040340a1781180d0b41941d0109461074245000e90502c601500200c064848540800c82880307800100280118002da4100341040e0078822010162504100058420b92004003c03100d024881d00080c1200010212044042615821803e0070340b0020f07800b40d40303001100e040501c02c0e0b00d00010a00010f2400816584001510704090101400700900060841d01440c20000e690b034002e50f401555501d809908010080051802070024101030b4002d071a00c8401001003000c0200c001032038400c2d02c10070020740285541d1050b507a07001c3c0d8001403c00c1c3c1000043c2084101e0303500e5030405800900030584840d10161a40c51000786030040c1540300b0380130007008400401c02848100126a840314a030710340450340000452125285108044041c0c0c25900300700 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 687055359 1250 687054109 687054139
    0x1109090601140607020303070f080415051801020f120c0313230907020a1118040b07020c19030f0c0f060c05010501081b060a020c190303030e0d21020702 67
    0x1090180c140c892882d000c0740c016814009014183c040e041e80203402da03004202d01000301c0c454204002400b0300c20030020b03151a40340c0c51120b4140507880388500c040380011a8540b8500d882d90b103e0303101000288010814014076050340f079502d48166a501107050b07000103900c080d840b0140101c50f05501c400046c4040c003a44e4030420100c504407009034030507001c1e0b03150304e81c0082c1c40d2143c202c0380034582c16801424001000d40301d81c00c0c00b480c02d44c1c1803035218610b000f92140c25605d01d40c20f248100d00400124401d840e040300040e0a10078000301d42885207240d0108500e011501001a0050b40e811101c400f21581c810300d0820f4035452030340c02003079441c03035030010000354164860042c140162140000b403210782d88c0e95280540d00d96010405500d141380340119002d41e41468006812109218030458000c01403c17008100d189000c0901d114a43c0b403854410310a0540500031440308000142c004d1001c41c0c80c501c0d0003407000b04450301500300600d2201c0b40d40285d1210f601541c0c006a00104010b840c02d03104 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 687056609 1250 687055359 687055363
    0x131202031906020d290405100b131e17060115030203070c0f0c06110f060c160c090f050c1207080709080f01050709062610030f140708030f070b04110909 67
    0x5000844040c00e1045d580b0607007420140a214000c40c1f03030b000c030a1041030900c0300d81c0c0003c4c8c00c8100201074080700320703000051011701014154482c00d005508000da4a0502504004624005807204080d52085e07004200c00e01c8030002c00c10b8000d06038034006840b51036000048451440c40328014006402520f03580040c0800354245004656142e15052500220b110038203403241d03215580c80080e5040000021021031880d8014504e501c11701c0740e0083c07030030380d07903510300c2c4e040347c0f042e001101501d070780e0507268182040c0361282035045140e038030f0502d040c940c4d502c01c1200d603410000e0220013049801004038107040d025840300300250440c0401e9074018209240e00600174003044503011f00080482c0310001c0c859004891120721902ea00d50b001e4071500b016610008000c2c00a0314905a040f1000c5e4000041480004016031892007003545a80424903000b9880c60003580382c004084603013080040b01700c0c186c02c040c11900ca0503440011000384e541c580c103007006000d8000c07905c00e41101002040140c04100 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 687057859 1250 687056609 687056651
    0x31e03120e010b01031a031e0a0b0907090f06080309120f01021204022404030836040b010e1e0406150f08090303070801210c080102131202031906020d 66
    0x100b0385c1c0800408011032140c4c00b1184100b841e403078040c0c0090810b41e8103504541c41d0b0b44a04081081202c8412002c2da840b40550714045414030440d03000700905002103020f5008511100031108001d0080c1c07414030b42640e0300c1e80300360100d641c40f585600b0038020343c400d801e006c41c0c40180c80d1000215181c903080d0b110043c030020221130803442283c0101d140d040241c80c480c09840a0442010b071b50b42054119238840c1481d5000000c0030001d240381084240442241e0342100880048520f82012140080740c14441071791a8809001d040c045550000c8029442d110303003610900c0c52010040d1000b00c81500442c004220030340141030304080e0350503041003107034104042c80840b441642d00d02d040ea95802185a40b06c2c00705a0741c060002d400a00104103c4460300d09585006281d080001d0005100c0c3d40c500c06640c400b0380c44424182d4010550404030102e40d0b581d07c009102110701003824020950010340c40340409003d2003001030b01c4912080c148903aa83c1a40c440d80040e080070811504031814400201c45 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 687059109 1250 687057859 687057881
    0xa1b03091103030f030f07052a0f280204020904020304030c0b0708070c02130e0a060e0d050c0c1012020310090b0d0c060e0111010204031407050a031e03120e01 70
    0x5400401c00c600340c01d000013100c404010001d442425512180d481c4011400060184810480b0511490804100303403a0762000c0e41c000382001c40c18105502d050141080f42511038503400d85c0101c0c5442c070110000c001010000c03104c3c114921800181440058024007030284501d8005101004000c205a04240f24003034a034029200c0d10021356603003500320790010003114144000350304c8603222401070400030401c00c1541750301d250110345140483c00301c6180c0301c1c502d00281c0d10030351a0180c940d001c1c507003440b0001440c000c0380b0301036142488003061955142c10000640340a0b228040c00f41003064030928900040201910013555207003003080b040d0240003404c0c098541a185050440d10306031500528803080c0c96485110021410b03c0d1110554500050080d01e60501400c600100c45211082c401040903500c42c22020340d4820507131026524143e4240c1200740108032a1030144089580510400b5900c0a400385d4031a038500d051a023191604401030f007220a083c14400d412442d10410b401c070280910b = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 687060359 1250 687059109 687059123
    0x90b0309010506010318050a060513020d05011e060f051009210506070e0f0d06060909050319050301032a1502030a1202030c070f02060702030607020a120311030105090a1b0309 77
    0x1914240c0108414540c6a4004000e0750040004e40c0009e41c0607003100f0340c400c0c600000d41c0c034666095004958003d40303401003200c031659a020590382c0c1c0e605511001101307402c0050204906820411841010411800f40e6407052036440c0319240c1c040d00c119070201c0940351526010006503401d4a0900c50781c00f00f0798040b503882c001d10002130115403148486500001004002c00c66041d02c0c2810302c40300c440c5e1950161075480d213035100810707000217900400000600c148003c0d0350720740800b88071a03003000e0101c1c60803040010800040010030341000d9000c0c1004060748111030151140c021010320301106600c080050344e10382c0d031300341c20300794010020b0441c00d0056243c880d42a00c0800d0f0102c124441280c00f4010303030710f051200303001081c84911a1340c00340e44041d001d07520341503040e000649024022181c900046e0301102030102000031341140d1842805003420306014045c02c040380a00c50313000502409000d518200d0000758a00c196401191042000301050303000c01b00501402406001d404100f03071041 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 687061609 1250 687060359 687060371
    0x4060603021c170f030c070312060b0c010e0a050604140a0c0f1e050a1401090e010b0703120516031a04060b0c0c06040b1e0c011506030c08060d03080601090b03090105060103 76
    0x700c9003400131150189050b003840c0740303181d80c0c488030101541c011040c181e08002c140703c820a00d08005115002c080d0100c840c280f074841d5030f1540d45c6420354608480d904490381040921030001003001075001e400036807200710020400004135000d0303e880800c1780b003d000c111801c1c00014151225154200139200f60292240d9001c1c0b01071040080030059110f00e58000c004080108180c2d480e00c50450300f0702005140605546a0741d03100c1c880c072113200f0703002402c003110001820403c00d0b4000100c0004120711550074082032510308492582d403a11010304e102855165001407102c1400c64400501c1440300800802c80e858840103044000d410507100c4c006030b8400c1c41d19a03002460b0134810348003284e0200718402d242c4848040001307000c038101c0001c415000403c0c00043d800000c207014460040c0d4070b0442000c0706078075003d0b00901b85c40d8022502d00034400f0403010710600e41c9034088203222080d05410254496191080100d528080d00c1e444000e14600c04000d12004040c19000503000d01026a014441 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 687062859 1250 687061609 687061643
    0xa0921050a0e0904050a060e010b0423090d140a0e0d060e0c030a0203120903010225050c01050412021014040f0f0e10150302090406030303021309021e0304060603021c 73
    0x20f04482620040e10940c03102c1ca15400082517130b003043c000c80c94684000300f17040f190b00002c40c041d40d910542c001800d5185c440039200f505681030b001c95000040c034008250300e110b24a03028103494100b620b5820582800a0942405400b44005000301100545050380b032004130309207900180300d407000d420094010100c82812070714000031091100d0b034005001e800340ca0f181c4264140e090384040322441c1c05540a0204009141050650f906104803514102c0000030741ca00d0514103203801c400d40c403818080180010710440486504c41420190305aa620a4640209501341c840081c945051512801c0000c0c000c945083c03241c03c40d904903040c00031501c500e680c584030b6401c0ca1180840d40303d51011118501004030000180e0714500301080c0e130600503d00b540590100742942c1d800c1d08241c01017038001a800903100803c0c0e900c0340c02081d81d0102103081c84107078035240b5074020300c9000341240e0400100104007400b03455032082c001142c4c01851071003c104000240c0c2140d14800005441d0031001014001c1 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 687064109 1250 687062859 687062869
    0x1050109020901051215180a05062b0f0803011202120d0509190f140f010e1c020103140a140c0703020c1002030c060906090d03020c060a0921050a0e 65
    0x2a120070143c6901d030805d0103a207900020218002c1c10102d892121580803a800d48584122080ea503d4802d04101c1034a001c140d1081070700d0001c4c01c85401003070240550300c84918441404105420300210414040c0501d0030281d40c0040c2c0f030380d006042c1510000000817903860700421254040c0c801e0b103a40c4264541c500c0b0302900c0c0d000101c2c9060119500301704880f81440c1c1030740b03a17a540c10a138031100ca010b9515000081040512a007040451010b43c0014004514100104c2099040c0902e000c01c0302046100c0030400f900c1d280c046400c241d11003e00c540c411a80641c219a8000c406803a040c0842d00d030003039011000d00f90031908408bd100042001c583ca1303051500c105d0b80716540540041420002a00603c140c0621f404d407400110300092001d00c0062009004d0a402914468001d1081e0309003041181d0510003219020b07424140704000d80c001c0f140b00425030701e9102c0c0c0d19220002e050042d5050200804486000802c658448a0b4000200a4003c8080d0581a45507940c2c0060000d103c420302c4 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 687065359 1250 687064109 687064117
    0x4060905040923100f02040906050907230403050a08181504030b0c0d1406090109140a0e0106081005041a22031206180c050307120e07030804030b06030105010902 71
    0xf4022066852001d0700304400a0a0340b2850101e1104440c1420855102c07401100c5c0e10780b81c40800725030009010045103416000d00009400100c130740e0011820482400f42000001450782d01c03481031031440c01c10b07207110300700b0a0700e000715084403d94082c8483c1c0d1400e0102c5030f00100c0c807490b44600f850103101450400a10300b1020300c1c4030014507442d00c0c5c25034542c1c1040c80b1006040070740da640c04000c0c3c1e00c0703403681c940a100001c10141841803d1820f02904000e020301058104198541c0341c50f04401c60b0201026815800c044650000240408948615030240c030f819081010f480c49441c406102003012640028403031400b41c1c02c1103841c0310031203100624507202900c1e40c110f2180d10850400da005441c0c600b01031054030073300304a0300d1b0309140703e000390565030281c2c03140140014030b000f1014100002d00500e101600207181092940c0703030810340940030000080c410100c050f81e0f81010b0031403031000c020130000f95800a5407541ca07140c0d640303041c01500908568080c085d500b40000029404100e009076 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 687066609 1250 687065359 687065363
    0x1e0206010e0a062624040b0108370b0414010c030b131a0a080a0605090604050604032001020f0d0c03060f050112060506070f0b070c0209060402220b040609050409 71
    0x401d1240d41500501c01389505986000e6028085d0550045912401c0c40e40b564a04403101c000c03070900d2a00381801450114140d00400b02d03604a070700140f01040c45041140740c842000c0c0c84074070440c00801d907244090741c60003000601500040d400c1c0700601500e504110507040102000f840124034100e8103c003078655103409a82c20800b090f4183d114502e00d034105060202100808100100070980001c04446459000c40700c03035048808044288503040c000c841d4001e040c08000d00013410280e48041d5124801403015041000c07444100074025101e00200908803882d0000b036448640380c40c3c200d8a1540400400300d441460442d000031960301901800c2d045503040407000300d901e4138042c015101c0d0703510780d109910a0f03691408081140c8d560700000d0025240504070360191000549081e0b1640070700039200106120030b000f840d10041c0c0e541d0004907803088040c2c80140c0c03070340030003d04006030100000c0c80c2c0c4525115800049840400407000c0c1007101d0803a074030810b4481d598001c5c08102c4104d0040 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 687067859 1250 687066609 687066629
    0x1c080403080a092003100b0d031119050d080109051504050c0f030103120e0603010305060604110403050a050f0105072a020607080d061d15010c031e0206010e0a06 71
    0x60200340a62642580600c0444010409a0456440e141d440300c18070344200d20411042058500ca09080100710700c510040c0300204141204c0078001940d00c1e41300e460043c05c10200f02c2d504408403005000c0d07001a071020301c4000000c08858034206864859040c080e8000031040f20001400d401d00d03010b003e00443c3c003601c40b134040c1e00e213000c00d00001c0c02c001031080c0f0895030304200780200084280c0065001b940508900c9101881c20400100449000d480c0380e482041c041c4018004200081142600f050040700c00142094641160316800d00031544043c246000300e602440030700001103004085a4920002042207039a021810364000c15020140c800004122070314200c0020500200003c50b40000d05090601c81166501c503000d0f4860354040c202182c44050800460b469a0100c04803450649202c40c0c040c40d00c2d2084007185e101c082c000c50b0401c0102408403051601581390003051056007150202001039105001e03549140c20700c21502c032002e810700000c0b1407000030b01c185000d9984240e6 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 687069109 1250 687067859 687067861
    0x2031e0c09070c030c0b15030307061a0301140705090109090c0302030711010614010e0a090c201b06070f0c090b0a150915090e1315061a07030203040302030f0105091c08 74
    0x3c442c810740500170040042882c62040301e0b1f1207941d0400207040000d2041c000801c00d00300708015500b070f460035070080305e00030303814840c141d060310403d546c415500503110b117000d60711140180012202c050726a40803080903890302d00a181c0301c543c140c002754400d410549480005000e00c0c90b442d401c035103036441044001d8000c4c4078619103541c4a204481e801e600c4c000c06400007a0784402641c421034131181141004565814031142410000c540900c008086d07040141103104203200e82038102d0204043c01c02d11815000a001d010042c100d110b0400f070b00d8100d0405104c441e124480d410061010b014a68801d0758900340004400040c0a03c04080004954440d0708840c5045c9451621003008280201800000701010600500902d51603124200301c0703010070801032070b50500500c0a0b25414108082c9401c1610910543c00c940d0300384046000d039240d070b40f41d80381001d0800b2401c500035a000254140914040f904441105410145c09245003109503040d00500440000580191034121000f04000704 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 687070359 1250 687069109 687069113
    0x11091003080d0b1f08010815070203090d0203100903030c180b040b0306010522091119050a02071e2606040206030601110a121e0e090402031e0c09070c030c 68
    0x41c105207071800015107103040b00f80c443c45440707072801010061900001c604e040100704c2c0c91f100700082e6802031a2003d08480f58100604025101d1040c09405405030000c1e9103c0c0c411920b0400159018090740700702004a40038034600100a0004250300f800020348101140032201c4820916400300d607469903406241a2811640304190b800040646040c0314040c450304481c4024a42e441544000030172800740300c40d0511001108440700d01c0d61051110380e091080591140d6142d030700604010b0035081c1a41c035203d880c03000303d2400c800b580100c10030a92541a0f040a485100e00301415164803c24400c0301d00b50f01c3c116440034942030903100103940c1c004000314015040220096421580c1850700c541c400c1c141d80e542501c2c0c9040350404480690900b04030b84401039000c40791500f20038400c100c031410141c91002c000d00d10b8500c001600e100d459150b011800b15a02002241c0a01040c40e01c074160790010010100d842d04c5540c80f0450084c40c141000070601c51183c0340c40c55883d5803580b2035040c1f030780c031503 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 687071609 1250 687070359 687070361
    0x20303060f0d0c0306091203060602060613020c031201050a0b0a050703180f17070503070b04091a0901080313060221161e1b0614030705090a0311091003080d 69
    0x40200303a03000000d446540b004241203e00f0b01d8081d600070700d80803403102580d20f40280084102d84018041514000e024415107601040a90f00810101c0b0303109014415940c4050003842a10301040c1c542c4400110543c01444d1218964100c80081310401680c40d51954942d5861085208110003e002000340100090081c10450100c03a8480406060543c641c09008044c0256420100c0b030f540c04115002d040e618200701d00800381505401802c1384510b021800398140c0940d002e141c6030b040d2120232a024050b5400d00d10307880c00e2001445100c855a6500e05261294068000d00d54100382c44900030483c03500002c1c003101040100c190404041042c0e10310341d0b1803030b0400112118041200c05082011801000c0c00b03251000d541c0401c1d190441c254034121401c4451a0b030284c0e4050358251042000c6a040b14a940412104810441d42c03039071403134802c58492107150303005076000d80070b5840032003403103006e48001c442c4480950710754403661661091b410703d800e200d02c80100601020040082d6400702 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 687072859 1250 687071609 687071629
    0x203041203050f0a091e080c0d0503190f090b030c0301140f211e0613020a080a05070e0a09170f1b03122d0c04030501051807050f0102030306 62
    0x40c1c5080c5090401010820101c4e50040444c00006056502e01388200c4100702040580400300344d03503d41c0d030140f0301500507480e8000b5210032880384080011601c203004042c000c6814010190800404440d10b100b00580742d001d0880840c800a900c00c80e0100b034540c01c010450f03028040074200346003580c0c43d090414051244c43e56007a50890854040751801d9150101d051604840700780d000b494421032180c1551038035803003504900280020086480300030801003030880d0041000d402d60741c0c0d091070310b002007000c1c480a03a000c01c2e00c034400c0100000902801060200544c1c002c142c0c1e145d6591940380b028003e540c00c440d40904078005501414a0310f401d00c00041c10503003000042d05040c07840301c5005041b1040500d17500241070300000b4070f00d110380310f1620740f09910090145a100070054401030400c061500c120140100006a0000c60f01400e0f285082d9001560700c00003d10561030810306100204900308000d449502c40d4640c0820035241108803030b141600180c1c02076065680d0a0200000980 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 687074109 1250 687072859 687072863
    0x60904032106060e03120417030c030316020705041a040c02010b03030a051806040f090b01020316030c060b030607050f0d060f06081914060f0117100302090a02040602030412 76
    0x564220001c8108400403140c01c070121803640000b410503c1c10201809101201650b00d100e42c20610b14050140300c000282c03801e492480e416008450400c05120340b1f5072003000c040001d944404030401102c08410250b501d83d440300741e400e841c0d400b03682d00107000990b03000405121656010418155850804d54010309007032034280f001064143c900b0003c43e04640c45050000001200090008810b080503800f1800c0b514066880c03038074017031802a00700080c5031140946e0401c070b42c035164800000c0e8400c10a844101e80d004e03011540b84580c9240c007501c1100000802c46100b0308046c0c4a000c185000724900784103007003540307038540780c20040ea00d001310b00d0f4840913000b07184555848020800c5c640ca25082c202400c071940329905182003c04894060424004c080140c05052000b4005d070001440640782d04036070103440c001c480e1407030480142c88064980505d054000c0341072041025010300004943e0880b40203490709203142d15494119800c2c1d215030702852015078001c0204200600a001a11880c4e81c = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 687075359 1250 687074109 687074117
    0x28060e0a030807031814151005030a0f03091a030405011505151605060a02040f09090206090d05010906090602030a0605010311090904080d05010602010614030c0307060f090302060c0607030b031506090403 89
    0x17580e1962110403032010501a07046a5010783d600b051002c200d0340720190011030314160a5845403401000940e47c40f00100018488207582d01c00b8000c041c020158180503240c01c1010740b6000401d10304850543d0000c640540e400d600b0705000700c1e094000244000f080d140701900302e1480301d0418a400c10700d0b90040da5004a002002100f0300301103101806958024421403a01582d107c2c40c1c02450030340418540c000e0b250143c82c1401c0500181c0e54241218882031050380d8a40d860f09150900c02d0041c0b40110025107454100780c0c4620401241d503004510071803142804200080d10742c00114125804c0010260150070200200b40c0140341c18031b81d207030b4858483d80190f4501858440079405444c0c1c2a400080940c2d156113050107003c0391103425078841c0348103500500c02072042030700017135035100c0f18403500041c81140c0d882112114842d4000101441d00506010340d240c5d911805543e65481c111540c10002c1d01d4907056940c2813501080f081c1c141c1e1120500341905869003002c10000d074001034402c03000c1c4 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 687076609 1250 687075359 687075401
    0x31a0306010302121f090b06011b0605040312092a05010c14240f162c0d05060910050f011a07060f0e060702030406051b28060e0a03080703 61
    0x210085c1d1304509081da2040a002c0fa074044c080c83c2c05408600c000d800c00381801f04146403400141c000204115010b600b1090100d0951140e06003a54114081850030304c2d0142422089000c0c4504245000400d002062a03040c41c004500300c4100d03188454025280002c0c500924100403030402c0d5000d901c05e441800940e02403c030340c9032481141d2a001c107460740010310410200045414030190303551f40b101d20500400740e0100b00c203400800c15a03120f0000344040c86010078290760304035101005040030301c02030688481a00366082c0f407036407001c2c00c8800c0038036441450a04281040103020b81400381003451841e40e020b07400e00842c084503030310540e000150b8800601409002c07400d1400307608030b229805032000880c88140c83c081400c001e0010071103001c0d0351040008003c4181d04c001220b902e040b485401c108420710702c100550400c05000620460700c800905c01544514083c0d03040c0b81d00354440d000801400c45c200a4041d2500c0c7d003940054045190000005c0c0c1582c0207402110903608120084451 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 687077859 1250 687076609 687076633
    0x60e040c081b01031e09030804060c03020412020405100305060c1c09020d0201051606050c0d05130203032b020a02030301050a1215110d0c03020910020303060d11030304031e03031a030601030212 85
    0x1101c2c4a00f406600145202381031005120040c41600c1c030000891905510b454109000003000e4040c605000303004030b540b03200059021142c144d03440f0145074000260758150034600c41e008560380140e02e11190a4094142560b0440d8151050100c21640500051070a6100d03030010748080c0c0142400e82845503200c480e007000100e09106031442001c000d1a040e442d8801d4131101402c40f44020042c2c01c84046420031240943da000082d610088a85800301c4183c85142018201440c60b12800b03c407040c1c00850300881890700840514141e4009440750f003a650383d00c000011503a00003d801600000481141407030b0503d4681140034880b845020700e17450910183d0b680c3c8101c402da03000c490006a408070382d030b6200b450000107000d00050903200035400c505080b070000746d011582803002003d9105d5480cc0102035101403098800071a002002824910808141540c0985040008a002074900394000c000b8030000452809060f40c068000c0680c0e0b8219824015030302d004c008504001d1180d408030b410 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 687079109 1250 687077859 687077861
    0x207051501030c03110402130e06040e06090601140a0e04030f05040312030911060c031c1404051c030e0d0f2c0906180c0a12060e040c081b01031e 64
    0x4000c62240f40798840403032460078014500502205518030072401004466031011032040c105085e0f85901c51180025100e580006d002400c82d07801d03401c0390b4050b01040245030503002c60701d00e0484c0c0c11a000981d0740c18440c0100081c4503032074052801ca29041c02c022801003840742000c0d42c0c2003039280c00c00600d000e03100c0c0c0700c0c2c1310744801c0f44c1e414100094685260f88200800000c00c030001400c152200e034144050f021b40342d40c59005003c05903035601400480204540c9160b0050924078a241c074681116050038107220703855051a8455100840c0100e01c450380041c400d01c180d80b051003595000d0010309401c3e030012260b2000350840c0360104240b00707452070811490501519040c043d1801c080800680d07000500c4031031140108103900c01d080c40b02d94034640051803856207911014400003d541d4140a0078161414214200040360051602a0118628182d030b0a8980a58040c010144441c1d641d0103403e60355040140c0c00001441d82082d0f03c075025402a0841440c001060203000e401d10400c0500d08 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 687080359 1250 687079109 687079111
    0x110a1a060117240a18060603050c0904020310030c0e010303020723100908010501090b030111040e0402010f03021e0a1b0230011a130213050d0206070b090319020606030a030302070515 80
    0x8500400700c1d40048a42180c5441b9000003050075040502152402440201d014080e0300d43c07540c01581c0002c0050450b05140106c1c6000d140d00072400701803140c0b566400555054240021400352099400106800d100c2c003044080010301895100c1200d00e00c0b505000d076400c0245041414060007150110300780c43c00f030180d035010340340c445400514203004030109800c0d90f0740c4000808100d40100001c1c000b41c3c0b21310544a03405a0282001400142e000000f10024419542000455052040b04200381021100101312031f1a05a5030319041d07503c045446503200f022442c0003907010300340050018003d240492075221800e40d441d881241010354107402825100442102e2801b40c0700518508000d140030351200c0783c03807508510114108000010703100501c00190040c10b00c568410503950086542d40b1040f10004c0ea0300031001e0045017841907841c0e0f46d9801001c4c3d4544480b45132003410540a1002a8581c031950f00100282051107060310b05034029400030a0a031514011804008090710310001c5103 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 687081609 1250 687080359 687080369
    0x16110d05010c050904060e09031b0a1704030314030f0613110c0c0a0b030712021b031207081501090e060a031709041109060a030c110a1a060117240a 65
    0x5641e9a0104101700850b031854006c40d680560890503ca81c01000100fa01d2458500c40318614058080030f58a920f40100654000d202c0e0380e07441c4000c5011600407015100f203a20980f0307100c007003d1b5070f48000d01c1b07603002c11100da03c010041000080c0c011314046002010f61155600d0018648550082c10121544040d1098503564072440000059040c9000184018407006480c01d055042422004003e0030941101000c0f0b83d40205910b260205c1240d04901c200c1d8091007140e59544035010701c2c882c1003d044810201003854403001075050100c4524400c24200c059482035041414038460b80e04000000d00388580015914078080005001c241c1400c043e9009440002d071122071340340403c0169242c03603860040f500c4042c0680c0e601612904255820010b003800c000ca144400207004856070401505811680d200d201041300500103c00c08075526062120308003041559010f006650161050030070b011030f468180700080b001c071501c54032500360170641e404e00241c130013003000024a0786100d9081 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 687082859 1250 687081609 687081617
    0x1602010c231e0a050d080c040b0c06061002121c0216030206010e15010e0f01110706030e0c060906070308040602090303120f0f010b0307110f0613030207090216110d05010c 75
    0x308840e00c188040645050301028005000c1400965900381d10740716864041d0082c0240400400c150b2000d60048d01e0182140741c1c0c02d19207a1100c0c01030035a8030031301501c0d41800707080315449800002d8408501c90b04c06420a9000794541840451404202e40c00201a040c040d5424049030300a0401703075004c196841d02030b0b40107110550509840c01c44400c1c000d0040b02510000ca00741654a980016509200650403245800101d6000c1d0050760341c803400b00030b0302c502c034001e03201c02040803901a400f0340d04030800c00f0100c401c030194000c00c3c410203209400066038002000c0c001000002d02c100400c6a0061040740c0160400da44180400d2540d000b0f40c80301107041c0c80c0b070010800d45145a44002d5804ae9041028588551410b050900c0d1072001400860400142400720780e200041007268030301824010003100d00c2460000301d010b842e007000c410100d00500540d000041c03102d000340291003190b003200d903420340d1610071075441c81c1c40702448040044c0c11109010320300c1c0224100303214500c020409929 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 687084109 1250 687082859 687082873
    0x803040f06080c190c020103020903070312092702030603071203170a150b0c0114090703021914041a06030a0b09060a1d040309030c120b0a021602010c23 67
    0x20016128180007003004400103001e001c1c03d04036400001e04c1042d40419410220100440c07800100d000c0e22988065582500c00d16070008100a00307110480301e0b20074590350b01802030382c072510f0007201004030303950004c1c1c0d00400d0006103807020780340d50040d43c06c07100080880355115a00c840103041c011001400717802150031001400b403c500750a00700c56000a42c036100300607003140d091101d5000091801415410040130580400e0240b095000b04200060b0591804080c80d00034000b60b030320811408200d010700b04640c00d10308000840015601a921014020103030740c03a000d81840005c00c03196048041400c070042080000d030301c0b03403070095018900564006c1800c0c200441804952076015080c02e014402da007000300074180007902401d98407090a0032200084d00e1704c1c1030445080e500f5800190900c3c0d100040060400e1051f1425401c50b4442c0b072000d0580da4a1600260480c013900c00d0500f46201200105401076218940030305149101d0042031041e00302403502d030b00c40c0110b0312314808002d030b0042d4 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 687085359 1250 687084109 687084119
    0x30612070807030b1b04081b061e040510050403021f02030409050c070201031a130b03030c0f100e01050c0a0c1a0108030c010b0d032a0609030503010603051f1403070803040f 76
    0x1603640700e01135129084038501b52038282e444c5c0d03031201c1a10b0490741e141c074580ba150303620750740301c004481e1b030810104d5080480340c0360000c0e21641c9501505c01e41d40324000075048040520f0003030b0160707401c43c1d40040c608002c000c201030b640d40c00d035103c2051043c1140010000491070301c10314414280968410190513440b44240c2c07002400b101c04001290150b50180c940c151101e56807041c4a0417510480341c408074800c132111011910b9405000400d582c58020110030840ca9840054107282817507030504d00303001c160700703080c851400c0792000c0d118a06c58607001c0101004503806403000030041c610418042c9880720707180c0341c101050042030704102e03c0d5030000280c0c540010000d000346550740c0c03411039694502404541d80a040270600040704159450607403070781c180c0200800b43c105030395030b0868010f020719680340c40c0c010201c0d40240134040200b85060081040303180c4040500081480c840c42d00203140d0306003610340c7c1c0f441a5450740d0945c184a039240c00710f804002440500700030000c006095021904203 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 687086609 1250 687085359 687085381
    0xb27040c171f050f0121020715020f0d050c16111203090906100903060603062a020c040e0705030f010504061b050f0306270601020d14030612070807030b 67
    0x40c002c00785025581c51030603996403190303807042c1c00c699003194a60084042e10005803201ca09104a10f01c4a0b030861240c000903411580042c05498031a0a017924000b102081d914128000c1c6954401009010310960701c105005a00507a044454084c00f0b909094400080d04803503908624116496a201c007902007940c1024000d20f00b00303a400001550504000ea80811181140104003e204040301d82c800200c0030b00560544014640002051040c0d580b42c1c1400300141c0704071010180c490704500d07602c084d401410540d05080048503409000c2a004620400c0003420012100240c1c0e8001c0c1040011959020880d03802d07034680260000c2020b15007414403070b003224120001852055a108040850340303030f0150456100443e0010101d449840c1d40d40414000030707443c24115000030003890440300b8104001d03100740c46084241e00b103404140324441e0840fa81c2107030040070302100b00c0074008944685400960a05038600200c100c1e07000720354039034841d40342590310341c0141e560000c0041402510340c4c03c = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 687087859 1250 687086609 687086611
    0x30903020d0320030406020c19020f040b1c0c081e0705150d050c1c0911030115171203041407060c02090103140c031204060201060f0b27040c17 63
    0x18a08003004005021288100f151946031101c40c032091000002904002a907815a00820011000c44070201400310408e1104074490505a103d048801c5603c0e12a1a142c0203241c2c1006010700410004809050300024000880c10100d4400b12416400304100104106502040c600401c1d00d085e80820b1600307050800c061900020b01401c2c40344407101454108504a410503201550002880d6440c04681c05841c0511000061561110340c801501e900194108a0000d0302500d40c1420307840d0303103000b01401c80d00c0c1e88400c150004400101081180380240143c102c8103d58420354491000078221956554000c840491721a4480b010107410400108900301c045c104506025103110130640000f05600c40520004100403501c0c2c69469410200f8401c4407045203024080302d035804410f8111510540241c010000103610b4841c0000c1d5111455802401710303a28070488520b008040c04110007011025071004650b1128095190021f84562003500c28145003540c500c01c103441c0120b445982064 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 687089109 1250 687087859 687087883
    0x606090b090d0803130506040b04060c02150109230103030302040f0b0403030219031e0210180809040903091a07060e15060f0a030b1008010c020d090915090c03090302 73
    0x501c07529840e522040c850454480e009500c2d01c2d201e07582c0940d1448507181c88800108540100c0090008002040030058040d038403480c2d080c4032381224021b007242d40d022141c0c08085000b550310f004000b900350700c1c0d026041451100f00e1626002c500d1140c600034214081e402203001035070028080010010201c515000b8240310300c0d0359842d09186880007580d0741c1c04d40411005c00760380600c400701058001c03c00e031805000304201d81c0221140100d000307034460180c8105c41206600f450504684000c1c1c4559824545a000c040a8145070500f0148402820141e504900744800b08401142e840104490389201c00004043e043e900e0285150800941e098003405040c298450f41700c02e11050580c080071a072005e429203450004040b1540010034654050b4000b40c110f0044c50107005818812004140035291401d0090048560b5000d0403a034600081c10340390300180071050148541c0046c0e80251100e43c508402000040391555041d1040760030310011200030030f80d1410441e04054041c081031841d0b00c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 687090359 1250 687089109 687089129
    0x705030a03050f090a030f0f060c09060903060e0309030a0804140f1c150e01060306060501050f0f030910020d0203040b180a0803041704030507080709020424020106050310060609 78
    0x86141e070701030001d01a042100d0386100004c102c240080e100c2c2d4000600954000b9010a4950620f003030043c040f5511136025241c1c2400c240f8030220040c012282c0400312209070b0b0742c07100521b20b1602c8680080c0224200f041440c0020030039a100ca603000c020200c00c081c068851144e44a1601c507210650300001c030300b035900a00382004000607540da480944040c2c125458403601c08000b40745041c100020300013072410011441c05100500c202015030000c02560f21440d41048860b4a6000550f01805214030700342801c2c104008071514420032101a5030030250440c211042d03001c0c910040d2090303070803145140d04e800ba40031040200380b0654519140d0040501400c0b03c00d25806080401e03110700c41e501020f0085280040414200804000d502e00f1a204008095440d81c1e141d180c1252102c806100d98100c500c81c074040441d05402c64821981142c03000c081e4000e1030905050b01d0603921562401260540d541c2d48000151038a045c48942000701c00200c00040d01c42c24183d01801103810381e0400a034003 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 687091609 1250 687090359 687090373
    0xc080915130f060609021c0b030105060916020a0807030c12090f06030e030f0c0604140f0304050409031701060503070327020405060a0b040e04031b030207150c06020417070503 77
    0x100c1030303045090740d100b90490010340010740203040800c081d10455210006003403001450f80c0d02c1a8140425070007001ca413250500c4101c80b01c0040500780c41e420b4800551100d0404c0c0401e54504910404500c0e030103030390056406080a03078940354100d0700070800940200c0c400d440c05004002c05801d0a580c0540e0508080051a05144542400035082d014034000d059076140d5002c4900c400304190754402085460080c0d881000c1418582c64082c1135508a80c007907400d40900c00302c03580104071465800d47c4c0078015402d042c0f46c24104406000910000d4080c0100074042146072140460701074043c080507152103030307203061005004040b14a03c0f044c4550f40e440500c44100074540b000118800940c04490124007902c030400040c136044900d5000070411040024009811221a140140300d1806601ea811440c50001d001104021000c1c1000300142c00c50364041c03010750801581124a00142d02d825401c031170141c6e44810403a0300c40c1d001510120185a05260200000c00164014000540c003030035607 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 687092859 1250 687091609 687091621
    0x80304080d0609050f0406020309030f0d0e12040e040807110907033c0f0204050d052805060f090c0d0b0609060111030a0c08071a060414060a0b090f040c080915 70
    0x5c800002d000140545c0d00040411040d0204209035010529200000c1e41d503070010001e050700806280344101c5681c0945040d61103035200c4074007550203d40013010800c2640da00c2d81c0d100780107540300c0d40d4100c1b1984d50031820451076864090034284118804e4900246280003000d03143d0a000e41030f04001000d2045440e42c009130240d0b03002c2400d941c404408045994a0392241c0c410180c042d503080260070545400c02c500c240b1000180d800d9400c10205269100a11044c0c5500c0b03044001b4900030f4903a50207080450411040c81c03d17403c6e44036449409a9061886050010303804070400703513040da021040310f006d0103c9840d140c60016040642400c254103068011404c80d601c9008500b403003414044800130311424400240210741065610901c0e100c0c1e0382d903200520003034461090310a240914038181c2c24001210140031030500600c0020440c4000914095289446901c40d43d40f0503009402d1603040380180d00c40d800f400200c02203d460781e20310f504d8503008440c500341c81c6c4014481444400018450303 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 687094109 1250 687092859 687092881
    0x301090e06060901210204090b0f010303230a050307020a20150315010f0c0210031a040b2404030f0c061107052202190305070e0306060a0e06030703080304080d060905 73
    0x309617003905102a10551150001800910f500f5501030040c0c1291400c008c071490518447e903041c1d0f031003900c800d403e201444038a025001c1084100d801410f0382000403400310b500900196a02c000340d4030403904040c903503030385040100803007400e0484442c2c0404408005450710520382c081c4102d1500100381180b6245600582240da60700e140c038103001c40302d1102c29007240300703091a01d200f030b80141c003c030b01e00794240200500414600b1360488030000a0b52000416251500600c0c044602c02044100085441107484220441108103c040354500308000000556050400900d5500984201010034034142028120b15803103080441103420011040c0101d94407503a4030381c08085401c8003002018450fa261000900c1404811100010311140b02c191440d0f044d042300d8401d4100755251051030041e03600f410307940e41c2d0994126610030502641401118004a40e440c0d1220000f03040750815036894841402c154003d03070b019a484400003486090002c22030080000420a26904010610300221401c2c = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 687095359 1250 687094109 687094139
    0x3060609011214030a0903140a23010207050a110a060503040c060e130e011b030e060c030a1b032003070503070c020102010b0a060503090d090501051b010609020301090e06060901 78
    0x314442c6500603441d0911060303280706080c901840045030380c1c81300c0909000e083c140b40351200716a1a1250528900d8500e0302048400300c2c258000400e12011000700c052064096501c0b640190643d805d01c10b1201141c0208a00e1003864004c9520140482c20507050144444490b084003050000400901002418a500a4088601c00d21704141c21000c08000241c0e030148000704d0b4440f0320b0400e038068981c0d01040d030005001b4401c3e0943d41d05064640213003942990f811440680c0940c0083c0b00140e6035000e46c0c00150b50242d0781920000d0040510b03800c080d80302c5410b1100c90000780d0b407142c3c6141412050a40d00c0000001850a40d00750320b8800c0b0020558030004007508104600c20f81e003881164000d40019405040080040c1c40164441d00002d066800440380410f0920500840700800c034000e0000209444041c0c2d1204e1410b00c1030300b803a0320500c0e0941d02e113018a65030303003000180c5012148080c40c007900c0b00e0740e03000c1400c60415aa051070040081c040724440c0551500400c04084441007607 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 687096609 1250 687095359 687095369
    0x1b13230a1403010f0e010209090105010305070c11180106021f0209371202150705060c03100f240305010f090e1002030c091305011a1b1b01030b0306060901 68
    0x28185091200100340503020072104c08402c01c1c28070004401110040d00541090b400a4500b82d10680c0c0c0ca000440030340e1030554015010500d4414240d000c03d900c03454180450070040c00903a5070f44e60840d50315621075000d07401840141c022419940912261040200c20b048602d913044d800d042041002443c100c801440310100e200302c3c6140c20300720680340f90070f031002da070800c2c141068420380c1c1e501e020300c1c2c0040c0b0f03c070220321440c0103010b600034203860302083e1034615421200801d240d40e00c0e01d4241030345510280c016103201ca2241e40000b0040c80842610700a0b02400210300300460060380259070741d183c401c1c0900305042c10580180109005906a842200c41c00301012030002d404202441c10400090001e001241c00003040060081044000306020002600c5010603101035600c10310403240280502c18410504c501d003a4421281c08000e401428500300e102d20509041420103440c06e94140c85a682d400742c2c0c10781007a01036805100303000c12814143c01034026441c20100141040a0500031 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 687097859 1250 687096609 687096629
    0xd05030c270406140a051c0f0302120d0b090f071d0604030f0804030308061507020d02010909150801051005030c061810050315100f081b13230a 63
    0x30810764024031200841496000303441000300d0340e12002c20950f040c04095030240035014041000940d41000c441d580b40d0041c0110400c070700b11846513180100340d00e1881c419802c610a401c030000319002c80030300505004a0185000401001c0369081c4182000300420100b407101104007088642d0b42c1000c90b030400d4511101300003542520b2240015010300580e00082c0440085d40c250900300031400005101f03580c000d417070b04081c0d9a40e810070405135807541d0071085030140c801c0c442c2d50014101004c00402c41c0d4814101007520075294035070360080b10304001c9901034041100b402045802420710401d40c20007210b520710310000d0b0401d03010076030340e51044030b115001350b0000505614148540d00203103c0b2000c010015140700036410402829a001a035804000c08503405030f4114903c2c120303505079042c07500d644411802c013180c031009507a1800010001c0c80428548858910322003000002003246103c2140481c1c0c100713041041070b60640c01c84110040c041024001d851101d07546d0062034904840e00109 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 687099109 1250 687097859 687097897
    0x1b0201081f1208030109180f06110f1c1b0c0308100e0c03040c05010201090b040201051b0d0c05060609010f1802040803030112050f150604020714031b0d05030c 70
    0x901c0c841c01191941c40500100c016911000c10016014000c60407181040e006102c0d602405880c4da141c0c240c402c00040c042d40011401400040e2240c206220104410f2141d504040c81c40e0400b031842d45c00241c4180000300c40328064070940707500b88541c0c030502411480300c40c07081d04d03000d501034044031000c00043c0600004800196002d00c12500f81000381000300c009199604082c0e8000e05c89410607038046540c0424807c001c1402e51051003a201d955407c0400a40183c0b103031b0f001500d07071307512080106211074040d41c01d01072083c40810115024111940c0c03020030903501400d009080c044050113417407050b5a984010807401500421840c15525203582c91104d2400210b9500024403460388040038600000c400004c2d002da0311680031105900540c1030300e505000c40341d2426110302d42c0c0d488415201111002064075401c00d035024007513441c8510321003602c550700030f40030500d1500319180411480c40e040f114400541070a01100c002c0c0c45490402505608241160000900a2901403c41c42401030 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 687100359 1250 687099109 687099151
    0xf031a0307090f1d0114090a030f05160203060c03150a030218070c0b09030a09060201020a0c080c150a09021002061302090604091209140613150c0c08030a1b020108 72
    0x2500c90f901400e1308894030085410130300300c114040e01404854524200c000070000f9240701021a5051a1a038555100061086040402d50740c60300060300503440b80f1504281d000050b10704009007406007090003006d9440342b07807603c3e950407074805040409008003130200c010801601c4045060744030449400400b80c1130358800c14200c03460648a4400380c6240c80c00c0e0203000c00b002010005040c3c2282981d80c001c20943c5510080c0d00381c0c4500038204000a0000075800046000107029041c141c6000c800d0302c5480d002e4065004002c04161120302c2050340d03e6a25004516040c01c0b151826038031800984410305e0404c100720f540d803140c010701138000c0010400090301503070742c0c1e1711407a12107a002100100c0b111250000611706d4056004111848580318001140c903d422002d0b01e41c0d00e80b40090b0005035078145075564014410150001007032000041020000a0038070501d00040c2c4583d0000b59150940f440c001080046000451103180215160325000f50760300115040d031001c03c0460b6154112988 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 687101609 1250 687100359 687100361
    0xb0d0b12011a04091718040f060524042d1409040605060d020d11030601141309061b050c19030c06050601020a052a060a2c100f031a0307090f 62
    0x180d03461005860b400203140001c046c4840c00315101c144195010010000329046210403100385015580e4018880c81d500c56001c0805114401038480c000310050a01c1d5540b04000401e440c1c46400c11b0004010100310035041c03d0801c0c03810020440300010000140743c007000f092410602030400307480e032515070002070140e40f515000d07019440c0d8003401000d04a0400c0c140380d52400300c0d801207103100740a010000100f810f150901f4040064005091024002d16410780c00020701004e607040b12182d4484590701ca602d5075000c0d141812206039100c59503510b003014030b602d040544604d043d40100340c401819402096101d4440643c65620040001daa5110b0200603407803d81c15042c000c20502c9840d44a40c0010200c125a080b0074040e0f5005ca501c008000301006100d02032888618005882d400082900c3d1041e82c12861140351103e002c00240000d100115400c00601c0c108000425155a12260b000d50702d0311410008000c280d00e003907015142a00040d813a81003600c2000c2d40700c2e031a141e070a05180d034a = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 687102859 1250 687101609 687101633
    0xb030c04080318011803210323010323060103030c050309030d030e010b0103020301032a0b2113051b040b1f02070503030a02070303180b0d0b12011a0409 67
    0x50040ba070300c4400021140f50240440c2510750b0001da02020a50b03c0240c0c00d4140c401a0303940040003003e0710a02001310008103864030b11017002c15494840980c41e103200140700151305d8841c155940000d60440c00c00030700c1c4401d1142c6009440c94079500081029002040680c1540c1d4103143c403817862900e82c00c000c0e2450180105055060080c200c98a4006030190302c40701e202d0300444020b00440c0303003000c0190f0072404248400f42c000c55000203600c10660409080b02e025080c0b85150f030100380d441e44070b4070b00c00da00107110451075810303c2d14111601c000320b1030400e54001c0300c000040340070108a940b1592111107000414624180c5280603103101c0d035032a00903000502001c2c0550141c8160301c001207041c40c05604494015000d031a9000c02c203410302004503100050309800034541d45156907411034851143c0d403200c02d000104040089407a0805200810070301805140c0420100150401c015504c1200c0c174500034a030785450419245450540d01c0c10401e00304c1180d00203500c1030241495144000 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 687104109 1250 687102859 687102869
    0x12060603040609150e010c03020702012a120503070909061412010f020c07030b0a060b070b0603011b02031225120e0d020a0b0a090209060618121b0d0b010b030c04 71
    0x159028104850145d00110152584000034809588101419401c034800c6402c040c0c0050302500d1407090710790806c0c20400000d00c00e44803861503001706807250540301c040d00b0b940c0c1000400000c00d002c002c9030720020000140c4004c0034100b0100d8030782940b01d0104c81c0c49440490040113810409a039a0401303600048101c442d80d01c09654580e129855542c40713140c00e01003140c8010034440071031054401c40c4242c07015554045402d03072800c0101d494242e10550300600700390707140d900d40c200f5180f4070180b0940034040700c1c0c3e10340003142c80c1c07410302c10f907015060380c014209900b6601056446a000280c0040d04bc040030315404c00382d485407030f03808a0402519141160002a20441ca98100c0f00b42d4005080300009000750380c1500103840b00c14046040e05d101c904040e60280410300410b102d4a800f40083c04c0c8549a100918038020110000c14840388500c000b24446800801114810807150402030303401075400c1360010003041042d55042030310b85040c001d07079055003c0400003500b00c0e01001c0407900580 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 687105359 1250 687104109 687104123
    0x30f0c0c030c0c03140f120f0714100903110f06160c32060c0301152708211606110c01060807090e150601030b0a030b0903091512060603040609 63
    0x2817024044240c6e51005000710b4913940c840c0004c3c11a0403503446040d21100f44450406074646030705502e0f90814950401e1000c0000c3c0540d44420040c04510f11130180034501c83d880300e2001c1000c00300d0780c0e802d0051b103242c5941d05030820000c02c640c000d03c10300c4408082d131660030080880411428600c9507508075841171100161507070100b44144c0000c00403074a04500c503008440c00c60780c0300081242e66000a01c102c61140c1003001c82a080d0601550107040340c40d5030543e102d844501054103424821655502ca202c0c5604040c14404000c2107407401a00e55060309603243d45480d500780c40802c0d1140c03841c0405844c4039134905117480640500c0c4111004031032194000e00090751100000e40d15a00284580c4942e0340c03403d61050410000880e1148521808505410242d07480c000150050114140c045601401d070f00004000550100ba0720b0b809207094900560701c0d10b01000601c02c108013001c500103800d040502004812030b17280004203070b200d0070030346070f41e07031240c03210701d8010701170148450014500 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 687106609 1250 687105359 687105383
    0x41e180b15040b030a170f09040504150c0c0f0213090b0a0c0f080108030a0f020c0a1205060c0906042705180c0a1406032e0303030f0c0c030c0c03 64
    0x2a8040441d0302030180c40444042040142d03500405959034000c4000403ca01c42004854107051440300241c103000080181e028130b0102c010380001c0031140d0458084034000039041e24001985894032800e0080c0c985410b0010411a5948403c1c00294000000074801d61000b8140080080a908003454203a804041d05200d800c00c0c3c003290025124403006940081d5501500c4140750b8403404d080c40c1200c00050145103400c10900003120149640500c01c815840b5811540d101c0c0d850343e008c02030040000c52400c40c265040c92420790309280014100b500d01e00f801b072103583c400d5036900080390122078201c81c40882c01078550240301c50221007a03410320b100702c1ca08000c01803181030a01c003104020064030300fa03e24445500b0108912034006003d80302c50420051390300101800c0c010000e641000e40610010a9140c401803014640c1c0f0010328407006040102e2800c000f0107401d40644403100000d908203014200d041c5000070812242e20002a04008805954105001c100103042001e190010205054 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 687107859 1250 687106609 687106621
    0x325060c0818010902090619031203020a020f0a0c0608090a0c140111060c03011403030705010504060209150403020f060f0912010c180f27020406120b041e180b 70
    0x4145012940c00b5004902419a008030002c103200e410318550740180503441c562521028801800b6004a9000640c0f40011001c0040780c400c00462208014555015a8940140d0300003030030131b80441d0403c0200c1d0312403a413202c0000c2010a82505940e0039207480c801540c0c40300c200502e4449240c2001e421450681ea0100d522150322405856a4800781c0703d00144405000100340d1303c0d00704440041c0b009100348010b20210704540110200b07418014110703800c040007511207508407041074400700c44040e400201d1038281e0812034070800c03141d0003003603905003080e103107401040c80987d000b1101c40c422240010882d0300ea0031414160b4003010700c0a016188103054108815000b00034120a44001ca0107000001c55403020440c419002e54040064440c4220b281107408400c0040122410b8805006507400c2034590842c0d04c040d00082a540d40c1e0101e400c1d1000da0600210b034510303000107020b142031a080c41e04a14004188103500c40c1e440000050010761100c1000c0014500d03540180604645410f001d4 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 687109109 1250 687107859 687107867
    0x1e25030209040f1707210e09011701020906030f0f161e0c060212010302040b121b0402190c03090b0720010e1c02130b011b08040f030503031609080325060c 68
    0x4071224280d0b00b446080300b501000303079401e40a15916a42c030072903230350052200e90704010035010b61250900000d410481038500041d50b03600100c3d000d05c1000c500d00100403020040c0d004894028100300302102c182c4e800d440c0e000b440d2500c6840e00290440a4180103140c0e0340c032401e01d27007403030f01e40101046448070907109011307441d03c1c400e2106910039420310402e0f12a030300d440d001103064803440800801104048120f000c642064060a2580c49607081c0400c800d206144075071029a11025901c18020140354600906211101d0700f00441f14030382440800c00064221980102c3c843ca070440d010080410a401240d641903240d0000da0040391980e5040400589220052400d0348215040041282000c0750b1200700e0b580e0090f81400652407603022240c03010803107180165203015401c168541a210036580c902e40003c3d40c01100c199000200b046243c1c02d08500d03a52448406203050109e407454101019903038040c0e03000034450080c01e4138106060103800044c1106160b1304c501c2c144407500f0040b002030 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 687110359 1250 687109109 687109133
    0x201090302062101050a0503070504050a02070f12140a050d0911061b0601120807080a0c050a0807021906140903100c051c1e05091e25030209040f1707 66
    0x3d0080c182810021510745044040403040d0341c03025008110031031600b020000a00307000b401080c07815500300202400b085980c24010040c50003141c1ca841030041c0c8c0030700141084100c0ca610040e4030420f10108007030350740c40380860b03407000010500816050032134180040d120f0306081400d64000c0c400240000002c0302281d04407000400300c0245e0301c1d1680e945103000a091800a00100035550030001c420005400d00007030112050285040d0074004c2040d0b42d580e19040b900c82d000c0d61082404501c1004524140514890130204e0a8800c2b08031441d10078060804480342101080898000c1500540c64600300180d081c1145407170401c0c07001c0c03400034401030001d03800b0b400d0a11036204035088841c003421072030140b04030380007580d0b03020583d2210301e14041009020143c80c0b440c690250100d0300399601d40c5607240c14140460740c0090120f1841034018000c0c05038031007025914490001e0f0080025a03182c0705070580c0f15410540c40320708985280382c41a4410006e0620244110002c9080c100340000c00d8801 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 687111609 1250 687110359 687110407
    0xf0605090907030f290a0803030708100f03030905040f020c07140607080d060515041a0d14070207060905150304080903030702191d01080316080d0c030b210a030c020109030206 77
    0x70342c101703040d005c107000300074a9500034501a54801c0001c1040c02c0c1c0304043c42c0750720861044d200344805440360f14000c0d600c0c0c1c00307500690005402d4041401180381074858403054a0200d20218030b441c1c00c81c07001c151117190910600700001c029000743c8000340c9403c800c55041541c4808011707900c50340c05c1d8461009020350b0007410701400c1c2000c4402d5581021604440903180701c004203660340c8104401c1b840f11680901468018a82c030382400c141e055041c822814003950301500039100031810030324014507002080d03000314031511f108040d07001d00361041d900312a041a000031040756180c1d07801d80464514810f01341d000390003c80c00c88104842040a2412130160f904107401c01900b00c0b0581491101d02c07100380103c00700c50f001080240341e801001d0f19904c07002071003000c019041c0100d4403140d80881c1da000e002140860f0316021040c403039113080810400392681c031581690201301c40400c0169070315192304c0c005061046c24080103003968000c0510030b0003594003c14603955088401c0c1d081281079820450 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 687112859 1250 687111609 687111671
    0x121b061c0f060614160f0b010b090108100b07062004030b010305061f060e041b030207050f01050108030f07060f050c0702030c030a12051b060a09020102070f0605090907030f 76
    0x319010384101c149503040c00703602c0022800c1c540000300510710113030f41c0c001c00c56420306c95a0484002501e060710150080003103104840d102c1131018005808100001c1c40307111a100705000c24410348458409962103150003080014404078207144031140e15040c00b480c0419110041000010480c1596540f8140c03449242a00c0c0039464040012232000a50400421414881e2205002540c0308100d41c00440c0c0004001051640d0303074103042c0078068000f490700030009800050030821301408011046003600300300700800042d0316152500d0788a008586550700805000101e41c8280300380d40d0030140d2016010402042142802600350613190720210701280607014420200201d03250124000b44804d4012142c008001999401200c60f0342c449295030040004044cc50100c42d04100b240074404c00d00148006032035405e5000185c90720302d4540c040301504810801c2804010f80c00b00035240c80480a80b0014016203900320705801a001c07420300c00250514111194002e000800c065028000a8110b = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 687114109 1250 687112859 687112871
    0x50c0a0b01061b0209040b06010c0c09230903030a2f07020f030c030d080709170303040201090e01150c030302210604050702010603020d111207060206070e121b061c0f 73
    0x2807118920f0f402d501000e0b620600090000c0c000c9604207a400d50b00810526003100341456540c2d0b890f444142c0d541042c0e000c40c0e80c4070680c9500c1c91003101038900300740600d0300100007864080000c81d6603200c01098450300d6901d1f940325040c0f00c008420004031400c8010040d0341f030008a0b849048407500060002e905c1001c0607127002502e410702003048c0b5113100c409005441c0089442000707a4140501500d03034002c00c0f5024000192040e0441c00505050108801440d82c9050078000102201e406400c100c88140e00c2c540100285d00606060700080c08203804c2a4401c000c141c201a0028050003030358500d0b0315040f9540144441602000c0c51080c40200c1d010005038441d54822402c039841408029048400240e880c004200c805c1c02c0000a021300910070302201201400107424580c0c50752040303000d4ad2280c0c05104005030441495807400105950300c0d03243e00409288641d6940011400b40402c51010400c1907081c2c0b140390850b022610000c038000402003034000d07000d0040010000d11501603103042 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 687115359 1250 687114109 687114137
    0x307090e01200904050414070906030b0c030f0106260a09020301290103020d090611070c1202091f0b0c070f080604030e1203091801031b0315020901050c0a0b0106 71
    0x1200091120380d00d40b01240c1040a59401d01c002400c01800c1901c0c0088501241544910f0400841c80588240400450450315500d0071031110b00d409020710311035039028030801c148030104011050445200d0300e00662100000c44035a0740d0720128200c01d5045010040411140441c1600980000b501c02c0e002001039804d103001c0111f083c0841d0080c60040301d01840c0130307000c5620a8000d01142c00c90042d0024003824207039108000c407034904d04070065640e4007141001c14840b18440345001031002507503c07000140c1c0c69000860240005110001c01032861451281d411a4041e4800c09803892014ad1540d403003454070710f1540c50100740728100400faa08000800d9190001c41c0302e50040b94161501507088100c041084041c151034012407016201c00d0246110b940e840604060020000d8844420f0030b506504040d8a0f400003d4105c040030580d140702040081c4c038592400d650007018000060b1181c9050004807180e101c2c1e02c2200e20035108011214003403004240a240c101d84864a4580010080d4 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 687116609 1250 687115359 687115391
    0x106060825020c010c05010209030609010506090c091005030c07020301060f0f0609081b03030c0601030c14010c030e090711060a1506090b04030303020a12020c0f06090a0f1106090307090e01 83
    0x750200390058000c418102c00310350241114070030710340c41100054209001800400d20384801122900c074144c2d1101c09000c00360038840070b4070740c00901d045220f40c07800c00414089582d9079040d98248080042c000002040300e00c0c0d080c291680070380d00030003d00c0a16510a400c024800789801401040d1040300d00000b0418000c4200c40215801e0902a0030100048404505038102586015406000401c07008007a00020f002d81d80c06540b02d07480040d4010b0506d501d4564449045d5107690501003400360f2080802d401246540200300300710795215103039031031030f208941851054a00c000d180c49090301740001008240c0054aa0700000c111210f00c8950710f03802154445c0c9039110740c0400c2101003000b0301c0424440c1e001000b641c426401d1030030250048420300000ca91100c880c00f0340e0383d04006c11480c0300303550900c00150844010001413000c0c01d5a0380f512410341d41c0070000100380899090403004503480d004c1c00c0c1d0b00c0001c401815146a242d43e0070440000c3d0007440c820008551034081c10b40b0380032070301c = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 687117859 1250 687116609 687116671
    0x3108093c03070b0721091805090312250e10030c0c082d070201020d0905150d06090c020601331d0415091401080303040f031101060608 59
    0x1d0051060915104a08480c0d03806204103960320714448241628000400c2a4842c0c9910240e440c1c041c011300d0124002808130017201c64032507140c2003c00340640c5c00740010070396003001e4101d2102d41064407050f031071031101c00e0b4090014000480d000e080403030683d003050b02c5042210054584402c0785080e444101e007281e584000b1807004c00d0b62510b04402003003202d005095101741e40c402d800641f0f820001c440010842d04100d03078042c13400019424046583c14040320702059040c1c00d00b100c449040c400051000c84020354280300f4601c0c041519141405c06401000041403100340c2081100c0311700400a444000c03d00840001d0440b030f207006498a420f80104851607518a034100404840c4444110341c1c030801c0038404401501c888a1186203036445115070202003c2070040c00304021b1a000301e107403d0b100301c0610048049907000040010300c03400300440e98030940c0280c01c8100c0d55114036040c2e03081181c42050308565841c1c45000f00703516070003441c0280150028400002c004104142d52180902c3d = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 687119109 1250 687117859 687117979
    0x12d020a03030617210c0a0b091b0906100210020a05030f090a050307030807020a0b0106021f0504050a14070e09010902090a0b010906030b1507050d08310809 69
    0x840452070817080844440308400c4000c0103110185402c5400c0d00042c41c01c44000c3c402e42d0701003a61014444ca40008001c104805000ca100c3d8021981c00003000902004000f0000b034003e404501400201600c2805005070043c1e4203001192240ca00020080c45a00104d070b2100d03141c00d240c0302007906030000080076a6240d0f03000e4019464021940c0e0304540c07000002c1c040c0400d520851640320006100054821b010700345c3c590081c407418001040d101c0300d0030041d84401e4822481d03c0c0c2404081080070485500f001c2d0801845100700121401c0340e80b921100d0390060000042c00c100788049000113410100c40d0368000c6920711001e4490310a580c0885000003100c3e40425040c0c0010032445010f5008410802d500801010069016840000340741d4003551089450350484619818965045501190080c40500c03041e402002c944070780b0003c04250300c5000d4410901201138808001c4054100e694000018003050880b002180514070303400801482020210700c0101002104a40b073740340c160b4854 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 687120359 1250 687119109 687119113
    0x241106010603150b0c0a03030c0c020303030f0c09210c0114031b1c0207020306070e091503190546080c01050103120210020711012d020a03030617 64
    0xe46080300c150000c1480782c1c00c020040c2d822100000b00300300c400002e00004801c56000c2d10360560146801011650581200400c0c401e4250502025840000640b5840040f40170000c1c079903191a0413000031070140804044d0310404807600161800000c460032145c101207282210078864615005542c0401010102c5003220814000a0b55500d0007a984104840d42c00740290f103080d07151305682d00300325049649600025000210342045007010030000b9803000e09450701007144445640081c20b83d00c400f07040e80e04070114215065a486d54180000e940190b100c00c084d44014120b89015130b15002600e2040c80c2c1d80d0000c1a0300c80c041c0340900f0140c0010004800b40408a4070411000c0105181c1c00034103a805080910074603a9008092180768061801022142014041004020f00e4000e041e5443d11a0500601c070080004144294041c0072520909003100e078140d0100c05606406034507018030200e89220085103900341d80219a548085d404ae55050285544030b000c0c0303141c0105a418042000d07 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 687121609 1250 687120359 687120361
    0xa03051b071715192003070306050906041404020d03020724030f060515160f0503121f090b010c02030a0c06021207081e07050102040e06011b200316241106 68
    0x4c0d100b9a80026507410038140c103440020308016a49440b5041143c5180100c0d0b940d0740e00780500e2030411000d9a1000c0c00721800e0000f0407a075101d0101e000e10281000740070702e180000f0a81054000e01240c0c1c00b0700114114900741d5001c1c140444103041041140c040803a03e003d1001d131030342225000e20010b03200003400c1450800784003120209241c2c40325001503000a0007108100c0001c00604039140803d0140005644400007a1503034500c0790300203841900c3c01014001c010790700503052000b46040301c0f6640750010f844c010a00058840654007000203500d80550000d40080010600030f00e4241d60856003281d590300074264128120380305040000d0501013042c0040103200d4030074078890490482a410240c1070034030960300d85080e600300f50000151810a042005419603025442e403006496100905c070890030540c0710080d900013100d0031241e1003440a0752072070440e10708010144042069003000b60310281da440020903104103428151043c021a100c010120503c81d0391850b840010050240c011 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 687122859 1250 687121609 687121651
    0x20105030903130b040503070e190902011209060f0605180f060a03050a03020105040b0705070807060c020f1005010513020c060a0f060b0301081b0604080a03051b071715 74
    0x840e0001021030040748070030801102e1050200c102d5a000341355290f6032075195400c14041604116240d0041c1208040b035004001e08001e9000040038070080c01d85001030b0507041400100e41070709506491020322401c213442e80042110701e910101201080400401c1000d48072010451034003265a80009403e200202184800700609100c5401100003003004c18015904d40d03d0311b0a08080610650160359a041000300b44401044001d40c46602071070024075103440790340ca01e0001d008403000544001c0e41d85034540d840c1c038020800c0d98107030310080e400c603541c1c0101c00300c648020b44400d0103080d008901c004c40c2503003250700f64001c2ea43d1042180c0041e004a0341c90703160100050580700d2089101c00c0e12844005200021382c0000c40c00f80c83c100028155020b200b8160403140c025545c4954002c404c200010003403207002003410501103500d45010b5076100c6642400c2e1101c50140551080107008103640022102030105500c48502e4ad000155074003040390103014201050103c90f8110254207282070141 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 687124109 1250 687122859 687122867
    0x2003041401110a0b091005010614250605091e0109020d12270806090a020907120603021009050315070914030114010801060f08060408340609060c1b0201 67
    0x14032900c25001c954030007516440e000310704c11081d07510303a049822401d1400f0503201c4502402d8054819030524030455410303c0d0302c11840f4412a1000c03c2d500b10070440364002c080c003650400c03170780d01d820410506c0141040c01c0c1094840c0c2d402c003840d41810002c1c5188640840060041800540c0c00400d81c1034034054030340700d5040402102307150404100d056510f2074040c141c3c00300310119403000e0044040c0c00c20700700007003640351103406441c0e50038940c0030124020040c0c0d109800960711480c00e01e00781d19141c03c200d5803035019203904c1e00005d43c8843c00300813911400b5800000c0c0b1040720002c8040f99804c80007950f419400d91005e480e40c03030000705007150512070082e1284140aa01c8806000011105d01044101e2003c4900ba0480c03440c994440008200b174004042010001d880e86034043e009074100303551014000d00c100701c603480282d070000c40c00d00c01a140c50701120180e90060040d50717900f441c2918040d00107119419080751600c0c9010490440d251040e045502000341c6000150b03c04203161300199 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 687125359 1250 687124109 687124127
    0x50702031b03041d0405100c0216030633060302091201141008160e0711060c03040b010e0c07151b11010c05090924040204062003041401 60
    0x54154401008540e00d0600d001c06000c4981ca520700103140c846041c0b1020b264000310a1441441e00006642031001080380440c0c44640c00c0000500081c490801d0a4143d007045c410001c500703d0300c0c01c0510300005011082c1c0050298000700c14100340b10491b5048000b1035014002d900b07030f00d41e40c0030788028050240240c0c01084100da00424181e03c80c0c10b004226070946580092070782400300b0110912010083e405481d902500000f0050415001e03011a07035a01d003032051191840004c21f0102185d2001e00450045500300d450b10243c07040b501e440d5028100036802034030100e03200e2070503000024101e14420310482c011a44180301a141078120f80f6020600410340034440421640d40403e0340302021580b6400071800440d8549841204d0801502421500011000c0050000401219115564021803281d104402003000c0f243c110798500c00d1000104401026500320f0b10003d004200c01d07400501c07c001e014541c1c84010346250308582c10513224001c0780319030301c9185401044811207601400841e = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 687126609 1250 687125359 687125371
    0x5090604202e020d0f1b1703100e060a0f03060515060d060306051e0402010f120f02030103050c0a0303050901030e0c03151816050405040614040501020d0f06050d0605 73
    0x2e0402062002e140c101104500d2042880e298040c0e86812185805100820304100e40d82080340344170f40c800e000600314118100d82d00c40002da0307102282c010404032004030341030000920099501c03868005054584401e950060001ca60f41580000d500d9240050035142510140c0080340d50f500c0c83c0da504e0502030711001d0100f038024000c1c00c0b040d890640b120700c0548001000c0e580007091003403450905004545c0050400c2e180400e82c0c8410401a070117509000760020350a180014079222880021210000615105021581400301000d810340351034020310306a90040341551154101c0318104003441016200080115509118a03241c179070199020040c101c1514081d1060740ca038a00c006030502c034042810f2054440c1c8003040c0500480ca1042f408940c0c0e030313450300400744580c0450050b078070f50b02d05100d07551145443d00000b07010040035030003c69a103a00d004000006003094580036003c1e4100b40484904079282c80d250548002c142d018840450f0000340c0740456845580e190b44c0003420005101e = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 687127859 1250 687126609 687126619
    0x9050a0920011211090607050a06050a0501030c05040c1d0f03030415031404050304030f0819171b0409090f05060717071e030b0102121c0509060420 65
    0x40e0110310200000d90320014818041d01020700c5040015000c0c420661240078000d1802813180001d035009400c40c2d107456001c860361500c41d039440c5042d41c9407405000008181604110902210010396004207040c2e0307200b008055101e03500e84041c8001c46048008603800a4441c06100a00900801d1403a02210340502444003074010200420311710b911030307805194007040c400c803072480c11507151280f8280e90300d080c2c42410060400340c480b10b0f03583c0190300014108040001003401048408012102c2c049114451120342080602000d481004d181c00304004801401002880040840142d2400e4003540c1807a9403c06060001c3d10005100940013200d03005403400c0303401e01066042090b940b0882040d660002c900f036111000920b078005c0907001105001c0640303690080e00e0300b129402c0c01c02640529000030909243c00040b4a408a2008100a22400020906584180c0d0f580c03c08541144030814005074403246401c42d0b44200403075026221411110420003240c08010030b40640d0000241 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 687129109 1250 687127859 687127871
    0x100b06070b1009060e0a0c020102070213020f043c12080c031b030d0b1e3102090a0e090c240d0b0907020105010311040c090b0c071a04050a09050a 64
    0xf90141150f642e90005c411000c0310303008118a04800d8000c400a0302402d00c000d5082c000340e07501040741f002401c003144138016004135002c00d0135005030064400801c1c1000000080a11049141c106020819081310550001c0ca149000354407882d1448011201806051380c802d021a403101e45443d04403070400e542501080001a4031071a403401c504416003c681d0103556115082d401340012030741c00c00704280c058070b002c4107120a117225280c1900c0219030185e071a2801035001071640c4500014200301c060380010102d00a44c0d00f044554080c0c041d020f821f40d40c480e9065299a100d01a014080725020a01c1e406411140c0b000e040107980e2b40500c8a036802888a18910f0b101000c18030703084074800403944c99483c84da11402e4602000107541010480c0002c0107a541552500c100c20000038a28030f000e80d44620507944603510414a03503000b818116075560300c4400400c0850348070f00d60703407290344902140e000003035a240785214101e50403900020500c46400386031030008030280c40024035810003290781301 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 687130359 1250 687129109 687129119
    0xa0f020115080c0a080a03120b0102190c050f060412030e2e031103070f0f0c020a030b0901060812091c15050703060f18020f2505100b06070b10 63
    0xa070110010b0300c251000b0304010248541406010f031560750005800b0340c40040c100011940004404408801c0501c01042d40c0140000617850720000c3d66800c080c507a507038009a010300c481d6006901c01d0300c0e8101e5070507440314454020004580158068010204556861480081d02682031121980000b410b0140c4c607045541d50340e40c19071120600780e401c9180038038500319403c8e4584109203800e03c0e0410140e056040070380004100d040e104260000f4051440b4000010b28011004881401c0d4000e1000c250207480789040d1100080c280c1e0b40c414290308005011441c04000701d00c010f0f54004040050b42802c48090412810b03000c00d0814a620140c0341c01d40f0804208a0144900b44207400c82010030710f801c041d50b0050845040764031405580c00314484c141f124403411a162444410404009601d4582e24000c010b84e0380308a2080700310f800341c034868002c000c40c2c00c02214116580220161070f0004980d0450105075a4010384039035000b81d081003400300182b01101c00e6074114007180c8002408607110 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 687131609 1250 687130359 687130391
    0x80909060a050a0305060103050d0507030e19090c020703060606030203040209131502070b06090109110a200706090608010605090604170c031b0f0307030b040b07050d060603020a030b0909030a0f0201 87
    0x203504217446940005005005004d000c00041c200f12030640f6100d441c00d400c1d914000c002990451030144100150f26200302012a00e4500001822a1020402a034509400040c0d035806840c8400c85038a81440c3c80010998007034400c1d2485240c000d03118101e00d5890f2107111818540c050701c103c42c0c20910302080704035903541e88040e1030350510403003112142e4148881085961807050340140344041c04d011200002040300002c2d55545c01e002d080641d84440403050040106160a040c40424410100009201c1da840b002c8441190015142c41c0900c2c0d8940c5c00448180c0320303060032180c000004000810034245000d0302038442c5504c0906882006003480b002030700300003d200940c444451082902e0116281151100950300401c070002d00302c0c54a144d850665410004101410701040e00b000038030703003900480865450982102042102c56201c843c0a402904545255030009107003122401150400140c80c0d8059600440114203012038078404440c0000814100400c5540364107080d0841448 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 687132859 1250 687131609 687131629
    0x60c0f0d1b080a0501050a06050f210123090c0a1b03031b0201050f060405070903050a0c090606230307030609050103060203061c0b07081320010813080909060a05 71
    0x4245004071904032000004004290182c070540245141000410483da02d0102400c00c8407806d00f440d685814003280180f4442c0234942003120354a41449900e058a0301401102c0d0507503105203d402100300482490150074003c030301a480e0420030210201d59000d8540001e011400300d40d1410140180d06c0d0340000558840851040700446c0d00c400d8890b03200d070b1500c56405d001e00c40a100800c4140b801e2001954a810081c0c0880c1c09943d8034008111114410500c200196030031404842c20003509240c40140c1912074410144400d18004010525502c1802940b2012001115582c03205109100d038105580c00136000d03005240d40e0720380000720700c0154021140214052140161645000310600c6416406640240c15010076084c4400000e60302611003170300140146800d42c45543d0ba0040441116030203400a426200c110701d4840e0300744c07001070009124250a0342c410381c054844c41504a500702c032207000101046000c1c000b03c800307401c10900c0541e008000502c04c101d0b2a07681c00100d503500503 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 687134109 1250 687132859 687132881
    0x234080d02070303030e0d05032202180702060609060d03030c11120d0b030601050109090207061d0102031506041503051f0602030307031a090109021605101d0d02060c0f0d 75
    0x8402010030625405d0710070421111100e201034540c48005541c014542d120040010000d948039040c05030394100d52100c469520759001d03210841f103c0700001019035044013103070100014811900019400e040c00c1714018021040a04150b0403004d40d95001d5002c1d03d0800d03100c50402c12900610101d004042161a0703406900d0713217005a598450310328250603144841c20704c1d0b0180c0c0c004001009166440441142100c0511000580707900381d03468100702405030b190381c0f4045103e1104070b80b8170305081940158001d65101c013070340e0b900441c25014020640180d11450465580005800115601942200c0da01001405428503a90890340c11104c10600540040006a00200804c2032642d014440d2034500c104c0c80c0368510301c807141e50000401c2007405004065145401040800c405842c2d00d91901c4801c1c0d0040c00e40d50a00210901c0400401700d21581c4004036145c1e1501801081d40403902811202d2230364041c2159603204c00c40c40c40103601602c0b40c001e80310820009402d20500c3c9109044480c1 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 687135359 1250 687134109 687134113
    0x31006120c090b010c20040603030518010c0203100f06031211070f0b07060e0c090108161d06012d03060e06330c01090b0a0c0234080d02 60
    0x59064140140710005076000030701460700e0095006500d0f80c20003210300748182c1c40140b1410b40d4165042034862026038006254000d810706a0100416801201420a800314140020b00d284005401150f202801e144e020b90540c001c80c480d100d10501e950041810500d00e0140818219078917914282140041c0c0349407400074208110101101e80c090010b50014059242d280380303c1c604180343c0e041e0324440e42c1802002e1568a140071440c95205000d140b02c092001000e0054541e9180403a907142c1c0c10441c141c1d04001190b1902051790943c900d00a13483e0302c8036083d160015030f642c000540b2140b2000310250f0842c48852499180c903500340404102d0301c1d8242d41c012403124586420090704007805440a03203d001c078241c0c4101c9414001c3c4005c3d40d0000c1c0c020005a01142285024901d072081500c0e1500550074440000c007400110b0702a2401001c61650402c92103258442c2240c5034001c03c22000581e841d104860404004600c41000da0342400d80092502e02c0e60f40c1102600d007051501c2420090303 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 687136609 1250 687135359 687135389
    0x40305160c0e1e100504091110020a05250302040506060913060509130302150c0d090f110a0b0a080606310603020a200f01091b09020405010f0e031006 66
    0x7611401001003940740c40fa83c0322683d605065000010506450180d107020320758880c030040074006503085600b070b0100080c04040441d4050300e03000f900c400b094070085d9a24460002c1c1c1001c1c40d56120200802503004651881c1810300710390810002c1d150207000c0e2503201c00700b40101d0380d1035520b006203019042138108001545918001c1807150300b07070005181000104040018002082d0042890b13010011801c1030045142e5036a0075400f40d9014103506840e42d1032810b0102030400c0156000b442e80a13010343d1098204904000c100180c240080c020a25a18803d204201206000d00044c58100c40700401c258242021410340102541c10b101070091943e03986884280f280b0bc0340041100588214501075103000d6011502030521110f0302d02074184001c07010070b24203a20005010141d544040c40c1c00a009801a80c20b00918200030751404a4550740b01e4240010451418400c607011510185c6460410034070081090300c2c1c3c1030203002c80136014000c5d0351148195160500c01c10015101c100030041c1c0e8 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 687137859 1250 687136609 687136621
    0xf0a08010f0806060d060902040e0f030a02160f122d1a0708011a04030c030b330402030a0b300f070506030c0f0f0d23040305160c0e 58
    0x320822692000c06180c01c16000e0240782e40f50343c44080081c1b40c00400108403030480c3e202144c01403021082411090113500210141100c0c04070041241551aa08640594880f064007101d0b000c01c03441a10345003900200200041c050301c111040026002d2008940c1c54004405160210411400c503512200101c0b500031081041c22040000000349690801d01145400c03840a01017050601541c800444a5241c0313500c12051541118041c541c440380710900555030b03251944507e202500c003900c10822414240c50fa9003404801c0e02d40e00c040000b2103160b042c500300d00b400300941c40a8031551000f80c4072038403c8166107883c0e0342d4400032040c000103c55003080c901000c90903120541c820000c0b40c1c00c5200491802080082c00b601a11400c1351034541e2610f03044070b80c11341d42c40783d1601c0c00740019002c04d585c0d00c074a01050150a207c20305e1300742070010f0110282c40411008103001202c0300c81d051700c0003140100e8490400b03000d03900e040c4859003050400036101c0f403155031281c0e1301460005082c0300400107 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 687139109 1250 687137859 687137879
    0x4030207170615130e10050a0c020a0f120309080c0f070501210203130b10081c050a0807030b040e1e010903021015030b0717150a0611030f0a0801 64
    0x4882002001d0001c07401d00c00407500544405086603885800300c1200d40b04d441409601c242400304c03565084400900d09030001038090501102e000c5036003494072130b40e01c000342d0010440c03c606560080d40002c0700305d41c40c4e6a06401510b48018030041540d41c0c150100040c81a4005212044d9006c008080f9110b03e1824240b420fa200d4100504010108510710072406220450744441e44250340056166590196216000d50320444060507002c1c020090028610007000e00009807a284015100c0c458007401a840702501c14074403130000214100484c2e8442417050388956040111071030301080c0300b150440000d080e510181c0307540032aa0800e20f10003a64038010042c41800c800d064000384449602524080d45072191a54003600b21038880794400c0c602402e4203000800356038003c140c035029040010b0024005101d6a0400203040070740300200d07a0b4048012041c80795010001c007481d0540d420410115204620340e0441b0005210512080240600b5003000d81140310b001d90f1141903541c90001920707 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 687140359 1250 687139109 687139139
    0x50708031602040203130c030b311b0e09010605030c120c09040606030b01030b07032301060509040204171c1e050c0c130e010b01142d0304030207 64
    0x484a600400c54141a6011451154401d0790121001a103c0c0e80c1c119114042c40349110008110400540000c01000001007501b03010b1041010080e807681200c0070b0540d500d040c0c05188402c03500c0301404030400a210300c0800662101004002401e440c0c1d2504a12850917080d2025081039441d48030505c101d003010080080012011545013104540c141c036080c1e201d00303440c0d000f503001c0d0f60584000b40c14001c03e0b4201600450b403000c0150310544e5a8100070000e51000c1d80c0840010341480d021180d801900c0480303e42c8200c40c000c081040e130340b0b00241610076a00c07140840ea0003903001e00000030070183c40307244a001030206801400380b40c058840009048038485070300d10144108035401206580d500d41c0004100507503030810568800054000384d10b0042d942c0c0300140e21605c0b10316081b174555100c0d00010b42c6090b400000303000404c10b40340150345089480d20309500040050000050070515100083c03078031540f0740484013140b07135880301c0c606650340115415405a8006d1500300422007010f00d0203 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 687141609 1250 687140359 687140369
    0x1118010503010e01060e030a051f050c1305090a0f0e0a03020601060927110d0f0e0d1215330905030d03090c090911030c0907081618120507 61
    0x4034074560404003603500300c0c50b0600482040000543c00c54010740c40070420210079540180131600140d0820074000c01c0300c12510b800038003980c2003401207481082c4450a40e60311030300d200780c01010103080800f404000a00203108918a9469032424020174030740348240c0c01c944082d03c0162000c0f030f0103404d01a00e81a4180e008400b00040c4c04070400c030641c8440516005403031000350a02c1982420a41000509140542c4a03604000003450030300001041e0321480070084070304d03000c1c01400c2c4000085070715288040500c0010441d41401800341880c41d0380943c4084004290120f030868440300917043d0000d208060f950542c061098181420b41102d424110580f41440d0400c03056050801080d1110400c0c4c51060030305445003090010003401c1c0d00c0e5000501405d0038100884070807030415004000e09829914000d0180c0c0660103814200003200c54410f80036a180d42c081c64980c3c50382d010300c10301c1c001809001c00c00014002c1c0b00183e60445880b0042840c0c913248880c445041c10a81d0800450b5841 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 687142859 1250 687141609 687141617
    0xb04030b0105120307170403060c0f0305150612061804050f010e06100e0a0915150807062709090308040b0a06030b1b040e01150809031e1804111801 65
    0x1075458600004201c171003403580100e0020001e109900b40030058055034000820480c20800c50101050380145c1c00000741100d40c0d024401030722000c20b01c03582401b80c01c9078141c0045080000d0440610b4501850b904110043c20f20710080000700d450315040e000688080700d244d0800d4124603c602424041d02c1d0fa0302810401800c51420000960820202030344609807000b06014001440764406078080280c2c66082200ca0000c445a0303069a4002e01001007910440d42d440c200220340c21400098040a0743c110346c40d001e4841504054607100e00040341410031840464100100340c0100038000c0956031780c440c0d19940d41d0740c01e15181040c240318004040c03402d41807a298041011501c5a40ca154020f2940c0c06000054052060701c50440c2c81260030205c01a40c2e40800016000c8000c2c0c888210660304c2c1d912120b81c1e8030b0b00e43d8001d4407440365100710f00d107802c1d0420f8484405031549000b42001d202044a192107407030307040003050039180500b1600d00c1c002004100399481402005001d6544a002d2030 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 687144109 1250 687142859 687142879
    0x3090314180d0503120a0e07091a0607020a09091b0b070c0b09030c031207030f1b0305090f0d0615090207081b15040501051e040809090703150b04030b0105 68
    0x1c0d1900781e11000020603200ba0410301c0c0303050600c00d05008903600d000701000c56491500e4000ca03940041c20941e100b008407071060f0500022820400d1050750401889403420302110110038080280d02d400a178400ea91202c5020800901e514043c800c500d80c0794410503503103605164034801120928070541c05072031050020000c3c80c0028031200f0450007070301c49040c1001d84583e440000f19103060019888181c042c82902d40350008403101e1000740800602c00c0e0b403081c4400e01051402ca9160210302554044806d25481c0c02c000240580d010707164406015100d221404507040000d01c1c2c41289082c00e41e509903440f8079140c0c1d100942c1007240e0150003000c5095140c40d42c0d9070345050092182c400c01036469045101203c1c2c1c6560103000990040403060480107076400e0500700103000b0030f4151080032060301000508075a00d00030007001c44c85950403000c898240700516042c0703c869100142020105503031403036045074904180c0303031a501529802c460b01d61501c0c00c0d49030029020006030001d51081e41648 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 687145359 1250 687144109 687144127
    0x60f050d0803280c021e01020a02190f1211010608070807060503040c26060601090f0909050f030c0f010f2c0c04050f04210f030b0604050301090303090314 68
    0x10088a4002000901c8140f62281d58140000303605044010510341c5810a40d61083c40e9600003442c0c1c0c1d001880151200308480e0100d8010b080344202c240780d1000d600141080c1218001800b0307541511401000022026005641c2d0400b002100e4141c080109440079032541c40e410092107200040c00a00000380140b81c10314100c0d07a0f45105a1185908219000001038108001100c9140040041d01148900c41c441002c0300c0180c01001c4011a0813071103001e000842d207600c54000e40c1c0886500c000c94003402070412482001400900d81e09548512860b03041e074440b403400300010503005545802810010900203102da0946420f098024070076405c107400300c42030441c1e424041182c50001d50a0340750411030441c4642c10007200890f03d83e07000b4540700421069843c403641e42e910561149007482c40214401c900440010700c00e01183e400100d45c0f45000307001a00991040700304c0e01c07004080f1803d003561000040d0940300f4905040380000c3c3c40e0740440c1c0805410026a03107004c0c03121a00142011055 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 687146609 1250 687145359 687145373
    0x30e0d200303070c090203310206032a0c0714060f16060f050a0c030504030c080d0b0a170706140f0a0e0d1b14010203031522060f050d 59
    0x103039810311000d844540010081d5001c100b19000a94441c445021082c1c0c2c2c0c40c03c40c002500101c9000d075004640e503050300400c01451400035800700c0040028100d882143d001d020054000170700c54001884520034a003460250b4080d56070070340c01d400500c5960781540000e2030342403c0060380a29407911159281c0d0001d83d4403581525007002c032850820b074030b5039040540d400110383d059102800051906221010540300303600518072400040c081404410140002101103c60485014000070750754074403a1f000809990040c0342c94030001e04003041214400380003d014a055504c8603100c0d00c808040c4280c501b034280192001030449050000c1c0e82c2c074070142082c00034803622803070407a9140c00203000b030002402916180e44070a405400c49403075807981e180251304c000c0314444281030b60220b801e00080c94140d8405000c40c45134183d004d181191078001001a0100c106440103078030150085203c02d10740c14030101900959510403010a040385047e030a0500188643c00a90141d82050722040101309a = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 687147859 1250 687146609 687146633
    0x1051e1c03051209010b1008070c0b0c091c0c0e0115052b021b011e09050f0a0c03120206060622051c030305100e04081605060a0603030e0d 61
    0x14001040c9030190491804450303510800c44007030b0b803e074038007401d20808100540c48022507010940d02070b1001000004280c0d08400115407000000ba10130807030000007823680304441c0e00083c45560040c1130400c3c0a00140006100e425a00c94490000700c509092001c04289003004000f0321720001a19410010f01e46540e0480310781881c00c0c4000050034a884104001d0351811034440f032090725546600d900183c1e0081d5100c2c0c80e08411310080c02103100001d1006100f000c0200c404421400000f000c802d20900140070042c6054030140143e800b0205850424015040c09a05c074035042150340341186881640c2ca1502010402103501085c200903440d1a0042210380d0800b409252075400d0070700030f0284000044581009411402c0d080c00d0304140485503407031001991080c1c03010700095846100044250f078203423058404004070400490040707401c000c014a01d038060192004c0b2200e03035a031141442d12905403915070019555900400c00c0c55400896400003800c100e546002120b06500c5001c0c05030340d = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 687149109 1250 687147859 687147889
    0x18060607080a020307020d080301090c020115050f0409050d0305011a04060c0b04021f0906090509060d0602090109120f021806030a03030b06070c031101200303010603020d020405061201051e 83
    0x910b169014000c105480071564010020100c1030b015103010f10f15a0401c5c030030006003c0c140030a9101180c018011071110f45009507070805003a262800300302c100351a0a1000303401c180c0d921004004030300184580b00c4003e03200e840100d52949007180c0303602c0c0c0008035400c0c0302c00c00500748021b1003442d921420154a240c1c02c0401c400746901c4074000103c651480d0040c19010070082c4070100c40203a00840310100701e032420b0b224104115510b40a101f000d000840d45554400c0c00e00c04107074006175140d0302030480711a0600d8000c618545440100b03000002c41581541d1032038000300e0202c2180303041a1440c058942c0c200200050381450b4011960f6403041072030044c14140c50b12090072154503040305030384203260800000c15030300d55242480301d20366078a0b070052400110031482c42c204104000341d000003040001e500440c69680703040c004500a41112240034515a000c000001e9140d80d5030014101101d00d40c0d40500c000d5141504002c400b9050070f51080302d68188501d40800c958405401c550041 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 687150359 1250 687149109 687149123
    0x10207031404140105131d0402190b0702040f0209030601031a15090402130e010f0501080706050a05040b090a181506030b060d1a120f1203010321111b18060607 70
    0x414a5007007142e041800d4000c0850030a00e00e41080d801d05d00c1064030388c0514020384440020000d0039160590021550045480c12142006800014105580a0260303030040e8800181400e001c080006d0401600fa03100f900c00a200380c0840f50402020a8882c2d00840d40750782901c904001e15001c01d0300c00000034800780c841d07030b80c44034500101c0c070540e04103401001e0000002c06c00d190f010341e01500108000c0c06803000501ca56400828142c0c002c000f00c40c40c81030301383c455505140c41c0a0205601d507204082068019091020001d00580301842e15591490748010120b8240500804c0d407a21a0803684804201414608003208a40320103040f03071b94012030f581002c1480801c43d1030404541a02a04140c0c01c070380c040200c038540e244041401161003203203038181e03500002c0e0401a000319020a001c00f07020b2a8840c0c0880d94000c1c6c0448030802d05940358242940800c5044c080c0c40e0a146030850301c1e982c1110700d030055945a1410110159212000002c19000d42c1064008500c1c14020034400a0041d = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 687151609 1250 687150359 687150367
    0xf01060c060b0310140f010302030c0d0611031806060d020f040b011419080c071518050f0303060418050627060108010c08070c050c012609010207031404140105 70
    0x4050640c0200b1007610001d021210a0344809200d1001011264800a0b1400500b03000c41c26100403202880d049a800400408291701c0c010101b180c21640d418045940e682d40e05148049400c041018520400429205000394009200c81c2805c0500041c030092048040100d1400185d85803080011028402e68000034040200742c01a201c0c4501e1003009888000301041c00d003d80b5040010b442d8450105540710090f03a141d000300b000f0180200c0c48028041c4030340f03290960200350540d000e8a540c2207507a4690280d103155848050030b20008008050f920f420000c1044190300b8140203480c40b004c6548003003195003401d603d5498940d41d002d091503600400d0b0350b244c442e0201240e03103040010464042507984950355500345078002d004070b040b400e0105c0c1740c20000414803030050004005603604440078241c42c05000b4011620703d10390240c44c8401150044172102a041c002c00e0142c405c6600400060fa50f000e0f60030058404200302940c01e6072940200004e004c06104113a40900000c1c00f82031031511 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 687152859 1250 687151609 687151613
    0x30d021c090806040f0c060f051206010909140a0e160306020f04150804050c0411071101110d20011506030203060d200f0f24090a120b09060f01060c 65
    0x2144116500030990361107143c007400140700c0c45a03010a4514891710090742d0903540c812058a524444a5811010a405204400c03452a032034240780c1e482070051611103512034803651904115400400c102c5c0b486812107041100c00340d09481754501146060000340a0a030b100388062034150100d000052a83d9004144481e041c402d100a50f009000e081103542d140c021880390082203188101e5060382c2c0c61103103c903007043c24140f074400c0b1000d4000340743d0440d25011307407622074005000d00f8050041c10400500032942041c03100703004010000d20160398502800940200160b5915015107204210f0b034900624002e242c0440c96281b0700b141c41c0e034100941c4954503180018811400f0880c080d01c00c1140080c0d80c4641c03a00c1d1011200300e0079086908001d4101e400342482501420a031a56401c949018040040100044141d400c6100001d0016103401810070100d10900796982c00010109440300c0340c5820800c1c0311018079070000240e1300400003071424035403210b02d054042c03248405010140c43c041007 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 687154109 1250 687152859 687152867
    0xa39030b030c0d031101180f06051e090d020c0316050d08040b0304030905041a0307060e0f06070302060912182701240c08040b090d05011118030d021c 66
    0x1c1c0e01000b0f120210b0504542005030441c1070f0070f00a00742135440d200c001c0e5407000f04808485510b60f08503922541e10002c69450f08020a005400412284600a041c0349001921000700d1b115685040c09001c2244151901900d4601e503a1001880707500f040c0407170351184070340700d031400110382040301e2200380e03005981460707075003441a9001132825036000410042415000300140c0700301c2d074083d502045500d001880400100030040c0b101e0340d0681104408011182c41048039070700d0104010001260050704900042e01580108811005600046c01300440d048003488140d800021601070189001d40b060b500c0350915a640c1c80040c8502c981a400103007280c0d010300d000c0e42400400a80c0700e80d0307513100d0341903d140e80d9042c02003462442d11400700801891003901603079281640304601c81d04181c28086603916981141030507a4001016a13841c0c0040391007409000340220741d20cc20316035205074810302c1d50031640e200c01c405806607015500d07408e1240d03400540d440701011511a040a80460908115 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 687155359 1250 687154109 687154123
    0x6031902161202070509070c02030604060e01020c011406210d080403030b10020106031e0b0a0207030e060a21060501080615040504110c070e09330a39030b03 69
    0x68030030b60511800c520030300e400042c81c0c0c0980720116490042903403408400c5490350000c00000b901504002c000c980003548540120790050f04140c009420032200c090142c0c21a00b0313060714081c5240500e0b05001540c1000c4075402e203103148406e050b0715040e50300c500303956a5803403001f904c00400490300c00180501d071103a40840c0c0c1c000c40c0100900e00392006401c000340642034902007a80c1c510010a0960145412007100030041d592009205480350380e11030581e002074004c0303001038080c8040c80342c258150f69100c070020b083c0301c86261030f04202d0010801a2500c00c5210300c00c081000d501c0e223981401903a0b0400e240d59481f8804036039803000090306a101c0400d5000d0360340000d070810f0a0000c075030000301c0518061f02170b0990081c00c0710300c81e43d0340e0204101510001d50b0944565040101110301d44140d101c81901080e840c1c551040144004500125105d81c0c200d4440f84001c2e075030903c40c1c0c400407030b030300e01e011503640355840c0064068415501c8600024005044070181513a400351504c490720240541 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 687156609 1250 687155359 687155363
    0x20a1113091103010e06060330030f0106020d0f08060405130b09010617030405090105010513030813180b3d030504121806081512070609050603190216 66
    0x14412072101e450007003080303000b08403014400e5007450103010285000041040c42000c00070010b040c2000ca00310707120b2030440b5084d070a1008071943d6003c80c0c800b040c00300c0154010504146444043c0d03140600c000d040800c40c180000400030382c2c4814844040c5d10511040c0c000c0000c480005058550b8228441181580c00300100303110448000c008a4500642c011001c0724503540c6078480c80300d90300032200d0700e07407140d402050707880390088005210130351094010f007250210300010000e070242c694030344521607007100c284000280d2070b401d4144942ca0b004502c0300002c01040005004940010001402c61100b040707000c028040702d00c80c01d02c4502c01c1207104c4480800241214441800030b500003d014100489050f1042d0001c1f14089080c54811070f811740700134103924510340900b0b04202c004c5034090390182002c042002c0c41410824243d0f101e121981e101c058460050906034501503018105205903801107100350024803c004480048505074102004072900c0166201160609000e89140390140 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 687157859 1250 687156609 687156611
    0x40c1a160308070e09040f082101030b070e03030c070626040f03090e0705030a020a05040e0711100204081207050304081203010806010b04081e0c1018090507020a1113 73
    0x2041410781102c03209010b540035a0303804c0b444030b919205000e407429042d28003e0030b0108401f203c00100d441200504403905941d40c403000c0540400f006140601e02c20381058030340b54807600a0180b007030f4000d0a00c03000210141c026508040013034003116114100751003540148a0f81045205541c04030341d10561840300c240140c00100d0809047c0604281c1c1c0342e50048001c54018000410622500c600c81032140400c2da540a14503520008254060f41001c034514040c03140621010440b2200b50503440e11070211076032890394070103405400901e0015036a0000604510400050042c030360301140c41e090a140c1c07008000c0e504c100505d022840e601c88c95112030f1090042c4a0860410700000005604a6103070f1401c441050740c841220b0305483c030031446100d03d50f520a40c1c8200f180da1548014080b10002c4c031040d55800c900e00008500201c0c06c12043c100010044020402500040c1a07120090314410208004a10340502c0c080e60300d0440410140402e6107406010000347e4500140160300426008 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 687159109 1250 687157859 687157897
    0xd020406051207020309100f0309120309021008152716110d1d040f02030c220e040b09010b04021b1b01050405061b010c0f17040c1a 58
    0x6001011a00403070704210207a60a800822803e5200005070340580e4002000703500440d81982c400d851070282480b54409142d11251250041000c4044840c1a03003200e1b200030030000c0851040041c502c44200342c080500c00b03640c0c280b10a02d461085080702c1040f0640319170300400e000055004c4130041072401041401c0303035001000048101034603a000919040c1e2a8081109a04c90101c1d40f90b00001c4010740003c0c0041911658124001001da0302003d4082c0c0009200c2810a010000303a170310880b001c1c03015000c0010f0300c8810040c07074982481f040c400880b61203085e5003480800c0e2100c000103040502000d4525002c01c0040d4030a6020640340400200110741d038480c0e42c24161510603100c40d2541060081c0c0b844040d103040d03615140d00700c04205a43d62031a00e41000d00700891900000d032031030741e0300074150701120100030244035003200b400b030390b80b0392200d0250301c100000c106480c03541e0b14001104408040c0310008076518007040680d03249110380c48140d142e18070040c42e00c1c0100c089003900607000f80 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 687160359 1250 687159109 687159119
    0xf011a0a0e1201090b33060c060a05011a0c06010902030403020316050a03110c1003020c010605040501180c0f1e0c120c05060901181e081809060409120807050d0204 72
    0x15006030b103514070400c40000146d40d1307550402c80c0301e00406003507000104100c110b255040e0381084600141030004003481d0902204610a900d070603c211050584c680d0f83d90014441540425a00080ea0542e200d07000d2038400c1c1e0200040d02e4040601c500700c00c10381c0100104e41014002d0040e502a4400e0002101098145007081c2d9508c520320202134020840000d04030040c082d010540c407030314180c00b9202044545a2aa04070001d6000c000f001240d0755035404085165034483c080c17103009103c88061000840a801f0751034003120b000d80401d00c2030140e100510540c21b5040300890724071012400360701d9411010b102c029160702d54210401002c4501007980c06465540207503e2242440c05601203a8151340c802d00007070300b2100c0080c0030307504000e00014800009140c284111800142300d03001001c00505079944e00001d034010981024820f44c2d190000030403420524061b40c1c1c01102205c040c0058071440d103c02071a075030070381905410000104c00141d0b201d401201103d4070075140200c110740d5142c1d60 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 687161609 1250 687160359 687160361
    0x501020301090b0603090c01210f09021005030106020a030806150703120b030d09270c09080606102c03031804060b0702030601060503070e0a0e0f0f011a0a0e1201 71
    0x2405000c090303d15001c201c20782c90070007600f40c9208000b108024039400c1c400c0401500c0c00000386400c1902801c2054072088054000d00424a0b03103079141c50082404103544c8104400b01ca8012448010481c046c40108109980058400314040e0941419449602c0d04404500e40d900e1340c00200617000d4000030048209907004400100302c1d17100c0301d820006030f500d0404064030340d100a940f400002e9404c01d000e0000740c0003100000a486024010340310390315428154002682d4518081601140c0048410400e03c001030201c20790104040b18081031402c01050b010b800b003040750464594054024000c1d0701d1242c10204402c10500e07008007100d0311580c0c6408002640d82082403414003c40c1480340c00180c0030001800c1c0d404040c0d0007030280c90560300f041400ca5460b01300400b18010480c0c0c00321003015a0322154039000207044d001e03043e00c080303140001d01d9a440b0070018042c1980d051000004101090100318101c03c0030700d8500700030b0f59608000d5001c88840b02446441540320300c40c00d051520b1382d001 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 687162859 1250 687161609 687161611
    0xc150408031603170103110103020a03090c06020f0708010b011407081303260f1b0a0f0326130b070201020d051501080f07021b120a0c080f07050a0909030c02060705010203 75
    0x101e562203200c0000e41120000c500c0c602880010034500c003981f10904158003903006810040b845140c009051002900e461442450300e81c442c0d40982c01c82000c110f41e01006005040142c940c4100074000c4018010000f0242d0031803c41d0100c8041c03002c0340d0381082018400c1182c0204404280c4514425101d00304003501500400785641c660707900c59998228400c21400380e8105900040006040c03840c2945680346600c0744825000d058050b80181d81d000500d80c2040100b80e90182d40c900c0080c21400100c42c0e5405842018110212030740c800300000480c50108502c541a480f403000603007500e500308141d01a000e0124009049801d041c208024044007113041408204240d031040c40b0340d00d48000501a00c00c05852020040e0800341d03010f0f0503500113002811441c403000c4d00910000003031044250411004100846011000e12810000200208116190b08220901420009180400180d4030a2041c801d64203c00d0700e43d03035458181401105240d0449401502d95541e030301c82890054000e40c0 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 687164109 1250 687162859 687162863
    0xc060905061501020d020a0c120c12060b04050a0b060313110a03060f11030f0a090c050603130302060c09011d030c19091a0a030f050f010c091d0403020c1504080316 72
    0x455880400c179130900c0000c807030101582080c00d000081e0704210f400000041400803d550f484007100c0c000a6180c035202d2500c4849008080c006155192503007000281c642c054649010701d42050307215013256903180c0840e500100c001d5501c54002c4140d1514002c8810b056a5040d40005246800414084150002804603103140410881c0c16030235411441c4902082d14409120004180040c00706109503001e149078600860b0318246465072240050f50329842165800d41944180c038058042640410900780c0215112403103d050030b92600000703003a0703d840703030207103520b402e01403040340041e201070100790405540a80358040c1c5c03078506c0324000140516448ac0c80f040301d161042040c0304040900c0e04001581c0000e140195040c0713507468410141d0f5900d901502c881c000c0500314041c50000348500004070703000d52601e500e9039203891444a90070254142c4d130003e04440310700300000280e0121b04035803103520850b0010403c00070150413502600480d080a8802e210015918401007502d40b8480100b41c = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 687165359 1250 687164109 687164113
    0xe0c03070902190c050319050c1618020711150301080f0a050a082110050301060b0c031e0d06140a090e0703061a0603010f0e070f0c030c06090506150102 67
    0xa0741c6000e030104a204115059a00010404404080710300c68071010002c58022800c803800c12000301a0070084009405c0c0b2140415030015858100000038440b50003075640b40741d00d5130103807464010000c0c2040f01200c0301c01070131a80010207604011100c083c0a035406c8000e0906041e03041303c030074a027005500a000340300c00c6200745500302040100c0001c3c4d940050b68000e000d04a236280c283c0d26a0002d40141c051421505112600901c1680f10b581d512441031404103201d0201601e0318040c5821101d45401070412080e00b00552500d841002040354152401c440150014040d01c4014060038000e024407a000c45041620000f100c00303400a1800305440c0841d061240f85a4034654501201d40b03003802403102d90400c50381080440d034507a20000c200b81040340700181c01c500c40e0000030320715802600411910040704c0c0b000d119244030100d51ba0344c030003420b09000b101c030300107410080c0c46414921001030070803400421a0341041281d07080300712015885001c90b901ea08100d00100e200c1608041d2490042c = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 687166609 1250 687165359 687165373
    0x150522110418050702010b09071b0303020d020705070609050d0803011401350f01060f031109330903060a0207020f0603071e140412050309060412030908160b0318010e0c03 75
    0x500e440308982d03029120a44030084003407451018841c400d2b0b0301d0b09003603050603824440d01030520014001800e00500c150040d1009609110000d002d140172a0005c600030341211020307a0009075018116410f40c0c203140310105252046400494160742c00d41410001c9203c0f56003a10403948698070030002510100074440b01030743c0c50341301d01e40c140c0c9000d01c580300000d0319101c000c520044c000d82c48081428403100800e46406100d03c041030111482c00c00c40e201011155000912031030b111100301c0b240780070080c505445c0c0f2515078002551041c010b022000826800945141107590700b1031202003805004c0d0001c1e803245021400900050440060f405a00c41030b04060808a44a04007500480440c0e40e42141044c3c100080c031081071411240c1100d851000b04256029690b8100c0500000c0061003415001c00b64140380040c481003459210041c0c540c4003c0500102e0590441007200799044000401d403a5510301440304000c0c0b11801d91b244840d4641001d40907100030119100300c0c803503425800c81d100303 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 687167859 1250 687166609 687166631
    0xe0103050606040c0e040506030a050718050907030309030308100306050114180c1e0f03150a06031413032309010e06090f060a0c1515052211041805070201 68
    0x165500460b00304c00041c00d400300100c6501d072641c010342d00800042c0c2200d91001440c0d48140c903003822908507155a040501d0443c11440d15401001d40c498440409030480602d543e0303015059202d0b0b8000181071007903000000d141e0301156558a0010340c0c200405100e00e59403884001c5407007101110f16406455504892521086405081402030010b40507040c40c1c01000c03000c001d0290a44940021a803004011841d01e100c0041c1c0030714029580f00300302c4200c0800c804d08001c0556541d5000310f0078182846610400c244004030740c80d41c40702802c1c0d07240704400c1e41880c1c22110010b42c0768034013070307100024a030884030842c244d0050580060700780c0310103446481440c1003195a001d0800c1c96603000280141c08803050400070b000d4495000507080409941d0303030341c0d0794040d9034621416008501d195150000030301c5940c600d072202c009140a90348900c1d00e0b2103c940c0d042c0c8060300011500202c94686500c0403542440d94129001484290103076251000b424400001401065130003100541c207040070a15 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 687169109 1250 687167859 687167861
    0xf0f210102042426130f0b0901050f040308070806120313090609020408100c0c0b04031d1806190b07301e05040e04080306092202040f0e070e010305060604 68
    0x820014442c240200e02c1111341c075110007940009204a01070303656102c030f610006000c0c440400c01c1a1045400b54071510303001c03003100d007102d100070045c110107210030041c000801c0d04415280d4110285280c0250f9681c1ca550102c0c0d51700c040950304400a00c000100ca15580d02250f6800c0e041e42c4400400b0310035143e41e2180f200c242d010b540683c115640200800c03e110b083c1c142d2040c11003245600b0805204001501d40c1078020034115016004103c20b1004040481040d0b0900c0009040c100e8000024006241174106070010090100e03005a951014183e03a040d46664180c000f40410103426545180c07034034103410340308280740800403035030391307002e010b4076140041e0b41509800c803d1396945ca101c1458416031041120001c10000c0107011f01004080707100c00011481d141b141c1d000b61029592800c15906011202c0d4008042620038010600343e441c009208402149503550102c0c3d01007180665104503000070210150041150301c2440000201c0c21102c1303071400e040b640183c0a44585940d40000e03c0 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 687170359 1250 687169109 687169127
    0x30e0f07050f03160f09050f0c0711030f0d2f0a080d060306050a090b06090f01170718060503120a0c061d060c030907050f0f2101020424 60
    0x1a0341040c9414482800c00ca007181d07020000040c12030340c80800601c2c0718024203d00741c1000001d0b0319150428408200f09001d2950001e00089201c1c00d0742c83c01e034031504124007981800038032080f924100d000701d03a5010050319401c0c158480540302684c8501c0d001170616a21051040400083c0070b403000051541044c4801d10050000090020000942da81c01400d90000030040500b41c1d4800300400424914403c041c03241c410541c001400305060300f00300b400040700801440c450100401040441c154446555046401e40e0f0b10342d00c5c1400203501c40506003c1c0c40e810284406084002101800f213003a00b20307034200c9500340c0640b5040c03290705042e01c80a1103418210300104040c500b01400140455000d400d050034203100400d09048869102401c02c5c000303489801c22a01c0120a0190482003400034000030007046403401085480715010960086481101a10034103503140820039101440a0030b003401e0802000855540352210440038483c51070b02c0310200c41c05001e00295160a00942c2c400c = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 687171609 1250 687170359 687170383
    0x1020d09030c1a0408151e04020d080f09270c0a050301140103090206030a0b09060402280e1008090d080c0313031e05040302090a061a090d020916030e 66
    0x450034240c1401040d0582c40280381c108071180e54200000075090005000800303500030200340006c2c0a041400c006512107108514401c02c2c03040b00c5083c8401641c8189d0b6100d226170b4802185a00d88500c5211441103004100300150800b01081403509515407207000c1000e0b420400f11840016198000300315500d001c0e104101000c90070400060007044e1211141c10b2042805240100d85104140e02181b46600305603030303007a030594850286c440d0074509190b00d9030340f040302584d085040c800817241840c0890700040003c510035401030487c0090078444c0f4103000c1c0100002d000c205c40d0000364407004004200032030300d0300c4842c01862900d1880303d105001581c0513502c0c419100d401c648550840b07030000d00303126808405010344000161440f2000380500d48c011001503d44549580c41c5005202e900c51000f07048132a040d180000a100149803400340ca0f484048041c1010b440b801804081929160030302c0700170390b0050740007080240e03031600e542c0074840c051090394044c046a8508003483e5501c05030000c017 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 687172859 1250 687171609 687171623
    0x603020304050d080c0405100806010305090f12090d0c030506040b090a03091512060602010c0e040903020a350d0e0d231c0e0f0c09061203120a020901020d0903 70
    0x312803d94800c1300030f10b421000700d0001c10316080d6520002080010100f045102240c0808100056580c2510509503c518050090003034a4004444207886800303084903003004ca040440d540003151100b000c128481e941c0560060b101d1520b9003040c654800c42200c040343c03d8062200002d6900308003007042802c4940c10341791100f01c10304000250754105440d071101c10030080050308890001d8003034090240200303256000050b5100b50194014810300040350001c2c0140d080400a9000990002d00403001c141c10005c10719840c01040c0041a1101103142d0310850748941042c0c3e02c01886064004041050f6104410040c2110001280d030700e511180303400c603000c1240c51048840381d0703c48007100c4502b4000c000160389010164480d8612158141c600010b00baa07660403110010720301008020900c1924034014005841c0310800134004450051103d8001d000180c0d1400c03020714108165040304000312000405441d03d07410311002500072418442c0184602100c1d801c005003d420508156a00300c48 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 687174109 1250 687172859 687172873
    0xc06051b0a080405240910031e06050f090c030a0c0203071a070806031902130b0904050309040c021504031209020904060b0916141b07080706030f05280b0604090e07060302030405 78
    0x20010801c0c00e01c00d80400b4135449d2200501c402800c20301680b210203030b1400006607141400203001e21140036150450240ca04801400804c402003c15258814644400441c4880203d10224114001c100c40203148801a82040091540045815200300301990300e4644a070b655508041e40c612a05544c410492032036179100016040c080d01c3d82d16540920003000c24050401c5020903540300e0102d900382c0b40d41d00080b6501c0c03014640fa000d110400d55092005010031007a2402e072149140f00a0001803c0c080003e10640150020f43c004040c2560000c15010380c1d490282480c0b0060140000802c2c8180c9410300028000f40d00c4844c1000d070740c4d91a80d50005056008000741e40039074851000c0c08101c0d0107a802a081e00b00c070801c1200c1c043c0c490800601001e6140400140c16101c05c8110340c18000c1c240b6040101d071109090183d0194100040700c40b0040d09440c0004000300703154070060350085000a400715400460f070300100c254048420841b140941d40d03101c11000ca00003510300a0040e04001 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 687175359 1250 687174109 687174127
    0x100309030c060b1f0c0b10240210020f0d0f0e03120c04030231050f1f08030406030c090906060507330e0c09040c06051b0a08040524 58
    0x60f0200141400242c880001c800d46010703c441c214070b448100b2400116210310b40420000300001880c0c1050b092240c0c500e500d8100003040c007914159240414400300508a80180f56108000b01c40c43c0080d040d4046603120030f001c1c90358460340e02c0300740d0103417070b460400c0956616003c003440307030302c80380046800a141450408542a0000100504500004041840088090b13529020444440c0400402d08154513020a118030f1101800e4561944003601d414100010b00c2c84118030103034000214108103041000440b030249500101e5004000244004100031034015010381c030500d12085c01c0e4440c01031a0f0303070b2425031034140c0d80240140c00000b0307401d110100000c0c110350408100048140441201e05a04005400e20402080445803c0c41d8039500060500c0406000380712410f002612200c1a900d800c0d1103000d18140c96114940400c040000ca10800440c4140300c1d052505d140c000b070341d502e0811802c1030006508103015140c4200a02003401101744003086085003600e00c04404c80f81464441 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 687176609 1250 687175359 687175361
    0x30f06210d0315030204020409090218040201051803030c0a03050c0f0f100c0c33020a0e120109080c0a0501060501050c0d030b010918050a0b0402092b0215030105100309030c06 77
    0x1500c80c060f400e04880b00440161b44600240000e40b10107100045e03000d1143c010030104400d071800c1c03041c02021100500c00943d0780003003125104100141c82c00d01d030048100129243d4030070081810b00034010f88020700e04140d0f000f8000c0c50258448001c13641000640175109884042198821642d9444021420030f10845034011280c20340481c100b030014108641c440c1c4c1082500c0d141c894010150403100d41c0d080349200200681c0c0e0740c010040c118101140190b001d03088151002c0300610030808a800892050707000d402c84185030fa44208810740303a80b0380c40c031015a54918603100725420350801030007182d554842d505541f4000c1002c3c008114400101800360010140050160304001445c640403c0c0199aa45400035844501000140526014070b519007192880185a4071841c0104240e051503038860500c40c0c201d0303000700740303116a90f00d50346000c11042d60b0f4040c000b034100b408dc0d114025000708410207981240c5081c2c7e00800c01c800e200d0000c80407503414050081c00303c1e500000e00b20110b002 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 687177859 1250 687176609 687176621
    0xc1e0916050f0c1014090607120b040216020414060a03081305101814011d031005090a0606061b142a0f060405180912030f06210d03 58
    0x340e042562400d038040091103540d034402400c0440c640d021001000b01441d0f0b9208a1540c050040c54141003401c108004e551a81e2001d0280c0c81000047c2d0506503411181b5440800c0f0804014030444d942c043c4084c81500d0211180c00c240d1003689004007880851840301c428a10485006241c10000f40c150341e20492950000b00e100e030750071901110089026102d5842d02e0300c0382403007600c0759000c080300d0181d040030442454000782e00425001c44140c80a9030405680d103010301031390320030740c004082450100e4a403c9490030122030140c1030400340b06c032000d400b01d1011178541c0a0303982480b00f2612044152400790340c0400d080307940b1307544044000114dc00c2c2c00e01c588200451405850184a130406c0800004002c607440f050b8800d0707459202d40ca64a4000e90301d00301810180c40c0b442c146440e11000901039005a0b0107420300c40050780001e40c0354070007800303290b8140c40c418815948a0034004200056224200c80383d034000d1810788a9655950348002014103c032480500801e1542d25070305044010307050b = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 687179109 1250 687177859 687177901
    0x5100c1704050a0e0915130b07020111030612030705060132130902043812031e16050607080106020307120f0c0204141f14060a0509040504050c1e09 65
    0x2502007000c641400b0110003600402e070f1f214009040ea612401c155801c031070058100015680352000b0789560306e0300032040e40c0c2d0120088841e071141061040682d410745c440c81e10b00429030b004000000c140c07910341c9140591200d080500400746e00c42c8000c846002c01003c0085554048991410810f000215800010140744090300225008c2800250b084800072509990103841410034040b07030040c0d8146105d000034a80480380e40351420406d03140903441e81300307914013003060001616040a09801507800c81d44901c1d40385a08035032508060624a44508050b07600c2c04c0025070000000a1551000042c1c407079050300401114001c465110b0306441c00e56078146054140001c428602c0c001d80e807113104200d0040d00c100003002d03842c030b881c04501c4111005500243d6440844200500800c24540315260181c40f058070025902e40d00700b901603487c0c0c00b4084180d54001e040008200800102258615103001c09407426a075000e082c40c5601202a000c406242d0028030703807030025081c100b007a2180301c2041 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 687180359 1250 687179109 687179113
    0x140a120813050303031501020f01110d05040c12080406080112031d01030e01020c010b03060606120712151715190504060902060c1c090b0301060804050705100c1704050a0e09 76
    0x7641e0741e800700e400c68000325511161030b441d000400b18156010f02006d01c0038084400200100250460060340e1030007958101030f0341990b03810010b020403400e501503030007400c0e0a82e1007440c219114900300072075500ca0b0054500288481c6c00000d24480d50010885019500d40c40b0000706004039446e42c401406103d090360b04051b00c8418007842100c080c4010601c2d440c900001241c0c48500f5000d00d464280040c2140303004a2042080d160403140d1100590b800c03100c6440c00a011060301e01600014000420318500741600e10000011680403100302c4459643c041415a8026004d1409d80b00c0c02800031039044070404200c4400d04d424200d10790040c0d6005101c2c410010318106035801041e1030f078003d8140c0b06186c0e402500f6105030110064482011545030313203020b01d611400c208540c210b42c001882140c05016000000c0340800405010381009000e016060310126003001000a00c5801258820750f2000111103407240e60110340070450302030310005080f00c43c84600e48030009880c0c040042a0701501c3c = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 687181609 1250 687180359 687180397
    0x1330509040b0d1b03140c0f060c0c030d08040510090510091b03080a120209031b01020f0f06010f060e0f011b05190b0906040218060307090213140a1208 67
    0xd00000c13202c0c2002c42e8405168040340e421864440d140360f0070341400302c3d49544410050b04803941c0740c00300318030749210039501d01d40c8540f00054030b5881d1283c4a400f0640c10b015212440340009e42c00a504c51040c0e00073b10485504401600702035045030450751014007150003d44403a0120104c0341c20000045105100140400c12015000c2e88403140c0740c0c20072100c03c8000100c105001e80d2000d003250110300034a10841c60300840c0c200081c0d8407650840b0720411180d1881700106168020712200c0f04001d008002d5428582d02940300d580c581209000d004c405650740a00400c4840c4038120348500c60074003520030210102c0700320040d00e0030400403400c0e03035800c5074085410000a4080c81885054003140a48590040e19842c210140342c1e0000c000c1d2010381d018004110160f40c802280108800c4508000450358480c10040381c10100b081d003050306e0342800000c80c85511000003040001b19220058140442c0e01c1100401105403014814500001d0030700c1c6680c400f203110302004180c0c0a0111050001c4 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 687182859 1250 687181609 687181613
    0x11727061501020d050f0d090c030605072c150f07080a05030403020c010c08070201140f0408060f070503190f0912020d11010501081b030705040501330509040b0d 71
    0x1400c001114003045074116007110032460758040000c0200309200f810320904140600c180104540601c0076040560703605c80200700180402c0d003042c4c0016540002c024001e51903d503c0c05000449420001203007030300c26140481c9081401344544510303c0b00145401e03902507a0b11a1880d040c1c1040d0035010240c4000c1145500040c010307070040c1240404c1b41c0302d164891409e810041e042ca40003441a0313040c03141c1003802c000010b041c00121044994242030501d010074612800400c980030b04510046101c900085c0410940c0c0001021807041d0010310719404541e4512a08651a010660300c0000c800ba1480f0140140d00298000101c8501079010000d04000d0f95152920000400074074040507803c0100c0c01007010740d0250004641608401c028403003540b524100660303441d880405800c1c49500502180e81c542d405010020051900600601655031544001180c1e18a80398103400304e54400b0070081d9005408240d42c143c54880e0791185400c08800d603081c8809005c1e190145640302014903c1600 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 687184109 1250 687182859 687182863
    0x3030a171005180a060b04091401080a08090915040603030512070e01230d0507020105060118080703080c100c030f1103010f060e120304030602070c05011727 69
    0xa05911551460300c9926101805020800e0240080e00c8460500c1c0003400107880740c208043c140440c0f544085203554031080690020100c0c0e400044101000040000c2e05e803071346421100c5103101a07401c6640503680c2d48061540c65020341002090f07041e0074070044282d4030700450010381c848006000d10040040a0000404072081500110080346002c00c4000940744a903c107141e00210b50309241d0b1680c4c80310300c0003900c0c030300540044440e50681c03952041a150801400e40d103940381107010038859401c1502e000b03400b0b000100c1d03110f07000600e429407181e0041100c0c19a0b05c03c94654a024082d0a801c584132400300740d0110b11110428800d00280c440542c0d1144140300c035006540c2c1e030000e000070f42c004044058400002510021000520050101d51f200300c0504003125000c3c104000701244c80c002040900100d2844402c103030002090001c203000e03154004144007485410782c421456120700042d55105000d050300791030410a20b00003040099011540d810782d042c413000c0009400403d2404c24 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 687185359 1250 687184109 687184117
    0x8270708010e03251a061216031101050f1c090f0c0602071211062520040501030305270307170106080729040504140414030f0909060a050303 62
    0x2c1040d40005192800c0d54411080400b510205600010315400c05441e000c0543c91041c5a0f1070350b00005101181d0b01e0f69032124107105808410301664202071240140318640d640d80d11050300e056502080c0340b100d1358031170700071103204048441205042c14598601c1c0604500301000e031044203030303a40700c041c2c0206081500c840406442100d1300b03000310b802c1c000d0090529090340d001016410b448c038810700c00035209003a1851142010741d141c40d1100a1403441c03102038444503c010528941c92001c1405100c44aa2030300c0703000c00b0803528210640c030004140002c98000344006000070740c040c80120104c1800100402c844130024841c0004d07409054002400c1c800c080e803010864544005511034100400e0050724000c12440d4050a8082d02d0035001a400c40048504000c0d600d52000850005817000c200361409010081d00c00c000e00c81c60503004081250040c2d6054800200d084141800b1007000022500d144030704040407400e240c442c3c4180100280080c04d082e500c4404060089103e44041000d0 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 687186609 1250 687185359 687185381
    0x9090f080d1e051608061c0b1b070f0b06040f02030903070b1003120f140a08041b030203030405040902040b06030c130609030503090607080c01060807080106060827070801 75
    0x98190602c900380b204a0581030950a00c4074209400c001500c19401c3c0501141032850400c8420b41d030b0303000b00140400d0141064040400800c610078418040c980503501c0c86411418041c182001101d00c0c0078001d400b90801c0105004ca005281000080c0c3e0f11043c2900518081d02c085060030402d0381c110b013660011610f81c0b81da0342c408580c50303043c44000c161b07042e088048071405901d8103080d46c40d00c0f14074000ea900301000f070101d4000080e000134170401c201841c011640e116962101c0714500d00402241040d03e051f103003d141d003201e0800900040c07010a040302da00070010762400d4030300070030301c8081c188003070050f03a0156548400a4098988000951040701c079034002a6840c9944980749011a0207a0044410080810014400290000100c882c4800110f900d9500e50301c1034a080300141c418000c0c00380c49542050030000307110070002103030000e030b45404000703000c0140c560404855402c41115811908420070381000d8200c8614984002100340d44000c1e14021070319051a6800d43e66110f9072 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 687187859 1250 687186609 687186611
    0x61f020f0a1209060e1c0302160602010b010801050924060403021c031b08030f0c0904090c0305061f1505090a06050d1416120e0703050105010905060604050a09090f080d 74
    0x1000b0a991000141024011600785124000c14400c0400c10702c41d04a208140c1c204540244142803500070000070904400e5106408e2509480e810002e0180c2401200140840c0b45580046101e2401c200b40c2031042c3c40720780c56201c50201c200e06101102e807584100c1608140b040001001507259916a09030300049240c0a42d160003051500170a03c0c490300c0c0e02d01080f4216618860009000030341282d800140c103603a40981c80d180c4000c0c0d85a2031180c084607544c801d14180f101c40c00c00c51180d8030907003241d00075003d031030701d0383d5848044840c410705e440840420314074800814080060030030034007101140145850b5003080503080100d8031040c010382240e000b0031000700c1c0c5c8420814440c016545902500c802580203401d1208150806094a0b11160144050f07015031600c050007a501184c0300d013145c0d03000c5482c155a01c1c01e0142c001c041c20b000300700c5524104000940b4074180101220100c800180280c0c00b6280b8194514000b40008001100e01c0560312240300003194225016104002102c04 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 687189109 1250 687187859 687187883
    0x4090c050408120f04031511040305010b0102060702010213181410090e010b010f050315030304061206090504020f1002120310140405060a1a0d050c0304140303061f020f0a 75
    0x1880340c82c040203400145000303c400c0000d498503100303000c00e803002c60368000091401d01280fa2604405010804213422202402040000a00c0015008204852030a80980c3c0917034590303032022402d034404c4072545a12001d441c84204400391107090000c540184544e400590348160400080e00c160701600c40600c141e00c1d0070424000075030030f807241d40c1c001410400200045840c06002a141c240e840c1900014400e010000804500740c4040071b80e500c03500181665a115154280944405071041411020070305d800ea0201d4484c425120f440d0049400601c412140b0000b442000900814005000c045014849452a8013058200a180a048001c80c02c02c156420601a6001400da4440341846241070006000454681c81102020307220f4840003800c00300070f0490f4403021403140310080c2410500d49410030040001980146000703030f2080800c4446031a21840385a03485c0410384002d684602007001e40f071088844521034990182c0540181d41e521142c040311241481094281502c64610711a = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 687190359 1250 687189109 687189119
    0x81602030709050f130f2a1a090f012d080915010603150506040b0c010b0d111309080304140d1d090603010b0d150612031205060604090c0504 62
    0x2200780070280046100410680c50080303a24100208050100348521001d02400703401e02c11540503400910340c0101048080c036048014054404c000881d205006281d81070700414150011840041c1c901d0300c07041214108174044040021300540c0401780b0341402141920200704604000044241c44001688055030440300000a40790b4180205607409907001200341400ac41e5288080c80c0c15600240360014819a07407080c80f03640107a09403c06a484071000c0f500007802050f80740241801c116000003408120724010600000302d00814000740040340c0058150007a050144c9402c4020843d5000441d110300f1544522200394001e0b24281d03070000b030031400d596401100300303d8080860321620301441105030060b0044480c03400c49a500d442203080c54041102545e094204401801d4000c008641146c502d00c6c00c0da403040746207040e00c1400f0741064070000f0184814203148103641d80589504042d240204c100e080100401403040da448001030001188601040c0300f20008600140c481700d540b14205 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 687191609 1250 687190359 687190363
    0xa050c1e010b100c0b091f020316140708030c07080a05090118060f031d07061d040902010e21031801080c09061b010b10030203060414060f061608160203 67
    0x203001d40c0f80a003a1801082c080c059001980f0b0800300e41000702c0c014582c0f41ca0180703609056808910070441400e01e0205540003841c0d50040d400f07403c48180040c4078102000041ea900d482d03038541c000007c2c030103001c101c2c08030303511500440d0700910500d5194640501640e500105421007210480040c07400718040519503081141d5080c050300707943c2c40c160007500d412401003011440c040160200341d00c41d1518450500701c0c005201a10503840c2c1610a00d41c3c81d0240100074580d02c2c0301409012000f045580071f6424580b24100d141e0b50181e44891b405036840c4107001b00060301c0c0d8180c070096201c0c0c080442d05440148003400c80076450b05c1442e8070002c0342c500010016070014180030f80301101044441955940c01e4201e603810140d2035442522008072241180c01043d030600f041e80c01840a40005107280c0e49540158880d20080720304106881840c1070110302c24004803400c0380c0148820064001524040000d8038100044010406010032266540b09040d001408039909000104400500b18035003 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 687192859 1250 687191609 687191621
    0xb0d050a090209061c0b01061106010f1a090d060f0e0708060105060d2d0f1b020c0415031b05100c080a030c11011a12031c020a050c1e01 60
    0x1140d03030501c008546500028210000504450b1041c8909a40c0c0c240c22071944078841045a009001100340e5a03488002500702201c024081c03c49005a0001040d40308282403010181c03245021301242302201d008100ca025400592101e5000b24406508800110540910311480381c0145000c210000e6590503a40f40501e41d1300f10540a8002c1001400a9168030055030301c010200300011613950540c00d04510140008900e078a044000080c468400e00c80503084449074070b00240d001c1000c580d85c0c6000031000c01c0c94a002d0385c01a0816801120a13107826041950300c0d006d00c6c15002502560b0b80d4505a01c0420400a000741c0b00c81810200300c18982030504101c100c141d820070000418041d65200c0c4144030b560000001c1c140e070352200240d8640b05402a4195000081c000c01000d9040a9824101056104440e01c81d244c0c4d402061070855011059412090309280c524100e4a04400c405001e5007081c0d03001c5d000c018003070150100c02c9004101503402c40c60303000524003030803510307601c26401c1d0307a2 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 687194109 1250 687192859 687192871
    0x6090605010f0e060f0903060103060507260a091106070302010603050c030601030b130f12022a030a03050309121308010b0a120b090114010602070612090302190305130b0d05 76
    0x20350100301c0c01ca4203411848038049480100c1d401342c0c3d07803045045104c1c110700401160b95094807524002000308100c0e40c0c4500c2c002c80f80d07910b030018074141424042003104150030043c070100c58080b010828041107a0031000480380309e00106a140114800482c0c0c80ea00040401d50050b91945010410303c2002e202e4400c22403010b0303014241560664582002d00600a050546002c1d43d602c0a0000d000c5070503a031180c840d80c014010302088801d20b43c02583c40c03000d40c0d60822000740440c0c000f5070442255250300e0703403241c010300503200d07690b05500c00b940d0302d0700700070f2054506000310400032103040303180c10040c661041058000400d041c1081c036680d00311007240d0741c4540124002030b01440b41105804801410b42e07070100000c815a540c01c1c00740780c00340088c081d88420103022000003080107a0080b0789a41a2882c51b59034155a0502455540554a0702e078009000b60300010f00785101150507440103c499400380c14180d241140d198500001c0c4001e56014105000c80891003141c4c58a25003d190741100b = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 687195359 1250 687194109 687194117
    0x50c250e0901060609031b090c1709010905281209060f08060a0e0703020702120c120105060a0620070603141e070813020d0b0a1d0a32010609060501 65
    0x5810030b00c0240c207210305804050310b0300e607104447d000d07600d072900c00e408003070301070f085060044040c007a801502c00390f41c0c1c0048424040070303100003c00001d8148500b0351420f1b0403200400c000e101c050101061b1a070030004403013400d20362211402c04210071000300c4912110fa0b0740e5601c10340745809401014501d518484100304404401803090b03540d03442072000240c807082c9020f003a5940b944a400d400074411710900035040f114194407103419080100f807600320030744280d0b5038921218515030303520b088403c1101c1071365011103040c0341071000d030784282841aa9a680e03a030b003c0d00c02104a00080f1301c0c0031055481080006d8a40400100c0c0090500e820358202501000301480d15403802c4650103101c000800b200c0410003034000240700040c1c1d03c00400031076034000d05403a4100b410740c1800c3c101203000f16450594241002d005114240500c50350306641030081c000f801c00404250b0701e0301c030000d906000d42c3e0102d00c2501c04142c80074001948040b200080903000254661401c4040c0040d02e109902a0b4140 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 687196609 1250 687195359 687195371
    0xa15090c0308180123130513060906050a050108151c152703081512010f1103250c080408010b031e030406030905030c010501291603050c250e0901 64
    0x4507419408501400640e11410760301c40c80850b034100c6c0d044a065210350342c441d400b941d20b45024030304d070351115058030303180318007130025075121410b1080d1686503100b02c40c001401c01e0300248800300945261034800030000c040604890040704800700b0524121020b03074001c03460341c0c051007600703d05109040c00b00c1c81407505031003000340503071600b90700b07181e800301c0a0140000040024510420131100b04402c0e80c0c000d00003d2000101c0304c01d2030081200c482a40200c0e45014105441003401d0b0f400c0c1c92264100364071300e0b0196501307040c901d01002908607202050100b01c1c002d40300003880400160001d0103040340005010300c2c00790105850048007400040c4051610701207289400301c048122426103001d03040108a49100d0318249107980304209402045501c4d2400105422031000000e4805010b42c490440400514610500c1c941c481d4103a4481c04210070411180004d004401402c0d96080860595289121542c1401065002e4008011484407168400d00441c110300520982040204000b0049 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 687197859 1250 687196609 687196637
    0xa0e0d060501030c15081e06010e151201050316290d05060102010b090621191b230103110d09051e01060f03020603040f0812070e030f0a15090c03081801 67
    0x107d45840c0314030041501c500d20000722683d00804444507039000c00b4020001d071390080fa681180750b402c02403510f10800311050000a0f50300c1c0002d5040c181500d84003058900034034141c1514001103030641604290041c2d0030b031106400301c54402510070501907400c003086914001d0002801c583d658141c40d03218002303840c2400010b440e150860418995049442240320030307842074040c81d00688034513828502450340c0741d40702040005c6001c0c183e060038159032000081d031100c030302c07940d02040c8a40c2c0900451401036500310340c0d84690890703000000500116807400100c18034120035500c1450382940c2c1c03039000d50441c41d07007014001c1c021380350045110020000795042140b8640403643c2c61002910610011001c1014010400d85404007940c1c05403503240e41e102076111030000520b04803040340218a000300000103c0c100032420410540908000c0e114a0105039201700f4031440301c1c1d000315656a03541201e200000d1a901c1e90f0f40166005a08881d00c4d0200501955400c4410300011410442d40c01c1c24119 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 687199109 1250 687197859 687197881
    0x7020a06022a0409080309030706050601020703080a0315050310090b071704020d0212060f010503190b070311040f1206050618010b030a09121715060a0e0d060501030c1508 75
    0x309034400c59814482030b241901c002000f030602c012010b80b83d440000b0910009610010080529038400c4500340301590b6160016a21000c1c9440054078030b2a0402c60029034512a030f00464102c9450054400403588030800b003440c22254900c00c800d4a560740c8500c5007803152141c516070340901c0c140340600502c4890164944018005040240120b40c19000c10007113549080c605038140703c02c0d0048891b189015a580c0074400c200b803041d00d00a0054082c09914503040a031806031a6802c0034031200e098407411360071002000080d400c8207803d003090002282c91958542490000c007080d11410400b1807040c00e003041100c03000f40807284940b04072041e038001e81810b40c002d41d044548031289603450f6614404500d0140c500810001c02000702c0b0501441d865810074500e07518203c00403140903503581d409801c00c0d0314503203005c1e4080d80084203110708400c6620445004424103000b401d1000248031547d03801080e500b0030382080707401401c540b0013030000440c084000c1104600c0362905070300c00d0405a100c44 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 687200359 1250 687199109 687199153
    0xa0f05010914010204050307031506122d030512040f20041107020a0513020f0f190221070302070f080d02100204030b0f0c070b070305090d020f0c0910080106030807020a0602 76
    0x24403201d000001d103440d030109544244010301d0102011282141d25182c04030de50b030000880031005c984400074000310007000e40020000c86605441e240c0c42c019884220018100380100100c6250701100c41c418002140003e015016044459081d844414070004000c26076016640c409261a4203010340b401580d550a548411500c040d103030a1048408140c82c0000791080ca060f141e80044000790745e09100e4440b9008044001d540b815013841805916001c9132600d03412600030702080b03130001001c0c40c24103104000780300e900d1103801250307010750382e52850342c8464003154856811504403d0100b40c0e0160140050030320100700580c00c51406046541e01645a40003801401c45005040c0000b80c500099404481c0d005400040c100c0003850440c10045c044d05080700c003451130f0b015503000390ac01d0600020310b910b12000e140d0058003d080e402000e00040c903a0091100e8022885083c00180c000c40170320070351010714001c41c4140e40e5040030b801401085821030340003000b1903200250401882c4c00700c101c0c1d1 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 687201609 1250 687200359 687200363
    0xb0d1e2a0815040809010507121206060513150e09040606030c1e1401030f140402011107050d0204050723030708070516020d110a090603060b040902100309050a0f0501091401020405030703 82
    0x10541710898034004980d140038034840204000d800a040482948e013244410f5403600120406110301902e40a04407850301645500d00c0102c2e8040c07405109040c1302c0c0407600380c056464a0034108540145001910f000c209982c00c0d01d106036541010f0043c000c010800401618006945880964600102c4502c400043c1700c0d54a01c5118800c0f800d00507072080d08a40741c60b5205040a11084401d040c884107040b909070303001c80c0070074000740074045551400300d604003c50b0300c010100504440f598082c0000341100074581c008110464007a01c0c3c29440d0b90a01c050382100c111a0152a890664405440e030782c0c018150f0b00a0110510200a0305c044100e807202c050380d4196511606c9030824506200c10311040e002c0a540109807402c0400c003604168070400c2124000c00040c01080f19040610040b210300b400b0103900245205030208609019800141d0303042e100790b040711001c0009440c1d5014140c0004d0341243d0381e94449603e0000d20581254803610b01200400031450b0602e0580040d039070700010300c00 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 687202859 1250 687201609 687201623
    0xf05101a0d0c020c0604060503070810120f060e010e06070314060f060c0715030c02012003040209090a08031e06030f21040807090b0102060702010b0d1e2a081504 71
    0x50003044500c248940b40c08208081c5c0555119500d5110250990304111042d00000c0c440030300050b04141c50b0f40b0313401304a0b040c00b058841c50b105070781c4414041d00301c508c6003640e0f025102d19210030301000034030406070340f0358003071002d058141403c1d0401000d407004580060301182020b000d00036503a44242d0b00041c4040c0031240c06554050306440320781020ba0b47da000c00d030010807a988148034a42c041d0014014501075600821000e000c000d05480781490580d41806d0000b024800a001414002c1120790018000c208940101c4000c1ea40c0102c070fa441103402803000c5c103180400c095819840d48501d9004202140602100032074000d0031680c421480201044c003e0440c2980314007180c1c44411100078103400f6055520960300c5010000c0079040703d0a1243c014490782d0b0009510078410301c42c2c440051401820f06400c100306803a0051200c1031000954a0100c03811402030020342c1c0121100c43c076107020340d410724403000503010300c81540c0c0c1c0540c480706003078000390321511502c84200030003503000c1c0d80315031 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 687204109 1250 687202859 687202871
    0x23010207050a06020327090604051315050601111c0f0203040e0903072f0112060503060921030f010302150f030403031b0e0d021215010b0d0501060e010e0d03030f0f05101a0d 76
    0x1032f514401007506001d41007020f15074040c40c952010b40c202c50711850080e200c511600c03031151a80d81d03545004450b41d0789460240e01d00070174228400c3c3d450040d800e00030f00c1181d003810384030942c0d01d44150095541202a0380700040f00b108010307440c1882c5c804407480f90661002c031003079140c4100d14151140c4c905410050300c2d000e0034105013125440200640000707400c9031801d203840010a17a2b01c910000d8903040d2038200c526811050020071003124442d000b20a400d083d141d20395402c5c0701010003043c844009540c0180080c000c007043d0000950b00c0340707009a03000700e200b8071121881c4201b80c42c40e0f40494100a0003603503250f0030703803102c1304105195035060303500d084160079000880d800c05444c241900001d00b940350001541c8020030303001c1c000d0360030030303000401060b681c5c0da41c15584107104044140c04502c11065100d450b10f0b1080a400e1614001d080201b10400580202030480f810302c0c1110302c000355a4010303c4803c809040c07540010344160514180744222445525000740208080c0c0034945071102 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 687205359 1250 687204109 687204121
    0xe06040b18040608100f0b0f150a02011b051c0e150a06080f1b030c10030207051032010f12082104050c0a23010207050a0602032709060405 61
    0x90701c190014a0b4080644003800e05c00c0795940081c0c094419406052414104005a90703c0d10340380307070402c04100410f5404e00450003d10040142c10108800003555601c00607840350700704843c0c101c0c200c03041039907840740c2e2664407a03e1080210f03c0940120315280c6400004049640c0008054640c25203030000c0303c00681c3c907460640042c1030309030410b0381d80b40107242180b08503184c0096000240c00760b2486003105000740c0018035030b42c0d40002c2442c40d03108080354608400603000750b000f040704e107002d0012b07121401032854484050b11121012910501c60342e20300034072081090410580c40c0104204a155194500124000b014850740601c548502581c1d591000b001051421200140955100558402c0440641c18407100c4129415a41800b810f5400c00aa280c110404030903990b05142e01f60074480803107080d001c1402c02219413410341c410014003140a5803141520402099298011552110340300c10890b40c0f8000c160311016146210003008501c0e0b03a41d048801e42c051010351300001c00742e07140 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 687206609 1250 687205359 687205361
    0x10e03040915080f01151d070305090a06090803011703032a04080a11090901090f030e030a021f0f1805010e040f050f010602010b0618040504031403010603020a0e06040b1804 76
    0x9540700c00b03c20720691010ba03a0f8802c06401451010740e000040038001503a5040051549854840e0004861001d0f0001031120780a40d00668101000d00115228551103680396012901682d409076001c200c0800104242d04080d0400e40010402e4406141141421603203c083d40701e8110350400402c402a8681d44881d602000b914000c1002000701c0e84444010308082c010b40500e080340038007a840003c0040c1800905025a03444540d21009103a40407000e41c50486100040d040000da141c0038407000c40e40583e03034603540046044142e2800703030281000408090309810007034007000e003889144c21859600021151543c030031500c003800d0002c07640c24a000000c00401c2000040d040b800d14003400d200c00302021165040c140c940319002000501c02c40130801140b4003805100c100b100010303241d00e1666041581040343c0052180c103103400202e400b1980010150400d8104900084c0d011030601c0c29503501000a84900b9401c2d90031500d0141004070702001c5215100400c001d240c1b5031100c3e0b070074a8440f = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 687207859 1250 687206609 687206651
    0x11e0e0a03021506011713031419030b031c1101050105010318240501030f0510060b07020d0204020c03071b050a06090e130507082103010b0a0c06090515040311010e030409 75
    0x9010f600c42d030b40ca4880e45803c0710080040c022340002d909002c480f41e440440e0411103807100080320500240b007030022030440251441003070041d051b00560761034445401e2a6508240e110742191515498000b1a00d046421944140e10a50402d410a582e8146041c100010f88007001d82140100725110381a00311128021300c504100070300c0500d428000424080c0c151a28107810340702d030b0295164407030610402001d5401c940103541d004841089854014a84181c12160fa584060070140c14404811500d50440d001041c082e610f960f640704101c83c11103040d5000034041d04084803906906400c02600412050150092014181500011a60005000c4c515805199201c0102e0b00c400303444c0c1071b407151904801040c01c841031400301e150010000c00b2009890598031548042d0303061100b0250300711640410300c00161052a560041e90340420300c1801403504950340f40340500520700381031400a01981440da42c542c280c0e458848154010000842150126400d034040818000f9841603d8035034410 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 687209109 1250 687207859 687207887
    0x1d010e130c030f0c03020102010f05070203040b07030905060d051006170f060f1504090b030604020d0f020114030a0b0a1d16051605060f01081b04110c011e0e0a0302150601 75
    0x9224943c42d8100124144038a0641c0c0c801c0e4001e10070100d440968900380e510a850420160308140014000c40c02e0380d501410946000b4a08501402d56810109145a202c1c1d10390751407280e12101001044041c21030144002c000350b103012504014000c0200a0495002e001c1d0b40c01e4030710040c0450056a1841c14080f145034004000204076188d100c194a0303580d110744a03114501e400c0c4140200640707000b08615110302d4015100540c4c1304903a13918101003140c0e03160100c1c10b01450b491000c203418008809188a000d000d00c2c0040c078610040108980d65210342d100082e9000540503401301e001d01d00204a80000140c8080a56111044030980300b0f0f0040ca050985070014584004041c8003000880b64040c540d082c4140c0303987d90321100d01a1b00d446c06412003002500c03030601c4080c5035003002e0348041440111903a4040c100720040e0491404d64420400060061090b068004118900c80c40b400212403081030081c02c8901c8182d50103500d400c400c100c4825801110384c00136140364020794030442d10031 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 687210359 1250 687209109 687209123
    0x7020904020409230705100206010312171503162702040909210207081507020a1707060501060806101b120c1703010b1c1b02071d010e130c03 62
    0x20381d01031510066482d01603001d405901c59103000150a0901e810550380c2d10206a015106a81c00c54035400c0200e8040051607080000200740d0071140c9001d37403a0540641095080c00c84005c102004040c40c205911121a03c1154080300400ca50384821210040d04a01d00240004071003040a83e42c1c0280204d5100baa81141403284100030044400403200c0304050088040e1002c0720741010880e6592164050450a9404400c89001041e200860305a1101043c1f0403998011b41c1d40c3e0302d161001d42e805001801c0c50202082520410071a4002d4134050051440c020500b45852000a0020b2030300b20122018010501c2c035102c071260082c407580358401d800c006106a402103151380100303c1e4580f4030f400d8a50703d0710f004032801644003100869049a80d0401520704009241c0d070403494000500d42c99011150360ba5802240e825405604000b890185030040e141c070074038288014070407001521900003070301404001842881c140720f0100350404850261302c0710300c0c0241d00e0001045001a040540700e4 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 687211609 1250 687210359 687210383
    0x11502010912030905190b062b0b18010902011211042606011202030307030f0c05010e010b130b06071214030108031908040c030308060114180102011503050307020904020409 76
    0x142c0c0e00358200f41d0401e8400c8044402d042100007414160701e0002d41c00411000c01c0304045034440c509007034040c0740b00300c1c08100364884180031040c0b0910325011440446000d11580300300410072210080060000d40e00c10000d100c00101540024102c02200501c20030310350f03440c40c40e0303440c0e40105803c0e100500f60210404490310341d0340101595029500015800d503108060000c42c03c54450303c8107003860f60f4013a000318180100d07582e0564030142c04004100800c0340e04903078400410824040c5040d4201e610000056007000001880b081c0690300385a22201030400c8074501142d1521800c4482c43d0781c10070003000303600d1903c4900f00c039280540b021054050101100124046402000528040780d165084c1c200346c9150310000d40d0652022907001d40740c0207248000300046030040174202d510034030500d4802d04003085a505000142c002e8500c81100c2802840031100b156024820036400d40540301110018a00e03682d1010741d03d01c01c48034000e0081030074130b01050454440b5006601180d41c44040c110b44 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 687212859 1250 687211609 687211643
    0xc0302120c0d060209030105060a0e130201030b06030406060e01080c0d060b0303040305030a02060109061d070e19030b01051201150b0a03020405060301030f0b10080a0303050c090d0c09050c040b030115020109 91
    0xe500600c811700d2082d4070f0000419024540402c4140840d8410003030103017039640b0600051600050144141e05144d103c4604040ca03640b00c0380290301c84c07886a01c000032460f08108540c64028016001a402503000c92800d82095803170b840301200003030348860041480100b20303010070700314002d55000a05510020400442140c0c020803414161000314804000356541c0f02006c00000561207000a02d02210202289007588a80c00c00680080090440305181caa101480012070249a006880508145005200301d03c0d01c040c0b000b495124140c000c5c410300c04c0c5010322031408246441140d107507060010701041d80c940031f501643c00424000b0f01c090f84035039503420160303038080d03203a041105d84541c0100015070440c003d0701203a081d5180c46000f0204d1503004d03a07080c1c000300806460300c01c141c07509104988640c1e50301034000c0b002a104500d4003050511f00024002664000390284001200910090060a50b100140c030b0441c3c07034818207110100503c800c10b034010141c400c405000b060009030f81d840 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 687214109 1250 687212859 687212861
    0x31140c03090d0e010906111612020306090d09050d170712180305061303051207110d03060503060f191506122c07090501081b0d0c0302120c0d06 63
    0x2200381e40c1d40050710054111420210b4140700c448164601107100f8210034007003548150b00c00307040a900344003218108200510703100305521941d1300c080104e03070f00c1091400440c142401600d800c01039150041501c030300d44e10f0303010b0700300090780c09440d0050059012070414805441c00304600c0c11001e900c800d58800c4182070815007951190f0309500490440903250340058284020701040b00c2e08140941421744506100d07030092680e101007601008000d0007030444071402404010f004074080c2c1c690100f000301409001c0c0c14072410501000605250071030412554401044040d40701d000012a03416540da800d03118545003d203480d610580d1403602030104150007000c1d405000342e840545415242d54102c45d03071201980c82414a290b0202240c0c5102c1c81b1100d204072902c40290703903074015521030a8030742001d0300480d50240d0090703000d507001a20f00f1a11003ca14040f00d00c400040d00c0141803400f0b5521042d0f01040d0758840280281681035144400c1b00d42400000002c0f40010b284d203101da010f5040c450 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 687215359 1250 687214109 687214111
    0x51507080402120c090415090206180102071703040608060d060c0206061f0e1215040305040504060b0408061b130e09070f0501020d120605090c030f010531140c03 71
    0x70300480400f442c502204400180d9140780e2100103250602640d10b03641d80e0f5070a68045104500700c1d40d101c41841006a41c0e4070080c00129190102480d400707002e0300002442c200e02070740301c032045104c1d4014000034450040120381c01c0e1001410203261548801012036082c0c48480e030701503c034528050300d40e40a1035012682601940b4100c620140e1035606801003041c0300e03174000000022601c90745028055090204044650320a03400942d002c0482c00c1250b4420f00c0402c8404600007900000c0510030340c50300e031141a02601900c0c4120381000c2c00e0070f5034181e8a403009001407100f485850380c2c100c1e903541c0403c2110300c00d0071000c0315024159a205d10032503c2c104207480210301e500404c54040348084408545e04100e4205a00404841c4180c66040d100e01c1c20070004402810784542c4003080c1611360f00300b01401170100010090741c03460301c0309031018030490682016100d070b1020403040b507000d09402402d182130100031408000d441904001750005082c0c68003600040d03584038003080b00600c5082c000d9 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 687216609 1250 687215359 687215363
    0x1c050907050405061e030307170a120204030b010618170a030e060307140a0329032104140604080114040302070602071a07111320070b130515070804 65
    0x440000791074038100000e403541100c015030040115010310070711132140111080401005001da0386005000e444580d0700c50005603a06c09003541c000b5030400211780c420b02c502c21a100d110070860509085a5402004600603c0313800c003003001c4041c07100300480c000c80002c0010045103403030310152555070031100c0e200c1d60050320580c04200012016101c0c1e0a1800480e40301c4d2916540e020f00058541002c8091500000c2000040554480c0d0720310a6846502c10786030352600c143c50b5a4000c000c03081c109444c0800445003406414101c10600c3d0010003428240c8044e154042c0314440d05c02c1c0810080340c7c950145ea4018010f075820500d40707040c1d520000550b94011b500079802e0360312454840307905030399422043c45058180f040400c0643c0b0f90b00084005030a0882c40364542d551140f07021400200f581d10380039081c130400ea0b80da0706041000841e100f410000c254842c0e4526003411070507164480d00b01c0004141d145281c244912020400c41e090100302280d01600e140e2201c03a052041c030007004000e0454003 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 687217859 1250 687216609 687216613
    0x10e04030c03032a1e0305040c030f1b0e0124090b030a0e060112030905090c0304021c14060a0c09050102031b0111040f05100503131101112e050712020f1c0509 70
    0x4010304030300c20b0141f0340c401d642110714460a9481d540d54602c1c0300042542c02c0d141c4295094041c5520801d4110040c010003901801013201c0d414058980c0e5000c0440c0300c000300350750046007003401d05508560424103c900800c85240c60f55115090580903004100844c141e80c02140300205502c1400003185130544c0c006e82d5440030607500c6c0c1051000010060710016a00c90052000a0051911814483c0c44681200c0b6001200e03507180e499014000c49c514640c5150380254040050a071400e100b0440319442034039000707140e42e02d4400042d45038461241c0d0380c00743d280000c0603410242c00c250021400c0686108150740d44d25a42c0b0512904c00b20716000c1c5610580554100385601881003040c0c90103007101c01c8401300700003450358880e14141000d01c0d44a041c08000d0305500029881405080f00309512120403207031441464040b5101140000002150030f881c12060141007036100c0c0c44802242da6017007005036030314120810006a400b071f500708046649000b01d100d510b01000ca0304164003c4110000f = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 687219109 1250 687217859 687217907
    0x4050706110c0d080f040306142d040f141e280c08070602100c021b040504023c1509010503190903050d05130b22060c030501050306010e04030c03032a 66
    0xa5880c00200348ac0000303c089990a000d9180030450640391150854840c0d10340e2450218990b6581402c080b100680c0100354020f550481c1c8540d0491058082c800d180d40080c2c814404020191300c42900702000c042984140400e03070708100300c0340511b0000a4a584001c9038001c82e03a40100940d0b03103500ca00e0100c241801c1050707062201d07000180080d048107806d070800c00e034501803900344001402e00a0003681d01c007805004440c204080000b0040c0c6510903c4060412490502104c8500409600c200e80c0606040c0c3c1b145059000d21a080d43c0315040e09207061a6070341c8520040c01c4410781d104000c3c88010785480106802c0503002401010325017030441c024000c642d103101c0c81000308442890068007882c60300d00000c1800c00d503001800c58030344d400041c0c1e02035a0300c11340382c4c01308a0700300d4100300380401e40d904018000780c03400f003000b5401800d00c00d500c0c2000b80b815a6001700250810040101410380ba100f580a400c208400b2041541300001319030000c800c01d2050003800c00d0b41c041d000c0070440c04008 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 687220359 1250 687219109 687219121
    0xd05040b010618030c090207110907030c030b0d0503030a0c05070b15010306080f0a06111c06080618030d0207030908061e0703021e0f04030b0f04050706110c0d080f04030614 76
    0x224410f000c60b500038035000c18491520b442d0b58040d501c4000d04a80c0d00d11140e21001481d41c5e03088016004013450390f400034041a0b0208060220340301030038410300c14516140701200041001089950041c0f4046001c2000a00307450290b689004100c4002d15800c174200402c41c1c04e0114403015812000c0036601402440d0303945000c1078841411140c45811078000e5100740010400a07048911410404a91203251a03104a12403d99281d030198200e121a1100801c0041040802601d600511056080c070114451600216903074800e00c0d4045031120380220788981454041e2560350024003030b03501543d80615110008100c941d150070071441c51051407038003141d10a0320030300c2621003056200700310043d1a83c114165202941000001c1c2e0100c4000300004800281d0903101070340a070400710120380050405d0b06d07040d030510032a5084001004503003c403900840500180380c078203440050b41d01d5139002c022400d10300340d94030610f808081c90241c001400800c0103040ea0100b29480000c1c0400c001c1506c482c = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 687221609 1250 687220359 687220397
    0x706140708070804020906011119060b010305090a0f0c09050a05091005010503030f071509051005010614031504060503120a0905190612090507030b09010b010e030d050f0d05040b0106 80
    0x2a9003071000150010f00107001801e01c03510310b0ba00700030141000610b110b0a441003502c3c01e4000540601800d400c0e0046404202ca6809525280d00c000d0070148454079198540c2a43e841c4002006401e52003100d2940e0284083c15022501900b05030b00c0601891a012440202412081e2001d01c11880740c2214030900b003c07148160b6040e42e000401a40c588441d24100c046580c114007401e488a0000e004005810500703446404a242d02c508064541e08011b0f506030012140140e2040050000134401130881007010000c90703074049d00214120484650000108008200369000300345c140c8104050400381c68a02005060000c010303a458100c0f041c2c503102030100900303540c1c1202c4400088034074244010340c022810030320f58548400d0b0000b070316090350f00c589107000a41d500030380d1143c01c502c044c0054420300b03010300d205100e000e00701162217011003804242c1d5025007055400c100240800d10304603600031402100d455003808002888681824240800c50400038403441c0080b0381c0f241e80c2d24543d4120 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 687222859 1250 687221609 687221611
    0x6030f061e060415110f0a0210080603070303030e010209031b03010b040b0d020105091c0804150f0207140d0204060b0316141e0f0a1d01111f020705030706140708 71
    0x1504150030300b46003d14445011303948036103410601c1400b400062031410b0400c10440c40b201d400c0c00915145086005004d4400200240002001552000c0140b140c800003000003c0705d42c117180001d480e8165401c43c80c0280690090950326000340d40601c045407424420804071310328118001c120034002c2000f044200e4050229158110b114001c03d080558054800740003041c402600180c159980f45402102000d0555421030b800d00307004c1014841260a801640c0e090f802606015070714082c07419010b5036803340791003100035400004003141c104d5185c3e64000f925550f4041c1051002644803101d1841682084600038041644207e0f4000458414000e5000c0c2c0040c070458585000b544e6a00000d43c81003652404406180800c060007416075644002c092560302542c840c614040044c070741241c0d81c945c40324154104240c018840b4503003180030401070a404545002608000031001c0d490000c0e0142500181603030001080c560140300c01c6400030004900c020800d40320b81d0350745640c15640380070 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 687224109 1250 687222859 687222919
    0x20f03010b09040f0c030206071203470312040806070c02060d0b010201021e130e16050313060e1501061701030f050f0618060906040305030708070e06030f06 69
    0x20842e80810302050308900c0c5202241d004420041641740c4a801146584d8041802140c0c4500076070780178a040c581c14441c66480d01100400340c040045100c030300d6015480d50031402d018003621104026580401988038900844d0060140c85104070082d904003076541051041340e040340a080c0009210501c43e12141d044290700a2455003041c0d0000d034400c0080c8102c8010782c1c107540d801c0101c060744402401100c0840740d0341d0048a541da00c1e814240c0f5a51483c1c55201c4100d94200c0d100303015216803900c0c62b03e248880d162a0154407a901c4142d4a1307108000c200e4003404541c50030b201841c210300c0c00302300c40103d210070b07642101d0241d81e2036000302c805426a0f54001d4a0306407540c0103000041035010543c1146010710b048034600f00d0401d0b115400d21405a07a00f000c01c44001c21980444502800400d0b4001351640152280749842e1301e01804510006003a4820410031100148080c2e020301000290250060903098680c54280c54541d1441400e5881c40c1c4101d0142d0900f18440390305440001d042a = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 687225359 1250 687224109 687224119
    0x30f04031b03050102070804150e030d0302220b120106080615090316090204090c0203130311031507030510120c1505090405040b04031e091e0e090a020f03010b 70
    0x924584865001d9004a881d04084400c00000080030072000d00140c00705501416605683c4d91405101e00f031840c0b28803c0c0c1800b44061b107856100c840e86c002c14918105a00c5040c05603035032008454820616910300ea80c03002c1320484240119110010901500300003c40c207841c803080b6626031506507180001200c54a034800c81011341e0304010100d01024206080b0040d04840721011880303400d0f4000390072900865a8194041020008500c45000705e803003060040c0013841c94400070703000c1203404180a00001e805610810522001c80d28200701400c80d40d44809904a010304202c00c00a02525003903550039400d00204002046940c50488034801007a8409401e00b202441c080f00a00200c421144440611009121401c210f844602545220318400d03403401800d80741a25000d800d407481c0300e40d13444c0f100480e50790035014150003502c01400d945c0c248200d000c56205820740c4003800d413180e410811210484006000608400098000b00307140b00b00c5039402d6007402d40c0140742c2209c0981104503400 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 687226609 1250 687225359 687225367
    0x603061b0a12050a1514060d110f16050d08160f0210020706020c10020405060714120714100e03090409050a0506070c0308130f08130f060f11030f 64
    0xe1500c8006000c044254100401c1000d5000900012214200d90101440f0349528444151261a0380242c0150042c154400e002c032040300003091b100d000b044100c075205540d030000903558902d080d00f80c81440b86020115a698401a90101020b41205004603200e00c184040c00b40381a014400c000c2c400c1308240301d1030400096081003100c0c50280700d41c46900b0b43c081c000000144c6912400142203a501950300903a1341e080d240c034402d1a02845003002907010f031051000344a07660720003044400e43c6800c000c040600170201c012030342c00c00b490601c40c40c50700302000546400700b107800481c0c501100c8a9500b5280640701e840388107020382e0302c80041c01d070b107940007048801e6441c60941c0c000e102442c01501114120740c05039841c107140040a54010b0041645040b0b1241010760041e9607591008031900f85040c0824103580745c8002d5010704070010000c1c1d030003040703902200500011400c0100015403503d0380081c0d662401a00d030000e001195000501d440d0a0031030320340000002c959151000c0e403112850 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 687227859 1250 687226609 687226651
    0x60e0108072f070803040501020d080c090901030f12030b0907140c120c1b01020316060e10020c0118020904030e061c0605042304140102040e011d060306 67
    0x12111004000505005203001903503010224840c020b120804000240b0000311103850301c00c0d203002a40c0d032080d1042e034001c200c213000a07640403030910700183c07841c1480071407622509160032440c01288070454003c00043c00000030300050b40c00710341d05c441c01411595121401044c0803820b075100034180c0307a0403d104901080070380340308141c40c00e1200741c112800350821000100f02c1c0e040090303c0c60000c100800100d60200500014840c1d1034421104034050031800c0c24010010b034582c01000b0301281c0001d41c40c01a8014850240c00a403803801c66801650212000030305403400942152100c05882c1d81790010b0301030300c2c0415400800300780340c00920840c05503a59a800321030780f01c0b4280c04150802418041205815480c0300ca44036054140c08010500c5400c110500044030f81c0c0b0000c0d45040100349148400c400707d601e00c000c4c0c0094004405220f01081d8900c243e000e4452684400d24001d40440009048ca60090ba9038150903c56203e03000c59403540401c05039104402e90740c031101d112804c140c50764 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 687229109 1250 687227859 687227867
    0x70f0213020f12011e030c030602090a0b120f0105010309051905011b1d0423040309050312041e050a060e040b0a03030509040c1110230705040306060609060e01 70
    0x21250116000c0545030070200e05151160b9007250560100d10700d05840140074101920712150744000c050104d010045180d501c41d050341701d9840c400034288a500042c0140c45440d14203040c03000e0110503070303166921001c100c075520f0101021100f07a041068010700224003507100340503407003840d50031070020001c00d4602030038407108007043c4000f01ca80d5907891120205205a03200881c11010350b5480d83c585040401c0c00d10b0f1004850707011082e20075072603c11020b5010070310002e82c0351807503540d000600890f60395140075181620190001589441180c604014100d40da400420a07559141c04441100c0341c1807800248050140c01820750046a40005114142c4145801c48104d5402040403840c1010b0501140ea1b20760b66802c11340001d000098480000c3c00d0502400445201d01d01c2c06210038107005441e241c40340780b958a2003c10684440f130900c0300000c0f040d00c0d481541c00d402102d90141c1000d460103086580988000c580b814105000002c000d40240041c50844aa81e21100d203481e0031800112 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 687230215 1106 687229109 687229129
    0x5070305130320030315041b17070905040606170f061e0d0b07050717041809080d110a02070504050c160507090c0201090b0c070f02 58
    0xa0352085280c0c035031426405181100c010b044110382c0248a40701c9414800d5188000300c00c2c4046d10f4104512085c400f242210304003e40031007a5901d4015103d04816840400c24620304804c90001282e092580726402c0c0c03808016036130300c0b00d001030110f0b151a005400061100005090b6404020b507942d90070034060118041e280c1341074400500c55130041004504248000d00200c829074640d40c0716401c5d5203a2160b0030201d1440c10303840092541c0c10050081e6010841c292140e00342c0007015044400b030743d40500360350b4006042c10f410b18010b0883c81800312030350380040000711b80d082903074443c4131018280c4811556855040e24802450a560354100034485ea01d8074041c0200042c082d03084840b02d44410300c030021101401c1c14030f00d00301925948105003050804601a01c0a50b066120f1050380388141482e0780c2035150b80943c1001d5028040380108040c03401b0030700802524044402d2 = true := by decide +kernel

theorem cover : BRFrame.Cov 687050359 687230215 := by
  have h0 := BRFrame.cov_init 687050359
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687050359 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687050359 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687050359 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687050359 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687050359 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687050359 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687050359 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687050359 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687050359 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687050359 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687050359 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687050359 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687050359 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687050359 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687050359 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687050359 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687050359 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687050359 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687050359 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687050359 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687050359 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687050359 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687050359 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687050359 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687050359 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687050359 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687050359 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687050359 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687050359 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687050359 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687050359 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687050359 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687050359 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687050359 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687050359 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687050359 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687050359 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687050359 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687050359 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687050359 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687050359 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687050359 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687050359 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687050359 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687050359 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687050359 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687050359 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687050359 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687050359 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687050359 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687050359 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687050359 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687050359 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687050359 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687050359 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687050359 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687050359 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687050359 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687050359 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687050359 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687050359 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687050359 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687050359 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687050359 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687050359 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687050359 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687050359 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687050359 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687050359 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687050359 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687050359 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687050359 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687050359 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687050359 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687050359 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687050359 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687050359 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687050359 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687050359 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687050359 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687050359 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687050359 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687050359 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687050359 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687050359 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687050359 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687050359 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687050359 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687050359 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687050359 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687050359 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687050359 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687050359 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687050359 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687050359 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687050359 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687050359 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687050359 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687050359 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687050359 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687050359 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687050359 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687050359 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687050359 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687050359 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687050359 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687050359 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687050359 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687050359 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687050359 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687050359 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687050359 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687050359 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687050359 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687050359 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687050359 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687050359 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687050359 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687050359 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687050359 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687050359 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687050359 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687050359 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687050359 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687050359 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687050359 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687050359 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687050359 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687050359 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687050359 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687050359 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687050359 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687050359 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687050359 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687050359 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687050359 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687050359 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687050359 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687050359 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687050359 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687050359 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687050359 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687050359 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687050359 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 687050359 ≤ n) (h2 : n < 687230215) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
