-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1964
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T05:19:07.863105+00:00
-- url     : https://prove2.me/submissions/aaf38a9c-a603-4de7-940b-37e2b4aa10a7

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 353057553 ≤ n < 353237410 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 353058803 1250 353057553 353057591
    0x1e04050c19060210050612032b02030f06130e01050108071805150d060b030304090b0103150807050d030e100507050d080106090b03090f01110301050406050f03100b0a080118020a06030e0a0303 84
    0x503c2c000340c0400100390f4420083e09c1c10001102e6000d0703540c51a4000e4007444002284810354903507821a003081c002134a6403410905180d88001c560a021950059a03120242034460a0308005903a03000584240107404010280845103509100c041c005400e040003800d04020004403010701444507440800305000141e00200e2032075101074212039445955407401c00041c203a803030320180080d00340036403140b603401c1f2021a00140c071001400f41c518149880100000e50302c0d600360807401c4c04094030520917641c1d207151152a600c54a511800c1d6a90140d16007a400d01e206c1322100000c0c0008440140303c42c59014446105881b20b608456640f52130b02000700e0b1801c0a0040b20012640c00c004a040230040c500c000707941240c8003590180f00340c0307031900200040b01241c48003484d00760b445180c0d80900075032079401401c0c05e0000030340300d014030b07603182c541840c2982c022559804005010b805054114103100501c440206150b142c01c002044c9014022600c074404010b0188c2055251010700101c0b500c3c40d11 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 353060053 1250 353058803 353058829
    0x5030711070e04141c21051611070e0103030509010e272d15090106030903120501030302100b03030d0204080a06060b070201080f1e04050c190602100506 67
    0x301e4078196902c29601c90760440803a02121043d00100a002104900040304110001d544c20a80b91110403440b04842c0c18110041640b0f010460140c074208051062103003134012071014841c600000004013024003011a21310494260ba03004120401a1a040c4004141901e90514000d641e0b082c3c0c84004840c981d03101c03180d40382e0001102c9485074904214030642c14440b04581482c24496946c0c20703107045203005c0d00c544a11196103402c040e01110380712307580f199405409082e0f0b090700d05d125a80030440c00300b0240c2007000880e0790344c00890f0505400c02400070350a240003a05101560441d41d0003515107082c19915000c0540340c1880d00358581e002d10544442c03282142c821500d49a45440d101c3d914000c0103c19210f042c074151000c0780020080c4216100240c068444210a4403a602c03620700540c0003c2c0170340010f00d003031540b200c400c644512505e03000301e000c3d400600c0004c080208000034405070340140c2e8002030030504c04018242d004110b14141010800d000101582c2d0380001c5171440d02c03110 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 353061303 1250 353060053 353060087
    0x4030803010b03061f050906130905090d020705042a111603030e030303010f05060d02070501020a03020904051008060a0b0f0a06020105040c17060a02030a09020315160207030c06050307 81
    0xc000440d489109102a5101d1300080303503a480103049502c280c01c0020003154111000070820006041d0504052004040980d20b91110169082d51f8044140c2250801d4455200a80009240d22a042d5040000c9005050129405c0010081041881000703c0c400058691000c2e803c000303070342500340240e00c41c0c1c01c07080145003038980036a5a5200300400c1080d600048000c03500326040b0704c0c403d080010030383c1d050b200c5647d5410840c0e820f0408219aa4100c0c01c003d001d010303020044000094400c1c00680364280031620056226001d1808020540742d00909209015401c458200030492002407802d070000032840b40003507000c404030040345007031322a190425004140742400280c07099056000c503104a003d60100704440351103071842d2000620380e0b4408601d070f52004010030300c00200d9034021604005100400160316540342e0200b4100b101c10351000c10025034810070011301e241d0303002d908030649a0b81c1c400342400c94115500e05a20601c0d81c0181e4040101c0800010001070061900c1d460a8070320b4 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 353062553 1250 353061303 353061307
    0x5090a02090916030e061501110c03031605030d09060501090c0c03020a0209060114030c0c0d020601032112090b0402150909040f02010e060403050c1f12090c09020703170c04030201020a031103040308 87
    0x201f40341d0803c800f03101040d000400b01b8982d0200381402060150a588000380a14944484540c6410803d03203154801e8840c3d01040000c9c0d98024814400c2c41c01151081a001c01e2170340c500102c120031951610707200c1042c01000d055100010b540403405045a0b0760446001c6442d448002c012507520b00c1820103489090710000a00501c0c0d410366000d400810316200803a00c0c1580c01300300c01c036140d0500384001060302042800d4a4600d908115401c10041124902100c0706007400d40c44000781d070900e91040e2201100381c4207200c15800c00802481c0c081d04001c0c2e50601d04411000425404c00c40103001a155410003072614045a103c0d610380080c00200412a6464540300d0501c41e40350f05e00710101c0385c41021000307071550702c0d16200790185200000c5074a45910140300da2450710050301d0032100c101d50205200c8400b2030380c1040b62014103d21b81c041c1e95a40c20304105442148261072011704807581e000b41c01c0c481000146e82c0050707020760703181d4946815030307505c44005401491406030ba00020007090300 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 353063803 1250 353062553 353062561
    0x91a0304031416080d050601030e030714030d0f0b0f03030a09050906032b020c030610090c031e02130e090703030c2d02030c09070f03091112030405090a02090916030e06 74
    0x31002c0940317090521320342d00f00a0b5481e110015011100e0444441b80c4541045c810f0710081189804a165505600c005692a0031140b402c142c0032145104002e00119580c1c1540c2c6006080414041c0414481a0011031904a0001024120225901c0b51030300c00c4920070006a8613440612101812000600d038206980301021035500c0100c1c9518102c00040c0300f1500e04c40814500001d0080c02860358141c80102d003400c01627090080d04540d600003082c10385511880107030080790215074004007030306440144c5500314480c804d034814001c0e91110703a42d09049005e0080003240440e0100071254942440104446c842c90960700c0041a403c905254482d890a444450070a031442880c20510890a480c204210381c0e042001201013a15101c0009594480d03241146000c8e92000003c2c1c0e0280340d00140313614101000810100d03030000003041c2d0b40c01c04601080541000780d10250040300c08407007541442f0390704000c00c02c0c550000b0a001401c2040c1d03100510b070140240d0100c4181240981910708600d0 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 353065053 1250 353063803 353063813
    0x9090308061f080604050702011e060609240c0c09110403031b150b0112021305090105060403050d051e1305010e01020f120a140406080106091a0304031416 68
    0x20040352400e0160760300c2c00d09100103256020000c10011082d0b11800590344880c4c0c107002c02040010105401d543d80c0d42d1407511b4501070b120346180501c1030114007041150502c4001032005081d07511203a010f5548401c118050581d842d40500f94800d03e1420582e00d1603542003403003485c3c02c10341c081d490061601400a81c0494003000410540303002e034a90a04001107551143c0c2c18052820000c0d0551141c601120000e4066070403030390783c001c030503d401c0481c9c01505610300200d030f0002041c0448410350000801c40307800c21080c160700400c01110440c5c1060b10f1612060703107814401130020108040000d64085200000d162500c2d0341c5404400180c40d103585556004e0400c5081c051107000c00c2c0408130820380d541c400545110301e0040b14000d0b00341c00c0e60f4180c100e149a00142d007001c0600064049100e07510395240d014200511070365540c503d195260800141200c0915045018843d03040c04c00c5043e5105040102c0790840e91501d820484404da940b449103850240c4080d601d8150755550613882449 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 353066303 1250 353065053 353065067
    0x3040f060b0a031506060507151d030f03040c060e012a0c080f010f020313140111070b1b0a09050d26270d0b07050d090c0303021606021e010204090903 66
    0x810803040001700d888400649041c000c24000820803035014100c811002e0b001d070081010b80c03000c20507066054100011090454001803070303042c2058008010442842651480e000003450355041c1f02c02c9101c507010008024514255401142520040c90001c40f0003405412000c1c26401c890340600e034a4032420000d8a45c44144108401c660a103101c00c610b0030300307034421240120403580b0203038020040359172a1507100c00401d000c00380030f55907050f1502a0010000080030107502c1400f0007580ca2902100001050840f81c0b01c410302c4e1002404102151500031507540180c480458050058452901e484016000f80410b0310400040c3d54040b0854004200c000e44103114400c9007200044015851401c01c0214075400c40c0d038803e100c1d4001030007181401c0360302900200b05150181c42e008040000009903001420300f29280141e5103c10014940d051085000301261040d10f0441c2524000d0004d648192650301c00b01e400703d05002d141c21180c2d095048a004100c0e0040510400d00346040c041e10b44 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 353067553 1250 353066303 353066333
    0xf100b0412050105070f0906030e0a0c14030609010203060d020409080d0603060e010e0316060c2d14190e0409060e03040f05120604031b0b0f04061503030503040f060b0a03 75
    0x103608000114510b1740c0908605154008155111403141d40381120403070244c001e02911890318011000e02801103a1034140d2140a0030040c880443e81e82d0042c0245403910070b000f0106101a4414406c1c050719540d0503c2d040007003a01281c001c18440b256013081c0e2140c2c441e0840000541d450502c00004210040e04200c60b0440c0c1040200006010006026100d214180104811000e20702c203000000c2c50692059410341d40c40d16146001d19111000f03010050004055075010800050842504950002404400b0f9422a82e028240b201321403a80705072582e01444181440f80001e0210180d484942c0708008107500184280700f08854a0101512988a030040406030b0342d01314001b003494104030042c0742c3e202c041c043c010311441c3d546880840f5a01d00c40040c000720b10b86002e085030003041020b29aa8010404000c42407160b042624020086820901c0d100522105004082010075044010380b90310513040742a060b40b400702880c011000f06141503c41c4d03440106268007106000320503000b2011 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 353068803 1250 353067553 353067563
    0x703020d020c0612010902161b2105030306090703020d0609090c06050a0203030c070503040b0301090f0e0f0a142404150b0f0d0309030b01091a04060602060f100b0412 73
    0x4914003082c148061842403046500e105500c840042095040e19030084c80140c800503010a24410290b8504800b01540801d05004c191646c0040c0005001d4010091004000c92078a0901c84100da13107541c1c80703010080c0b10740e100d10030000000e00e0290082d01114070300c05c0c240c401000810f40301c0f40e9020041441000641e400c1581c11004076545000e803084070b40d01c186130b800441c1950340720314107240150310042c000c0b0390074001403000080440703e0001840c06404004400724844048105c420101c440001c0800b0203a071040e10100b84146010407a9100300e0b0300f142250f4125210082814038140c0895108a140d0300414400d001841402c44118040c40c421050744052401980114098500c074600c49580003c0c010960402c80c81d0020081d05180d1207030411450545d52911010342d0b0810907072062011b16140d1981002c2d10a000091000d925000c6604000d41414114020360385d6200615406805a1070000325180d1107005111300020305440a215544e25250a00c4a2540342c440d40c0840b0 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 353070053 1250 353068803 353068813
    0x61403040f1704031e020d0b10050a23040c0906030b040e030f0703020d0e101209060e0106151b020409020a17100615080f0a0b030609010e060108061306020a030e030703020d02 77
    0x5203001ca40408204546e40082503203414007101c1e21460021100030344a04e420280369400001c16844814804008001c01c02c244c038480203210b0000c80685a0700700304140b00d41d18000c040311602c1d410000c003c0a42d01035140c00104000c035003010a00424200450b4803240c0f1011038070000d800c90030402040124403d50a0b15264440c008083c3d03025000c1c3c00d00c0c203520107452114501118420251400b1850001c0408034a81c0f4598441d201201c00d038081c20780340c2d651646024010354113001d281c0721203241c840c0351503c0821490106041852204080244900c1c1c441c817120041d99903210100700503040c0b50a1500803e00041c5455a8070714608112184071410900000791401180700a07941c00c10f20361f181da0840c1d43c1c03403038448602044001c040b11440b80d0388402801454404002062080c51a200001000300010003103e141440c168440b91050340180c04015071f0b9140c000444200341e034000c0e000b40c1c54020040080e03000d00000e0340810414440401c04409155002070421007498240c2c00343c1d0 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 353071303 1250 353070053 353070083
    0xd06030201230307030b040b091f0803070b0a05040201110709020301031b060f030b0a1e1a1e070201031b0e09060603071b0c05030718060e01061403040f170403 70
    0x1c02c05034103100c181c580c6240510004070b40d280241c010075203902000708006280c0d4401000100100e0055400c1c0c400600b20381955246081d11800174409009000011410110903564115042d0402030440401035294400b050459000d410f0a004003410348003543d002984851551009410900c82921403126814000c005c80e081040404107584c0700b5503e03c603a0041054040c1c0c003811a5141e00c03a04281086000905520031405100d5485410400e070362040d403500d0810f40703100c04100b54030841b085080081101d11489d0300042c2d207101c68460542c0303403907244c0e03400143d0041010001040c0300240c1b2801c0c00e1040c960080c0c0741d0603d01030481e440702060f150340051001c640401c44200b000708150238001502054643c0d52450001c0c0b181103580070b19174030b41000c40d082c100c4d00d0780980500c00c208403080c10200302e540070380301c050559410803503215850514001c3c041004803c59002003400000414184a030f02d0340c032441c409802c54011601d0340081c014a4a103948644010f41d40c40050b450a0 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 353072553 1250 353071303 353071337
    0x112d0d05120a09020a0e04170a050a110106060f080c070803100501030c0314060f030f010e0a1406040b04031413301a180a030207230a141201020d06030201 68
    0x2191001d401074200501c4904003034819509481c0900190f885040d00000008c0a6420740001e003200e40c1e0380d5490b40d0f01c03054420009001d03241015465402c69040540500c80c040c1c2c4002e005800308654070f8290080c0c1c44104602c1100d10443c0c0e4040d003c070a001082128084141e00b04000300d920a0742c080218400c140300441c1154284600810190300c000003044503864104002001d4450007810383d6802500c80c44d0150854814801c180c0383ca401c1031224a0030321058509000300c0700016000342105150643d07816800041c0140001c00348a151481c0e401d10503000000d49900d508402403040900f80c883e422848115000300e680001d0380e5203240041d401e0000c4184814586a0056050403160341c462806c84008100a1008181d52400c207128200c12508100d180e010038080d8000d45000b50520801c02d55820018900580c0c0040304081d0300b0040d04c902e402502103651410400010702d22190021b2000d154a01c2000380303960011a0000310302c7d1362076003c082224400d0f00d402d51107050900f46 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 353073803 1250 353072553 353072561
    0x80a0c2306100929010203120a060e06060f04120807061d0105070201060501020c0f0d0b100305070603110a0f02010b15210105061902012306010807112d0d05120a 71
    0x13007440036200c2c1658040c41d41ca800c4494111440c14010749003403c0410f58800b1003544c08880460071503440304410007118601255040c2c00c03240558080c1d260405031840300c5814440d5100341e05508282100c910180b213031000542c2d8013154051410710410041c20080da641204005014066529100114012500510420302205d0040c2c000d052040c4814042081010489842c15040007000c03400000044a060b03680340308a030301080c40c011240c2581007451070301e0500e0704100d0a0500d004520503030324180391b064800d00041490303c00b0070303440803800403800361000800c0c25402c010144209007100d2400c6010340340400c544200154000d80600144110390350a1040300d40200c0f04000c0703a07800901d40d01c290306c8840316500000c1005840f01c002503d407000003441c1c02010307250010074840c0560b4000300e81a001a402d10b010102c0c200700801c025200d00b051036501c18007c80f00302c80d4541c0000b01000c5c00152169802c260f8440c0d00c4800030280041c5c3c8442d4129149842d000c00180041445100b = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 353075053 1250 353073803 353073821
    0xb070e090f07080c2b0e03042408072001110a020c01120c1b06060b0a260103020616020310020a0305100b0403170c010b0a030c05150304080a0c23061009 67
    0xc074801074013107440440c1701075001604038503a949501c1d1a805c012010402070000384421408544030708404064503281c1c0100600f00b41c10000d9100c24003030016400716401110945429500c10b03603d5441e515940140b154000e114001200455030300485074010844540d501400e032240602e1034107461464080b924502c00810124102015080c00031303110706580c41e0124804d039800229a601e6aa81101d650000e00441e00055440900d20a0071240c101c00000011504410b07060954159800290b1600441c03400000c400c424800c80d40075981e040220340442820300000310b640d03c3c80040b0081c003a000483e0b8000c51a030400400090340b0f00200210390445e03801a24181c91240c8050f070120f1903912035004100950340314401414195191101c00c40150700c40c0c40c101c0b5035545000d0500ca0745000d400c00380111048280108008140d2101c1150020785a910f03020f0050364603032406002608044481240078003521100221540c000543c160049941000300300c001c69803262000250740180e0 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 353076303 1250 353075053 353075077
    0xf02030c070b13050708060a140f0c0904020409060b0706180302100c0905090702060103060e0a0f0f03140412020a05090603030901141b0601092004030b070e090f07080c 74
    0x81007001c10440d51105410071041907a9940d21021a2101854001540c005200030382105041c001820654400d800c0382d0880c01c41c0c0c1505914000d0900504008000c1c40c588604100292607140c03561240d040707e01908400c1c9081002c00c1d01d50104000d40d800141782201c044d490000c8441c08031100242d01001d00f0751650007885030b01928400007000d0b144010b5080240b00e51110b0105882d6551100340c0d10448056005110030b40c03440c100481a903003000d103810040d401140b00c050220301c040e10500b00300358000f402d0124084541c038048504110f51005031141c510081808a0a2040020f00d110103038000c5038034141780c44d01d52040140440c01950382035850780c010440d2204550007100d4a00341c2c030380702c1c402444c2800d0059400c4071040c1c00120b10031259810001c010f0002441c0c2d031241c3e12014600400104801803540802c800070320403400003914114890000a4840c0c3c496a1640c0740b581c00504003051a040c40303841c0201c0000150303043e0f40450301a1000604c01803c4805403a4408698 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 353077553 1250 353076303 353076307
    0x2041d10032a030b1023060708040905160e030309010503011707170d1e0c03050c030403081b0d0e03030313110406080c10050a080601030b010203160507090f02030c 72
    0x5940d40002c0c0000340c81250419018035109807540300e001400320802580a840c08580a2819502c0c1200c1e07841941c10003820600d0002030901c2074008000076440b003a07070a4621f190344920604003100c00340142e5110040b607600b01341c00c0103c0d14101c424041c0800180e40c41d41d0008810240c01c164507401080840d90000c0c1003800100400d4050144021340704010200707a80501e82c0301d0541e000304002c0901c4044169100311b039440f010550004400c0c0344020700411110308881c5100004000b440c0b21040901007020102d041740301c26070180210b600540d40409415170700c9802c1e0001c88902c01042c1c070354689078011141c806071901e00550310b0180b03e40006010714031b556202c2c49640301d200b00c01502603d6415900802c0107990b16075114200280c0080c00044c8044000c0000304448400928030000030002e0030300c00e0001e4540c00842a907080002401d02041c0b480345040100c0c50f50040c0c0d03d003412900603107801c0c0f074180a0b0100d5010305444011000f03105014090010006074482a24646c0402e982 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 353078803 1250 353077553 353077559
    0xa0908010606080412110607211a060c070e0403020a03032d2c010b0a05010203070b0a1a030a0605010906050303130902030c040503030703170f0403020c010c0201031b020102041d10 79
    0x885880440c0412410041c00b01b82c0480f04161800e81e0840303840001c40c986d4882ca0b50a03188088540032800b0b15401c0a00000800c0c4a00304500350100480d980504400b0465802d042c80a0100c0d1014209a0300300807900e1400e400e0095403000c1c103070016004207291403d0400701c590005040d998041c0d400d21141e0b400c2c1e907151001030050280c0101a2903c4d0665242411400280e6502c00780c1002c104001103074448119041010051203503001c10b040d94820045000018a946041507218108500000b0349003180011010865501d03080345a041c0940c0740700904205d0240d03c5241070ba800c0480030400541c4981c01d15035240700743e0115001020003400100205501038000b1030307001d11146060390034241c0e01d4010a14603000690704401203540403040445849038140000d40c0300381607501c0b0380d40e42d040984002e51074001d4a07844a04200321103a0550035640660400d10103014002c0781800e4003001c004009000790020700850241d400303451220b018035a001c1d0030860059103100c0809090503d = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 353080053 1250 353078803 353078813
    0x40e0f060f0412090b160c08030c0309090a0603031719051e10080a08030c09041104080c0604031a270d020606120c0105031005040f050f090d0509010e040b150a09080106060804 77
    0x5c80c502c6c21107429001c0c0d0f1000c134104005101608440880703400860701d68055004000d202c29006001002c220b00c1c004082021036402200350868090810b5130113250b488142c41c03610507140c071a24036a25982041d00f0311050b0107075a003003d0211003406211072119103682c8500d80307500201c0d2003082c54940c000c4602e17030041501c1f03000554200160380c40c001c2c42e0522000118068440700c1006c038040c400302240c01c001c402c1042c040c2c95031201c812241c031850241160b682c0381c5031030101507401d441c60f5205000900c030510140715a40141c082d9103812110480e1800d1016652003e0480040c010700a4001044c110705008040703010070264400900303c1001c0a03401111180c20003009a00400b03034500c00042d01340c03698801d024804e09056000b0441d8a04680c2032802010041c00040190740310322503050000c0d60200c1554500403092821512820711140058050701d00098001d41c04441040310040001491006044810941d142d00c42c403959a80101800ca800a10400c4003098090001900140e = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 353081303 1250 353080053 353080087
    0x20909040b0f24060a0c0b0405010509060901060b0406081f0308091c08070f0305070605040506071d030703240615021e0c0907210b190311040e0f060f0412090b 70
    0x2041510700705140d130b00c00e0341f80c40c2d60b00344041e1713030946199540c1c01c1072020f03a01040c4140341d4496100e40007400000d01d001c05108242c8561311440d404c210b8890045030307407401500c910410680c00003000020b03041c0c50b424072828990003020818480c0d02d1900e41c0a003074160404c20241640d42044859040009540310304407541c00d03403035040301042410041400096220710865000303d004100419003490000c4010f0001900344501103108e07030341001424031035600015400c00f43c940c003510600d004071400200300c45c802410118004154148003002c03480301d04030414100c6a00f5154210303601260402004107100d01041c10b29509500401e03000052030414001c2c1c00c0c0c0045103460301c110032454003100385140500c400003007040c0c1d50302c0e03222a01d0580761031280118401520300c0004801032856a031106502d40030204540980d40300e807130014442100b400405c5080041d0702c1507501c1840c040300101039803a8121811202c007240c0001000c17a081c0714803560001c5c4d4041c00555890440180382c00c1040c8 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 353082553 1250 353081303 353081317
    0x1404060605040b0d0603080f07060b060403150b0411120a0b060403020a0e09030f041409010807380a02100501080d0503040201120b03010c17150102120d020909040b0f2406 75
    0x30345c50f1840000007030264401000d140c4010901252503038001e25180094440100030180724074402d01041c400b107031010404038189801d9071000500001590041405800c07d803130019000007005c1640e49a0400607003400d88189a443c0c420040341101c1010050140550f02010b504040d882905102c1c0e003402560598002d130703189044900341890041d001001d82e000e50010340d20080d10480b010441c2c18070845880c0908402c07006050981e003051400440c0b07882821150901c820914081c05009110404049041554003001513a03181c032042c001e50740700d01c03501c0c00c044100c2c544400018003c02c041240c001e801e015a45061a6840c3c0790011941140e1048211030040d9490f0000041e580d004d00c00d05103212660b072604103c03110070945441000c0002080220038009209221605a902040d01e007003040c1e01018040e242c26200414400038003d1804032504001e80000740000d00000c1d584c5c0c54407500480325101d070195504404030f04512000c40d07003100798145000c4881010301d85200070b0040e07 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 353083803 1250 353082553 353082577
    0x2512020607060216080408150405061512010203070305060a0801110f090f040f270203071509030b09030318030702010e12030915091f08240d0c1404060605040b 70
    0x901d034913003c100081c4800d1190889800e034001404208800341402480d8041c00c07030b0a82e07040b0502e0301d078440c99101c2d50010684820b000141d07124484c2581c6181000401208000085482e850400c4c000b07801010259417007031194007c4000055140700500596050720524400a400d01620003200ba1840c1c210010309548a0007079052400d154aa81c41880c50180ca480f90100355403900c01c1c04800422030f5901c6a15481d40000451b078090385000400c1812140200b84040203004407a0048502c100c4982008045500d0b04080c4112504000003440c020341d0380420030700c100710100c00060360324840c031540280810b81e801c12032607c616103d02614501d6131010142c03850f11500c40005551244a0320a034010080041803095260401051040400100070500072540d64421409004580e0040608064100d8100c03180421043c9280720441104041c5c03142f9804c908503c1c00c418407000314015a088031030414a040303032900c0d01f0702420044170815201e180c0392a040c0442c4c00c05075848840d111003 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 353085053 1250 353083803 353083807
    0x907030309090203190906050a0b01090302220e0d0309020109050402030103110d1103030d0f1d1011090901031a0a05060a03021201020f1201030c0501020102090906120f0304060225120206070602 85
    0x10045009000e1b040341d10344204400192450604806421a00b04c1c1340490b04109040e038090006854050405491303204d68908406030183c010b0a000103032080380c612040d507000c1d648100002130303059000074140c140f00362504000c1c81d85640038001280002d00c40940a003c510095a45a050211003e440c550103911068050320201000c02d2550b48880c0d40d00c00c1d6165540c2d030300d9480210a100b0030110300e1151105040f82040004184e44c1d41d00004004100d656482260303d0700c00d04104200c40400d00060034400c0150307500e003000c500d000106030b07002c0c0640b0740540020b5006842c500c2071521400000b400b032410039043d5000e101c03140b024900707c1c0440d590b003040303004061014030010781100d1000e0302000c0c100c0c1d030452600d101c40103602d6000d10706580c01404440165a16861180e50158050312511320a504400074145031200d84000014103020020300850b91950104041004603a0801000c00d10b011462017a240e0130ba0900c55500120007488550740145000380085c0345050043c078002d4 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 353086303 1250 353085053 353085091
    0xf020102072a05120706120b03120d0b090a1a0f0927060a09050f01020c030901030e0c0a090c030e190f0311030c01060501030501080114010e070504090203100302090907030309090203 80
    0x50041d00321324001e82c00d40d400003008104440e03000740c3e08000d03c0c41c0300341c0610400071000c0c08269036100c101d10b24003000d500828100d0b42d001083e841000b880741e0003000326044c2e007455802a002803160b00114403442c0100f901c1242e0700e05001a42603190700c0058540e0390540c1e03406058003002110f6001400502c500e1a15078400070030304000c8a80200c800700d81c001030300f0300300b860017501d0081c0e101c11011059005000c907158006000c4140c40c030b0203501303081c00700d00306100070011400c0400f642d040a51200740841c010407100b03603e5004414800301c544040000c080c00d2200380380d41c0c00c03071108070382c1c208a01c010700b54000405c0ea05280c0c069600c2410140416803d400d00617086402a0405440036075595804200c29a45070082500400e40d55008000075041c4070003d5640586c140151801144641c1c04100711a20600444009000d8071908544078100301034000c6820400d4070060b80700314041c4020510741900460314000f125490b841d807500d218600120311020350001041c80070700c044050991 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 353087553 1250 353086303 353086309
    0x60c03021306110f0f0c10081b030a0906020706240e0a0207050a02150307020601150c020d021203070311010f050906150409020d0b0403031a0a05090c040918030f020102072a05 77
    0x2070900c5010910107081c02c2c22110091051f00c40f64100c040d000c100d07840782403215021030030311300003030914040402c0c0359a40d69050340346000d0110310300001e02c81d52002418905111180c1d00401c2c4035130808100c8407450500c0c00d4411a90074503406060b48660041c40070400f48100740e401882200c3c815002d80b14166400e40004042a084603001ca0342e05d10000f0410500a505000d4039000d88400c56000c1000e40341010024020b852440000740606003216110080d5521000a6000c8900030030032281d842c1943c0c5801051502410030400c80d540c03c00c0a212802c2c0c81038040c0750f208400b05401020701d580c0d080341ca004000b003c440c0150704103a0303400611002d82ca5040580b911540036260385001e0313081500c1d0050880b401405a041001d10034200d040300c0390b403040b0144007224400c80340c4540c1a22403900d6003d042c4a0f503807009041c0c070f1034000402e444030b80014418150b0fa01980b5042c44076a01084103900380e02c40c0600040003601c1550f5140c4c9545003100101c2c84a402e80c81130031903034988803804 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 353088803 1250 353087553 353087563
    0x32310150908100c091403011506051809040201021906090203010204031109130b0a0f0b030d02010912050301121e023a02030a0803090a0807030903060c03021306110f 73
    0x10220000399a01400c0c40450400c01000007800d04030282009003036134840c40289005668061000e1510b0305444d03400340c03a602500411225200000101c005a56a1001402d00d038132a1901504000c1422200071051800c040f05074840e0b601138014001c01982803085106a40301e214084590355510404c4002586003440540081c40c8151004984055000104200c0100040085420180200d41840090035080c0c2c800d41090b4000c0000c1001000c40d20f036a00542045c0e4200d42e014072416500b42205503054201100f413a0203221540014000354004645600c400d0080240c0c5100280310311002a100c4c0c9400304682c4400c0e04010b070320040d66130010744165144451940a2000614806041c82e824510510070507a010a01205100c80c5d601194980030706a5000d4170400c00480010b080490500564905c15030146516684031014500070f080f245442c041079035041e00c1c0108013441366020b80f08076540742d0b40304580440760303e180003800c0315504090b1620805500981c0b0f02c65500150400c6 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 353090053 1250 353088803 353088839
    0x1303030504030b01210b1314070603050f010e0105060a03020d05131101020309010c02040b22090b1b070f06020f04080f0c031204060309020109030c08010e010c032310 73
    0x180c0c06654a2071410070040c28001030704541540c1040f001c6109041100d54804024554851305100705542ea443c442c4481c0800d0a901400070f101f90044009031030380c040340503001d03940162400c0200344c0b40c1001c0d11040d00024061403d00d08005c80050200749412000340155400c203140c094030302461622500c09840381641e03081151038505d9240010041d01c900356003480c081c284000c50410303400d40002400f84021a05c0a40581c0d56041d04203020303283d00070a0312001d04d54001c00300b2000030185040006090f0000103a4441e0700c0b980205400000607608189000c040078a0682880c050340c9030304120103100501101d03482c1c0d00304860220119640302400c0104151005400d4038001c00d002141485400f241491094201d4158004142c110724141c2d010b5541918001810210501c0181e036181155040903001200150001604c09015003000501c02300e100024003d1054018065042d05c010100340450b04c401a9500141c050007504156441540d41c80000081da0351145d40d0198400e0700f103 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 353091303 1250 353090053 353090057
    0x70f06030b0427030509030102070503310506070206030a15060504140603010e22060f02030601020d2d02010908180102250504020d0902130501051206090706050a0203130303 76
    0x441411a26281c8a9007524000101c60300080a4403002c2d20140e181000340004c06000000c00c114403980c03001d50546196a510408580e95008140501c0d8120071a00d0143d81a01c0104900b0799846030108031000100e0f40d02421540c200920382d4201701e01034100820b40350a10ba52180c2c1010981810310301c240052110f91141940c90703040007441c00201140c145071034018041000104080101550221b40c0000e8880522100f4040d010384008000b00f80300d40906080e0400703000b183c1b030701c08a9001b140540c030260203d80e100a0402c006a500410303101d046010103021044096020241c54100c1030f2480f5244000240c0d00203656603802c03190001c03402169034010240c048511942c04010a0410081078000c1002941e82036911043ca400a0300926006903000f00c2d2003410303101250800010140e00521a40440085400840080100b4800c0720b01c1490044042291514081071641c06641d01d24040c09209003030103003d68a60f44114000d004504c8100400303c1142040e6410300047c1d4030a17 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 353092553 1250 353091303 353091311
    0x290c22151706060403030c03050d231303140310080703150507110c0103020711060313060b0d0803040f0302070f0308030604060506040b2b060803040302040f05100b0c070f0603 77
    0x102400820001c0007018010705a8094024040c070b030b542e80c005643c21280c3c5480c04e008030200516040382d4600a01c3c14811005060039184c000620450b500359100301c030500500481583d40d45204100780140c8000500401d06024543c6014004139000359030004840c984400d04640e120021454912030f40d00507908004800c148800c45602801520b030001d10a01e4252107a00c03000f00041e03120100d002c2d05e50305040d80010f0302da003007110040d8100d680101c01416035840f8604080403002c0900015002c541c907501c3d00c442031607a0315058035400fa0172a01b1040080c2995a15030315112030b0418420103a09500c282000003c0c111158250180594802c22180e0380b1303402c1c0401440141e5102b50001403062109000c24400210243c0a440204202803400806c01d03048520b41036150303003c4201d5200c4241801e0000c07811081c000000c0c02264802d940030403805040d0380b0705000b00c0c0c00a403201044100701c1401000528060b402034104644d890007503400c8141d483c20384e00d12074031841e8000e001103602d0b = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 353093803 1250 353092553 353092589
    0x4080f0c030d0b04050603060109150504090807060b041e150302031921080a18020406080d1407020a17010b030a030f020f0a0c06050d0b0d0609290c22 66
    0x40c2d40a0b40405000568090006040410029480f110140103a2900301c6e82c505d0072251501040d10003400a001c0a0070412030a41c1500300445d0342e510000e815110203003042d62984450615105801415600c5518112035400220070240502881d1000c0846800c5007207001c0050b03901803080011129165188401101d854a449202c500f01001300800810741c01c0000e00c070850304a084964019504c00c0001803018407412400f0040d00345500103074020b0303e01100441c11060000324003004043d10f4403400040b01108024007118442c4010007500404a940c0070009800300c40d03604005909214004120900b42001007403900c110040c0c264002108581c2078001e990b014001c02441201c06806481e886907a42caa551510307441d44030f007070100440003e28154040c0d4540c05000303051801008001c2031900c90400101802580009030741c00c0f0b005050515102c106e807150380b001d920800d0040d6449907126500c1d200260468207005041c90b041d1040f90b111464001d080002500041e0034500c0e331540 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 353095053 1250 353093803 353093827
    0xd2f0a0515041704060509090402031e0708070801110901030513080708030f0708130b2205061b070c1503020d02121f06090e131502030603010c080105130504080f0c03 73
    0x290010796003c84400c100414082c5641c400120b455040c800d42e220034071602c0343d202183c907240840d90891480040040d104001e01400301e1401c4c00c841a41003107074a0592980e1259080f030300200040d07282c20000700a096120b50180c0c109640c0300d803090012001d1300030b01d81c42d00101030384900c0c0e081f10280c10000402c030300c4409242c921a040344d214a444011481c02884001e85e100e500303540a00010071910000d26048003544403e00107159054426082c4038940c9070043d078940d819612041011802e1031079040202c1715206036400c0342e421000c54022240b9101e00303410b035403141c2014001055000c0003407828141c520300042aa50101064070030031132600c0000c0c0902400001c1d4070b203070110f01c600d008100b883c1e071008024041c0c400c074803000c03001c0303440c0c1500c1c060b5500c1000350014440111f20481c17208001c07203580a580b00700000d030000e121b02d0300038034005c80e0307080800d002c0e481e404400068007500348803d580c48a03a100d4800c0080c9480e0000907020404070f5000820900703120341c400690004c0d061 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 353096303 1250 353095053 353095073
    0x1c0215181510030201570c0914090a0605070c081908180a081c05010e09070b03040b0f09010914100b09250302091f020d2f0a051504 58
    0x140e426180f0400080c14280210000f0814605031404d40e001400314a065200c040380c6c152070748102400300c2e01924520b412a09100a8401c0e00000762070203000c02500c0c075050500360b11a980d454080c0448003031f1036131060002c1001802c0310003000407d154003000a1303001c800420043c289110707080c0c0c8035881d1400c0181244002040701c031024400c400000d4403408002080d800c6c1d641c1c84040c2d1034071501405a04001d01c13110b40c2c403008071242818000a0300700000d07100c0340c0c0550f2045081c1c0c0d18442d1183c24880c41444180c1d4010143c000f032030005003514010404198010102c00c0001c41c82e03070320580301e4078122069132111126503040000c0c0021a9004c0f032180411458080d00d585149190030392009017030364504052002011a010344415542e40700b030b4121419080000c114042d00138000c9070410b90b1209010b21000988124003960308698011442d4240144954003090f091b10313041a40d104140040b4407c016583c030036610013400217142802195010100450203110903d868107008a0403 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 353097553 1250 353096303 353096327
    0x30301090504060f0b0105041a090405010b040302310c050d090503180f0f06030601170109021b03072301021c0504120f05180f0405091c0215181510030201 68
    0x80c5445031791019030b40c00c80103070b4088400702400b0505100c1c0205402c1c1641c8039134021a68801d00c0c06002159800d160400340c81a0b0340241c440140103a070000b00d000201f0040086c90340e0500c0c8501c00002c4041991300504c15820080c40d1503410500501e440d00281c5994980842d1141c1020074031003d45c110b00c64050080070000c95401d8400204500421000c80194014502803c0f00100054036a40544030f0310640890b00d0072810541d41c1c1d02c0c0c40c00002500010640c25100c031a10400450b928000000c2c0c5070525080b2640056954011400003151003060004d1407203950244603100752484a0030010301c3d0910030032404217191600c0d1420500200c0445001014880c1c10036000d030382158041b09840b008404c5114500c1280ca0040005042041940d20380d50f020303042100300840080086541c1100309150440c80c0c44006015a003030317072121103c0c221214901c444200043e0001c08001003401031940290135140c3d8503162a0310b400103d04211030084902e46662030400442d42d0124100001c = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 353098803 1250 353097553 353097581
    0xe1b0a06080103080c1f0f110408150912040e04020901080106062a0804031a060f0d02010c020604080105010e040b0a05010b0304030518090709090e0706020c0d03090803030109050406 80
    0x210908005024186980602025001480124100d40041010060141142982c00841e0706241c08402c0c407401502c065804040f1650a100c080e4200040038015101030313400c0c010107000c030803990344000303920f40d03c00420b02d03a020b200382c00ca00e54100700500010009000403c10322802e43c41c103401440080307101a0f02180c2e00e42c0c900201080035640c030020000510b4264000044c400c503403c4102c50328891014800340c800d07a000030340081007012020294100d510001101c0c10a0750355401009002003410411035005034841014100649c0301d40070f4855090f100416041c00c0c42d03180c84003503007103074000d03042000d00c00442024001400305103901694007004081007030003190305150003c4564080a4802824890b02040c00000c0e01c0c8400c0501103c2c0c0c0c07014141882a1410300d1006222186600c60a41c40d00d2030074005600c19200070034031005a61241d0000c10711182c580d018049508421070050f0b040010410780400d81d60001d100850090801c0440480c40d41441d08040301100c0110040d440 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 353100053 1250 353098803 353098819
    0x5270c0c03030105150705030a030c111507050702011701080105010503060a1506050d020c150109060f08030a081806012615180f100228050702040f0f0e1b 68
    0x15010380000c2240d06580c8155804c800d5000f10f48203c00280c01086d000034a140008124815800d500d41d0042c07406416641e260100c0000307200206031600050740140c9210922140028044c41c0200300a240e25441850900c0c48100c10100074072413004203030009070050751244010801841c0c01c01000b5000500d29008000b001400501841c20001e944501d00c14020080749000e110070310b0740c1c1a62904540705066401030a420000441001002d01035983d00c4c602c1c126003c90f4541c1c000d944031040e9801d0000039454041e41c0d10b01600c25400c000c2c03184400101d14211820402c3d030038420940280a803004046284160411009603218941440300e6a41e01914100300000303401000139070002005a00c8170350301c19102d140c1c14241150341e10742da00da61044c0d02d00c074940240315500800803122020b0001c0c0345000c1c43d40300003044980c0e205810002038814843c44026241c40e600401503480c0e00d0100198542902c0030703800940311040d42c0c0a02a030003086c4d85ca4200170104030030b0407103103170100c0d0550 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 353101303 1250 353100053 353100067
    0xa05010f020706140906040305030306090c040b0307120e03070506060a0b0a1710050d060f1406010503070c03110106140909030406051c0f1109040b0111030a0e030a0c0b0414041112090705270c 84
    0x190c503000042001c130402110b000001c44d0400d0701d90007045c190302901d003030b07030f54848640c201155510380c150b038024000c4481030301c0007880c010620281c0704a07407600d0ba62900280e05d00e0685056081d009000361540400040c2c001820f56141140b1084e00e512940021035100c00c145112001c031524120791112408a00c8208441603030300500b1240d00c0605402c1010714541340e82021074855a00c01c107684000d40c030700140896149005500b2940d04042201d80072203940d90a0710240c2c83c0d0150303100b4540070134418845945207801d0f09030000109081d424002440f08102010300b001c0c1d0302040c1028920200000c0d10100a050134012486074240c203007811400d200721031103e03568038481d82c5680c2c02004014559014940d4040c89103048450300241c40031a525160760f032a20b80c40e07000388611604026410400c005c1814140941025518120119030070002c00000103006103100811619460040c0700c400710f07540e601c1a81015030100082800c410380500c601440c4580310307000c1d05035080b09030288555 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 353102553 1250 353101303 353101319
    0x409020a030204021b1b0405160c08030403230a020d0309030212070204060b040e160c0302030a050a18060203090a09140610090e150a05010f020706140906040305030306090c04 77
    0x11504595042d42c1c0107070358104220200304550850f051701105030050722194401c00312800c1081d00b258100b11000c20441d1070350445c084e68841c00c07d24180c0840c0200f058000440c81d07a270013640c1e00c5402410a41400b044a80491195501d0641000b1071000c02080035080c4513410099689001c007681000c10620220b9203020f507840019003500071000c0b800280c1c000445d1182d0b0020300041c440c2c407030001d403505d07102d040c1940105011120005910841203110705114890b0208041403905a0065840c180d4a00b20441d100e03403000680000f480300d20000d003600300543c1400d04000342940d0f4003554803000d0090800500c4030f0b080e032043c0c20003070602030f04401950400c201d550304900c0840b10550782034003180d400c0d64010383c00d51041a80c5c64540c0c04101124115a4031214140350071903250040607151b00054030b040041054050059008500c01d10441340503c50795030040d1103400c80907040c42c0701c81d0005001030780241c0088400750070200502c1a5400c10b4002c0680200050480d241420b09121807 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 353103803 1250 353102553 353102569
    0xe030607020c040b0319050309151303020105130e10030501110f0d0209041404060519090b070f02011503061a010503070203161a0906040c15020c01080615030f010f05040902 76
    0x200070f12a55132900e03803111682e010090301900b00024150f501d603819850510549940101c0005401034003007100540040d039105003200c1c00d841e03400c40d024500070700b5a001111035800881d04540c48a41050002c2201c50322445620301c02d4812a600d801e00e50b0841c5015400e45000d060300c02100b43d0144010400e000000301079030003880200c800181ca60f54010001005044088150802d4619107400e100a001c0b442d040984188a403400302031102080000980444541c0e040140a0341c0221b0080b1b420302e441041215034003c031900c008240d442c1e040d07403102c1c01c090055104980c0f580d61a5401a00b062008a610034545000d0034454214a0800d4010b500c80c848c00000202d41460780414408101d09925203441ea0049401c000486150080c4002e5a41e917003907a05071580b41c1081400110303e80f000c0d0348440c07004a0355010f0a12012440019240c1c95000380c0388662102d07072078070110b8002030440044c510030340082c2c02a456651604451040c00350702500024000c504010a090141c1c40b0001 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 353105053 1250 353103803 353103823
    0x708181009061206170f0d0801030201140705010b0a061d03070b0405280b0703120c050d0911100c020111030c06160c0f0602030105210d0318210e03060702 68
    0x30440f40140000304554014040c0d504500b03110240038038080000400050006625080c080031580c0300654100305681c1c24a00740700003400101005141c1e0081020a4040d05240744158008034085980304005961070185800c504009645a00740c0741ca010003a01c4a042e1003001940689444e90516015103594030485c01014014002d1310200d4150b81c0044c0710050050020f5810890134940f12640e249680e800b2220170390002d4900f030403000d1000e80300c0c41503400d014000e803100c03450980006940b07030180070752074030030356100240c1d0840e00b0700c03a100d03108000c800140c5039850a07080ca203548005841d00822800c038895035481849040c907034080000b060b0340c0000302c05d0b62600d00090461313004c41c2c800d145c0d048010103540c08a0031005c1084450307000f070b5060303850846005486507603100e4500c002803002028102c0550164081c4582c1c0e078000c1e40325464007011140e5500c000c0002e0340f1002980c040000d18800b10035070801f101e001c120342c460030340d00c2d1529044000e460342d030a00c001c000f551081284 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 353106303 1250 353105053 353105057
    0x3060a0b0313060902210c040e031305010e0d02030703080702100503090d05090d050a14010506033025021e0306040b060105041802031f060801060302030703020708070818100906 78
    0x41c41c40f0295501c0602c0b03806c1c000d5245803002c481105440215443d0400d20340e0280c092414910490000b5074080140c41d07442203040ca444441c68601801140c1c080100419a80c1125100a03ca000750320b041c0030b810090b5001c8c00707900e5075031800c504c10300c0f80d40700c07500040d1010000e0500c284800d0078804201807803401d0703a0389481034a640a80c0002510700030b81d850010414850384c883d0904102c070500000191042980c000c100aa907010107240e1074500050b10000e10070780340c9043c2d20151400c44101c10101d048000e42c1820b141545a80403101b800206210900d00c027140038140440ca0559402002c2201c0b0585c00c400c051044c00c0880d82e13503240a0002012001c0300000110164420410344c1d00030000540c0900910120740b0001000390f005540c00c5039010b20800c5000aa00c180085070302c111903465803098a02e80c40c020003200250405081075041503002c200c09808030310600050803400340111001596000d07007a40c004102c13101700e503502d4000d00c20310700d103620000c0c1c218411000300c035554 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 353107553 1250 353106303 353106311
    0xf08010623041d16051903022101021c0507020309060d0903020f01020a05041a0406170c07021306060f140f070311060a090c06090b09062203050303060a0b031306 71
    0x1c000090103000c024121164402500c07100e030009540000d0190740340050002d03220506a10303501440070188240e4405100040f04c00010001420400c0380f00c0c03144002010346200c08098200c025083e40e101000050110b0b01106510700b612a0a100701508020b0900086180c2044107000c12594010b03462401d4901e0b0391640300078181402802241c4030000004021036607002201006030040d00140903500303480b4010038061030984807404c215400d403007150f114132304442d10060100c1d04540300100003208060050080c5401600c454111588a04480320049030450400e54018090301c2e0b001c20001c1000b082045009001e00a02c00300c0300b41d40b088484195990300e0504090710b00a094908800c018401c03c0c04101440c41283c0c86003103001e204001c0041c00554030b01080316807466900030241800b00400064609141c010010300c40c15401003220200f400008014103030540e219801910180c00000401c6807900e00b12145901414561000c64254140065214034200d9803a100621442ea1 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 353108803 1250 353107553 353107619
    0x603110a33020a020414100b030402030c0f0307080601090228090e0a090b090d1403070905040c0905031006060207081204090203070c05070b0a030b01030920061308070f080106 77
    0x1007030125a043c250054002e00180b008210603500c024011a403030300c030f014450500820031130881400c40380180c0d0014001e0034400d0641d0200020704016028190340f5200c4c1c0341000409080500c1a00e0007000403640050729464441c61891501c015000912558101500020201d50b005040c100641d00a60103a01041d590b49013003800401349180098800580402004426240011146483c001c1959065040000712800780e11500040c1e03042c1001c03c1b6041010703c2035040681c40340303551160301c2c81c1148080b0b65903004a400c0070100002d0301341443e00c41105007c0903404009a40041000303c005011000d40342258189900a90085078101500000440c116a11608942ca011500401522135813541c1301e007900c80990001d400701c00428101174004206600034414000780b103400c25400280c00707844c0300d60382d0f1080710762100f2154440c409000c0b8803900310b4910000f03405405004020314030207041c410074007541650366000d01c00c00d81c1040340034040c0409014407a50020840340750880e20b110 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 353110053 1250 353108803 353108807
    0x13121515090f1508060415020901050d020304050f0c0603130809040b06130303030b060316210f060302090a0606020c0105070602040b03040b06040f0911011209060603110a33 76
    0x903941c40001d8160034040c2200742c40c110b030741c40300440380386508031821007556401400da150181110003409600500d001e6500b080110f070010b0810300c105161291800001001c01c030100e130020340f02904e01c0d600c00141c03007248120401103124500411180c0318118504140b04046c28205418014111600800d480508ac1c40c1c6800c114ac4206000305200d440b01044602c00d0a80111480180d0000b802c0c1507410301c0e01e05209088900603040b42200401c14100c44005440b52101080403078242d115075406100003441d5031180c402c282c0650080421a10300d54010032552071800b4040442d0f491500b01c08004090300001c0c004861a02820503030340718030050a04000038003942e807000c100c03200300200b04820026100200303032140904690411510540504130402c84203040c10050072500d010011280c0e070760090070741c42c4a85810a40114100c01170365a000151200ca0748202c4580b52080c1c0400300358940880090b019110641000644800580c90350407150104254401c5450f086421003032418 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 353111303 1250 353110053 353110091
    0x9030304060908060a1e2007120f0e060714100e0105010602070e0c0a0f050f0c06010f0b2b0e0109050307020102010b12190f1a09010e03070b011406070c030305131215 73
    0x291f14183c80c0c9468140ea8107101c813001031081c129200141141c1850041c26003d8591440304400160801c0e080000c01d0361400d00000e032070450321509204280308500002c11a0046d00b02c004000c4001195552511030068030305112a0000350301c81c02c2c1d02041010750003c890540d84559420300c1d08103509202e00f00c0644040c8144442d0007032400c40091030b502a8100040c00c0e80c100c403d40500ea0032604c0c0e40c0c1c0d80c01086800f40001d020076400003410501080500d900120284211100c0d0004a80c010841c0d15403c4031505c0c20f041b10305801c00b0034103e05541c0c0a119605900700700351031000c1c101c0741981841d916040c0c84040710902039034544e80744042c030600c0b4640500441c0d1202c441e85041000980c51003070380c0700c2240c0e4080550f08000e00da004005001c8242e90020342d03c00d03040b42d113690806a110110704460700405030001e00500c58840418600e95180c80210b00035160655185015000350012031440c3e00403404c41c04500e19101c000444004424014503c03042c400540741a191240c07041c0e02c = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 353112553 1250 353111303 353111351
    0x17060a030f050109050d0906050307081803040f0312050301180f090f14120f09060d0f1103100f06080408090103150b0d0e01140112060209030304060908060a1e 70
    0x15a00501c240d004204055100000050043c02240e0b012214550100e80701505405130100240701800411285400744040503040101d2034203000315007403000305417851130b00582d0180c00c0d480310505003041403204d10700790845441d03079519009140d0346c1006052036098604a0b1801381c4550307260400d0181145a034001340d030250f40100300304c03920080c504000450800c1c50010100c0341c042c0030b04c24030514850504075100481c558846908140d0b10b031040016a4220b60070031110b490301c0d008811959507503803280f210954003c3c08000d440b801c0c00c034020294088a134004140b1200c0311a401d00c00c135030304840d03035951003a8071042c401c1d500c06416004a002d8114441c01d001c511860b444003049160701c18000e441d00c3c52a01204010b17044021030418261014105220b1800d014200140070241d148400200940c0c00fa0030054a440000e0f000b1902d1a8007950141c0005282440140f00f40715060240d2a0018503903001881050f8100c80990b003110841603040d40031999803c000eaa50514440c004084 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 353113803 1250 353112553 353112563
    0x7031e1809060306050906040201020c040b0f030f010c1b1e0305090405150324010e0c0408071509060f02100209030f0a0f03020d1805011805040207060b01020c010c0317060a03 77
    0x1200d90701d820450240140340800c80c0c0e103034180b800103020410000b4170302c0e10840e0164018a0849507144c2444010080c061030310b90803420020454069890404c054400b0025580000a51269502c0003c0000700c140d440c2e120940d1103505a100401c02d00d117220110000008207100c81c0482c13500d0280c8091003520740c82c9402c182441c08006400b2035080d405a01d141085d01920390f1510889800c0d07480c0500000320083c150701c071030014852039000240302c42d40000710003559403078541c5940c0302c0c82c9410415404081e105070125200344690b07510007072100042445c0c2c02d10004c034040b0650013035110382c215210100d516502080c0340d003966908000360075040c1c0d003044c1a51019030072030070920156500300d0b2080e009840f42c4118181110310858070500c3c454100e1060721803840c1007200440340582c0586100340000b115020108441d912440281505440349000103481c13020f66002908040508043d10b043c010b8800044d0f01080c0c2100001c400c0b020640f0000381d2954841d40054040e00c90f540000c2c00b = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 353115053 1250 353113803 353113847
    0x5040b0d0e0a0302160b0418021b070f050a0e09060a0f061805041b05030a03030c0302210601020607090b0d0b15040f0f0905070c060b12100c08060607031e 68
    0x205150300450000c072001d0785c60410562075a00d6000e00b00d0607109034804da48012200c0a000c0742d0318203181d400790000030910b00321184560032028865140c80a2504032010541d000117003003002e440d00403844c4004200c090a41000c0746448250390b0313244c40005002c56420b030384821b04600650300992000001e03100c040707800c859a5002d0350317400005020803202158081301c4000001e1003030107440081c2c03048070380080040c2000201694220041c000140034402850340a200c0401c200100c441e8a600140340309118044918010000900d41500600403000740400140f040c406207000f1000c84d40380c00703001d40c2c005ca09088000d000c40d41c01c1c1c103044418050003101080208070328041552140480f00341c0c0c0316030003d2548a95171041210429240360012400d0000881c001440075005040f6800b030040418503058908218103040c03542c03075075007026810b80e11240080100e07041200150030500580e00181051501e650103416040c0160b0b040501c1d0105200d01007805114620760700c1c003e005130000c44 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 353116303 1250 353115053 353115073
    0x4200309030414060403050a03180b0706240e15060706060b071a01050d02311b110a0b10092901020c130b0604030b04150e0d05040b0d0e 60
    0x39480390018041c11000001d485048919442e10005507006e407034100010b0480c2038030701d59007521114481002240c294045e903000003260588400a04041d82c091100031400341c40241c4c00110f4084061034074110321103003023411300070603845406082c0d00c130729000100301100985900050650141480007800582000c2003c034102c072a50000c4c0c004070744908420341102038001051500d001c003d000e00382d082022046504058541500c512591100141c0182070341d019100d007140582c0e483c950100b030b540c0c0d1100c3d60388030580405540310b4000c44480ca4095a00f8a00b00007940d102c244505003d030000100c5008a0803006425010100130034000504000d00000f815184003c0104200c5c03540b05d00a192032040d04550000c200c50300c1c4050006d040450744d030f11640860000f0b0040b90384540d009542440044001205054650b025a020300401c0b4072103401420540161440c0940e0259035420002b442d5241c2a0000c050b1802d554285e00c0d481e490b6448240844018443e12510021501c00c00700c1078 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 353117553 1250 353116303 353116321
    0x9020f0f0301081606020a11090a060503030316090b0703050d05070905030f0c0108010b0a0806010f02100f020d0b03010b0904140c060d0e0708010e151e090d020d140306042003 77
    0x1d0300004070a0256080595517900041e80c031070f805400050035201c001e1803003407603500c0c1c14440d6a600c4500c01350005015521000420310710342044802d040300c110f50300c03410703049540c1160b2000f00030001810b2040c50100f9640d0028843c0c00b45114400d10306480d5008107004501407030700d10b8050000601120780020380d1800c0315a0320b900c0b400403280450415400440e90841841c100c1d903403001e058071000310585500b00110b650703440e828002d0045001c0c550174810000040c0c0900c00000e40c1d07007040036883d0034000320503808a070800d890b158441e0785890a40491601c81140f810307409a04402560940c2079103070041424444480b00b0280e114100103a40700c00207040c1e0780300c0d9080c03051250840d0380c5c064503131100c14226070016331010520390040c0c2d0b030708031558202030660347e0108103400d0035002c030820081030010f1514150f804801d01d400840b0075040c0541d04209450001a5601e0f20108805021a000c001c1c0d10014107214000c0d0384441e0741c0c03117a40040c0718624a40b500448a0b455492400c00d80c4 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 353118803 1250 353117553 353117563
    0x30203041502061b0703090306020f0d1515050c070806160305070903020f210304060f1b0c1403010b150d0b030a050d052503090302181009020f0f030108 67
    0x1d0031601c1903545415a010318400240d8912070030074107800104110350150482c00d56009118110200100e2203c0031001034482e00280450101185d481d9440e05120602034045d15400042400c10314201d24081100006c0840c000044a0071410b0450781c0c0d540e03600303084d0304060581c2c101110920440c400d020390410f50481c503070282e1070a95070030891a1107080049a03072202600c00694010b0464444008501c0c00401c01c0d11714500c1403040703a06941019a525007180c0244d030244d0045103c50185c114815004288110b42000c4140e000d07508080301d5890002107405070181c18281401d034010307480e00e600c007540b0152019200621311024545081500380c1d0982c040480c80303541e9030421100c407405040028481220950010180c1220030341c0c6901220560040c645c4050011542181e070b5104004200c124255103001742e603100074590a40c01403064561070b01d07660204005291080051682d251814a02561040c0001503661b600072200c0d6042d50003109581c50801c14004000642e00e030f40092 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 353120053 1250 353118803 353118809
    0x9080703030509040e1b06030c0409050f012606041b031e020f010c08160201090b030c03010e01141810090e010e060703090b13050712080309010e0c010e0405060f04050403020304 78
    0x9060100080d0418915102e0309a800074018041c0ea403036800d11b551078903002440d880749602c0d19503424075075201c44e840b05441f020b41e0742c07490304403098005101c5a280780d81100c40c0c00800540b0340b948401c40c05006560380900410140ca0a101d02e4010016002c149681000854002c0c4910300d81400b5606100114141e400040307208541d40c000c0b081d095400781070748900d82d5070440406400c2a00044a0002c06410320000301e0400400580105007610402c020313600403000018850f8803076040c110200010403060b000081700d88a4003070111055900c10080e20b109041900315a0001c0e205c003540d4180a003166002000c003542461080d07031100c401548040c80d1103a980f42102c06070749480d0000d42c00c445503c48058002914000000c2e10345c00d402c020700c402e10380300b0400c40d2081c5039580c1c10080c0d005c40207039045800020000034050b40d41824052064000c1541c07001d000f0700c030307150310001e8150f020311340009001c1d40c0c48200182d6150364006a5040f040001303032092015140c60329000b501c0340e2081c0 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 353121303 1250 353120053 353120059
    0x6020309040c1425050a050a0b01091505010c050f060a09030206010b090d0210050405090c040518060102101a030109121b0206030703050c090a081b04050405030a0f09080703030509 79
    0x4002c500c00300d4420040038000981c80c0143c0c9103010800301805075042084501c0b042049555644000043e0040250f481860702a5001d03022501c814500f0201202040c2d02403c2c001c0d081080e8200c07443c1400300c0b0041114002d003407640300100c6d145450307810013007207105202450042c94100110841076800501101748654242c89aa07a220800101180907050401e90000c4200009000509050581103c0111b590800c0f43c20300340d40d1000111701110446800b54003541c042010841030400740514111103440c031800307142a18041000275030343c90050000e0004180c943c2c010025210401192150502028000b17102c25161800c000081c180b004941d58005000000380d56a00304501100f10b0359a1341c0181658515110000200e014080141000c0d00302c001c1001503d0090382c0e5294030a000b08891000f80c451840c5242c2050040301d100d085040c042c138106030410001980204c1261071a11150030031800306240c5c800c1c2215200daaa41294510380300d16400071003416009070103031400240403 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 353122553 1250 353121303 353121311
    0x10b0405090f011113050402090a081204180c140a0c0f200102072403060b031306050702032a15072703020d060f021c05041103010e0703030e190602030904 68
    0x1041608144604603e44441d15003560060000d0300d088e40003000c1c400c0340100014802d545410b983c500b03041c0c8601c0d002c00f1900b00010204070a420b00080c200940188000030003d00307030003041c060000c0701c0890441740d5003030380010b1028440c3d01510f0881040b039003005200d100240300d0710388041c09091130411801c4100c2e40000c034000c150300c009219800c1d1501500140c0c0c7d1509141450b40503401d44420380381c00d1544076080441d92981201c055032089400c1d10f141d00c210040d90070700c3d00480300044c2080d01150010440a9210a10403407100c004481070207002c00c401d01050655403d207035040007024198010917003488955a8801d114140400340c540740c6a00e6800417141c00c0c0b1000c6280d03c002034200c0650300c80703400484c0445e44500040c001140c0003600d0200c5984003c8c20003402413000c01105940d4000380001c4c0940340070f04045045041c1e00820040034460a10307540ca80f901d200080c02c000500b031210006454812554644258400d00343d03010b00c0e02d601020303450390000e0b4440e6018070b20b0 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 353123803 1250 353122553 353122571
    0x170a020f0c10051b03270f04021602090a0204050603180c06040f03080a020703060608012906030103120c06090b0f0f040803190b1002032107021c02010b0405090f01 72
    0x21010200a5060b09511203a1611603044401e4000c0e0480c0f580400144c0820310804000c891107141e0240003442d154040c4c08103100c1c000070014440c03074845856024a01c1401020b0890201c105c1c0e480d40e02da012207154505641c3d4015110180c031a94101039000003020050040c9051900080c1049006040c20b0700d080810306000d20145015512484580b600702c076404002060303c04000700071f80c944501c1500e00f0140c480d04c07042d040d40c1c01c40e4400328281e0b649101e15200580700c00f0b840d061041c08400c0803498940500c00050480c04103000191071035221490411040d4050000381803000c2e40800180040c10550501c00401141101c980f420700b4081000241741c07481403c9071520440d880a8410709603198881d42c4200f000b040b2101017002c030303525200240c056036445100b21112025900440d914003201c804100d091218038442e61001c85080280041c2c6600403508241d01d103008401c11100e12080c4800300d0142c8803055210390024a03010a00c1100340010071500c0e01000000024422119 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 353125053 1250 353123803 353123809
    0x12090b092b06060e0c071505090a240c0516080f040f0305060411091003031d0405011403010606050c0a030c15020c0106170309013501060c020a0914040609170a020f0c 73
    0x114446c001804c40000c0007400c41889110351000e50016071050494140c001240e48003d400071080340111b00c034140307010603007107581ca0500662200c1c1e0f55520f031a0b0b0030580101c48104140f42c2c412001003a071400882c1640004ca490b4003030300c000f440c84040030399200c0d51364146a6200c0344291410b0f030b41c400052034200803604040209600404002c002e00c0346203031968404842d00005d16051159600c00703050702c800a6519409004e002e0040c001d510b50810f200c0b6000c00d800c4a4066200740140101405150b01d4503801045840c81250141810490781c41145031091046111501120702c0c2880410300d500c04a00c1584040c090780c44900c688014450121482640d0780103c600080c001030700d07000020080c01c803010811044058008882022040c800b0325440c0c0c0ca03000340c12090006000385282ca040d45007900c0322000a141107541000340780c0101f08450342c6000d001300301404d055140c0f80410200a01344280c544902a104c00140c1c88a0911310001e44921603524003564038440d0b8040da02d4289 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 353126303 1250 353125053 353125057
    0x6040903110a210305130b09070503010905010b040b0d0f06020a0e060d09061d070909080c01020412050709110904090213111c05060a0632030412090b092b06060e0c 72
    0x40032402d00600c5550203588087c2c079144020078a4003d401400740000c1c0703a071030034010b0344243d40c4920700110707102a003001840100c500b005102d80c426089142c1d20404140601032101c5011f030000b6001d86e0b01c0c00c21000582d0a40107444045801010008807140321480950000c207000744241ea05002401145410748102040c444000c0c1698200c1c1b1402c21945c141503000c0c1442d51710803000c20b8103100100c4502822071308280d000d640000001c1030320301c1c2080b90600c10302020b40b0040700201702c5002006131041041c000d9000c15402950780c0c62000c4150340e603041e40c0440080013504140814880044204019001101241007140c0098001c1079218007a0140510884c0c0240800314414030f024002c9401180b83c0c1c00e450200c01d1040d03003540030909450540800c0c50001e04005550341007501d00080c40540070151a01001803c11f024480703402c4400803114016800c407180501e0301104207102c0c14860f00d00e000280c96049004118080107401e03001b5404588511526040584e41c502c410f0181d8 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 353127553 1250 353126303 353126311
    0x30b03060403200c06070b0f0c1c0b220e0d020a0213020f0403081315110705060901030e070816060f080402190312020c13090201050306040903110a210305 68
    0x1c103044100c041285241a12003004241c409001c584c185003e00d40490030780e60048009403000b450000801c1000300044c40100c4e04644072000c40751034540300c9000b91150001030381c40d9012260b2682628500c0da07403460445017410209040d002000c1034080d18160051400c0e0b08050918091101c601680307174008503039075200710b40103410343d174146540100b4100294803d1410b6001c651043c030012001c540070f1805003420072008124440c125061030890000398050b00c030120100f294003030b003050240b8004200310085038415608aa140c2141000590140401608183c0940304100c3c3c00210b6240c0010540c081106518280c03407100d031a03900445940403207001406c0070488000c0410010b09081780400009009030b42103001c42a10b83c1e949600c07841c901d8a5800043e4402c103003c40462603d82c42040150382d554030708108003c0d00e40e0000e00a0300005004c0303032296580340ba40809150180f140700d586800f105003030320000c15076071a014030448450f140c1c1085030070381c0056070340b400c41c001e220752805 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 353128803 1250 353127553 353127557
    0xa44060f0606280207080d11070f1203030506040b0d0c030209010b270114030406051e060d0f0804030c06110d020105060a090b0111031b15060d33020a030b03060403 72
    0x440031142009422a43c540c8204821442540400111601c06101c08102135815940e0410391640850445140c1519030b0800d0001100e070000070006030703140c01500241140d250a02123080d0f65107000050040050003011034100c510030b01d200041214001155058900c2143c2c90405a41c0f10f004a400034019141c041515400049011101c4040f4141100d602e04c4e05150500301d4081d070081a6003030741c00560b011a100ca07105c8062140f4091307560f014107851940e00071066018a09070001800c001d00c0e4100241016089180d200140003011045074051600b1000c1522110b0f07480034010000302140340007840394007511400e242c07001e10602402d4002c03440242410801c500b03014140c4000c0002d00c08441c14440308003122004507100740060100d90f8858201c11541041c04218903060941c8106032528100c4000200002c958907a0b0a0000d1580c125651241514010b00385015101c0001841c021404400c03d0340f0241200036002418028441c0d42d0500841402c10107040e9922810b56000340 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 353130053 1250 353128803 353128837
    0xe0a09021e130501200d0e242506020a050c10020408122802060105010e0609300f0c0a080c010c020909070504020f04060e0a44060f0606 60
    0x8050342c800c85500d21481c4403c1740c0c1c840c0106520300a14645000d8a442c0000b00c0d0f180c02c0c1400240c80c1900f1104100404180d01c07045155201c90b402555218118682e01c80340500c0c080080d4203030841941189495002004540c1d4041c0c1c00750252654104500382c0039580f281040780c01d100440f5000396803c9895280082c240301010030101031054011750485103203141790102d0030503040301c1d41502c1d0300c3c0180e01d5005082503504010005152441d00c000950141c0030030860701d081512000e07140100c60740d111607030500a07651101c288850030306a50380320303100c0c0c4100b40307500c1580280450081240031049680f4a1442d9491162030b80f110582e2a40038041020198614090b00304445c400707034000e01034001e41300d03500d03151800a0101c3e0021b000c004103c003400716003444110340188400c2903d0f10304441c0c181030702e86081c05c003040e03072884155a803944803078001131200002215032405601032104d07007400743d100c0c0440383d038a50794803822a2003469140600010581300c0c1400c1d02164800350390654080 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 353131303 1250 353130053 353130059
    0x304020f0618040b120109030806030c030706050d021308100c0e09010602061308130f03060c0513030305070c090212060a0501030606050909090a0b040309031a07050702040b010e0a09021e13 83
    0x40028880b140c28075800601c0f4607000c0c1d07490117080c811032000c03a12a03160b8280702c6c107080d01850704e0418500000c038020b601c10f040910000f03402c00150ba82c0404e00210141e5582c1d0204a10100780545034012501c91155030140345000702140c100c001c095800d66641002c0d2039112040003141d8200380704030b0001d0f81010303001c907149810190b5110406800746040034a8400c44030304200a41007264000740d85880d551405004200700ca01404450400303e20744242440d003001c00c0b545041c50144401002e0100c000390840c01c000381442c00c0001490040821501c0303540e1000c6000d84502c003121000d10500000300c5c00304841d8040e20622040c1e40b004d94806e0b0900c102c0354184058a0005003502000f032040000441c0052450002c45105521035070355580784515500d802c070041d08441e4291100036140b1820041c1c1c80e42d101c015111015011900403072030703240300001642d0310ba0040e101180c1021070b1241c04544028160014506003080460502c181050045110070500032242c0081c4c503c3d55842e010 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 353132553 1250 353131303 353131309
    0x14010b070c080304080106060206090606010e01080703140f04060f060b160c0e04080903210d0f1b0207080f0a1a0405071809060c05030709061d0a03080304020f0618 72
    0x500186840303085078881c0d0315102c1d19400e1030358101d03600c80b500c075039154081400b065605000c030603041954903008080314208500042c10b800ca845980d64100119040001d01c014070941000680600809503610315040c00c800c0c4100403202100c060701c01509016003581c2c01c0c0154480c1c44229043d581215040c0517400c07024841031280c203a0240c40c826000000032a00c10b0680b8401c0b8050381c41007401c1075817028214141401e00c43c0c0b2001c100c40c200021004d42100d05489070880b0a915940e900014044140210000041c92042c0e05103110205050b111000e05400182074004d0754440030440e001084a1024160f6440c40ca2000812152240e441a00b4901801d80423980103440b03141943e45064487d9144103241040740c404c0000c3ca51926080414012244103450700c0c00c00501d0b0442c43c510300ba6038003030054030852050b402040181034512002c42110310614501c0540104000e4640360750313050191303541d0804d43d410b0788550481565104c03103242075411225000c1800f400c03064110014010 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 353133803 1250 353132553 353132557
    0x1e0f020d0f11152703160c082509020a020c0f040612030c02090703050411090a0b0a090207110609011e0903020919050708060f0d08070605160f0314010b 67
    0x26880500c050002110b000d581c050003d010b0045038400300807064500103e002d490114818220400040340c00300d22100c40704040101c0780c81d0050600c8010818425203000400c180c1a540501414003c0d1006121b4502002c44041c041c9050852403104640d00c901441c8102e2103017901200250b4400c0c122900d4a041040c0a241291001000002d800e551840c920012500b15141100000d16003050300c0300310700e0040c0c49990080c03401d2400304a90300d082c4d620b040c1c20200c0602100d1242500100080714482c05800c00594030002500c41035100c0c0d52503c5280180d006104115050707681c2c191240002d0400d60706844c40e0180503034491618818600c0c003072074211b61031481081081504403010025845000420380280c482c80c010600e0043d48442e10003c582014012a0811103050300f401035690381c078140c0000801c8100c50f8034001401c2c13441c00c0c03002231154000003400c0b5420a0200074007507030401c0a050020000d511440031001060b01d04500f202c0d082c1c4d240041c0d0300e1070000184910718034500 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 353135053 1250 353133803 353133827
    0xf0e120c09041401050c0703031803080105060903011b020d020c03010b0a0510021903090315050f1612110901140c100506030a0c09020a0905010915050903030f03071e0f020d 76
    0x2803103c0301162a28820707007510022581d400080300d0029611040640c98800c401d02c0d0140348071000d8400b0b6050f135005060200c103202d0141708060103d28801180d6007984505060184000315a20710003000300080d4540380d483c52500054014554010788500381070103000d01c0584010443d80100b03042c03008014050519150802c11803140306c4c6a004cac00c40c1d000550104171800303919551f181030714601c0d08030307107002030304844410850900c02400b070500d0701c0d2410359421003410402c00e051885038140403031305035603041240c0209038113180620310720f038408400910805000b0380e140380c600400c0d03034404d46880c1f0034801c080381c06601c0041c1d846030100c20369000c640c0040004065502100b0036441e41c0c02d02180603040300740c9080e400204c0404440c1c0000248000303000030300b480c40e10989003a149120144104010b40e05002000405403c0b5a0f410720482d0581750b982d0b2503140d202e042400b0020403e138210010b040c811b0100d613081d0001035000312001e00005103035900924600e1800603044030301e2104a5 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 353136303 1250 353135053 353135063
    0x60907020a0609110a060e0d02100e061b010b0d0807030e0a1502100605010e130b0102070b030a020a0906030e1908040f0305060f0a09050a0816120f0e120c0904 70
    0x10405200054450141d83d040742d008442507907910103644104200080c44d41d01c541b0038070103040c0e040002a1120500c2400e00c54040303c0340780c91003036070360700507107558803500600b681c40b000c0020201c0440c1094400e12119001000c02040440e90100038800c081e500c1010107050f550042c4601d0703000900c42c6d05130308103602001d40304420307042c0c1d60a0319480040000f2059000b40c2c10400c0d001000e8409485000020f02003440d0011603044124003045803800c0744030a5410407500c0d900840456402000314100609000958a03a2031400340071440080d08614000400118a10030009040e07105c1c2c0030b000c40345140c6201404161103c101600e07803a00703800300c08446180d1f0500001aa0384d4031040150300440c003c41c040c00c1c6500d801005000d021000400c0100703041e10740601000800d60004d59025a03a6100f580b40b542c90036400c030711400c0c614010030000c0500c65070400080b10039510130220010003055440325510032040f041002410f00e5608c80c035407034a9000040c42c0c4451314107401080c0e0003502030 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 353137553 1250 353136303 353136313
    0x311060f03070206090609010b0a1e050d050304030b0c030106120207031101050c090301150b1207110106030305090f042a051309060609080304080c0d080903010501060e0a09060e06090702 82
    0x6420030125030402c4400401607085601081042d0806108031544001120001c102c0c5103e0400015040601030080b0400b442909904c01009024101e5010140c00020003604810342c00b440d106940c0e6010303000031500300750b546c00407500c005840c0c0140d038107907001d40d110988001c1c841c1c40700c50000e4200110076002c210300d00754282e509032001c2c0b0038070b4016480001100c2d0b03141c03511030605003547c0c04880a4612940821010045512003c0544803018045121601c681d1620a0112030f00074220080c07142c1e07546003060000070580c1020003000c54500513140c00d03040d01c602c481000121904401c5456903a14400400c980210030740480040314412400d006082c100c0441d21841c061105410010b041c1c0e82d1000188186500142408014103208004600e00790400c3d40503901d03649601d01e16402854520a240c0810000b24182d403011800a0300030007843d030f034441c001400b5249a542d140e025000c1c062010400c1032040c0502400c0d00c8803182441d9942d104c0074203000700c4280040019045000b8 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 353138803 1250 353137553 353137567
    0x30b04060f05030c1f081e070906030b060c15060402070c0b0307030b1c020f0609040c080a0c0f02061302010e03070303050309060f04030f1110060902030a2301031106 73
    0x558030416015100da01d01142a1505003000d16180c0180c03460094880d200810b030b0303007020061149040d114402903160a2902d91124a001040680400843c49a0710803130000c10240c02d5116050030100e031041d9409000799040a000e018031072050000c4081203070000000c4400c405244075031180c108001a200601d01841d0351103600b003c03907030f54100341c042440000c02d0010880e80350041220720b1004a4000058259a000306920b0481c5540300901900002040d50000e40c1d0300e20990340c151602400900c24040a040f00078003900b0300321070761028540ba00d0065504076100d8002d401c00109190020007942d1500c00c4c240b100711140030f20032810060f0555940300c80b52420300038100114480c1c1c80d15a00c904159444a050050081c603007100c40803240c04000c0466804985c00c071641d610350820f480d007108408401401e00010441d0381000300d040010020b42004654021840784441042c10040c10008804800010071071840c0607114244040040c008581450811003400000801d081c2c80c00c41 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 353140053 1250 353138803 353138809
    0x504080405031609050f010506162f041505010f110304051c15051302010804050a0206130e090f03040b03090a0501090f02010e1002030d02090103060f030506100806090a080a030b 78
    0x110f01c0754226a00d890008040000804a0040d90341080090344a40215070501020418900690b801c00340c0d07031440d50f841c0c8024061040301c54500150303513122012100c00301c007030360326554103078041d00304d0155140800521110346006811001e40310b0595900411080742c92085410345400300820032140000c000004107030341d400c203e00201c03204031420141955541e08107404c100d0140340c000c001351424807040080e11403811034909020b5a090800100d607440f030b03092051030448901c00c025000f4000168155044481501900840e101038000e117800c0c1d90341020311916048004d4244170a0781c0300344030038403030241d007a40910780c45105c0c00200d40a40320701d82c481d83d007941c41800d010f59540c03d00c00e07400c0065582c0701644181e030800c25a61000c1070080c40100070350342c2c0b048100c100c82560b4003145c404480c0e1700c41d0b00041d0041000d1405600c0e069140d05103140c0324902035813109180c95100c0c000042007140421594840d0302103c014040701c0d03000d40c49064280d48150700c00010142e8a0b0030f87c8500ba6 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 353141303 1250 353140053 353140063
    0x14010f270f0e0405060c0408070b0d0f0501030501050610030902030c270c030a11090d0b06040603020307090e0607020601140d14061f081f0b0d08070f030909060602030904050408040503 81
    0x801d0b150602e01036403d003420300038100040506000340c1a41c1c10030091002c0346001520b40100e0b40c16155459503500c031071031510024003540d80c0e9401d005081000000c180a015000103003d031008960902810b824160150125210090000c2d01600003819400b02840c001100c078100741d0341c0c0ba00300c1301e4909101400900861045461a14962001c814030180c880d240c070601c104282010701083c54021500002042c08400c80c400801000345c141c00502c541c0c4580d00403900455010303044070000c0d0744030700b0904050314070900c0110182c0328000005401c40e02c0000c180781266000d07e1181150030102c4140f102c510188001a592082002020386403e03034200121842022042852222001c6442001d00e140256900002d00b9500c407102140c404005114104031550040800083c002c01c05404550003100744007014144d180040341c20700034419440034507223070755100356189107040e40c0b202c18510440c2c000e806820010703401400702440d2414603038060764116024405003400d2584c0d900003c0e10304 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 353142553 1250 353141303 353141309
    0x512011827030201050105011103340b16090315050421020c01020606030d020709021e030c0d14010e01140307080118030201060b0f070f0c080105070914010f270f 71
    0x24458201e6074002d0541c20320445003d001c0134a4440c0014080140540c0d0368083c00164410070b1fa80016032940d41c18102c00000c4042140c103280d8402c001c501d040c01ca80c000f0040720b60a103480307032000c00840060700c21050031090700e600809c80c4565000e0320030341c50011300e8014004c982d00040d20381040c0810310741405401c2000416030040010700d0240c00028100380014003c94002d41c40b00004d00002c0390040703182015101507681c01615000c2169500000d445004039003100100000f00348003010b1138a07801401241c00d409014003c8046600700700090340c50900c078504c00d0700840001480f07480b000c0a50088644d000604450707070280c03905035213803c503403071418085920110403210004060f02806035400810001c02614200320a82c41e0342c14207031007103800040003001d01c86074810801c04404088000781074008020081c51801d01d0b000307480b14841e0b016604030040344003150f040303070b611901c2c903092032040554070b114485d0000c0758600d140081440c49088484220140811803040452150b002 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 353143803 1250 353142553 353142611
    0x1005090a09060c02060720030906070305040e07022a040e070b18030307051e15011203110303060a0302040509010209030105091b0a1d0a02040b031501020d05120118 72
    0x145920714500002200c94039042402990062400c1007212500300983d032602c00c91024100001c0f04e600042241107100345008a644404003040410501d540040030380207450000701740340815154032009030390790b50150b500000492100c0d1404256010b41e04e03070702c51a4540161010a10200149000303007088031980200d0454500800c0b45210701034200c42000740043c0913005103203406010349030191140b8640d403c9011313103200061020306c051400c02004106141c10910705201d5615120f01984103902c400b420b82c0002c030680d200300744010000c8101c902508000f4034900c400361a6038280401307018000e22450895600b400b010240d038400b0300500e80b003100e07400082d000110420302411422902410001d005148007041403040b28490300d0080b00903091096003510319500ca605c014080d114a8000c060090710102c10700506480380201300184c07000903000d0351120b20011400b191386015a54040075154559001041403400441001965600c81c0102044008800310340407000e0b605616080e407 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 353145053 1250 353143803 353143811
    0x170607030c05040302222904020309240f06060414010e0103150b040e090705091803190203090a06141e0c0d20010506010c0b090f0d052205060708031005090a 69
    0x40400054030440c10a11f00d03540c4000320004a420000d0700400040e0b15083c01142d000002c6000503100300902c40d010349a518112a640b905007026854078082a0b688484495050002ca111b610386501540d00ba82e12280485c1c4800e1080d0004450f801405191a070602d80c1d0761000e0080713100b0016a110103000040c002c950380318039084401036125001403910700b480d00300520510403aa03568003166049000d001c1001c040071f49491755a411482660040d82c503890000d2998010300e500031020705a106e0007108c0c11852260340c0c2c1e0b0305440c001d89142c40c0461000c800c0201c102520981411a40404440c41c509401c000d0300c040300a1401174158404000f00c0c51100e501000340042c21070f40030b07403109410000c0c030440c1800c1001a004d10128440207111085900014640d0305040200030035010425048400160380e401c0d0103005540807044850b0080360b2805101d1480600080c00421188042c002c0c514104040e11441c0c440e8001610b85620384000c2c0b00d0000d019030320710341d03854050381003028002 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 353146303 1250 353145053 353145109
    0x615081e06010503010b01080f0c04080304060e011d1c0c0306020409050108070801060506040e2823010302030604080c030f0406020705010306080d080a18051203010f170607030c05040302 82
    0x381c60400160700591203070781010900380103660310036441500709605400708030658640c00255043c9019603000f07103003d84000b040001e0080d500078217100015400b81c1303070104444508110740121008039035143d41c02204071040741d02e0b225034000040f01c0c0d00340100700142103561299509801c4c0d92103544407a07101512140148503900061054800500b2940001c000762490100440c5207070040b8840e02d00c0d4400e010000401004903486a82109401d5400455030413001c010403030010240183d2901d1600d0441d0a900c0140c83c5810303010781070f0f1f5001401003801d59203d45c1c0c1d1149a03031140c01c07a03044c140014044100c0c204001d0018001510b0250090161039041100040c101e51050780042c13a5039120360702414495400c90340d0150402c225241c046026644002c84075080040030100400c54030401003020381c19003414020710705803003210407134a81d0035036110305107144c0313648030084581b007500110040b808442c000e9000e1030100d8410300701035041030b6403500007981c806040307001d0745c50310704600c00d0403 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 353147553 1250 353146303 353146363
    0x60a060512150103020d020a0815060903030909220c06030f1a130e030f0706051015030b031606111e0703060b1c12090b0313061508 58
    0x101025010510303100381004201c42064601e010050710080902c400707032004203400d912a4040b2084d8040c207503415996010700107001001a1021103c1c060410101302042c1801d1501c0022140300910060045003003020003800c001082c03202a180c080c80041a84410360001104540100c2c44d50050003110080e41ca00030300501651042c86003550410320f0001400d807610070100c1c0c003402604d021b42c0c454000703a9045c0d100314001e040001c07240c203140c880400c03400ca030440c0d020001d206072445603205014680341c0000d1034074516824020001146210030200d402c040c482d500192900000804951254607890070321107a81240c4d070040000240c840001d0034203500200708015030410058864030350707940c00141395501c030071150200401064480000c0305096548140380c40c0e00e01c800a01c4081c0b54075451900703c54100344102c03d900030503942c6900042e084140400c2d00d10403d0705c40d102c00e110000c0c81d0303110070061401c81300d2070749503861602c40030800810130411480205014200107504890701110 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 353148803 1250 353147553 353147569
    0x6181a1203030411030706080103030c0212061317041a03040f02090403030b03190203060115120c030b0a0801110d0f0216081e0c030409020f190806040c17040213090609060506 77
    0xf0482c083d80c45284201f21190748820b000341100d41502e400c0800d00214030000300c40c42c02c9010080c2c21031140000307000c00081e511b05c1d24110b852081c4007007006c40c400c601e031f0088c3d42d0140c0d1041c00000c81c80707040c0c00b800d412151001180d2051180e011304103000c185500081e5100c41c25031301500003c3e994109050541001c106213160906618008101000158002582d80f1014011800604242c0110002ca2406030420b451001c41d100410f103c80744255000500500c00c0400c1d80e03110307542c061000540e02106102d62184009221710170f5180103144104034001d00144144080da0a03800c111450000d078825410b0300c016882808104d03a903498020f07615401041103024006c4c160820172490381d40010010854007281d00d154805615013000f02ca1148441c002c012000030000045140540031a60102c4114401d44003101c0c108240300c0c2d03c00382251452200140a0f02e407540910204025191041d94031a10b152100c00c0410000e15541e27509007a1141c0d080c0440340c1680324001e001c014039003445 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 353150053 1250 353148803 353148833
    0x105040e0a12020d1b0b04021005070b011e1a0f130b03040f0605060609011b050718020307020111180409020f041a090903070c0306050615030c0309070906181a12030304 74
    0x51600d011710b49a4881070a900e002600003880341d81034000800d40b0f14041c500f507441c159007050b6243c81380d42c0d41d914000741c245030740e01400e500d03036200801c00320b200c1c8003910015034000c907031400c850f00780444064140c0040d0b100c2aa03251b0318440000b000208895560002d511075032190139800c641c80c00502d0118107946024055901c20802480801c1071030343d014504003d000403c0d090703003110301d1705070420700e0802c0c58a401209000802104a0582c0350040d001940034400e55402000908006c00241d016405040891800305201c5226017007145410303040010348500041c0411000700d14800050106c95030301c00c010501c0b0072880d17030300a007a1420580315527110361410041c6181410344c1e501e0010519507800300603c0303a90b458010810580350700c0441e1820313001241840342d990520111940c9d0756041100c010341103102e40540450492400e0044030100c4a00f402c0034507080040f0f840c05005408115100c0001c5803840c3c081c0d2007a599a4003a40c0110031000014550320304060034203540b03241d0156 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 353151303 1250 353150053 353150087
    0x20d0f0b030d18090501170c0d0201081612151d06010509060c0106091107110f031b03010906020d0b090a020f031303031b1107050108010b030105040e0a12020d 70
    0x190604140c0d180802c0c00c2015107078900d051102001c401c0d1004003410840e400421110b4680000418142603246110134024003410840f10035010002c1000401803803010001d0000314801c0100704054440c800c46004c3d0440b41c104035036a40d5010420004444c011500d440b111318100c0420040d4600c94200145942400342c0402490704d4030100181192140c511618007480000540217040710003948060050a4034050902896000d454000c5031500821000c0c2c607642050310041103640f81484200550000c0600039004034a048000103c5000400e0030031500755403110381c0600000c103103200920b00700890500000750107a0020030300822440045c845080179104115181107120b02400740e0b54070135407191052200c24681d1038110090110f10344411840380304038140b220510781100320b5080e1030300d8141c11200203a9079000111140c01081c07184048842042005004a0030140c01940c4507654001c00c59030b114585686044c042d240700000300c00140c000225590000c0e07441440650180018 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 353152553 1250 353151303 353151311
    0x19080417030301050a030215040305120d0609050702060f270102070308060306010b0702151b0d020d0c110f010908030a050a0810030803070c020a050406060201050402180f010b0c010915020d0f 84
    0x1303004900248624013019125150301500e04190054030300440d0090f42c1d12409441b0510b24040b0803082940280040041003401d041000c95035801c14465188501600e900800e82902d85180ca41c00215001e400d01d50043c400c5001348080300d0a5145406801160400042e038842c86410003c080500107011148240c12503401003080d104000c3c2600ca80a40448a0b03146440500b500310b0300301c0c401c4002d801040e141c030340820b0800e07500103ea1407505503402d0302500d0020b6140301c2c0032140c01003a50801040b400d180b81d00142c00e400c040c0b40742040f0280604202840e82d07110810a45147c018001d101c0000f0030004040e0a46580014034540051f0380f90040f07000c00d4216561400d680c003000b041c050402541c41c040006640d190346c0090010003014004100c1a6180c0340000d0180c40c040f0760070780c09154074054182c040c0100c213445500c18540003d40c00c030143d007007130880700099000d54811009992614100c4000c03c1c40c0300403c81112160100042e035030080244240165122000c82c0e0214a1030 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 353153803 1250 353152553 353152559
    0xa05180a030308040b0702070e070210202706030405031b060609070f0e0a1403010524150705071d07020f030409020f040806090a17090a0b0c19080417030301 69
    0xc159000c1d04079a006807041401d5545050480c40c0078402e034050081001d070b10b0140200340d41c002ca003036102c1e195800d8083c844dd501c02c002041c5169001c5800d035548140811450071030140c025081540f00000402c20000a03ca60001441c0c0740c00c240c400b0303540703900300280d290000c5000c0364000e5a04011880505003d2a140001401d914402844501845006139401c68054030420130400024002020341d015070303860b427082e9003255016100c054040e41c40d003004103001888640b04007003281a420140070008800d8030503c21180c1c883c502411441106000d150000358051243c0720250a038a050410070401c00e0030036001669002c0c24038401c0d9004580d04440c03180f004821241569000e0070b0150b82d0701e411510017840307485558000c1e8498007580040c004c8816003c034034010071a000e0705440051108201c201541d911842809550008810f6402c2040200d032901400c541001d000548442502c035030400c064106051104071014400083d0500c542400a804400032040401c002c505542c1 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 353155053 1250 353153803 353153807
    0x3170a1b030506030c0a0e0106020d08060a0303110a3302030906010e13060504050309040c110c0103090309120b0910290a081002031b09030604060908040b0a05180a0303 74
    0x11104804142e00c650000d249500c080048080b0b04501504030362186680e200140d42001082c080d135001800780803088280c4500c034106050280200034084103d840c9150b4040e038510000c00e80f0020107010381201c0201150380c60000005442d901d020203910358101c0e410030f007080541c43c11748011191051080c48030903040029136505481c445101c8018a80714030280c404d440020200060040f4285400c101c01c0007000300140080d510103035400c1c400c0c0d40d01160280d902d02074121405209a120810380e0110b036100760800282c00b400f03030505462958480d0344491040003211025a41c101801082c481c0d01c820402c2100403500c014941004044c4116040c000f100504d070252003100e1480d9014042540d07580c80081004215810448080f2230b01e003d500d074003941003140c03900c0c0c2c01001d51015111905501d011241c07603000003030182c0034964466036002c0040a10341000c2c2c1d1a51028440171036030445c668000d22001055842d00ca40350040403e0046d1041c0022007954000d40d080f40701000040d0b = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 353156303 1250 353155053 353155091
    0x302071d040b0f06150a0509180c03190b060c06040c0e090703030507151811090c0901031509020a02011a0303040f06050d09060c05030610020c030c060901030605060703170a 76
    0x507a103c240048642c503440300117002c40031104a5140d211500040700900a90000020901804143ea100c0c0d11407070882d01641d90002c08803420300c2000c20400000b940d0b5000c40300890320b1708041ca03000054400004020035502c0d0000141501503900c610148004d01c40c1000c44c18006010141403a95903160454006880713501c5440014240a00441e400007008000c19002042900b240d008100710442072007082412032a641040d20415207030310840b101802c1c080701039032007440d06442c40c80c6041030b00401100203009070a001c1d03040002c40000820496140c2c0024601041d00c0d900100b514444070403c00b044240000220b0305c0303035200b00070800c240454418204212140d41c20701c00d480d0150310f0150009810020001400b0b00e103001032582d20140c000c005940114070640f4103031100c1e920280e0076039450940061865041d0700480c90315029140800003003e55103010b02d00884c400b03540744080f4003203800c404800c03800304010a64081c1183da042d48882e6104403040c2d001c0c4020308000200c03090b88 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 353157553 1250 353156303 353156311
    0x6030d03020f12091c020c01020604032d020c040c0302090310150e0118050703020901021f0603140a061b0903020f121b01090501030c1407140601030302071d040b 71
    0x1241d00441e02c04148210340c01520050f0641e07640a01844c94014000c0d5141d14410f01950118004200360090003840001c152200301f106800070002078941da10700380c034240001c00c0406030411030140c0c8484440307191200b086010619070000c1ca0700c0710b200010042500d440d61000ba041501c1400014a940d50000c1e001c500d400b4a031000040c40000130b402c405585000b41c100c14130301c500990002402e03610500c0310170781a1421443c1000a5200d110b001c900f0791181109850060b81315010810018204000c031382d000c0c000e5414000740d00b90303070303075890b45040c051484141d02035400c06101d0201344002801520003a001580900080300010b000180c030780c91070f9000190140541c0c9120751041d48429401c0d012400c00c01c012202440303c140c5002070b0107045c0700f0445000445445001a05500030701401c3d1418082c2e44400b0210b105140b40800035801a060a8810b40c1e21100441c090b2582842000d01a6000e6400380124500340095511404002c80d10154480c21217800c11001c01c41e0980a1a00 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 353158803 1250 353157553 353157557
    0xd02060406020f07051629030f06031905010b10170705070314030f15061303081c110d0c021507050a0c08030126060402090423060f0106080f06030d 65
    0x100c1c42c08030810b183c0c0d8090307100000e03c00d03c16000320000c09211501868219507580800c082c0007400300324064071603402200000103595081c0041100090011840d17940f0410240c11590810b0702d0206807030b071444a0050558040e5500c01c01d00c042c1c0e041215086c50003c070103041140d41748c1c824040c80725000c8402410f1004002000c9a944101407181d040c103400c00394801182a101d00703060002d078000e0740081d00c040480040351100c140c0c1074242102030340c02c0d8500b400e4800c1c20041c0b840e103400c14581d208241540a0108403042000c9101c81c611034401311400412001341c4500056980c20300b15504143c84c1d00955010401c035202903070310194169809a0b030b03450b000740c480403082c81c01d8405681107038005040900c0440003240d9602440005050700340313580d0200c07800640a5460a859500941e800394000c6500320001d0b02040560758109c5d411064a00061860207a600049003801401ea0b01290300f40805801046642d90164501d40c10204030b000745002030400400007692021410713001e8003 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 353160053 1250 353158803 353158807
    0x40c031205120403030204171c03110f030709051309020906060702010201150b09010e010306030c0303050708070507120b07030c020a0b1f03050a06200906090d120801060e01020d0206040602 83
    0xe640e0744620250340d039005540b16044402c2c00c0918001d0080d4120f401f407044200071408122000010020300490301d0300380d402010400401000c0c00301e02070f20002903209250641001500c0d4441586801540b0400c407580d944029070b41020104541c480400c045c505155080c0441d000c0940c0c0c50b25034485c2c11110071200c0300c0d40c903219480180c0c00b50104905503030301c0981d400320010700c006000b0300402100001340d81c0d07180400941d41c019001caa59902018059541049060001070b009900410f1003500601c0c4141c01c080c071b55564185071843d071790008050341075688031510401c000864015003111803030034244072010064500070f55640e0540d0020341040c0003e004198604129244203264400300031540107a82d4881c100300765913078030b070a10403101c451910740d02c48200103003c000381c0c1040a041c892245804400810422990403085074543d20003141050880051044000103101d2901501c91085c2903240403000382624902540240c10754000c000000c0300356602045499010b40c0c4203000507 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 353161303 1250 353160053 353160083
    0xb070b0610030f140f090106080712060b060f0d0515060d050a021e07021305060d030302072f03070803030c0f160516030506090d050a03050604091502120f040c03 71
    0x7005800000341d0f03412558540b80300c0504c180e4881182521400c0c1072032a40e042910340700000c43c2240d9640c840c904094000800c14000b81c0700d070101c6440c0440c0175850200708800000001161603000700840107184900240d00d9005481c10b000740b9078032400a00080780d138030403540049191407094618904407240e448001407407070311042e41500d0100710104049490130309400060b010b20b50100005a1050051148582142c0841e00405204000107000b806000a007564141e010790041c1e1000c0b01ca403221010503140b2141d044c05400131680700c02101d04141c452140525041c250301d500112000e0304200200254048100210b550000d402c0c000545c0c1c0b00c4c0400301c000311316061043c000b4410302a149a00b04c1c2112075211110940c2c0c054410388210761201d4040300c0c0e40b00c521101800114000780624051640254007007680900040c0003c64005401c5c4c0c0c410043d00c04005094240700e501003500c80c462810304020795800701640d51581128241030319000c40c005000e200040c06104c21702c50710 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 353162553 1250 353161303 353161307
    0x60b0702061605010e010e190309060c060204090213050f040501060801050f0f0a081609050105010c080703030b1003020a030e01090816080d09030e2707032708090a0b070b0610 77
    0x601201d0f0020020401e41e51103401240c0a4400d080401c2d02e28441d10b8410840c0100c5072500c1e50301c1943c151a43c00c20f6a103000303420340e07a50319000300903030b04a50300348070006105c035035400200404542c04008030030b40c50034401004211800b00030064029443c01006210311a0031a03500c80c19608100e4148202024541c00284590b0403414600d03001400613000044000c1d0000b46800c13200c0320054001911034483c01040101d4000748100341c0041c1c54081c01e60301140b012001441881d00a29002c038200050202140b5500c45030140c13080000d40c0000c0080030a0703418400d02c0d804440b10002400740c2d00040d00c1c1c9000781d000304559050511200c0021808001400003240c1350014a804148a01e20740c608014111044600311280204952100c02c600d035012801c1c42ca02d11102400c140700c480d00c80b45000c40040c0440c1d00003440e10180c0c940121402144014502502e5110300c960710765500e0a54140500c2c0400d55205a11611052000000180b08904041e03840700090350038000ca03040707190742 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 353163803 1250 353162553 353162587
    0x1a010f060818061504320f0c0f0f0d0e06060102010516090b0a020102120117190f0b060102120c1b012d09050a0801020a020c1c06200a050a0210060b070206 68
    0x1904c1b0034440d031000c5042580c402c1c9410783c040c8061940d0544030070341e140c5000301d030b14181c12908000014003c1041c2422075504e0030240c50255541084107007042c1c035150300b410071640146c00304025030b80a00e040210541e4240280396000e602c51000e02003290b20800050b18582c05130056507084500802c200215034401d505507200c0c2da0b82e161180c400c5580d101c00c9900d072101d0341c60a05242d03010b0f08450301c49139815810200c1029900c54405030425115844901d00410701078111411809412400782c00703101b04d90082d200d800c5c242e40c0984400709600011321484c009806185060210301442040c0c41c004400c0440f80c41482c10450100c1a180c10b03404542060720342d002141d001d00e803884040391002056024140405e0141c080303503844e203013210800c40078010a0414074400d00c004508000003a2039500a60070349890320404105e015032000c076180547d00806000c900080c0042184042107504110701c94603c41c5002042040ea0704040c0c00c501540b1407014040c0c0a0080010f00c07251100303003104 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 353165053 1250 353163803 353163821
    0x90d11210f03180c0d150207110301061e0f0e19020d0c0504181104090b12010504050f0625030c110709020d0c0918091a010f060818061504 61
    0x10a69580d03d803038810104084054079100d9121321428002449500703001d40b10fa541c06421130718120340c00e005400f600000c2c0d408604200c42641045c0c4030301029440074020341c4080c002109101a000b45110030100e284480c0d5400341250f414211401c021034800d16400c1500300b0210280c00c018882103500765006803141c018010b561070b29014880303040c142e00c00050b2003901c407800e450010891888480c202500c03859861f0082010080000b04031704925607100703244444002e030080f0001294904110308591040b039003510640c101c0c017442400c40800b0b00c00c6e10740c407040c2d010481c54544001c040405030030490040301e80c14150703034200c07100c40701d4007482c40c1c0801c1000c00400c5070800c0e911480d0b100003079000210310b0544941848412044107000b01421025241c0715181041c4030151081031001030400d000c000c0d0783d900303070110300824011054108070740a0005603071440c150342d10b007003001061032400a14040d68100201d08420030030b48003080c41078002000031035101751100944001401040d00340 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 353166303 1250 353165053 353165077
    0x516171b0c2505150a0210021c0f0510060f080408030612030304150606050c031204080403020d05030c2812020c0d05010b040e010905070b0a03020f030405010203090d1121 75
    0x1805800a012003441c48906840060364001d42c40e901808071301d1924080e2080400158010580144402900742d01800c0c1008600c0988d030404ca00310781d804006c42d0110712242100710707110010414001e00319107005008000c2071a0205c20102d18820003400c010300500020208080000403940325900d0320342001d5200108002d0729542c1c05c0618115110102e140085d0628509103000010200c0c000c0040d02c0c100100140510701c0c10b6400c4103908507a150040040707944c108103000120158440c6a580c4105030310a07402999036060020b2014644004141c82103041413500c0c480404451200100c0b2610070341c40325003c1da258030309034020303410001d58600b0300c1d800140320b2498105000054000490307004042e5000c010303c00c0d0358600da600366078003a10050701c103a112080400041c1410001812040c00c0c41c50014202409541940680d90058800b80c40f681c1d000300c14040c0d182c005100c203184503c02814800b4a1850740d191041c0c85c1c60070342c02a48102d0b2880303141c0c00c0b070a03034801044405030320802c = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 353167553 1250 353166303 353166343
    0x30d081003021002100501060f090506030a06080a0c090605060f040e06150c0a020906030309090c0315040c1d090105090106030b031009030801080708010501061704030c02040516171b0c 81
    0xa040f00030343e120201d502c840000e60526000044080c0158049407500da1142d9688880c21300300000d0040c1a0301c00b80083c1440c1d0b5888400080d40e5000348010600d0728803508203000d40328541004001603030100d400c0580719200400050104c1c03840307041228110b40105070040c0150340c8200001b0a84041e050042280c0d03100000c1c00300202e8004a4a0104c4da0710850304202c00f6114042031641d40d000301c003507880e04001144042040c1410f0903014650140402140d00d10f5207c444011038292000c0700d88400200340c4980103060141740050100d070740c0f00000d07514041c9540c90700001038448181171164005055507080f0321881d607101440511140e241c040000d21200c0d4407031030010321500c07003449181c0321409078080110310b041041c083d0904030380040d5100004050140602e441c20400034204a040c8000540e00c07000603103880c05190f105044040704540404040a0003404900d40d045c241802e4580c0c2c43c040110009a1003206458003008501075900c42c000c9003d09071910040440030702e902040 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 353168803 1250 353167553 353167579
    0x608060f0423060a080a1101030e120a0c0c0501030c2a02041104030c0b03070c03031a1305180f191a1302031207210203040902040909061406030d08100302 68
    0xd04400c103000380d105880b0a0300280d6121010746d20780c0c0c08040010401150b65240221662094102c0810b004406042d112154806162002c0c1c991220422201082c4030401d54424044400804070040c1020b0070b05000342018044c0081c2680780f020340948034200c446100004011281d00c0c22003c090703001d08108020800c00b00000f403144c000d0303c021074261020700c2c0d0106d000f2809400b50390250417130340c503901e9640e01282c0c0c0030782c00b0b040050040d40001030b001c0e19a40c0f85d5918240d02c80d541807030f54080007a00e07041828003010385641d00d150000d11a8410284841c11042c001100701d00e207041c4554683c1300c90118580078074021014005690021040414410449048640058020301c02c90031201c002100d10041c40e02c030700038010701a15184450801d00502c00007489408441d46092040d030785455121801c0300101e03001508040300342542c1d0141c900030001144620601185401d1035102c0900e400b034002a03456809894045c00c01c0b0044000c5108005001d52003400781d40c1c01041c40b031810340717 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 353170053 1250 353168803 353168861
    0x10b1507140c031b04050a02040509041502190305060114040614130b040806241f0e04050907030c0905090d051309020316120522020a050301110a08100608060f04 71
    0x310441138540f1451400c000305820340d8180c801c82e001c82c0d901505c500c2c13259503242c0300c00f80e0500c0556052012103800b0400f03285003002ca40c005030b243c0d400e81d403000201401c02e00c000624450041c0190f4050f410f00300810702c9045d403c0101e001c640461998000e40d034045400d138403941108030742d1181d1080c07500410301040c9200d010078058441c2d11410002c801c4002041c2020003502e20441e1a01d4001c0348281080d1030051803000c00306810146401e01041c0e03140203102080072500c046511645682100400b4010024049010401040548000d014a040c03002409071144403881111060080000702d22503a0050310202070000c3c54501411034683c503001a01c2038038001e540c80004000340940304003440c15001449818041e0100c6502000715285001400101c0080080140d03880305100a0000b0943e800740a0803c1104010040d00c2c0c50390108a0003500c411405480f03440703441c101003020301142c0e40c0315204552004044841180e1036084501040080c00a001c0112030800c64201c01d00c1c4120b = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 353171303 1250 353170053 353170093
    0x2012a051b0d06230f07030c03051e100902030a020a09060518060a18030602091504212102060108160302060f0708131205010b1507140c03 61
    0x24000c50a440d54500070315224400780140e0615981c2c0407a0b0303114a10045211503201e5425445403d015a0b0300000360a00c5001d00b0034112401c0e03c26041d40c40030049800c3d0b15004000c0c40076042c0c14244002d0030002c04030201d00080010703000802d260782e0005120b040060050000030412200e0455881c1000d400c2903019505c5488e41c1c60106143c450001080380c42001181c0c0e9034900d0140315103074140081d04011050f44a124001d0410644025542009912120210046100d0800160385a07480c87c00d1010301c1c603104000c03c2d12810240801c01c00311500180e140c4154150b219403e4485001d460318a9031524421076510240342c011810019464000a40c10b05851142e800c44500030581058014060f00c1400025040326060050075403041d2004050181c03d44181216070a1920003008038840da4080d138010140f8071000110101482002e120b801c2d0f950300700352215a00c001001310104140c1c81000001000c07008a00b0300d0141d06075003406036454404004080e1a0318030390010700c2c2e00c011 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 353172553 1250 353171303 353171387
    0x30b0702030307090b04060c230d271511030f1206010e03030a0f08100546030213060302120d030f0b09061215040c08010b01020601031106070201 64
    0x80707513120f0800314480c0c000000f542c046800300da840080d03105060b0384920b103030340d81e84881c10704403100103800729050320041c084408560744940d00c00300da030480010f81040301944505109003c901c8418244208072990b42e00f81c04216a900b410382d0b10486890026285120f08903272040740240c041074116122130300743d07101801044247d031156440340c45201055100d104041c1e4140101c2c400403070380c2455030b0240070303160b520425050784090310690f1800072621800144107144e0f91400d0301c08110000000582070001e00d0f12003102d15204040c20070000c00c24407280c41c00040c0c4a0015080101b041000c9500002d019503030140c40ca50883c0b000d0034016546202001403031002c0390070b02280100354a158414400003001c0103011960a40b0741d60140112219641d44d8103c40303001e001480002c4951400036140185d11030391001c45100d142c1048a070846080d900454110f400003001007010413441c0304482002a0125455640e412040c401030ba030451074070094420fa440d01881c0c60300c0c5a42c140c01c0740448 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 353173803 1250 353172553 353172557
    0x206070809120d021c0903060603051e07030506190f0c0504151706010e06130f0f12120e0d05060901090c050d21030204090e0d0912030e0910030b0702030307 69
    0x100c8244611003603103c0110010b52070040e4095001000d0002c111100d2508500e03481c02c0c44601c8136102d4a421098418a800c1558103500c0f40f07140b2503035040400c0c00c038030b4116040b0300030300401ea0442e035885490300c0000c0c05500c1c0d00000c40c19000c00010340d81c1c0c8000900c01c10103e04002d00840390102070700e160024880c0c0c0300c6118030030788418109800340ca4404012180c488442038070350707070781c4005580203604250569003200c018041d94150081d4038000d4005000e41a0b0030903102c0d0b10744200010040190f0b006812061013510b40c2900040b890780825001e04800c2c02e2050019840d05c01003400140302c218094100d200d00f0041c04001c0c1030641c048001d480c0984251402140c0b501c00348071040c1d0342140020034540c403a19140400c0f0f180140540da118041d86070144c07825035245005404d60b1a1420741011a0708010001e034110f5400c10301031001800400b403041045041070b18040c003040c602907a00360180d034000001a5040280e910b00e00040d5a0007214550746092000c0b0081d500e0300200c40d0000 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 353175053 1250 353173803 353173819
    0xb1c12030c030605030a061a030d031a01090608070e1203040303080402040608060708041113050f0601080106030c140702040e060c040806070203041202040c021204080f0c0607020109031b030206070809 88
    0xa019803103400f0b03800c10303904090010640515035584100040c001011121845500c40444400913a000c0c4011103000309140d40c0401c1207075511744889100740011401c01e042c408400000c000c490f40000c20250311400600380320909040e90b002043c0c2074010034000d103216001c002404000c0540016070980254000e0340c0400001d038403200c020b682c6940175201034002c0b45001e030000d000070fa03144100e401e403424040c0c44c00d03465002d144051015500280c640390460001b807410082c1c10350b03110102600601452606100b28007100d00d010303040b80341c01100c0702e042140000b0028151f495a42018100340f4000d070880e005480c00800042054110380224031140c0584000724407070741d100000f603c01791002100c0c041840f096030340c20800140301422180c42503014011420200c00b60100c050801000703110094a1480304800301c40b410714151141041c07007140c1c188a00d2015036840803104007600c0d80000c881c0c1c01510000b0500060113615031000b94007403000a440d904010720721015115500058130390035 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 353176303 1250 353175053 353175071
    0x30b030a02061317070608160c0b0f04060b0d0309121b0f05031002030910020315041406040c030519110f04153b010509090903030907060c0f060b1c1203 67
    0x1d1300c2d6911845406e001038801c202280700100307298000450800241042102c0e212560b4410048410031030b8980700d686960010441805141e00882000c01d000700c2c3c900036400010358001c1e10380701d0b07035000e00703209418800301c004104141807000c0862000004000360103a50745228107000103101c0c0c05518003d015150704202d19103898000d9034011901c0d08040c0103040c0c880d44400307000303400c0100030790661134121a0500c0c95864920500e84d12900100d2102c091707140c000706010561700c400101f581014039010030000c4030956030310004042a258400403801101c2040c110701203004940e0814000280083c4c0060000c4854450039501031705621200904112540c030300d903a034501c50307000707a84911006030460700800b0f0700c8061520403541410074034100150f600110340800421250703c0502e13840042401107203203081199000038515031415984009a03980d03118081200f01b50020041901c0714950303280b503034600c2e00c0c45003c030b280000d00080c1110300c7c1c10003018160b070055801010a1a190b003107 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 353177553 1250 353176303 353176349
    0x4030b0417030f16030204050d0b040605090a0f02060a2303041a070806010309020307120c0503011a060d050a090b070305100602010c0504060e1801080604050d030b0a0303030b030a020613 82
    0x14a00c182000001c01d43c0a54402107051420301c90680740750101a401c0002103400d503294550664030038080c4001c0d48040c81c00345050021100042c1500350340d41e108449440000e6218203403403007a154107480d09a101c03a00b541007610440e42d0320311400203408a00d0341d0304414809184c05180b00e41c1c01000000100e03100581140e848402c190b540000003154070000070000c1d4000e03041102e0303180c40a0200d0346c5007a65020503005880700158102c601e00d204100802c003510b006d0117074101c581490b0501107158408400091554480c090341b407140c0c952075000003114180150300980345103412400005040c03078201c070011b004250894199400382003149012a01c1881440380c0005c0500c19210f0034034007030508800352810380140150035401204018400d64803110100d0217402000403000134007940c28145415400c0c9800d0122a0301010700e050014201035480482c42811a80c06007000101a4142000701303003401ca140030041e402030030004489240408840c03403882241d41070340305000f9103071104602c = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 353178803 1250 353177553 353177557
    0x429090610320406020c06090a0e180307030f23031807120f140a0b0103140a02031c021b0a15020316060203010501030c210c020c03010204030b0417 65
    0x2225810480c00309410718254001d2140c12003009521096542c6015a201030704070300301c0c0c0303034100d082280c1020800b0045a13070104401807800408030780d03090416001401103048a8120b200318890082000049454032040d0680d80541629080aa175520846820090302541c000303007030740c00000c81040c40c0c0d05450440c0304403441038602c1e942030240f858450101c40c9104207402d480221490041c8400051404011445002454030956280304406024100070020302c0d8944002501d51300010070600000d000c41e1082c90640341c1c411320001c4d503000207508403440d158802100030b42510034920108030059000c1c0c0300c0d03100080d06500301c603103042c6090056a20342d450803112940065080c40c0c1449540c442e00282c0d00b060f81e452048074140f60444401c0c56003400485001c1e074960f80d0000052003156414016000ea42e0400c1c00d011072040c080c0288140740c1b81110a060b00d0013599080c0444d4424400c1c00010441d0300010b00070345d01c440c0c40b4103260801c40e205940c00c41e0301d055170705100d13020441c1c0001 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 353180053 1250 353178803 353178811
    0x5090a05040c0308030a180b0105010305010807080d0c0314030703050f06030c010c0209070c0209040f1101080c120702010204260708010b130b0f090915100b0403020d08040302042909 80
    0x41e2224110314640e950701d44e5030005000c0c07110051700c40381c11280c50312040700c50204090241d80442825490031001404503041a040300210341c00c0240240200140029070040303a1105241441d8500c015080886180070880e1000741500750000034020385907810782095020321a844090748180c0c459604066941d10612078450208000c42c1c846005848d00e000c5556010b801c2d42070007000619940d00041014204403421030b14002907044400900005c1c00b045c006220f020f0030a035499080461010240e07020f40c00c1d00d03c104054103800100381903c01c0d01903070000d1210510700c902600c81203c1000e070040c03414858065610401c04005000b00c014024130306400800340c0160340b030f41c01403141c1001416800c032949421550f0144a0400354541c101c0c0c0d2803161007440060003003191111152640d04801030040585400300c600207100e00000c2204680c1240d5044807101c40c10b4601d40f408407018062507101950152a1160801d0b400100b564071604814103410055a80c40000c8100711103948151 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 353181303 1250 353180053 353180063
    0x513090c2606101d0a1205070812030c030a11180411120606030403020a1a090105090a08041e03080708091314011a1b160807350106060905090a0504 65
    0x204a0b0304040e4044c08540124074111614210000074440c040b443c10740156105081c1c41402449207002d0107001d111030b8001d0045000a403c01a01090a03c01e4030301010309000c8080790000041901a03156611108880b070010b98129140c103140f0341c0d40d09103091002000c03802141000c011503100c0c0c1c0480704803400c09404080707594090701c0301030a100d201c0d0001442101035104801209010642c4645104102090304050815903d800310003d800d540c40644000c000b82c1c0004038cc18000341c1c0e04810341e03040d20360707400d809903156107640d94030b04561000360b0000e0304000c000242117060001500c02098605000d071098417486016640308070484203040e0610f00101c29400051140b148880c107030451405440030403a04000c0d841c000710b0500d40e076862034003540340c0c040b40c05100c585824540020040103840d0140c2091403400721907001421f00c4401c820900c00c079451102061a40304071880318000d2814000b0000c40e40c80300005041c2140500400d4071810f051000034028400d40c1c041c2c14030465000e = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 353182553 1250 353181303 353181319
    0x1107050d03052b0204030c06030e0d0e010212030c03070e241614010c0e03010b09010e060a15030b0f060a0203071209120804090f1b0513090c2606 64
    0x552021540e50b0004980031083c1c60306601c0f0900c0004450b800061950810400180d0381c0e0b1561070f04c203005003829800238050604002042d40384201c0856461590f0b204d80c02e1940c01c94030440e00403828645913101040815038084140030707107145444040c51068840b0b031140c2442c07081010030419542d8075840007440c51003070300148003021400742d0003900c5265801d02010940035204d55410b0002164180c0c03c800d180e558500e6180c3c1d080d4010098182001d0550080100307480d41c60108d090690140a110414042c3c98045240360326103140c800024000c92080c003030b2081e0391075801005060780d0b0f1111440b49039005148082480c020045031521450b82e00118500840c039561412480712440b0040c09003c0816030000e5101d00b0302005002e40c40c49a220b82c4d54540c103008499040702d00b070031100000c1e01e15010803405540702a074514103801c94903091090320340303522282c64201c002c41030b08420f403c9410600c0040009400408040950510f13800401c0b40c1c03000c01c500018080c60407202281c1c06200 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 353183803 1250 353182553 353182579
    0xd021c052512020f09030106151205060d0f051606020312150a180b040510030f0b0c090a06031a0d051e0708010501080607090f0e04081804110901110705 67
    0x4440301d07500d504054108200d00d81d003101212000c80c0c110b00750200c040a80003511105c0c0c0d25084c032070301000c1d0841c500919014402942c000f89150101c0800400d815605c1000c1002581c44201480038964050f44a60040f8910300c2d0650f150814142201c0c2101400c00d0301190701d0340044207a80c1b400200c2d080c0c003800c99a8107031a04030b080340c400707040c03582004c0d011101003500d010b0100e60071404221002e0210703114034600300388012203400038260070070b4000301401840058818658104129040f9030103205540f940c80100e43d55201d8024030640c09404500005201394041d000040c9480000d0150390000e0b140c0b80610a90804240d0000c0c02c58201c2c1ca120300180704507004100414007000c046440795510395840e1400c50780700781c002c0c40c42940084200655268484481006002d404090107040782c5000e2400010b644050401054024085011000c03921350101c10881100000d20610031940450380342101948003502960004606808070f420303c5000050040171281c01400003250401 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 353185053 1250 353183803 353183851
    0xd060b0c12040b191b0c1401020f120a20011d030313120c0c08070e01060908120f0702040f0905010b0103090f0b0901020f0c01050601030c1121040b0d021c05 69
    0x24112140303401780030694040c24882c110070440110120703c14000e1001e0141440b8000a882c00341512142c1150701910705050300b0b00004c1015142c10020300e00e03064070b4001d100c0b01030300c2c0c044910603816100a1801100d8040c400305401c00b940c01c010481040b00c00a800b103d64036201e104c11503071600500f070300c42e40c508d0000e21440311180d40b600e0580344c400c0c8806101e60310102468040e41c04031102c1c4c0d000103010b04c02a00d150313003042c0c010103490038403c84251030000d000d40c0300d841140d003418002401060f030080da0b904201c00c07120100d41c000c0007003000d200c50b236139001c0051185c0c0f50251419860611202e0240d4060312071044002d402c00c03240e09110030719585009040c20b000342805050b540a00001c0c40b0106014090b18843c410340f000420b240c80c04000050445074030745005030404c11030140c103440c11071010410440308121600c900b500103100754403a0140e0310841d844000790240015a8035040b002e20780c00342511081654010940007001032034841910400e94803031003078140802260380121 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 353186303 1250 353185053 353185087
    0x603020708120403050c010207051b0f0102120904021308031e03010807171c080f0c0f030a0e070302060409090213060b0406050d141e070201140a020706020d060b0c12040b 75
    0x71340b19140807480c01ca000b07242207007a42c000500c22501640604a848401045c0840c00d07010361000b918120b018210303250000f1356034428a200500000c13400141070541e51245e40440c2e181c170080f25484200190f55001041d5664801e0891102c00008207103681078a006500899040f02c1e4044010101541045030300920a07518001103500c0c0d00c0b070303c00e200511041194031070b0407018050b00ca60b6914030b40b1060060340b5600c02004100307600002c00c00410000458400d030b0340c2003003400e04002054940c681140b0300c3d00d2025000603502c4400860001400c1107140c101d100344a1095881020502d4134459013030955495001c0c0d150140d00c1440207100030b034458009011a100503c034081145103581d0030b10700d9119416628181072100000030741c44503402c02c1500c1c5420000a200820400e0003980c1351245850300985007081d180d0b0006424001e1141c260140c6085900c01001048000e0f90346158000741d61007030340110400d000300001c000e107009644090f034048400c0e8042c4149031008401c1c05800390 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 353187553 1250 353186303 353186311
    0x15020c032a03010609141017060f0618043207030201080601090902030915070e10050a0903080408010207030905010903110d0c0e07180906050a052103071209060302070812 75
    0x43d940d80c100050342004d00e00460404030510314022259081041038488209469005084800c15031050b004407c100014000c8d8005105007a5007425198500082c2d555020404850301c0101880103201c00d0010000b2401c0c2c00745c0a09081c00752419080c81a0ba00b61000e80072100c0d61074000100800c00742d4002c07040700360700c07440514080c4009610380003010300701c1c0c106071403201c40c65218035110720354007507280301040d0480c2040c18050a2450010002045000901f2815040250110702d10b00c0e407a0091410202541d804402c540e101d5031100c035503d000b904000015030000d0072000c0c00103170950003031040301d013900d401910070650245e1503000c2c800595400c0707400700c56402680600107000d481014085d801072089075210b1090560003400700e2190f05d101d410104881c0d14210003000190f5070b04151004444050b2103650701a4a0282403560cc207260080100d01d50000292401c104449500c610030b002e1007640701c4070055070300d41d10102c049020380c41d0000c040355801c02c800304c40c2c2c0d802c6183d05a44 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 353188803 1250 353187553 353187559
    0x2210a020307020a150201050f190c141204020307120c060806060f030901090b1f06030504021219060510060f1b1211060630010b060415020c032a 64
    0x42d11505038013098000c1466886a600180741c0b40d003005084c0d5082c054160080d90310001e03207060342800311307e0b48900310794a0740c0303019025500e80c00010b0b600d0140c0d0303028100026110341c054903001103060949611000701e400f20300c04e000d0b4080c00b048100f00c402201003095000301c6209503c03401c00605842001c00604500c2d03000790184060400011550010f602c1a03181100100f170782e00300d40c40c1c415088100a01f004295230340d03805004080e81c0c290000c032012119145800700340c0307456500228000b4081088501c42078090442400b0300041200207036160580f00383c4080096030b96002c41412800824051180060103403590003100c0380c0700eaa00860011114800c0c2c820382a0303207503146070902150701010004181040324030607803d40c05008403584502c0aa8004000d00040d00b40042c0741200d0305415821290525a4004100c0013584142031540016000760f641c0c58980d80782c2c0744100c60300c6540c0b4006214109404443e030401040040741d030202016140c00031000f0b6010407042400001115030 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 353190053 1250 353188803 353188807
    0x30a0b06150d1514010e03060c0d02040503060411090a050402011b03020f100507020f070b0301030611160f0b0919031d06071110091d040c081608070602210a0203 71
    0x800310b5031841020700b115080001e94000c10314103100e1a000b40b0001c24103a050059040390030b4041c1d24040785c0301d68420f502e42c1030155140300d1885100000d0003241c120b56051701c00c075000c100400c07800c2003954140820171a501201a034402030710070f0544108030b90003400a0901d18010140c1481c200002d441e05106c0d00654005000c2c0c80c0c2041d00d0100380a0034406030355290320038401982e4041c4900b009a50015018080d01401c129010f01c0520040c07000030203099a030014402003d80c40c0080e03e00065100c0c50303d2980c42d84030304041120444000c001d56045030750380b011880c0300c900000d2918040004084540c0d901c205d6071429202c9034402c03003080a076500700301d80062143c0d0300c0f10014408188950507842c10114041c3c02d100000000e610b440060100c0201306002000c2841d4030500c02401c14407440016a40b5880c004441d46103940c03011030b4074402d990a80070300200041c1c41c1c40694000108447d06d05550302d03800ca9850241d070584240443c01c07280c0c40c0ca480d600c40c0c401404d84c80e00300c0c01101c0c = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 353191303 1250 353190053 353190067
    0x17130323031e0a0608030f0a020312092506080f1008190c1502030412020a0506120603010c0e0105121506030f07020106050607020f04090f1b05040605030a0b0615 71
    0x100a80c0d0040b0344a2202101400c0303040c803001010001c40e604103800003c10403081e03041c00c0455503248035075008900c0d00c40002c600a407010784208110f44800200b50b60002660030403600642e5940200c0f0742d0b1502141004c1c070f041c03482d200d03074280c40400c0781c02c66690b1400c241c64030304080343c2d807200181091800420080000c24030a2017040601d50803e800d49128082e01c490b81010b0a0b032015980101c1d41081100b5000002154000240e8041c2c401d0745031182504a210310010300585440c2c4d20980e08810042445401c200e000251148034003825402070081f043c581c5411507403441910136490200748184001196031000403134541d4042880381d05c0401caa640100044c00036001160710310201040305040202465081c000c450083c41309444250a1801c80d0b030005c1c4a0014039500217004540e0b07403000c9420b2003480c0d801c01c003229401101004401540d02282499121f4900505024500b0050300203101d09001a2910107507400c68075445054955104024400444071410311100000340814 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 353192553 1250 353191303 353191367
    0x250804020f0a0f06270e0c042418060207091d1504020a06090602062d0108010b04060e0105090a0203070507060c0302030627040b0702161401171303 65
    0x480140c0810f000880185140c603600074202e10100416440110041006081184054058800707655580c100400382d5030300c0a4058283d40919484001080740d0380000403101c80000c0c00c40d201a007255600c50f8040e40d0341c000b8014001070544030b0040168003007007040040080541c00b1000d0070f00d84070424609040009145880c00c03000015200d4140f07003e8050100718500016600300402003414000640307440c0c108081d4551500400b41c0640c0d051a01e100d11804030030482420107003444a03080041541c540b90b0850003041d51180346405980b0b000004504074400b881c021341220001010240541d403641d1416004c3d40010b0011428040d0600c0850b00262391805640c55401940e1740060b101d242c00ca00304000095004403668160b91080103000707001114003646644550001d101c1c0d40a0b07111a1400c900d40984000c0388003440d07012078804150300604069040e000c0000740c0c3d0340004c000c16402c1c5282906801d0b510050310020810007a800a0b015003520307400100c0d00c4040342e00702920007000d = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 353193803 1250 353192553 353192569
    0x806010e09042627120708150411120708013803030405060403060212010b090f01030c090807080708010e0102040503150703061a12070311160804050a06020d08250804020f 75
    0x709400011106041083c5c03d210254824884070240181521807518612585803400c001c880050340c2c01480c0083c0601591000f000c24800c07021b80210501c181e880c0b140c50b182c148a025050544d401e11302d08582c034080400c50b000010780c0e0402e0b409050844172419080d5800b0b0040b0241c0c05000501002855a1f1500c0142000390f028000c0036030360389014501030700c8044058101401614046c841d55a05884208140044040a0030000380403031010b0030903a0144400da228009034410640d0210350207401091503030850f00c0400081c8400c07402201c1c01ca00741e010343c0c003c060301548111075084008808223511074100e1020300b0300241b410303180d81b04d001400e01e5445102c07000d45c600242c940101040020115440120340c5401c01800e103030245950010b01c500ca20003090403440d8440e0f1028000e00030115030040c100104000190741e038904003e501c4100892503a000306444c840066040701c08004440d4016410045000c800c45039100261090000070b481680c10141c0e41e8003074581a219554 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 353195053 1250 353193803 353193847
    0xb1323060d0b09071d010b040608090a06020a03020a0e0a03050c190902040308040501020f0d0909020a14070501090b0f010501050307080a0f1409010c03020408060622020403030806010e090426 84
    0x2c09031407040c1c00d11071411401d4117024580d000751881a00100803501d0310800b40c03800d031801403800f01303404e44480c1801441c00c4034882c0050002840000c51115954059005020510590702c40300041410901000800b50843c400a000fa401c1404c840d00e0b240b4055040f400b0001c00340040d070000d140c80701c6602e01240c11503081250300309400a0305004941c2c040162415142e41d820003000e280903003080003403070301d0404d03c03d0018407500480e131540c0340d9000c0c40848807c154543d40a50701c8a10908181c2e018203481641502c03040107070004114140c55150703242d030503104184c440d00d15584074a94112504080202100543e81d510701403600b02c40c1c07903400b640691600700d5580d642141081c1c03c2080c21140d10300d50b0340b0281481048100440704000c0f0310309034404801c8420804910a480ca07503102109204907103038286200003030110406400403103071400b451080c1c1c2c0f090041c1c03480001344046428280c41c060003441c1a0081401e24110b14602c145031121201c5125084c6580300c95092400700d1885 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 353196303 1250 353195053 353195071
    0x203041406090d120c09031e150f0605091b07030309121e020a11060702031509060f061c060b011e030218060a140307140d0b1323060d0b 60
    0x12103541d0340343e4006400c3c0604c40040a040240b0f00e22104003800b031414600c401005849180b17071a180c1505100142c00405401010307079941450082c9806000b4841c2c02055154a8500407005c900c40c01d21020161141409044c1282d0000b00300380b00004030b8000d07140440c2010307143c4008000064503020b90081d00d050546800c0446000949144601c507036104400045601240750032010500400602c500c0b904150390f0b80b40d0750111400800d0800b500402c8030706084402009000341b004c40000c5841c407800041c0d000404030303114401048041e046c11851101d072855211141001700700340394030140f4070f403030b05040608200c0c56038450b01c1c0c0c10182513540000843d9003c501d502508881000e2070300461012500a40340045409026002244011445d14111008000502040c0c0164081880e010380300751015200c244200d0000c018003500d420b030307038024003034015101210360a601444e80980c200c40c1c0c00c00e03498010200050754500c4003c14440d4044042d51181c00070030882150107000da40c1c48 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 353197553 1250 353196303 353196313
    0x1014030a0c060e011106100b0f0c1603051c08190e16060908060f0c03070c060908180d0c090b060706050106180b0301060e010804050c03060f1905041104020304140609 73
    0x444005043d1742502c51040359a40c00c004100440000901080819200244171080e05c680001d0340030b480034040c000341058203105280050b4242449040c92000f160310072000c07142e407000c64050402640321940452804148d0120100d180c203500d0102902d8140240f140010303124000341c0c0810714000784070f40c103240d070703401d04034410b00c851b0303610080700c3c005012014000c107180d050480002c409502d0051407040d80c03032001300c007049078240714044115042c2d030044418044074130603082c42c510540c1b20141d0280701501c0021032840a040c800310710056650072030200e05403780740000c0d100180c0840c041c40b0764881c4082041c9400a0221b00c9128040d00300d0f95203e09070710088001001c03903000305822003b14880148010400c1c941d118003800041c91080ca003541041c1c6492910610303102c02440313059410700a0508110000b418025190322402c05004080c08131604401d0348402c0380c4040d05d01410b0001c07090101840b500b0550001c0d80c0041c0704103000400b0f83c0d10700e4995403d0080c10342d800c801e56040 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 353198803 1250 353197553 353197577
    0x16030318050709020c0d0c080d0924020d1a100302030a181103010b1203030a0c201c0903080d0207030e1509043902010e15010513051014030a0c06 64
    0x401101140c501e25040001f104185d58580340c081d40600c0301030034034094403400314504001007032030300000c00a4582c003210004407000100e1f40c0650060000328203800c3c03504007880404d61080b0300d02424440050b000000b078001c2c030b90741200a58030007085401e480c0e071296200d204003650780f410058400c2c020400b5903001c072440420103081d907090514841c4030700401a140540d800c008011aa0032044001000448a43c004401e640d03400e21403118003406550354040700e00700040400c12408150406000402940081000b40d852021a0001815071301003808407425038032050b070040a1642c080e06104400240c02800034078100d00c60840c0769444c5001003110440c0781414000c0f07002071040e42c1c9110020f050000c0d18200300c5084036a1044050b01d448459030f090034000e501510f1000040d82c00e0300c000700c883d02d00000e0031010030b10030305025040c03079414070700e21240e244101402080c0c0e401c03aa4a1030342c40c151032802c80c00c05203400103600d40680210403000880c401d00c10300092030982c03160114400 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 353200053 1250 353198803 353198827
    0xc0d051507020102092b21020105060901120618141005130209060d110a170c060337090c03021905150d09020307030302070305060a021603031805070902 67
    0x4000c0c140c14156030062203984443d40d25140e6202c6d15500300c2000d01003410003641c9613141003040e100080e00c140080d440d03054011180d400150f0000c0703180c4c1c0090045888060034002200700902c65242c1c8a01140c0c0d0038000200305802041d84e504488012120540554880ba148403001004122a40d40941c01c003040d420010300607564460f2000d80e2201c2000c03960b4006c9005e481004005920440d03460140c14200044000966214280500f00c254550346900945204000d0a1000c501500c106400000c50303152440850307200e81c20600c905889c8070445800c24010102189a03216411095000801421590310810611078010400502c01e186140180075119201140c03517801d007100c41ca81441941c0f14818100780040400030f00340c1e03030f542900982100405020400952600901500009141d0f000542500b605d0140003991001d490380785001d000c900c00ea04040c80c050f0040100600401e029500103884c00d021600c1c2c411201869588180c01c003003140d0020a16954081001c01143c4 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 353201303 1250 353200053 353200093
    0x807080105040804030b0613050c0c1e0c0f0604091a011223101208030f090601060c0f08120a0c0905040b091504150b0a030c030c17090c0d05 62
    0x840144000c02140c1050703116201e251056000140540310010042049611150944c07405119551820415814004040c80303640d8001408121188610707000e20001004600c1a10503c4003000c000f070080c46840e0080c0295a0300000c4a258414014040003900810301d026100482500300c40001c030790380d00701c400504884291b400710034481c6d14201d44c81604060146448100909100750b1004035914501185130041142c0c0188212001c07404d00001080002800356000c0c0a407040d00507810750b1030110140c1e5641c024400c982c0001c0c0702e07007000d502041490001000403800307980c00381c0c90404407400f401c40c040425541140d80307a9440303885c0f06090307a02000c0c0002814080b5020310103981d00e0300000740aa10050002111681c0c8034141c5035260341ca942c008000d6001d11400d4040e600d0355071114038125000f5141a1010904040d0b1410f022440b070310035048818001d80b507039088100012921003440340010901d4a4074400c440585845540c0e07017030105400741c4a4001404c4008401c078140d0802 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 353202553 1250 353201303 353201309
    0x102190e01020715050d2c0615190b0a1704050a15110409050a0f0c0210060b04030b04060e072121020d0c030212030106030605040b09070203160201090506040f0807 72
    0x3c0c004c408115070740d8890119411000420800b148091207141c0ea810b1030105044003803c0c0c000d20145900c0215800300e0064810f0482e41000c80413043c44405105201801c864818074030b880400d03043c08142d5154001d401c030101a80380507003004e030852a0061500b40c080c0c5040c1e80a0307002d821102c007008014642c00f00d0340e0340070781005e02c2100000f40012005018030f01800f950203031a0b8001a070500e42544c070825803e9402070082c005210000c40c0a034031020008903c5000d50708200000c00c0c001003410481d000c4079840801d10500759520b89400000f0440c036280650030b03000740400000da81c010300000782400d0010151580342a141c41c07a00ca04030805100c0620707000000c02c419009c5140d0041442040c03880d4074184400c000303c551900300d040c110301004203000300e00084000301c0c5403949580310105542c02079800304050741018003044907003001102c541300103070b2040241903111840201c1841c0300c0e61041c1001c030b0314591100d001500b540c11940084004407403164040010303040812148000b = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 353203803 1250 353202553 353202569
    0x82d0415110304050409031413050915060d0906140901020a270b07050a15090c05060c1f0e060f0a051308070b070e060d0c0206090d090e04050102190e010207 69
    0x820041c40c180ca51207009034441c0a208030740e035100000506024180c04500f0028a01c0d00700d03502e06240000b4207500005000e1140503140413000144001581c4021107501345008040601308011b41d01040058004550219241a25118003a154400c2e000f001e0b40216210400540c0301c3d41d003010004c061b00056040485249841c00f030074040034580303c05000c140d03005000c0d460790303c01060409920f0300c0004480102268840b14040013010640c1e444012054031070350a1a00881c3d907601045802c6c043d00c0c080c5400742d0001600308000084640f001c80780f0104401c000300785100c2c001c041c541821340803510041016104c0040082d0401c3d42e100c0c141d0721408131028a500c620403502c1d000c90394068007100400c010140320100e40201e008007010b0816040c0100002c4d85c03012409a0070303018143c00280300340544284404242d401c1c901260926201c519950342c548894a4090140d030908800f802c00e443c55507003004100d035080c3c9000e14003210b4010750303218002822031501c00240340940591102d02 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 353205053 1250 353203803 353203817
    0x6090210091412010b0a0e0919080306011805030106080109061103040816030504090606180608010821090307120c0603020405010806010f030b220b10020703082d0415 73
    0x405080a80107600c0c14501c191105410400503881c514010610205d4156115a00c40c00024139500e5600c8180d00c900e05041c00c0d14000380412008810341152080c00410303d20b01031000400d0b43d4821a6000e505a85054050032025600d00c082821585240c1100d402651503103151400e0011341e029908050041d410000d2552805807500c4015000342400e1850303d109105c008028188108251406409035460401c08543e0b281006000303011042598100300820100002d0018000d44625040300d0307200c0003410100c000d4581001240e091401051413400042c4180e00840d10200240310290521080c03080352a8000e0031701d1030541c003c5602032810107004020600c2641d0340b1414164202401f82410810040203c000741c004c0c041072260340c0c0e04040040c048401c1c6500040c0c0a002103401c4cd8800c003c04d1201c1c03018400c444807041c0381140542d00c40081003000569140007054141c2c0140c40400b4000351140d41d00f10160384149560031008001325061018401c44c03200a01410035a0130255 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 353206303 1250 353205053 353205059
    0x41205070e150415030507050120011802030606031614130e06070212040609051c0b070503190513030809030f0c0102041701090201090b0a02070e040803041a07020604110a050d0609021009 82
    0x11f59100304c240a80c40c1000000ca10722140302c0310800700c2031035a6054a0003480300710380c01280c21828052104080e0722030302c1084041001800c01240b038034000585030703107100e1185080c00c104031703a030000c001d10040d046a141120703680300c001c01e4401c4d08044108007000d41200c0c20b04460003480c281d10300d440403002c0340f02000b0030000b0036044400304048800036030314000008444002000b240c1c0c3c803000d02074460b20102040281c02540500158404d000f0102c00510140c2070185400403a0800c0307441c441403441d005180c201003401409071951040d800d40442c0d250233071145c9102d80380d40000c0795012007030390089400c3c0032120301110700c4184440c414008000605070342c1c000a010402c40c0c8a0400074450006048120030720034842a00a4a0640d03412003450a2510340780c020740c0d008540c02d90301c0054101e030900249201c241c40c54003c40b15a0b008100d0343c0c450340c40344400940d024412940c4102000d400003070540350903060461050040000140070031403401480b0400d04139405020411030000818 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 353207553 1250 353206303 353206313
    0xd060e01050907050a300c0305010801060605040509060307120c0e24150903010c090306110a020d110109020901031a010608070f1404030209190b0103020a05041205070e15041503 78
    0x500e00841942c03815015281000c40d044910360b20000380310403410802c40001b0144001394000c0e021100043e0b404100070ba98441207a82201e000b80202c100068007040100020310300144d0b840d410650041c1500c104a54600c0341c00003a407011139007240c0c031904c0c2030410401d1900c6c481905074800702c0540004244c0240340c0d0600e9110760612102441001410210020f034501d00090b240345030800760081010a40d0703084064801c6001c0c0c482112042d06207a8008181e09209042e1a0120016002070070f940c41c0851007502d0782050a1a00441596921920360250755200740070b0b4000d43c0180004000d500340d0004848504405030002014400d460042c84141503000f804080d010907140f03011035022611085181c20f40c400c0c0d510280d4846207510230b06ca2132500131250300701000300304801008195690300c0194181d02400041c1e60106006110402000b400001050385151045042d900c0058441a0560380310500350780410300e2544004901d515402c00d4401c2ca14580b00ba00d0001201c00e180d45e0751 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 353208803 1250 353207553 353207557
    0x705010e01050a090306240f0e04080c0102070c03062309120c010605040e1c021506090c2b150305071721070b1509040b07140d060e0105090705 63
    0x100d904221001500c2c00c26203100f031030400c01031540400140814a8444428001a981c1c210700103150b000c0600c0010f10030104555004c100c40045400c1100d664690b21003081980000300203083c595003c00014001407520241c24001c0c500c0342000140503800210080e178480c3c00410115444544401885100d01001900540000c10710051595a60650000c2c038003500d42750740701070340280c01c01c0309100349544040b40e044002400c0d84002407030040703114001ca80d40d01d00020710140340d08040d8003282090400c0ca41403a0300180711a0007501c0e01103070004012040c07a032040522207440c55074521503210b140300d000d0b01044001200c1e401034202d0640d101c003501c80c0e0040c419074004502e082e200d01e103526014040300400154489640d035200142c400c0d03d0f007003607105410407903520344000c000810200c030340e203504090711340003a0603014951f03200d613240c040c3e610010341540280440018070106107040f03c8000d196400c00b032000030030424a4041010151790040c1c0240e07101c2c0c6655020002483d5000382 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 353210053 1250 353208803 353208827
    0x21204120c05030307170d020903160825060507020103110a11010b030705060d020307020c1309030207050405040302100903121815090210031104030606090209090a0c050a030203061503010f060e03070501 89
    0xba009035a80c4a903005280244140b09c80d0076054042c2ca19420710603410101080e049801c180c05440d0740c6210070700805500150021404030200081c00e00340001845500688401441810005a01d04480900c001c0075040aa003102c0018285021411540307428040c03042c10300401e6008000141c1010b0010300c49018010b200341c0724a6010000401c030502c00c000d00308030850003515122001240d0702d140030240c41043c6062380540710b41c8200040710b061900c41e9600c02c45d016400b0342442841c540d540c5024113504c807030a60400c03000c2c100c0c0010301400c61003040f01c8603503424114100e600f130790f01d400900400c0c000b156150a83c90840c4900144c1c9070402c202c5001081c5190004244410021000c1b880c001c81e000985082d10b048000f00b9036011507402040384801c00c42d0328070701c296a5241d145c0e0640d0a00c5c28010300265003884404800e0b406034010303640144000f8900040d1540301080b07440e075038000342d000c40940c183c0c2500c1000855081303544203800c00403d501400c00f403420300300040c0580d400c0c11 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 353211303 1250 353210053 353210093
    0x1803090f1208070809181e01061e0e04050106170a0204030b1812120405010e0a170c122d040f0312020a020d0506090706030e0c060703021204120c05030307 68
    0x141183c01c1200e0f9000305c85ea481401407030304040141c070030021400c00400301d860010101329650300e0040d241141a5480c1240c042e43d5402c3d80546d54a402200e0055400c02804280301c4489a4406079a440303000b039501a000c2c0d941d854484c03080040303550381020700103000c0d2223080344104030600208110104040d400021300704915050003141214500c2d100c0c1e0104004241003000c28903003030441c0d0018407507000d103000340e00900060b1514100140c5807040300030300500446498038200f2a0160b41405018059500d81c103442c0d088030351200310340e999131040441c2e507101c04000c8504d0610030342c4c8142c40c01360019208541418203080403180790000e842400043d1424042403242100755108000c1d00f03121f164043c0c0306844542e003a152465a810702900c0c000c0880c082c51502054141c400d20a122030b0f046a140100b00305d20036030b01445599403101c01c040c3c04500450040385050250300e8000c000510525807a102e00d0340380c2c1c4c2808240c8401c2900082c1c0300341c2007000300344082554401c074000310849031 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 353212553 1250 353211303 353211307
    0x21306181a03061512040c15020c0f01081302190e010e07020c040f18050c01120209090610021207050c04050703020f031f0807080102071b26010207061803090f1208 72
    0x315068410b1402600d107500c210172031900c1003004000c50301d0102d0007145d0b45010314100c4030030031150698070b4003030b907000d00d54011942d408560015807040b503140da008010540540c20b40d00c925004104c0d500c120b0510907030b890741888010080c50007150840d600400003039280450702d0070042d030020340318000700d2051440380e42c8554520089d0704040c2e00500912000d80d00803000b8001a2402c191a00710010320640402d0f0300c810401213544481c000ca40120000a041058554a800410001039801841402107100d80001e00215a18000090800d240110001c040c2c0c0c4941c18104810f43d14000c000608150043c003040c4c819180703040c261780e0000000c10a401d200c82e510003031074001d250540c0c4101601d1103603103000130303940d48103500501015006484210030400c20001d41207218045218117184204c17a000200041d10204880021502000700050b140c40e175140c403158141d1340c02800085000310741d100031008054110f41c1c0c500051040354500c0c00514900380340c1d1041f50204560280c144000 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 353213803 1250 353212553 353212579
    0x30507060f0501030311070801061a030405030c031c060b0405090115030f1802010e06090603060603130609060b0108331305010801021b120f0d021306181a0306 70
    0x60703030440d070490300c01e6103000c102c0c0350380d6814001c201243d103130942a0140030351840854000818003400040e070322a031504a008054911031903407240d10042003900c90340000c1c0a1201400018402841a0130b4001810122180e00501d034004a8049074006140824208010032044d100c0000b01b41c1128990801410310161144040e8050703d040002c03240a80e15103030000105410700c902c0030342814000ea9850441000303080c01e001d414407401420030340c080b0040c0300080c0b8600e4000010359100b800b2000f0014000b204d544d40c02c1c1034561000b012601281c94000309501540c0c0008110390045040c1044642c444e282d41c2e1940d81d03052080080e11a4203d52a80d50300b59490b03419402e00c50f8208000100899170396115568000d4201d11062068800307002130f0103d0401001481200500041548614003001c4004c106071550200e10b42c000c4440e001d000c101422040703510b0000050400c0c2d01e41c84481c030200b20403c441001030303070022080b60b16404145042d001881c41a294801025203031002403600c = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 353215053 1250 353213803 353213813
    0x912070302010f03180b01030302100f02091305040f0813091a0f01030b06040305061623031303030f1a0127030b040c08030a0210060e09100908160b090d030e0703030507 74
    0x10b011780152010003940000002c25600240701100088401c10801c00d0071510b408a00907407060104180d40328040c0d61803140384401c0707980300e60f811622803400d00c428402300c0d9445120075002540b02c8603d07508181420040424030340036603503000c035400d0382e51300c1080401c00008100c0080052658101617481001c40d5140c0c41d000211005160072200b22042440c000500c0c0908080b2414020b002806c00318803c0740d12080b803011800f8502040f04100d04581c0c40705005100044101d205404268840e145480314043c1c51250f4044150150b03210500380c0c11000000d040c940b01d50707440400c40c1501614001d880d200e03d900040590350f114000050039102c44c100711080b00c0441c0c00103031290100042d00b843c1240c00081081c0540c0484c901030000301e070385031028040c40c2001ca8020380160010104d02000e521240d000d40704503031103480302d0b90600b0344420b88205149c41f9542c0441e80e1840e40401e00400340c40070030000c101d400c1c01e0325003808001c003032a09060315034a69100050a012010669004005c = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 353216303 1250 353215053 353215091
    0x22419050405210403020406060507020d06050a09120305040b07140f070f140a0c0905010e2205010608030909090c030a030f0903170a0f020706050f1b060106050912070302010f03 78
    0x35100308245031020082020a200b03e13401444100d1195150400006030907000748203480070305800a00d14007107450140c035000c4c042c00c0010188078505a0342d40c609000541000010030b142d5034142d070001401e28080c034280ba444880035092170288041044462211440c040454036060501165580c4a1490b46400d1140ca12030300c5c80281400300c03801101c001240000b032003a000c24000d070304011185507103280703501c100d0f00c081c0520150031444d0320003d80100d40340a0b50205c50030b044228480d0354482d5448080c00c440c0390b40c00c0054160000a0805007034604098040d400403010000341c40050001d200003544c80d418981c00a05020400140713010f003600441c407810040d80c10240d070f11030a03c1804a056101d80c080d0301c040c40480d030340441d45102207200040394015130b41d0640f1110300d060340000a07480743d81c101d040030204221102c2a0400f41d40c000b80120ba000344002c0e2917190b110841c80c410000303d410030021401039070707000840800250303a11003042003e201d200d00b40051440284080f00d5511 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 353217553 1250 353216303 353216323
    0x60c030e2a0a05092802090303030402010f0e040501090c0207050312070b0601090e0403030207030f0203030f0f0603032b06080a0308130c08010e150a200c0705030706022419050405 79
    0x414000410107414031102c5400703015041003140b1507145842c5c0031240128082c408149405a00c188001001540554904900c1c1c0d2098103100e41c21041c04000107050b1402600080850b9484080760703416030f0380402c00c1c0320180c0801c0700a07040028550440094900400101410001c0000c000c41d285074006e005820140c007040c0f07003584d5245000e00b009806580300703a008400081d03014a15450140c808800e0b00c2c01500000709680e103a4403010060030600d80c1c06000184e05000030410301400c1e000b10405c4c00300b246050220052242c008044c4c50048030000d500030aa190040800701e40007075032000002e41c0c4545001c03080c003501d404500384100000442d0b00700c2c3c0b41942c42c0400c00d103000400066000c1001e1a102c151048681d20b0011840030b07902c0c0120a03e8400300241d02804a00d003c101c05007000b20700b1082244c204680d80c8000a2801c119940710300003681044a000da0051498411134401100c0b0703d10900540c24041e09500f03840e0041140040301d1507458006c5020071900303008140c01 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 353218803 1250 353217553 353217559
    0x7120e0d0c0f0e010311010c1506061809050c1c0605060d0504061d03070204020c0f0111030f090d27050618031912050c0118060c030e2a0a05 62
    0x1184a5481c0200c0081c1c100c0c0540c0c5100c92460030700007000549410300728103803603020810407820390021b4015103000300c900004503410a03038211400c0780c0003900d1198800810480d6140729200c4c1310000280051045900310b802c809050604011407907980404654200c8900403043d1140207007110b8010041c1401d410582d0301001c000760242610344c946c2c012174003640c000c8004010701200f4152a5104104010241c11240c03c14003200015141940c0500b40c4c00b2002d0007a2400044c90400d1607085803400070710404080340c04400d00401742da1582c540c0c2d5021007610000e10800100c5a40604500600c4640c50001200c6003001110b40350140a990001c100150500381c40750084945081101c0440d8005802031050b2481b410030401c0c0b2030740c40f160464010311052f90402032090111229441045d460002e9901c915500c80e41045090300320b90b00c7d41c01200000740c4580504c0c4020141e078030002da224010780c080d010040c00c55409034554900781038100d4001c50ba5441303007004928100059440154 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 353220053 1250 353218803 353218819
    0x30f230c0d05250f1b06090c0e0103051e060f070203070b1005030d14030c0708070b040318061106011502011d010e0111070f080d06090e1c020d0507120e 67
    0x900f5610351030003040559490005100b6182006204584040344003c40c54002181003080d0101e228110521130380d001d0050720301140e0703505642c49103248441941e02150b600b0303406a00420038403100740001c0106882500c542c400310186000b919581e40f0000d0062645040020040340d102d500810484d0603055214070f00001a1400c0c0000c0d5418444901c40c0500a00038040404c60051141c00858a01e5103000035140c01c688401301c003180130f900145811180c040742003000002050403005043c2c807941c8203640d40401c15104010a804448542e40045d0a00500d000c95070013101001c0b540030f042d200009003a03000c4101d12501280900502c00580c0403406850700703007020010b030640080a80f220780c0ba00038460060005542d80081c0305a41010300042c3d41d940c991000101c1e070700700030003541006180100e107030390b141c9041000f21060a003042625600a11650f1200e440320003030140380c10200e0000d0140e4946c03001010341107204010008281c80b850829900d4828054509150780c6907002c3c0500c1 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 353221303 1250 353220053 353220061
    0xe04110f0f030a0c0e0612060a0b0103020f0310230105070605220b3403020702040b09153c1804030f080f04080708070507091a01030f230c0d05 63
    0x161020240161700c0c01c541381038000744d99401c00d58021222031001c10f00822545d03889007001030051020301c84850425403308000040c120860003d1409070911a042043d22454442d40c04940803424030901401040c100b0303058407680e008002d840980d40c2086012413240e44500fa0f0304512091440343c0b214007800350703500005100390f03900003510800c00c8059000900007503048108000c0c44203900f40c03108010070a070081300705100780c002c1d0003000d1000e4404560504040006903040c00201c036804451410104504e41c1e40c90031b1006481c0000070355182c01e140801c0c541c10904c400c104104d00403126410540802119100c213441100025402c2001c001c0500f42443e0080000c4500c00110340000e440308040340b081c03051210600e00450b40140c501e45400b4103955281c15a0b0084d4400342c62500400c0000200311005000c0c901d00c44507038550310700b98043d2450014046a402019404049150051388100c91001c0c0c4030404044014098440642e030744c141188485106038141012035606110030b01c = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 353222553 1250 353221303 353221313
    0x1120c020a021306051f120c260f1b07050f060f09060f0412020309130c0909060e01170a05010c0c0309060c0b071805041407090e04110f0f030a 63
    0x6440703058402c45a6850300610f03c1c0f180000c0c0d643c0c5019071988a016010107081070640c03860600b50584103410040c503c8510f9401644c00c4914010151000c07900000b10344641101c8946907049041481150318010308020744d04007181c5000514070030550030042d00f000700206d403a0080d500d04680c45400c4482001c81c24010603240d10090303a201003088012808208004800302d4080d10901c0c96603207582f01580c070703501d0701d42c03001444c450f83c001035000c10860364041e80c0340c040311002c5194241e207001c41c1d48040c80d0300c001c0000c44180e02800007903103810414083c07054030009150458104040b20500071492500145c02c1c8142550300425a6181006000809400c0800058114000d48a4003000c40d0303615400d4414240c4501e004042c0f081d0200040c4030203014000304200741a0049480c405d141d11180440c0032242e003203008a055030090b104000300c0561007002480a41050700d030840707050505590340d10f000101003840034441c00701020203042c10f44842c980c1c00c1e102200201100c510114038142 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 353223803 1250 353222553 353222563
    0x4031b030309080327010507050f0705010f0f020c0f0f060403030816110d1107080f070311010201110d0203060303090406090e01113105090403080106080907030b0606070201120c02 79
    0x31030116400b0741c40007910410110646800d400781120554030050034030351410740344144803a120305006e002d00814000c51000c0041d0004400700500500b041824400054201e10000300c4600070020981900c4010302e6000c101d10b00e00800a03039120760000030b03590014007529004c02046070020310106000081c1640310310541d006a045058400080000460450305200c0b0458003143c29400980070404c42071040e0b4181c3c1a9648020568851540340c1c00c0d690b0520700140f0b01540d55034080c610a0081c42039105074148002000d00007008003041c8018241114000d0180ba02503559001c000074100ba1018002c64400440052080008a449503440e41c0100006803c40701c45628081038903941c1c0700c2a501302c1303440b402140d11041e1070180b5504e0060640f5040003201c100380303070340c3c41300059141c031180710300c40c09a0301c6038071520050b40c100400207101d00c0000b0103800e01e50f801014200045405a00c11075000103003900c80035039889140c00142c0d000c504030780c1100403140c6010302c1c000ca51640811 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 353225053 1250 353223803 353223809
    0x210501050c070309081203060105031f0b070311010b0a121b0612050615042105030703030c0f0c02131d0a140d050c19050f030703020c0a091505090c04031b 68
    0xf1a12085a00ea04c26a5541d46c80380031011b61a080800115507958000c00145910803484100d244203400e09280440e0394940383d0b48400c41c124404240d0310205508422070b15a0380c040344008000700c0c0703030351000118400c80d28410080030a1410036804248030940340f11a27008005924030009013503403034800400c500302c2032041c02441850100403c4491410030300d01401c82d4200206141090700b80b507983c041103602d244401c0c25010350316500320000740061000c0d190180c0203407400030b005807907035034045d1028143c00b80b18002c0100d550740b4400103a5a00c1e007409400040c00c140014090305240804503405000b403180b0203203105c1e24400a04100318690641c081004400035100e040c0c1014809580c0c902840c0c40070703165a0440b24600749040c85085011f09118000d104481c54626440440c07415903021160540060700700071900d800302d0619441c210b00610f511482000045280854200c1311007440c0038180c4106c5040c40403890710003016081d140556003000e0550f020030300d0030780001a6540c0c00c1c4 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 353226303 1250 353225053 353225057
    0x52b031b0c090f050708043c020406081f0f06081e160303020709110f1309050f06031005041b080c040518071203090b0c060f060910210501050c0703 65
    0x1086101c0300480030b000701401781c611610381031903684036652101c103184900c4500c4845140d16100008851182c241142c001141402142c100f41900d80188000d0f02c9954100e0011540728204084d00312855040ca244c862940400c0010101c031342c54111005003c8076800705030349109040a48180c195032844226014040030100d400c010300220f10780344000c08501c4042c0140c5c001c460104111403081e04090486050091064039005805280d05442c4c1c0140c40c411040030800c070018010840e0502c00c0e02e40020030120041054544800000c1c1c0e40e401003482c003078245450f00d01103070802c600080e40441c07500c2800901100c0d5511222510740c8d800f03d0151843c400e41c24080032070149400304031000d100c0d01c50140508003580c00c150031400c00144103c0110100804140002080059680a04400344010014106c182050102c075013103c2d0026011034450a0040140706c21a9a606d0003442210540800c8012140c0c0001a00031628201c520242c059400c0400300404201040001d190517807080e = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 353227553 1250 353226303 353226311
    0x142b06080d0f03020d02090a0308180901030c0b0c0c030f011a0a03020102073303050a15050a170f03070f0c060c050c0f040b1008060a052b031b0c09 65
    0x1644a0355a1065041000404600c040c035149000d24401e40080c08112010b0364054548a118000300707440e0714050b0b0060340c80c1d4034040341d4542c500da00000e602e81c0b106e00c02c66550b00c5c954190b4440c420a81e1070f80c070600300e85031400110507110550600c20400d2580000707050320001e0301440c000501800600a241d44c81c405040d41e00700d890302d0040800410b598042e4010320140d410054018424806003110ba003800c040503078801852214103c1c0c00040043d142d40214840c18203110a00c1580c14026503041e003006019402d001540b190212141180d02e07d09440d41030040802c5c00b542450544000308003940800906031090100d410440c0a0152184841c40e008650f5910100c4200003940d4004040350888181d04c916403600b100c4034066080300800000300598620000b8039400d010300c105402244003c6c003041501d10305011010000c01c2c0c00c0d556071100e0750a81400a982001ca840ba955121024040071000d152240c0c1e5160551000002155605245410701907103ca0040c882c00c1e41c0c003410 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 353228803 1250 353227553 353227559
    0x405030303060d03260a110c102a03090b0105030303060d080d110c0c01080106080f07030b060408030307030e0c1008010306180b070e0f010e030a0f030201150f3003142b06 75
    0x1003030101c560a080703d802030058450850b1815015044e5216400034030007a410002186000203101d1003100161a04e0009205030146881937403040140d0100340329800c18010070020352600d1801d802559402424641d50b0030401c051003000784000008040300a0000c28940e08100d07001a0106d05400c09895a030300d26a6114800c96102001f12003e021000004010130f9401e40283c003d0303145a138006120178103140e202d40c4001e10395082243c80d5400251914100320380d8a8041c494050b4802c403d8404031540c010060018095007418880104115a03582001e5841d003011244041d156602000c018031500700788a0041c401481e5218a901c2485ca1f51111720a030360080c804074002d201c02502400d00d00c01c1540782d9218111003000240c040d5501c034081040c54000f9080c405000d00300a0071100350440c2030a6060401c02c0c80c040701c0c4100b002031070039030004c030480c03e0081d10a1203500d45054409a400582401094043d07280d001c6050501e100c900c100d8442c2d00600c100061107485070422503555 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 353230053 1250 353228803 353228831
    0x12030e040b0604120f050102070f030201140c04060917010905031902060109360803012706030804120c09050705070b060907050a031a0306130212030405030303060d03260a 75
    0x440d51140724807140075140c0304800107850174001000580508001414100d00b911380303005c4c002d582c60048006035514448154140410306407241c000c0748202c1460308203800d00101604044132809401c0454241e40c05d6100712074000d401c0001e80c00d50000541e500c1c1c5466410125003604501115405030040303400200395038026110f14a030400b0202c000b100046000740c9482c900d00789a0701c001e0051001c1c48216000b00300f62000940c0203041d501c0241402c01900e22217100e0503244541d007060001d040030070401c0402c00c80c60540303003555966032004180c0368481c5071a4564550580c454000d01d4140010007014581110142c03400500928890000c1c2c4e41740020024690703c1140e42102049080c80007410007442648020b01403541208505020880c94002a140110407104240d4185148140c0811070920a003008501704100006606080c1018006a100c2c04028100c0b80035428506054061500c41e424020800ba4881e0307115501c43c0000b0058202805d0450302c41c030f010340c100140d0703001e1740d1 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 353231303 1250 353230053 353230057
    0xf09020705150907171005040506240d0201030e07080a0303050708160f14070609080a110a030206132f0111030913020c12030a0207112b080412030e040b06 68
    0x3c40e02d1010b0729505040901d00a03031112203051100352403140300034440001002e03200d80c5000e02d001d01d0060466207461a03800006441409581d895036007940700d003111341e4580300007620103294242004142803120244030b41c504502a4046d01d610310540341d1b06030034181c050b80954020045641c545401d40d850140800004a981c20b00c80c002130703030801a0340d07142c81c03080f420518200781c00400149001042e480f524245e90803007100340d45030080051013000c5181c001000d003d43c001440f000d0000ca4855441c06505d91030000c00300c1c002d800c0103412134010041070400742011044000e4404408450072030042218101469105021607646804211011000415900c1c80040103203200d0700e8200c0b0500b8540a5046615400403d11034080d0903c3d40d04451000b440c82105074440040c1c55010a05101d2403542540710520700902c00180300ea1103041d9800340f14441032202c0d030b8084052043c80d00d0085906c5c0b0071a030014400f058613414190403d54030501800501004031030034080111801c0401c02c0c0c40c = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 353232553 1250 353231303 353231311
    0x6061c02120f0610030c140406020106080c0d0209070309050a062d110d0902040905010504030f0e040605060304030f02070f14130b0a030210050f0f030a05070206061302130f0902070515 81
    0xc9440001300c185281c1c8660004c4160a0b82490128218010313500c076106a50441d800071030140c2d446030420301c240e00e0200440105c45000700d40c00c0c0010310198020a50701d94014154100309a16180c0e52814040b04210b1071114640c0400308203d255130840c41501210030840e5251003032042a0b01d19245c4114034050215000004080186000c403d8052140107040c00d81007203030000d80342c0c503052020030403e100c0c1c1031040d4000d0b110341080092a89004000281c581c513000c1c8030f9442c0c603505010540303c0b28180e03a4400d616007400300888082481c20307440d081c80380e44482c0e0021000c80700402c240040000458200d4416195440000010b10440e0203640083c41610742124481c2010030141c980518010312035110b504025140070b402c401c044520350300001001140380c40010034010003800a12940ea408951403001e800b00381030500004880542a100036070319a034011031045585c24080641d01e0060401c140656107056850a02001940080074265028081c10104609001c86000c4180c86 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 353233803 1250 353232553 353232559
    0x4030821040c090b01021009030e10030608030403030509010c05100606030e151303120501061d01020102070510150503010207120f11030306010804081b0705100f140306061c02120f06 80
    0x160030f0605030035000514503c60018114807034030f0f2502204414512072004000d010b41e481d4031040c01d01d04184413022480703010f02c000301450128104000800802500c083d00d50500e4115521030b0301100482d0110b80b280405021030044010140c0301440d15070100c01107516540f002c1c17040c180d0307042605898400c0c1041d0f01074940c0e41800064080c029200e9030200c107501c82d080c582c854030010396099003203540981240b00800d03c0300c841c8080481001c840d07030500040900c001e500d018990b90740c050b1221203400c0c400b60200d440c0e1300e2041c0448811450100034200c0138008646a00c2d01c0d00306640780e141503030301240206070061101d0403a144151848842030b400000110300e9615802c0044600c400001c0054a00358800d022107003000305008804800704184c90700910315641004200003001c20850007800c1405005040a50715a81100f41805c5445418001359203075550400403510a2299848460000300c80a040300d0134000e03164050101c2c1c14002c48d01d83c0c05a41e810001e01402d02c030640d44198 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 353235053 1250 353233803 353233823
    0x190234050a0b0c1204050a05060c0a0e0d111201020310080c09070503040c05100c120801180225080712030c0c0b0406150f090e0d21020f0403082104 65
    0x4080703052102c119400222201516143c09900c441080701200180d40032116908111345010070302c03030204012070f00200c6188c41a40740c5180b0030000340440c1902d0080da070144040700300803000d03c0340043c040f41001601400308414002e00803040c0d4000c1d4011034000d103083d080403001081903280081d0310010a6805042d802042d1541d420945a98000404c1114602070346000401c00e511404031400e0445480d0722021600485032030301e015554002645076040040c06001003121100030148000042881c40b001651010701112050b40c0014085c0c1405450210796848230800080000070f008281c003c4180c0382c1085644030084003a10040a410f20015000310b01c5035010444078052182c100748141800114052080c1d5030007100110b03948a6109030020303010810082c0814050141c00454840140c40d00c08041800580948a0b80c607415174200c00f0055207060070121741d4112021105000707481910740f55286443c0040354400020450303481d01550050141038a030803034881c00f039640b1080c2b540c = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 353236303 1250 353235053 353235073
    0x1170a02010813050111040509130b011701020d050106081905090307020103050a0216150c110d05030c120109020d0b0102011e0f09080d0c09060c03090e19023405 71
    0x100c2c0c0e100e01034219103150300e041504000050003449855a102e41190503107484d00d00d884104a4503c20062081100c0491624190001016442e2660542d24403c40100f000550207851900a0150364209005c03986004000b042c41600060300d2440b070f00302c520724803148201c0c0c4a4080190b43c2c007526525031603801440407070015802600000c1d0b000003003c9005007000b03200348541e103445c4420076040c0d54803d46003022814170040c2e401103a0b40708001e802c21140d0503500000071a5035240784291b400130010040081860303001420215015090f401c3d4108c074295850b046281c00035400740844040d0300307103800d6046a455006014100d04040d072405204980d42e28240707020051f080e0301c01c0342c0c8103581d5105100350005015001a00342e544200c480010180e4450740050010352503600401e0901c00745208210010b50b100302420251800c043c2009a951148840b0b01428103400a050003441d0002c20074002c0c1300310310346441d4940140c50100091003540708410354865441d01e8005002608064044 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 353237410 1107 353236303 353236307
    0xf062a030f22030e0f031c05030105030d0806100c06020c030a030b040e03190516020a09090b01090605060412021c050f011b1e090504050106021501170a0201 69
    0x314a01c110040d01e0140c10315a04c13202c440c0c072a051140d09642682c8050005024010181001500440e00804090050342090084600a200d0203000a1081f403140d8520790040d00017500402d05100c1d81001112080f03a04441507032030a0f02001454a412804c000914503c0201da40c0001c042c0541c4080105464030b58840089941c0b00b0b1140390460381d01d00000224070425030908590320320403008001c580070001070b0040d42c80107060310000396201540c0c11a040c0300d4403400004445a1b201d21011044071018050749030854010320003031281c0d0030440c0030100e002e4001011380c104100d00d0710601c0c43d16485800102c940742c0104084501d405000d0107080c14140c64a95410380452821000401c0c9003610303a6181d54000b60100c407080722a01401410015042c0580300b800130b5078440741c0103582d07a019000582130400c000d400026040800003142d1411030092009000070b00915001 = true := by decide +kernel

theorem cover : BRFrame.Cov 353057553 353237410 := by
  have h0 := BRFrame.cov_init 353057553
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353057553 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353057553 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353057553 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353057553 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353057553 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353057553 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353057553 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353057553 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353057553 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353057553 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353057553 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353057553 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353057553 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353057553 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353057553 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353057553 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353057553 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353057553 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353057553 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353057553 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353057553 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353057553 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353057553 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353057553 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353057553 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353057553 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353057553 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353057553 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353057553 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353057553 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353057553 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353057553 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353057553 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353057553 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353057553 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353057553 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353057553 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353057553 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353057553 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353057553 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353057553 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353057553 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353057553 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353057553 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353057553 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353057553 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353057553 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353057553 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353057553 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353057553 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353057553 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353057553 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353057553 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353057553 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353057553 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353057553 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353057553 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353057553 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353057553 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353057553 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353057553 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353057553 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353057553 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353057553 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353057553 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353057553 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353057553 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353057553 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353057553 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353057553 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353057553 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353057553 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353057553 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353057553 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353057553 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353057553 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353057553 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353057553 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353057553 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353057553 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353057553 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353057553 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353057553 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353057553 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353057553 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353057553 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353057553 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353057553 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353057553 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353057553 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353057553 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353057553 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353057553 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353057553 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353057553 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353057553 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353057553 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353057553 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353057553 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353057553 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353057553 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353057553 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353057553 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353057553 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353057553 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353057553 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353057553 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353057553 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353057553 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353057553 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353057553 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353057553 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353057553 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353057553 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353057553 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353057553 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353057553 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353057553 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353057553 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353057553 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353057553 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353057553 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353057553 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353057553 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353057553 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353057553 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353057553 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353057553 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353057553 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353057553 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353057553 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353057553 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353057553 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353057553 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353057553 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353057553 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353057553 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353057553 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353057553 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353057553 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353057553 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353057553 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353057553 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353057553 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 353057553 ≤ n) (h2 : n < 353237410) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
