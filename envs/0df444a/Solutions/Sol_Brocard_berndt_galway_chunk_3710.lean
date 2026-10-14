-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3710
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T10:27:08.773932+00:00
-- url     : https://prove2.me/submissions/74b8f6f5-1405-4b0a-99f3-a150b2843337

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 667086330 ≤ n < 667266187 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 667087580 1250 667086330 667086353
    0x91c02030712050f1903050d05040507181a010302030615211305010b01181e1517100b0307050d0e0102030406050f06090c0f09010e030303041a090309010507 69
    0x100030126010590b48402034280001060b00aa41d26000b066045064410501c680c14105c54000048121224a964090524091142c00d024120faa94000900300304c002c0180201038038038200703c13040803080503600c8809000c2444204507844428044801994024002d5038040c0f02d0003000403daa4143d8503c009954000d1240d00101384e00c040095541c00c025610101e000d81c0c16606400d00b80790060414a00351001a00c041d410481503a2120b12185001c078404401d0740c5034010070701040c0b00940250440d14100360419003001440c40c00b83d40c1ca981d04251038210500107030105820b603a07208810898440c000340f069028900c420030000700311a00c031b40014490320440032000a60b42c003003040c9050072608212801c0713504656034028070569815040005030302620031140c0113042e180c058076198080c003038500c0c200400840443c0070b01060b8094280ca40c07800340050304885c1c0b64030f0a03007070031410b0445100300e07001d0802d40b000100da011800807048991804060f1180c9180c090b25a864000010 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 667088830 1250 667087580 667087583
    0xc071a0c0f0d08190b040f0209031204030f080c010930031e050603070b0c070311030109030c240207060606110a05030f030a021b0a12053f0c0d0b06091c 67
    0x5940305605c1009070396034400c00820304016000180c94210110034075141c0750240200a0020800b4401000041c50201d040708480340d02000c12500d60316940d21007805028150002440001c10a2400540403207800070355200502007249400000080d800580485140c01f170780c0040560824980c0c04440595040150825000380c22036544603503440c40b41e0201d8000e0441108503410a000c10424412224441d81c4400c0342203000300500c0714507507805020440d0071303100100f42c0340c590f03010303d070240c3d40541058200101c5841d0030b6558110f503140090007020303c1c0c05900d02180f0407021800400000003004410307a5801002075250950030405d00b2010741005181c03d9407982c0810040421502c1409141591500c00000301100d01321483c1105100304200344c1c038401c112080c0111595403e240501164000703070b480099410900c1c0c1f801500403085a42040b0020300b1405c0b0900c03540c0802280106050310b10040100020240c1000700483c81c4607401d0a40d41c80441520342d2816a0380c2c0c0008050b00706d = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 667090080 1250 667088830 667088881
    0x1060e1f020c1002150a0b0d0f020102190303051b070503041811041e09051501110c030303041b0605040b0a081f150305010e010803040b0c071a0c0f0d08 67
    0x11500c8000080f4504240280300006810004030711180c40c500c541d841e6040350706c8070020f00100c0c82007804070300c034401900805096107140c00440d40540e40248449244c01c500d109907440315011904000c2d0150130107507040c041c1540c00701c80c00004c0c240c00e901503910340355211029604d001d01c1c16061052a543c40014850320360350341c40c1e0400b0b20410140050000305900d1940030b50345450310300610b1502c0b105611491001e42820108503421404885078248160242080e0100b080760050242c0340807500c094843e0188000020b010521003058151001d031843d50884090085c1c0b50a01142c03207006510405403a2242400b41840d081e0003100415440840910b880b40c003801c0c0e00d440075071000784035440303410312a10700c0c603090344802d034507000c2c16014040200e440102d651402a40d2a070300c1c0318610070180107050101d400021000d05120540080a24803a101c07034100340000044c41c2075010b801070100f40c1c450071440031386080003c90003d0043c00a41c80704c41032507640300c045a6045010032250100e5 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 667091330 1250 667090080 667090093
    0x414091503300a0f030b0a1811090a0905040b0106050a1b14010615021b031221040501021c09020d02010f140318070608040507120206040305030d050f01060e1f02 71
    0x26400303210141903100f2031555620020505141c0181c100e5001c104494020441d0440c00d01c803000741c410761700c580403200300d5002540201c03948440310903001781c049166105040480003e000303001904401d020740d00403074400c0381d1666030345002e807400d1103640210340108158141e1910108101a0948201400343c941c1c04d240541c2c060026003120115000f95618611035070a0128403541042814003000c002020440342810800000e81c0e100c25030150b14a0303140380003800000251b40080001159000f91403003003054140b516086010b50016071a0920042520322065400201409070850300754002e0040e040f104e186030011107101ea016001c920a0025141d0f11203228a60341004511880400d200320004030300941c034441c100141c552017001000b041209102c081500440d1010031200c65101c0d1904016451001c14041c0c00f440d03201070801d01002c10040580b00141d0001032240743c100c01645c0060380c0b12002550308180328016540c0080c07922050214a0f40ea560700d0700e8000c1e20b0703401201ca5 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 667092580 1250 667091330 667091413
    0x20609040b1003051b0703050d1812110c0a0e0601200a03090f06360e01030b0a0b06031303030216050d110607080601120f0f020414091503 61
    0x2d90516011480b40081d58400400c10b841c041514803a40e800c0442c68114600722160f00c00525034021413810306511580c0c4c003642111410984260400d4591150a0b515020000e10010705064060207020849004240b0504441e10300301c0e81d88415100d603031040e44841e40b140c1c8011034046a84c9a20040315006800380400c0c4410300300010f041c0548a0790781e244460341011007041e014940b0740d11a0051103074880c14074181a140312152800806891403d1900724420070945840c486154826015140300344004028403401045003442185041c00034000c00700d5020900c131851004031002c5c00d181c402d0b0703602d8074002031281d001080f600442c085000d00e1551203454a604005e8401503510200e2014104da0110040a01101d41d10480c60b0400d85035515100d00042c104c0f03003040b03604010841d0b490140e03110f20102c0e58040d01d65240781400854555032180445c8202c0d54600c242d06100f0042400000c14000504a940c441c1c440c000c1c0140c030399120010501d100b204e1b05c3d003910602a03d4030840940 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 667093830 1250 667092580 667092589
    0x706050723070c09090221100f0c08070e010e0120010c020a030f080f0f0c122404091a1b0f030403030606030e0a0201051305090c1e03040f020609040b 66
    0x11500c480c80c07031000c2d9207441e9407030859500c60f8036074040c801503810003c840f07001d40da4130030034018030044507040341c090403018202060400c014105d40300360341880e050f00e21840340c105a00940540c0600d8541265580320410f01780c404020801d1140d0019a40b188010640d501c101c0340030300085070040a001c04500210086401d40301c58074002d9006900844400c402e040e8041e070807440b803454504020001c3d0400740021742d11814001c1001c8641c03003401c004500c11801c400121007940c0381c0c2c12400b800d2410480d030441c0310540908100201c03d0007002407071042d46000d00c107480791290b0096a10600b000b401c2c0100c2d09000340140320380c1a05014a100400c0101013000900c0381941e50402156645824036003d4103d07002a04801c040510700320341071007200c0000441d9210b49409082541d01d64282c1d040300d103074610082d0406904211141c050003100b40a90340901226015464011407104556103030172054001100c02900c002e27803110300b10026043c68401030008a070080c2000c81d000e00014040b8 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 667095080 1250 667093830 667093877
    0x3010f020306151215120f0106080c031203061002010204121b0b031509190c0905100206070c150f050c07020a08030f0d05130f030503040302060f0105010507060507 72
    0x21840c0d0000200b00d1140740c41010541c0d4680c08032440e44c18401020300c0d42402800c0101744e5840b00140f100300c0002541c03030000b107200c0d4104804c211104509402000c0e40a00080d00c1980902d1007021194109403401090340499030b00600c80581c20b59540400b049030413504000241c0a40d54204400304100018443c1c08000c0c0780129181c1101e00315401400ca0242d9180c0c0c002e6482074010300501605260416401c414036001302c52401e000e80701c1051080303815031040304904950345400f45400b00d030b0b07402107030b10802c4500c21990101c90300d180000c244c1c1c842200f180c0c110300040d1012940400906648a0850001c01400300010381c4818001714004640781079034a145c0160b00810180700714035011034640003410311500030f541051070b401085d0078280141d0425840c02070701e590000c1c80000240550400c107941182e80312203407a0460070054041d900645080d00140921000a6000c0d43c028002e9070485906a550741d1070a5980d85403280103210103440442040f0300c0c00c011880c041340c0f201e442c = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 667096330 1250 667095080 667095101
    0x50405040b15010c1101120f05070c0302010b060c0634030504051e19060906051f09060522020c0715020d0c0206070807170d0501060f1e0f09050301 65
    0xd9074560400350700200c02c0e05a070440302da0401a010100a00058041d0713121405e040d001c0c00c02c0361015048811040c0035140c070401d40040c4514100410602c5548481c0d4282480d009030000c108054142d000c0c01280d103d00c10081b171859000b400071504144905000140d40016030010202a801c4c855410301200554000c110000e40c40740103000c2403020a018216414995451421161250032111780e2941a08540c40001d280501d414000f440410740000a40a030700090811407407910642e191700200701d100442c1d1554145000220380000c99208503c03d84500510800905c07010002d00c00401c107080030707400b00d40d5409010a0618943c1004207101400060030250704080a00600900d0040c2d01142c0104200c03150b05444090307210082100c912a4002d400207a980125007130817690301030182c14505c041403000448010804081d07200364143c0305d4035501c02d0355142c00800101c0f5541d0421082080b4500780c4440c190007039028050040358001d884c1403400c0516520000203003119104440c = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 667097580 1250 667096330 667096343
    0x108130c0311120d080105040b030109050a080301030b0610020c040f06170c03120405060f1303020310090b15011e09050a030302010207140d14030907050a0308070204050121170405040504 82
    0xb50389101c0c5003c0800d0768920800700024406240802c41c01041200188142c500403582c4440034039142e10290410300305142c0020031101c0a09540c80c00981c40c0d07000344400c2c0e5500000d2400b04003d894000b5a141801007154003c10102c02c0d107804100040c04201c1d0186881c80c0e407048001084980300c1070200c0c0c4d111404000d800e0720b030a2801454207104800d08001c030014000c11062141c0e07540c0c201078903854080c1c40240c54442c08144081006200f441e0030281d854440c00c98240312089444d0013410f0900d2003445c08030425141c80901d1101c1c101c4031000c003408100b244d102000c00c0904075034201041c003481c1c9064844240d40d100412040c008680060700142d4000818006000380e40c0c98500d00451404010b00c2d030b403414103400504000740d003400318180403070010101d03140c04400c020071009482d0050500d080aa40c80c60907840a500054040340504d05110000489019803070041d49500650700b83c8007500d001c3d0ba81c0752451803000003841c501c440703000e00010805032524850280304034481c00 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 667098830 1250 667097580 667097603
    0xc092d0209040f0e0a26030906070207080a0201170402150c0d111603030809034b09040b060403051905120301052b06110405130603050307020108130c03 67
    0x241404150b460006040d00d00600f09000440381304c81c0000d10313004540e00024a80002e01ca0b00c0c00c0f1201c502114104400b1302c81001c400c0c0261880c0c04a942070250140d5000c0340e040d0365440c4103440c1c54100400c4064040f600300c007070a80c00d1219256905500510060040c203820240020400441c2c011007203c0002e139002d40991407129030003141604208452070001c121101030803200044001c2c0601004041201000c08940001e00c1001036880502c2408040359443d108505400c807980701c0614a02803c0e04004092800302052440c0f4242000d068200d0901d4503a4180601c03001e48802d469039504400e00304000004154240320202902091071a2020380d40c5603030503d00e140004211000032074020400c010015542d0340403510441320060070400469440c08003110304101c00b45500580b105041c01c03000300d03803079000e03500800540e00b00321240c0401c0180111804200c40342408001c02d5580200300c00405980514000799000a10a041800003070540d41d44c035071100c070705520031a000301d0882c = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 667100080 1250 667098830 667098847
    0x909030409060e0c0f0f040f14130e0706050922020c0115241407030809010f021e03100308070515070516030e0f06070b010e060d0c092d02 61
    0x41c040c0c10010500d04400781007504001d00410319a21580070190b0080f00700103914585981801b05031001400b080d400010999a54035107015148003080b1203500c2509180280d07030102025200e058410b0701120f009201084c2400400c2d23415610400c50075901c40c04800c10400106195100005034540041004d82c65004d00c200650a60b165030429800c007405102050020040d2500e420720404101c015021100c20070034000c1c0c0e0300013841200d04443e008000b401005168000d03003014002c85401c00208a5141c48071030f60002c0340141442c1140720b0710030301d00091864422401441d0000c511070040101d066403941c0d052100d50100000b00e40b0358001c00400c030391480025990503440038103810842e290500c401425110703411a00d000400307201800c04818110745070311400d0802e02c0e070094003540d40c07106582408851140248603040c0883c4101001450701e003428480c0d0503402d9030140300f5006060500c0d075034001901d48413100c03a61091400b503402c4906201e440c400d1882d4500700e640169500c0e41c0 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 667101330 1250 667100080 667100099
    0x106231c090212010b011202030c070f0308040212060603031215100c050d0f05030c0a020703020909010213080a1716060204060309050d03051b0a120c111608060a09030c0209090304 79
    0x201020425a0f905d007600400d80c40e604079803003010381c5085420041c4d9a03529208800d03154001c1501c054008404c030000d000805401c0805640140e000700c1d110704500b0b20009080d69204004c460711038240d0002d014000007060500491500310705141119401c1d443c2070408541258210095840040c841c060300606200c01441512142150307490700300e01c00407011002514510010f0103a0304500070005003407034058809d01071200030703541c000c2c42c8a400e41800a21103001c6d410440504c070288050100004d40084006010141c990b0310001041503482c00503810581034102c58103013064805880400800142148000e1000e0302154500007603c008604180d03240ca0602c003084001d051400060001c030601000380300038007070041140240e4520a002c01110806403053341c0c6682d05042c110852502034014030540b80400c0700e001180d0014400d803900d8000c0c00b00602c00c2184540104001c40d902038626000940f455000f4100862844825404100503043c1115810401d800c00f21701403101d00003 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 667102580 1250 667101330 667101349
    0x90207021c050a0b2a0a0507020d06020318062419030510063219080c2403010302011409130606020609120d05040c0f09020702180106231c0902 63
    0x480300c241040060441c145802400001318211143d004041b0303000c20f180e841081182d401560190000c0c0240c1c8842c6071102c041e401c107540c2c020b00e000c5281c48860b40d04400061041c41900368198020302251208003a04010b00302c0f04046801118003040b07000300300103500c40e5900445c45031005003541e5914142c2d000840c2d01a40000140144c056001c000c03c003460f54031014844c60040c0380200d03e54210b400600c00c401d003c48840b024205141c0000356416010503800000708080c3c031404810302d00b9103080110140c10f00da0040f0114030a000610155214541c8006480401160b561414030b021000400356000a4507420085071510014000c459050188a800a4002c00140300c0428001c25100007401605c0682008030f68510006041c4010501d42c10f00170081c01440c241c03043d84070b0101c030f00658040c0b41c0030b9014414031250303030b824440c04d02c25280c1262a640c0d070710789107811611015151207503110007510301c0a00038081020800740002c00f40e608a00c42260010f00440d45206010350b524 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 667103830 1250 667102580 667102591
    0x20f030d0f021c050d1d0a0c05040f0501030308040807062009011404060c06020904061a0a02010c08010f090b1513030b01080109260717040924090207021c050a0b 71
    0xd03d0800c43c860001d030002c05403000c0310310020f004101d2070001000c0849200c01040024501e1141144290600c4003110400c2c003a50802d440501c00142c4403a0f110064071420311000b0001805c0000040c041001d031406891900c0c4a442c010410381d14004064000e182050640602c3d808006140c3c3c0140d0b8200030300c120100c04194009080c9890914050038202d0b0010015041613000950745000c1d50b41c85e4005c40c040d1905603e00034640340c03603801c0000c540c0c2103020408059860070107006d10b003130302900d2540d04070b41e0840c2d0007a200c45d05003061007019025010b420343d081a0704c0418841485032403c00385c400340780d0b42c2d1007204c1250700e035040006000c01c044c3c2c00f41c5000d91400101c007000c600d000d4513014a10b4000c03038041d841041500506200b9208620014081e045510384580341d003042d5500400869600d480148551604034400c0c45621021b040703070040140e0084400c05c5a10480c5e00600318080c0014034490102c0c0026803c8000b81161780421078035a08208211000c2000d215401034111 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 667105080 1250 667103830 667103863
    0x10201090206032202120f06150609010f0302070606090c02071d060f03031c06091d071a040305030d050f0705030702120714031b0c01050c070b07020f030d0f02 70
    0x216040e801103291480003a20303030441080b00c3c50f184c51110346a140100c4807150301070049243c904d4841c4407140c94101000c19a00280666000304500003d40d03241410040d400400135807411942034015030311140134040d01c600f410b03020310a00c004110300340b02e440c0040c00035480101e000040c4010003402c0c1803030740d0001071040030103841e01e03400800c07400e200a40c050816a00b00504558040009140d40541021a44400d0050344002041c08071074010104980c1c282d44c05020084041368421015000c42a18005030303070101d0000c001200c040c071140800007188000c0c0d28506600d0740c41e11401c2d50f20a00b500581c96884005200c8001b843c24440c903406100c43c685030b070460420181c0203440b800c061a1100f49050b001c60700c502800500090848145908411039030f85000101049003158a40300400e50715000d4a1440a480d50207102196801030112001c0c2c1141400c060a003600d68011407000d80e08144c2c0d484501c0d019407410461a107482d0110345800050200c0014002d140011204004014 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 667106330 1250 667105080 667105091
    0xc1e020d0801060f050f1803061302030606010509010f0f0e041109030c040213030303020702060f04060e01090510200f0f0a11030d0912051015030b0f2a160b06040b010201 75
    0x85070300034243e0b01480c0c6802d0001d6076800911050147d44840408034030b03030500648040c000c0c403001d202040d0001c148290180d07040765071142c005490324001d4014003808505209502100544a140c02182c42c90540c184100007280c0c00c07000c0b404030742441840e6600d81ca80060455141d140805c1303c7c5008103c11a801e40c90550040e89640010000d84402400d00d41c0124094045540303801c1640c0c0c170500c948035000d45580c1e131150000d10040c11888070b14080f4072981804156418808040c0e16049003d8032841d03041102540e590083c007022081c901c2060040c074410542d03881c1d0038031100702440d0b0070800800091540d42862038603c0d05900125200750b2000450010359504011590300310380c0c000500d5101d0080904100f42442d40d03a070628030007580360120040e20107202c2901e20701074900410664030350340d44810382d000d00f01d00141c03010039410750300300f02018182600042d0102145481c10580b420000c604014841100141104031049a4800c2c20006c003414180315140540e002440203020 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 667107580 1250 667106330 667106357
    0x2a0212070f0b0415021206130b0105091210090c061b021c021c0c1401080103021c1406010801051e040309090e01110d0c0201050f15040c1e020d080106 66
    0x60406403070010040c0040c00c0008080c40380d50403040b1a22108503009640c1c44110300c4000c1e031aa142250082e200e000c842c41104031440092241c0f5204c0c0b90180c640902d81b40d0400104040303503c006500326a01c0c131801e980c2c0008004140101581d8504c11445045403d0500401031700c42c001034400e44000c8041080c100340540d854800c0c425921000b100301903440b1000f80081204400000030415103160217910100c1040700c00440c03c0100d5100c2c40148601c07403620310045540300d00c00e00c03001e58040207408440c1c0c0700120b000c4164601c90b200c1c64003100030050456185007048426402901c040c2d6640d0104610301554003100c2d2451008201c40c120546490750f00501010224040e20300d0583e559500306050810135440030000035a90b605254541055440c1d80c0050134645541c10015401c060101e000118807000c00350144d10300740d00f080783c84500882480005d04031010785000f0081444c015485000608520142e001c413242d010340303820b03040300c18041c0001c081079002100700a0703521880c08 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 667108830 1250 667107580 667107593
    0x806010206070f080c04030f0b01090b0d0b040818090403170c040602100b01050f040f140d020105190e0a08160609051e120607050c070f0b0f0901032a021207 69
    0x22580b041c4e0500c1d1960b03888120101c11240030355040200300039001b2380c07044203011140e40028100c1d03d80640510182c0e20342e0003070003490404070b500203001d010004040b0b000217201d98042d1800849124804007050031180010300c08c06000c0d038042d80818100c1d507030b4814a0501c4c5000552100c0121009450a481c01000969481c4404401000903a4800c00030146a06c03407022141084402075103207031169160380d02401d400040d03114204680e165408252000c4c00c02015680380c0680503100c0c130b410140740559069501c81c611840e2382c1040341d002c2203000150f88038103204c0060304034140100840c54440c83c648a2646041e006002841510b04d4100500c0d0344100450b5007251101545406c0c02d101032003ca2010700c8540c4181c20a40104820810016485030247c505240100e04031810340d41d031961810b0f014091405800d00c0c5102c10803110081f501006c00400c1c507640706140004000c0d510002440182e0080000080340c440746102011203507a04200e5403c001542030103440c6003681990f5410b = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 667110080 1250 667108830 667108847
    0x708030106020f24091e01020c010e010b0a1802041e030506060906030606190f0909150204150c051f15081b0904080f03010b0403061103040224040306140403080601020607 75
    0x204030038135240c00041c40c58105122074111419004280e1600c0442001c0e101c3c040e400c91595020b8561800c0812201c0070702c14082c1d110310304406420003481d80e02380202c8450301f0150018050041c0d400b00000144148004c20f120060840d502220f5103403030452030120b04150000e45070740d204140c62004d200581d6000b08003d60081401c540b14003152500350f0740302c1d4070002554440c0700c44600000001510251b00d400100c0b8262080740700011548504c030702c01c400c83c040c0f4000c80c106071000e500340b8484903004000310745c4c005d0f0181d022211850b01201011070040d01c0502d503601240d888206007031701e01d620300058102401c49d000c06008090000c18450003400f00801e103041c0710b030180c20003060034041030a086171038418070503000f65030343d40e1186190445913105110841d8001d180104400c120310341801928010355008100c440b25020700c00140000700c1440507805a1500c0170000003001035078600c28809846821240c0340070303d18045c100500b07075890083c00681590000003c110307005501c459003 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 667111330 1250 667110080 667110133
    0x2a050607080708281107121107030c0e0721060f1205030f16050a11010909060501020303070e040f0f1a06030c030c131802120a020906070b13080708030106020f 70
    0x10010ba1380c0c20501380304082c1c10700441300ea000c21400039112003408910380740002c980506032203c520b17030005503034001e5494140d840050220001010240a400c043c0014140c00003030515101c460b044c90900c03d02d01c00310b00d08804444d81941d4030400c10020007039485080050881821054826055489454a80c07086c0c500003010a84005062042e2080e6044643c4040f03400c039048841403405468010303140014140f000b40440d85034140011b844106000340030958006034044c41c21a203030984280c03190310003107000c0703076100c6d07120060301082c43d050f03109500460480b100041607004d446003130181d1750045c030000075000f03c03020400c1009002020041f00d41000c42d014050b03588144008124203141c0366034002070348110b140d03c8044114a4990007410070109201d41d0721130181c071501081c07001c07442070685003078024405000803004541d030030b680c81d68050741029485184103d541e50320002680247c4045a50400100061018950401800c103141c00494001c00008400381c07455050500d10001 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 667112580 1250 667111330 667111381
    0xd08010506250602160503071403070c21051b0f0409030f05071e031709070e191107052a0f060721050315010513062a050607080708 58
    0x482c00c0030008940e0480301090800b0800c044882140d10b000c0340c5a034070000c0c064134514803100e162800780201004544503154404104100e040c9060462035120303004e55201d411803052049604042403090021503006024100300c00003140a0318100924028100c81241c001e6150082100020350429648030100340c040c100192a52202d24010410b581c2a10002d000344240c0715062007015080060848028282c0030a040c180d42c844581a5540e040c0e4420300031044218004960b013070301780b80c01388015130042d818042804501c140c06488a50312881d8215035070b0344540280c82e45d03d0703581c89000d214038040c11507803c660048000050080b1250050407485000c0005042c010041820000305207401818281e030f04400d000c600242241c3c108480310504600f461004106d50347c0700340c00300c80c1620407200f214003c03d03080010403625903002403117160745580c407803035a40c0000c03007c81e18022020b442407008040c14500350b040100501c0010306044180040b00c0107001141c0c400d201c12400045c410203 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 667113830 1250 667112580 667112647
    0x904050906071425050f0a0606030b01140a09110d090c0302010f051204380a050703181b05031203010602150402030a0b07031e021908040302100b1f020d08010506 71
    0x808500b00707004103400003114810302c1d1800c030821041da00141c082b64050301030255107070b903200e0354480e0380381903d0b40503540b100d03403200300f406040080d60107203422502440006060003030011500c17003180c0940c501074070310f40f2612004008560748110149659136503898003d080c0340c41103a000a4400b0060300051a02501c807404c13141c100c01d41c2031404804070344000c1880c00005408801400a10300f0303107480d04964144400101024001e00a688054402c03c201d22000c240c00e0311a0085018030200010086911040018842d5000c04c038064241c1e555203001e5030380c0d51402201030b1a1100645030318004042e40c60070880076071782c04900d901c0141d401c03043e8800c8640e21020304070020240003c000c03040d1019001d00e609030100c9079029003848110400d081c503011428102c06e480c0c24408641c0100164000111600a80610707041800b05003c0503101c1034890307042203e0000c43c448928180c40041c1e104858101e01c041d40203000500400341600c0b01c0b858100e071b40140c1103e05114200c2a200b505081e03 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 667115080 1250 667113830 667113833
    0xb0906010e0a060e220c020706030203010617100306020a0809070f0f030f03140a090f080318100908060c190e01020d030b0a08070b03060a1d06010e04020904050906071425 75
    0x106130000c00e03a0100001042d000c1105c1c4440204441d685500040c4521113011890600034070860741602d034141ca070003808001401da6001d00010040c0700031480d00b030a41000000a003540080e0103081c983e61103445552130078000356860410f00b0b41c8800f121481d001403c01c130000081c01441c055940150b03440403da00c0605007540d00d407402c3d05c1c15105a620003e035511900780e008055206442c81011442c44d0640d03030390b0b69141d480c000e0501c15040013003014130031009440c0c1480b500321403039514101066403c3e0b41c0c10102d818a07204950310b001980c00002ca030750340d800300402c044078500c4040c100fa1000304c1c0c4e6040000d40d2031070703180000c4062541d100e10040c03050f80c8216184005010800880d58184c0c1ca4003a418195001030f01d1181c01203d99290225940f221444056108200300490135001c3d503d50f4011910441c00341100e139003141d0308103d203407026203d030300440c3e00c6a1500002441c00d410300381d01c02006030035001c0c90094007080500000d1500c9034210b0030300354041c1d00c0b104c8403a2500800d = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 667116330 1250 667115080 667115089
    0x90c13031502070b0720011406100212040b0d0b060c10051008120403210f030f09020603040605011401030905030d1d03070c060e0a050906220606030b0906010e0a060e 73
    0x72800e002d0101054002007000c5154042d10000c1c21b5142e030300514480004004c041d50903104007141d0040020300c602c00051040c2000401d0030501d03111071045480c1240c2c400606036450340300b42c10041000c3c8000032003c440107140d008508801a0503079510740340440702c00165803550950b920082c5a01d45900208040c0300e101c40401c1c0282a80304265620100380c0800c03001320358810302c000c603100c54031000c00301010b088100003001c800009407641e0540c017109600890081012051101c40039544078003000c09a00c0c4c0b11302440c4141c0c400c03100040c05504001c03c0820711120704558a0405090503951800617602000751441c0502b08807001c240c2c940c50b00241f80c0540c094030f100b18107030f110118220b818040400100300403201030362034210005070803400b80f10101e03189014854200e40d04801040b540d0a282d0080b0002184c480704001c528100111400c4c103031842640150002521050b4005d514540400c0380d80e007140c824200b011101000c0f101007604854144510070910007d2071440441d03486 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 667117580 1250 667116330 667116337
    0xe030c121006092403030206043002211813090807150e07053f0a031d030d0507050a0b010306050f07090b090d110303040f0302090c13031502 62
    0x1d50303040501c038a6856141c1e03d80140140c4008000d454a0070307011984a44440c401042621340541c064480e565031500c45102c2d10741d0700b121581c00d040d82c2c030074030074925113108010000e4980c442d40034021103044400c51541584080d00144071071403040010700210300700b02c86d9540350120203032035aa201d0591422000300405c0000340180c07440100164640c200320420b506030b00214540c413000c12036000c2100f40b6a9070b4405600405800c0001c4d48040701500010170280c1e050b00c401d04105084161140700c420300da8540761408020254004030f0008101a040094091a41c0c509940d08400106910000c0d41c0c541507205142c06100d0000740d940103110f4103212000c00c16401401d4020256980e14118000701011104880071426800c0440c00c0d10380302d06c05002c100c8040c03a15140c14404100b0400c014451400c0c2c00312044c4454500740f0313409442c140041d00007001c014502d0500f080c5035006001040c40c00411a649040702007006024142c5800250400d59401400d181204000700f01d800000f0b20 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 667118830 1250 667117580 667117603
    0x20309030601060c05120c030906090f210f0303131b270507020307021f1701030b152209030e1f020c030703032a0b09010515010e030c12 60
    0x1d40d0300125900e6005589244814422030848261100d4410048143e00884003a60415001045220042d24111018010100c802000e440b581003804000074460702080d0a10500e03944203c210000455040c00a108a200c0701800703140f4514100441c912613004000004195040303105080d0044854405420302038180c081c150ac200348100c60b5006100b480c0074100095440c10040064031040c808001d035210141c0c0a0080002158420801803002c01070034405001c0106411205801c030003580c0d0114000c6000d024041e02c4c40c207003d80c4800c07242d00c040b1201400b0729460303080d040d20701c002800c0328201500f0b02c01c0e000031180352500e0201d40f0103200c1c8481c81e900043c0244141c0d104403a01e450381c9881502c0d41c00302c0d40160b84820a041d15186070348400703008600340c2180100490f100100e0240b0b0110164102da00300e000c0f5135036018044005a84039049a0354500400c09620a1004001c924843c00d08080c0b242c00180f9000a80c0c5020241002d0301440403280b640c150000300f00f01d1a030b10030 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 667120080 1250 667118830 667118833
    0x131a0702030f07260a080a0b03010e03120a110406051c06150f030b12150402130c0c03020c010203070b0a0905010902040c030b090112030c0b100e0103111009230102030903 75
    0x51072181408041a001440082c22480c000700c844131100c2c8800c012070b01c0c0048641c5520071640d070ba410106000344002c1050079015500c0721085541850180000d00c04080440002d0a042c1402503d0004850101d400110000b000300010301105410070306407200072122015058559010040d02009014260700140d2500031010359081003940240030101030440d1550108040e00b5900c003040702459031016540129080710b50140e03546540100010762040c00505502d4031100034800d070604446803402e84400040500b42c1340e108050381400601d030200d100348011814080940c44003031814201800d254425075581414908101080d0000b1035802c0e0010301c02c00ca108681c0ea03024000d8050741d416640324101050020a01160101b03646480542680e21034000300c02d10f665443c02018060b00e61a0100c001100002e04000d050750b81c20301a52144a00790700d01d070b180c80140104e40c1405440c1e80188030700741c2003d0125046000504180112004806442c42000c0e00145d0642c03186440143c0c05 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 667121330 1250 667120080 667120087
    0x3021f18090606080609060a060f091d010f0b12060904210504091812051c060306020a0f05030f150105040f080717030c0a081c0f0e06131a0702030f 65
    0x8511070780600125203e40c3c0740c084481c0da4403401c02901c0001200c606a1181c094003050010380d01c92400303240102418100031300c0d0161107007920404041a2030b4000d1340010030381c00600c0302d04008078a44009141c070041c620300b012403601040f4502d15001386220300440e0b0010000b030900110300741640700c00c0400480c1d071701084104a0000c0250703100b8082d001e103060038150401119510003c4034800c1c83d03002024400e114441d10002c54141e0f00040c1440d2504e2012501c04d110710602d485071b40c3c000c44c841c002c010b0341c0780ba0b113030340c080c1c00ca1800c01c8040052000510400550210032090303141c0c09a00c0400321041104010016141c0d030140c2d40000703115000e2218045001c440004183d0305130390b5952a1440000d400680c010743d684115401403507035030801d081030000070300500090004900d520303420040c0400940031100841d0780c0c80c3c0100354a69102d403021008034209008050304000303401011801441d0545440d4402060400c000841030b60000001e00914401e00a481020619000c107654 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 667122580 1250 667121330 667121339
    0xb0a0e10060207050d030203041514040b37080406111b1207170903010b0d0b0402041a06040b0304020f03060412110c0906060c0109081b010f050103021f18 68
    0x40440c0e4058100984100d81010a440c5040b8100c5486a0b0b8142d004524080c2054015846025080b070740f80d043c0850b0005c2c0d01e0413007880d2005800a08903101c031140d180c00d43c80030342070ba011001e85c900e003009542c144500300000d04a40001d070041c05060500f10400e46482c5043d00040410047c50324451201040304041d48840317660010f20700c081c00c800c840d00114410801441745c4100f5800a10042c00c001c400e101500c0c0c81e47c00780c40440e6004000080d40c5800c60081171030030321144011140c1da00038000f004118a001d20074000c518a040c00305101c41c100100100303c4130710450060340d00101707010001400b190b50700d00a110007098041e0a4070030500305072038a02000d0b104030001401091034850300c2115000300083c03402c100745005240c10801d80794441030050030740c080d50070282d4035522039075001c0110b0104001045d2503005115113400b180c21003956a07003180d0746240c0012405051000400244e1f548100074004001c0e052003074103600d0f000d80750a5440c0000040304c80500c0160280005 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 667123830 1250 667122580 667122601
    0xc0b0a020a11060c071202150414010c0f090501140f0412050f0a0c052224050402031005190e1e0718091a0607080d110406120b0a0e 58
    0x1071100c29440c2d11800070b20079404540c80b00c42c216a50398015406008480c007040b00350400c0240e00c06103005503400ba01e04c064010b464030348100d40c20380356850340110303d1070118000d1042c03200000d041d1a20b0f141c0d40c1e52420f03005210300c206214070b03810071000603100404402c080080741c02c503100c0c81c20300d03541d42e030307520b03000f100b810f2082e01001e88440c0280d014080d585003022030440681940f03c100b000f0f21905120400402540c0c404190380b27080c2030491007400560983c0728a0000342541484800810801c0d42c01d04200190360300308600590061060024a21580307040009641003150110500d814143c0c480c901c025056002c018007401403c00c1c41030002c0f6152050000c042050400c00c07081d90703280000d40396030000583d000c20f4502e00c00010024040e69a01c15480c04120080d9004c0311701d00d00001604a40000300d069a500c000040c1c039280c80b4480703125000d580342500d41858140f910300340001c1c0018024511002c0340c05d84608000c49280d0314080008081c001151140c42107040585101 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 667125080 1250 667123830 667123837
    0x1d010e1b130905060607121211270411031506070c0f061704051b01030609090302070e0a05091b150a030e06060f03030a05160803010e0a05010e13120c0b0a02 69
    0x50080c2e5150401103001414a9022200c019070000c1c0b0b107620804d250642181c403882c812180d40d0400703940c0c42040c030500b5003d000400140d20b0b41098035426802e80401c10b45014460272540b44503624101038064004111002d0341d03403140c40402c3c088140b62101000c200b0500c11144028a40e141078200401d0404082140c1400c0c0c408a6480100c48142803403400360030f04d0181c03806422039010b081213688242842900081c03c00c2c040c50702144ea15952850b41c422f65000184c00c5001da0003220b41802a142000444d075404902c0000c18003050810341d444da61240041d42080070365500d01c00c0601401c0d07c50344c0400c0e450402010220360703941e620f89802070040c5101c0b2850070060042401045952a1043c680003200000401651404902140640302688004c4c9008046080c0ea84140d000c00e070020051402000c0e11104400940350490802e02103030b5050f040540c83d8030140081c0150301c289101210081603114101820b4140303903140a84000700c0c0303100e0003440d07061450100410503c054018 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 667126330 1250 667125080 667125089
    0x110d0c0305030c011a0a0302040b0a0b030a02041403010b15071a0a0b1305070807031a03010603140d09030309030201200d0203190e06071e050d02010b01091d010e1b13 73
    0x30040a60b100781c2c005c2000e05250f5050381c0c4008000001c2c0301624040e8402035203241d004103290481a035035160715420350801c071540d95640780e010808112103e0861048011064104e008100c041400c500240c4102d4030040c5c000c030381d100041015010418501840c0302803080441c00b811551912514103800382140f2292540102c1c1c2d28200700c811485940075550080000f52030781901d0b6690300300200c0080080e50a84c4140900306500d18000d41c07420701c18200a1806040c030514280348204001e4034100340c3c01380c05000c10241490410209a205089c8001c1d00d0707091800d0446203026031512220441441c010580c01e019140b070070f200c0207400000800501c00c0036880802e4690000030142c86400c051001035030840307010480f42d80090520b11808809501004c12441d918009840301071070001502c1140c40541c0d503400c5d40520a681115000005041a06251640300d503c600c000341e42c410188140c0701c408070030001140005403c4505000c16080c842e0f190342d100c4002c0d000312205141c480c0309 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 667127580 1250 667126330 667126333
    0x5030d090c0608040c061803080f04030b010e04050c04090809030d020f3c0111030c0c01050f011d060f12070f0b0301060903030f0516081908090a110d0c0305030c 71
    0x1c0c000b60050250345618800c6402c002440d50f004d1520505a5107202119040c0c1a414085400400015010409004111030000ca95070300c0b01c0c1180b8004488200c180c01c0034000b0790041c0100700001d100024050001c41003501d0100d0f1018091a003144203000c1c18400c4c40c0d141c06028408480c0d554000380c02d0898a8288088503c6111031002c0301850b1460307842920044010090701642007807500401c030a4801c10344000054036031000c0105405904169041801d007000001d403580c00e03050034000c0c190030040d80c18000c01e195141c070321004071295071700351f82010401011001580e00d030784402d29050755440c0070300401e48070401003007429121015030040b00d440c48013031107020a030703820380300e080d079040c0c880700d88500c501e580c00c6032000c0e0303542c2a100f80d498041210821404205081b0b00802d0003506204101c0903403500c004020000b40c0d50040030900c41000141820044203480009031602902c0d00b0424420660710103c0114081e4408007101502c0075030200400002c00c5800401000c51810080 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 667128830 1250 667127580 667127603
    0xe030d030c0e0d05030706021605010b03061e0a090606122010051324080f1015021e033a0b010c14071a0906030a05040f05030d09 57
    0x5400340e00312200c141845000600b1040c601e41682410509502c28a024004a034140401aa1460140d034880445a402c00c0000d080050401400340590809140704401402c0180340c22583e80001505540180c10070301076440104000e04140e0380030758061a0800c801b40032450b201c0600c0c00840b01500301c03c485109055685641225041c0403245103080020070340321550f040d800041b104c03a0006402e0003c2c2c02c19110000a00d80116507001e05001c1098a407000e1182d041d032000350451400034040c510301c4d4008010000c91105000d518402e0306e008007000300c1c11940083c0100c0c43c0400c00d298101020f940150080d021a00020150070406002c01801c0c0f0340d003803440181455041d194104044240ba21076614020307074001c1d00015096481032500003445d442c1c98480c000c11844000ca171102d00e421000e002d015010427000404985202c0a480c68500010356012400c3d6204c01400c50764026500e10102e01048022a491007040340c10000b100c1e101c00d11225008000c20b51184100c1e06140c084 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 667130080 1250 667128830 667128853
    0x61b0e040e19023f1609020d020d02121006021504080d0b090a15060903081209030912062203020c010f02160605250819090302040c0e03 60
    0x500034140003405201c00b0b0040300c0e503240d079828480e4040310000c980c4102d402480684501c1c0c00f44044100207000f0120409641e11148007005048100c1901d4496801c10464101400501c0680313004031b40030038070010396402808021400902501c040c000c642c0b80001196100b0b02414907040d400b4200c02034403080040c0c0e84000507a655880e01500b0020720b98000001008a84840c026040400c0c45050200d043c1803031000140d915401220700412541d540e40f030442681d050100c02402410b013a0070444515411038403000c2d40c3d40224686020815500350006102d0b1105106443c1c10030006081c0800780d01419a00035145c5104880d030010031020440c0e01d40c01c620041001d0404a6055006048418055030046986440905828040d032155003070080a07802031400e120020074a079a25561181c07907a0b08450101c02021f440001c20040644460010803d00c0342180d210445c04480c0d40b044590344401502c21102691000e50700524050144c61aa0707000b280000e1071100840c05d850074403222 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 667131330 1250 667130080 667130089
    0x2040b07120f120203040602070206040e0a2d0e01110a0903060c08010b040b03310c0b0306012c030d08060103180c090218041a011101110f070807061b0e 67
    0x2000c0d00600001c3c091844010500d405500658006019002c003500e054195004190664001d41c4030030b41d01e0702c92004100074074400e8450007003800514101500c101e801034512039038090032503152200d096900c581c0c03145010401d6119182182401101d40d4441f01501409440405540704c243c42c16418144402c900034400c9814a051380c140c80b006900300f03814906841e031290001071100100001c902d06c1c920380440d034068818802020134000c500c6038000b0b4a40401e0400c41d40d40f200461050074000c0c0b0800d40c0e000700c13407031218100f4074030b4504814030103000d10402d0081c0b5050241e010301600007922000e60340043c2c107601c51542038905100c0c41480800c1d480369100e00e280e0150050042d4131042c440390f52150010503800c41c441808070315044201000600321407210b8422a103219101e440d200165800900202c0360001d00400ac0010301c1042500441e40d00c40d421303080e0204040041d203882000580340079208240d410035001c11286101244076681c080030006508007140070781e0060695440d1 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 667132580 1250 667131330 667131347
    0x911090906010b07081b070b0310050301050405102a02060708161713021504060801080f0a0f080d050723091309020a03080c0106180920031002040b0712 67
    0xb810030701c9481c00c0d105840e1200c0c00c1c0c02c1664101e0281c280211100d40401e0200170040c003400ba00e00c1e0b46270b501d062030034000313030098441c0d4403a41c0641d0403d01000b0210384c02003806c62140115401c0440c0b0104034800322039080301d0007982c080d02a2444210044250b5000444912404c81504d68070030944451f011009000041414070700020b50311402c102108165841c00c0d50000c2d0288000ea480444507400030748142d849a032009410140410101b202590042c0390b01d0040258501401000d02e101c0715043d00c4084515010741007141b030070705190400c514081144c5400611040c00c1080c0d05013000010165070f02c54009000c8147d021310a000010124011600507a400900012208009603449806800e40c91000c0ea4043c140c14000400300e4a40d5005107018401e034000041c4207401c01c0843c1180d03441c407120307405185140011440010f444103103024070a40700940580c025106140c0024600a07031000185e85490003c030f000521040c0c00d801034551648151407181c1e000442d000125001003 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 667133830 1250 667132580 667132589
    0xc07051c0c0f1809050f010f0b1009032d08070f0b0619141c0506010f0e01050901030308091213030b0f0f011e0308030c0301061101060303050910020a06091109090601 73
    0x403002c43d050350601c01d66002c000400c0c410003d035248410303826461402c40d590070017960071040e224040b201e007610785055414003141050400b18921425510390010b1002e14801e40068100e01100540e040e80340d580c031014006074011001c0350350310f1251801d03010728900d21004480c180f505c0c00204140389040e9044842e5113085000f001e0240c0d2514944080f80c04410b4001d603004901c942860440c100c158194001840c081c5004010030351410180c1144a8210b50010030300c01c42c03840040c0019900c4074007880c11030b41c16203400e024070344070490b2903410226110210415040001904c40040b0206d2410004480c01840c1c801c450780d64010725803c1c2d5401c00c40d00603980c10701030401841000714254180001d021507101003007034140c0760303900c904507039109459411402c1404001004850380c040d80019aa00d520002480788030718580d0040c1c0b841c06000d404034410405041141d954034400c2180300580742d0000010706c00400503090010065400c09151070003851582c0001c1c0005000003101c4c1d0484 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 667135080 1250 667133830 667133849
    0x50703060305190303060e010303030905060c040b040b0c0c19060e0411090d03090902030c090a0b0c0a08030c210601020607080112030c0218090c011101090312020c07051c0c0f 77
    0x203c010851481038802d2400d401c50034035584000108180540008203806588640c400003612030306800c140d441d0400c020b103c2c01c07140d4800c000511044a86800350f03800c651905412640b0b84890303031505400c0003000c0300b100703030014a0b4034a03026600c420805403004407105611142c1c44590000c042c0070035146c40c00c104480c0e9240402c200e03034031803c3c2503481400c0380e0b0080c45c003010125240c0600900f80d13401a5012030b05014045001c50ba545010f0b881708000344201c00c640d602d00000310310801e40301d4507a464050304404021000030782c0340012070100c40c00380955062100c01c1c0c0030780309140e01018009940c924018850000000c0e8641d0060340102d042c1c031012a001c802040541ea400c40b8624032500e4100d0f0090b40c221107080c00c14011f403d00902600710100a40512059000018012400360681c012603a050215860101e50040320401240c102c0d45005651440c810b400c441c548036480d4072041e0401e040b00380046803512007408017101c0c1445441c55840c495038503050039030783c0212801030300d800 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 667136330 1250 667135080 667135093
    0x230c060f090a03051e0606090405060a0c0e03100603061508070b0304031419020f03040617040c0b030f0f0a060302060301050d030210060f03053f09061c050703060305 73
    0xe28841402034a241480182060032054032950390900740404201e400c501e501d207020032207041980612015612440c180c4403024240ba040e220260341e090042d00003030f0020703a2002010302d1a4451801441c41c1800034040742c1e1885000c069107001030543c0c0c4019144545448812500c02801c4100d03c02251030340c200408005040c44c12000050340083e10440a102c20000a65840703601c600182206440001190740d40d100f2006010342080240d0200c0794880e04100b2040c80030ba6001003080f022104e089401400a07591881e041c01c1e4400303287c001c4c4c160528003004100d49a02d0440640340304c0e4103a8850100e440d2142034200c4207845c8a4000294450018001880315041c5103910403580c90081c8101c039803900019168900300c0d219600241404445e500060003482000c2207000384200f113000c190212040244040382d040d16105e0090ba4000260300d003001c080321340b0103090315400f000003030406039290340780c1000b240e0388404414403d0800c2e0814002420307450192184004903030304900607280 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 667137580 1250 667136330 667136347
    0x7140f0f010c020a2c160831030e100f0c02010c02030601033503041712090708011a0d110d05030307030902100e10180e131b0609050607031b230c06 65
    0x640c107c000381406080c0d14258020495010103500e0345541d0100907001c00003483c01428002c0c09901c950101c0f40c05410f03841388800d0341c154030031000c1c0c1c1c1d40b103003030300c0e00031400d880501c0101c5202850304000396050fc40e800000c030070700c504241441064003282e640542000b604c840340300340080c486030058544110600005001c118200713050642c1d104e490a41078940088160a180070b40020f642000300790303005100c28010040e00344940706040104400d42c0c00e09061403c002554003141103002800150310715100f040350748801c2c040c4801d0960002c1501e403646000b500080050007100405d91140440382c3c0740e490042c1c0641e40d03415020101070240d0002801034081985c600700060744145804112140c0014054420b00e105401081d4071103412001c0301180c10021790810222202d4650f403000349900300456600600c03100222001070701c02c2d98803480a402c068980b0102d015000d0941800012690300300074460894919101d00c10201c10300c00d6110029503030743e4080352288143c204008000001d03 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 667138830 1250 667137580 667137587
    0x307060203031f0302060c0a02041d030304080c1e01090c090212070c02060f04060e09010e1e0a0612110a080705030d0c06060807061107140f0f010c020a2c16 69
    0xf0108651400d0031400ba076a69400f1840760392200c0d17401c08468124021017000c514060180a225131050806810b50340b0f41c0450040e103d120182005001e0000020f2414031031005000c0114245e050410000c01d400d036200d2014080c04924004860203441094007184001d4a403094401401c0004c03c4030030940c7c4d60043c15103850043c4d910907a4000070034440114880003a0b4002c00c0034090b07650303e89a01d41240310520000074011307009490156611001c100082c1c4100c140c428000c81e02d04444000c80e02d5141c80ca10080c4510303000715401280020b122028854452101c0c2002141038801e41364985e84c1e080390b541c952800340100d59254000c040c0c401001d5100d40c1442c50040e000381800102c0650701c1841c117242058a603c010045002c21510070b00002c8148501e07801400300104414402201c800003030340c9458551030f100d01ca0100c4818001050744a0f11218040607809444c2c25216912038480c0e82c0044412042401c0c02d002500740381c5401d201c0b203130b84540540d5900040f460705803500781058 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 667140080 1250 667138830 667138861
    0x4090803060d1a091e070b0a0818030d0c1107061b060f021321051e1005071119110d03020f011a01030c0c030801091a0301050a1a030706020303 63
    0x6480001d40f00e08010304030400c0b01425401004464002c10a070040f000c0740d075030013480d80c80c6415020342000d0001c00c03119482c0c2e000c8a40401c0c0e14500050207a0b02d4002d8005141d448641c0345455100c0880c800c40150741d268000d20035041d10384c41d01e40402048004855482c00640039440c00150504003c002c0031003001903550026208100229050804400c16412030304250398034445903208010400c41d011070302c0c546468001c0c6815035000401e1840d19515030b103a002c190943d2882c2040324040d522024140101210040492000e0200d410403c90080a80b84501d842d10028000e10a003955200c402c1d44095001940c032200c81c1c0026040c460820544100c0e00100341c0641c003034140507540c100428801c0a401600025813819041100350005080320090016141070024044030100071a4020800d981101c1d03280c4008150780b02000c10a03190348a01022070740d00b5608141c1448443c00480e00100801c40604044a507110003900816a603804a40304800168008002145030241101e141 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 667141330 1250 667140080 667140083
    0x1a042727170909090c010806190b070618060c090b040807120507080601060507051506060d0e070f0e0a05060307060804080c12040605030f0a1e050603010b040203180c04090803060d 79
    0x1e09007425408008a6050b0320100ca2542541c0c021018500481d078200e001942c11440c1940c82401210b40b0701804811101c0b207020741021003030042590010884560451070300c04c01d40300035540c6c2d00d442915007940540f90070038001c0003054106c8070108203028103600b078600311380b1090014101e1525000403441d2402550301d0654242c0201000480c0c0c0b00300c104440c80c000d004503503851b030f503030403150a0560402203050740083e1088801018018507944000c142c940100e542000040c10a81290050345403010b2588600c05400c2c0380c01c1d00144480058207650311401807070388280101c0c2c0d5100201030700c40b400340c001c02c0c02103400c002c08039005c112890090612500042c080318041c4580c1521a031081d001a44403500281000081049070079100640c2da41190045009002c41d04402452921002d612962690b540d0754800000d6026a42500032010007000541b045599080c800c1903151001c0c0108842c0c4072910505074010b02c01e0405100b0107407810707040034007282161240d0080091f5980401e40 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 667142580 1250 667141330 667141373
    0x801110a050d0f1104030302010506030a0f03120905120c12070f030c06200c0c0307051c08120109150b071e05011b0f17010f1a042727 59
    0x220500c041c0361441100e03080f13900c00e0a2507440b2032544c9802820b44400400540c0250040d240c03600001c0c1a040600f26040d516007070210400c405a041070300281900c0c0d5001c0c00d14442e404840101c00d0441000700030010400003074580441510003000181c0c4656a0000e0561803406410404a482008645c428a214010200d128003185a072404c0c44406041e164401643c00101a0b45485040012001c1020160094540c4034a007000054030601e044225404101d62000c0420402a04200300d514103e9204034110381c2c0e5031501120002001c2140703807160f842e0450000811900c4d0f4072401d50300c10542c015001c0c5e896021000350072070407440100007110250b4070b40c1030550041041c1030103501000401c1d66882c040190a0400a101e0401f640fa201508401c4400501c15030548443c03480944ea8a6101381120f440c014500d141144915800006074040c0a203800c91244504041d203826110150400e0000c1c0d010343c8a8140281d00240c0103d404070f48000000c00010400310580c2c601820303446 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 667143830 1250 667142580 667142591
    0x5010806151813051e06010908060f0a0c08010f050d020109030b0f040b07030c08060d2102010c02070501030501150c150603080702040c0f0f080603031308010c0305010801110a050d 79
    0x1c0080d9407504041c030115035541004070595810300342a500740005031880c0ca000c1c001801c00c4089002c06a05480c85061003079900c0b00013803101d9024a175074800404201c8112142407404040000040c00161901540c1906102ca440e0819100b0000c079810380340e4078011000506c3c50301c8104144491201022410f200840c5000404034145c0c03240240f04994014007091146810700e4100000b140c014541420b0600d130810303841c0d10580c84203003ea8083da05890501c184110b0b41002c035001c40e0100110b02c1c00c0138060b0701400b03402c0d0b4190401d0080c840a50201c950b00d580340c0005500303641003405480c0351910002d00f01505a0701c070700c558082c2940194040341703002460400140555405420944110703c0000d040c000711308207881a68040307041072500828281c4850001001131040280c51800c2081030800f150040e5000c0c8100c8108610341c182c2c0419055840403198080c1004000d040e0109181000001c1ca002040c0203180c41c0461100d034440c94208162801d4881385c00c42d07070102d6041135582 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 667145080 1250 667143830 667143859
    0xf09060804210201090302010606110a230d12140c030c0717130512030a080103170c0d03050402090f0408040b18040213030209071b12050c0604060e0c03060c0405010806 74
    0x24a02c695000956500100300c00311542006825954140c0c070000403c181e0b201303040032100307002c940584080d40c0560f036a55124502d010790700c240c216554464540d409011500700f185508003035a0031052030803a0042c0040d680c0d1080191000004448801c4282000c10000b00b8080002c07000301581481000c0360680c03000610940c450903000b903210907896158895062046103021f040703008040c01410f0080d45040040c010040001c0c1041c4002440c4c4001d24506607031040149040c1c580071400c003c100e407a1030300b803068024040c100070750b002da00913480303c1e02041d0796490720260300c0d00c541d81020005252a2400030000ba042c1d0101d9004c610441c43e08540c03001581d600d000034841c013580101072540c07403130550040290080c8007503c620148000d031050040030103180840c100185412010141500c0c1e40c1c100103076094490b0b41d840e088035018210400007000603c0c1c0c0010205003210003140e0303120307850300e060564541e801d651281008000380010006507224034500c640c807410140603460300031140d = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 667146330 1250 667145080 667145123
    0x9010e010c0b01030507050118050f040b060f030a0203010e0c09181e090a0b010803070c09020703050706021306020606030d0912020612070e0306070302070b07080619060504090506010f09060804 85
    0x20703041211982c100c1d40007080590392000d00312042246406244101c9ea1a0000040d642c80c40004003d01864664014001a9440d18113450804203071121056403803504150701c1001354024010200140440004203180d541840c09490886801038001441d620039001c01c46c403003550040c0b001c03610048807420f0745072a0703031900000741c010050800181111006442c0c00054903005070001c410701d0707009225003808107800a10034800c848603060010398600050070308640521a4032006030501c1d000040b031002080e1014400e40403030fa995402d40b101c9880d68800c05807507802042040000592400c42401222549030441045500c0244178601c2d20031102e84410060104445400200c0d0003059228003e0a050205542c444801e20301103152141c03654900101c0c8030003030406030421050500088441d111000c01344a075104181190002c00e41e9108000c08a40c0640a40f00c1800d05001c04140994080c030040480407030143c544890160525101711034001000300700b543e000e40c1c1c8082c0003200010 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 667147580 1250 667146330 667146353
    0x120e0309041d010e030702030c0904020102030f030406020d1806051b0d0509010e1c020d0509090114030c03030412060614030304032406060e01020c0a0b0a110c12030406080a0c0509010e010c 83
    0x41e13070146031180040d004260400110301c40f0203009203070000401c001130f80c0c0482142c06142038504202c1e1682c65a0620400a006800b403418800d880d0141b040c3c91240c0f078600c00c0f1116480f0b0002842207690f45c01483d1070001c40c06113900c280310814000660303800c010350807080d4400140303800081c40d209003203805498400f00d442100c10013124140302d0701400303505012440b03460f4090b0508a140c12124004030f002d01030705224021341c0c4154880001200c0d5024081e800700120020120ba07200c540328141c01c9006110508100da403140b42620000d400c44140c4c800c142c0107400200a5410180303140c40d1185070041c0c00300500c8001c01a2517000c1d6010185200324800390015035141a0354624140003e443c00c58070404883c4200740c0b4100402c003906e05002103900d0030569240c03000203050b40425940c9480010080f60750700060706003800100c1e45001000d0011600aa81c88103c01d49442e00d07000211500c103403c003800558200490061540201010b01c105d51041c9403550b00300f107942d03c400425a6 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 667148830 1250 667147580 667147601
    0x40f0b03061e070f020c0603041e0501150f240210020403060b0906030a0c0501030e0c0409050d0e18060105070201091d0103050607050c190501090b07020607120e0309041d01 76
    0x18a40c100304101c0889054240d980034410f1300b000143d00300c804102039503441200305400c1c481e07d00080080c0410044407500c5440d215010641d22001001d850040d001c6c1c400600800611205003600090400e525041601143c81c5010420716505e855600081d5041c41203010034103510a64100366942c0700140300400003107010742c400146414002c070803c168501d01031f14161090b407103400d0326804603d0002c0c200741260024200054251200c0c1005410215040349075540540f40114800a000001c520a45c18100c0790740c4142410810714100580c285940012804000015002603481c0d400340e4001c01c907a0b401410152a01c6036141c020800d0000c0c20b2411001c1c03d0703803c0004108000703003001040c0e0009803604096007070a0386030061a035609240e20b0a9000c0500c2d0521641c144070080d800641d0152300941d40c140640340c01071000c1d564401c10b48560f40041d035100c1c058101d80405206890080c030201002d1441e03c1170803810003001e0000302843c040e10000e00082c41550030000d1284804d0322 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 667150080 1250 667148830 667148851
    0x3180b271b01020d09180902010201061205010f0e060c0415030603151514100c0807060c02150705040e2a0315010306050405060a12060b0901030c03050f010e030306040f0b0306 77
    0x4401d100009041c090105425800c0c05403611003444803c0704041400c400e44a42240060a48060b00040b40500745560004c000e8903004030110040c000b042d0402e101c0d1041400041c8201c20758440103d946640c103c62044208600344014029002803c030b480750040709514020610f01c0d1651500764803010002600b025150703642c200200c15070720141a000c0102071b80901e920f501883c0c00045010702100785829030070000106920820802642c0a640c50b668020900308002d691920010356590050001490500407017000103044070700c00d504541c1a5800305000f0001612500d24107201c211142c42900811007a400340c00c03500840c01800f4501c1102c3c1c800c400c0c019000e03688000f500b154200c3d00f00034069806c2c841041140d85408500d001100d210060600c040700e01400c1080040800c4c020042c0e101211800005c10301404180d40030560b070190080d69010000c62155600301c964a04250b5000d82003840001c8203882d0903071003040040000703400030408070700c482c001034105003003250700e161003 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 667151330 1250 667150080 667150123
    0x17040605190e01020304090f1d030c060a051509060d0f06150b040506071101050d02070326060d020f0310110a14070309090207081606050703180b27 65
    0x144444100c1010403104034140390381062101d0000170348a10440c00364a4055481d61142040704010381d21515941d07121104c10a40502c4203d03440c1d8903940412030540c1c8a1040317001140020b441442000d01400c007130380301c800300000302e41c0c02c0c050058401132400364404c040130402c4000c03034080004003a550b0700c00c2000149440351152103160070750341500540c9003280c05000511251300d81e1002c80314541d401c0043c001203000c501c001200c1c0e42c400d9456405086001054180c10550000d024880b801e000b101140200208120500d80c0c0e1181210019030041d0001100c00144c20540c0d800807000001600b59102100342842180c10f981da0040b40301200d9800168090318581d101d0000c1d07080300b01c0c26141074984803003514010000b81982c061800181e5000820b40200000d07001214500d0415042a0380002170904000d00100000c1b00c0c04000b0034182622601e103030200d4620300901d143d110042c142c040d180c1c0d0050103070380f208846000003c001da1054101c07041e4403c0044076100852807609468 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 667152580 1250 667151330 667151347
    0x70b04050a05251e031502030f0105120309150c161502030a09091a090702030307090e16030b0a0807030f0312110304020607030909050c12060d1a0417040605 69
    0x680f051a48a00076800d881c94010144241058018001c85202c8042e09003908a0719038051010700d4035600003441005c2c201000c0b10366103030704d401462041c40040503242082c1c2e49c52084c0011050014013016850700104203241c45840d020840007011815001e10710300340301b00050800c0c0b5040d02002030b400401144e080400c0542000c03100c01001c0001d520207581000442d07000500740ca0228058030507455181c140401c50100504ca082c981408000c2196220342490100031303449500c141c038002c1c000744604d080031403a407a80e8601f40d400b03440040111164549000781c210010324281a003283c1c0071401450001d29403508102903005540560446100c905c41c038038002d0401802443c0d00e521407401d240c941c44c24140d1010541c0c0d0710a4040d142160b541440b464120303005101c507007020b0507086ca03203400e0041c1910142c0180c180c1d23015040c12a134454503030100700304200d140004010911013420040b5040e203070707510302042d800134400d1070321600411010110f031102d900103401400004102040e81407 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 667153830 1250 667152580 667152583
    0x380a0b040608122a0106170f0a03080c1605120a08070c030c0f05010e06070906030614090a1d0d0807270b031e01080a0302060603070605031b070b04050a05 68
    0x81c0140100350091202003090032128209005025481c40c0d00440c50400208420200c1c10303031440b403400f43c002006410b40320145015000314494240f9180d01c00c4044007154000d0006400f543c0740e400d61500c5000750350b650807810103a4001c0300b01001d40c000800c0f880000500c200301403c281c5003030300c9049031140482d0303c00520120700209144100300c1e5040c03140c00440e402c0281448400d1b0454000c080d1082c0718100705015040c0c50848003140d104040821408a5010104c80262070460b5420311646503150080784042410303200e180c1d4051074210204250709416403000140d00c02c030300800007000001d2103140d42010600301d000b0f404035075400104551250b01440c1e800d5141010404154603580074543c12203442080d0041402000000010404c00500e0300d4100c11900c80c8483c4501d065030f11000d0560312a0440401100507200d40c2012411526010070b4041c1550440e82e1030504550b1905650540840d031795411540c04401004440702166040422601c41e902030b40040141c0502441e045 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 667155080 1250 667153830 667153841
    0x50a050706080721020d1410080d03020408030f090a0f06090f0f03051b04060503010c050408060f13120504050d032006010b070b04020f0a17070501030207380a0b04 72
    0x407001c001e00016050100ca130200200d28a400b4445030040e00c4403816000900103090800b40c40400071543ca0400180501c0421040c0c00d5a04140079903649150f100d0094060740a20b02400c0f80982060041c0d01b00c81e003040b4054840210003e03d81e000072641c551040e441d00308683c02640000d0580c26050000d000d46040039401801d40c102c920b2100742c955180c4030b44500c0c00c500c00340c502c442d010704050011707915a0000000b4210080080203404590350000d043d55016100f00c5c034290013004000780c000900c581070240300744043c07007101c0a0940156100704038240400860401d0140a000208d0742d51a86941441442c3c801e1300c40e031284030000c003018a50703004190383c5201141e000c44010700500616000707503440c41d40d00c902c0e00422500c49200203030b1729910030081d103500050080300025a01c1c55a0004d01540090001541c0c40240c0b030348011002d03071182c03041c003034059454403801c0010a15404008040764503584154518045821203600165200b541c100c1e04141c3c40760100700d01460544200f = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 667156330 1250 667155080 667155091
    0x108030a0504031119140102100506010206131401110408011505060a031a040203040303020a11061308031503061810060e0619081c0801050111060a05060607050a05070608 75
    0x45040c049841801401449035000042580180406010445c3c0300c905401c5550001c4001e44034400740c407041c1c1c5d41c140f0441ea800752401072094040c00c11182d455841410b0040b60180c1c040c0c1203130b42c3d13101d2180c3c448200120080b80c91030365410300140840000c1c03003164110141d10981aaa41e0310742241e4509648007820b1081c0c0508842400b000380fa03660070211140032402c0e040c0416020008070443e0b8110245030905500a400042000105a8035038004d01c10400d444c0c642407400310507941c400360388440c201c80c000d44100c1e415070084081038001029652200311074103d40449880032004c60f0401109407049084050280107034403002c0014005c0d000c0029582000f0070002d450160050188100074183c0c5004002c412803004036030349021401d0006c0c05480c0d0440d194901d554140e00c0202d0446045040000c03250000810150300c151001080246407600400440c0c9a41c02290010a00038080541c4540c2c1040004009041840301444040c01400940101440c042c80a407036480c00420 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 667157580 1250 667156330 667156333
    0x10608010504030f0f020c0f0a080316170c03161e21030e031c020f030f0103020415030807021e0a0f080d0e13180204050903130e100509130b0405150108 67
    0x114801d210780c0c00903061f043e507001200d4150312428042c001c16254481c98015a00358000040d0b580600030b061982d010007184102400c0c1103044103460440c90358040d401c86034400c1c0d0800c00520314242d09219030241d00c14011540a140710808070000500500d100c4003c80b00703110f58903002c0e88038140c84024104500040d08050001905070720703003580c483c450007011010302c1e54489114409080c4c140d0540e200c000d101082140e881c108050000d844038000d1104a210f1070400054001050032804410b04903136000c5042414026143d080244010b106070506101ca018003403c84100c1c1c0d10352018500a1894180c1c400125003001d500908203c0e040360b404081c04565200d4528945403040d130303207075903281c62a400100d540903919091030340ca16940c800b075072160411061107404c0790040b0090032140f842c04070602040c0d84d10018202e45600c1200d0444080030842005c1042c0e040094a0950003250b82d48900c04500080d580d040c0319103015242651282e00c81d8a0304280e8404400405014020000 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 667158830 1250 667157580 667157597
    0x30f020d02010c021e2103091002040312111c2d080408030a0e073206030114060f070501060302091305030a20010c0e03010c180303050714010608010504030f 69
    0xa1019603180e12101030b8140100341807210389036105e8180003a402504808158500c0e04000300c201107403030b4000341c0b00300003d4003078003450b40e8041800d4801c50f01240c0c1d000744622a1800801c3c010b451109801d540700500b4002e00c00812040f440c0d102c80001c40070080e8440d440c44540c1581051600698001082c0305010000c190003401504100541c0c1e01550125000d42c1d20740c2e07038020800103080d01c0407070500c1500c00c484012400c46400a81c110326180590350005912020102d10354070f10505005060300100100300502181419401c5403070182c10103001540b810541e6844101694030000c0e00b81d803103075516174050046242050240e90440100b00f40907203008015200c803500d9120315042041400084d802c06d2001c02179004120060707102907002080340000741040a0701c00854140d500e4481d510385826801c1c4d040c0071b0700c5004030030244000c071449014116601a18154448002503074229100c20843c0e26400e024013809014207000070000c10030b401c26150192840d580c000111083c00010b0 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 667160080 1250 667158830 667158851
    0x4021204030206070e030c180c040e01061e0e090406020a09030209010906051005030f07030207031b03030e010c140f1e03010b0d050f221115040e1303080f04021c030f020d0201 77
    0xd000c0314080c10001ca10780c50041c0c884e4500c51007280714980c000300303480a1202c00040d1064100b00c1001d540344003548a40b64141cec00050072a42c00600d0103841d0b5000001c1400300d0b000c180c155016202201d414188547d90f280c898000400551099000d50020354840c0f84c144228144414000d8030a6403609015045091941d420a80c0344002002102010790109800040c107120f40c1c0245d01c408042d01c0c2000c40700c800c03811f00501034011624600f8040d03003000403c40b8800d100704500008907a129802074100030510031a841950702400c00118200b080c452688000004400258001c000000171255180c401c08022015124003e2512000f80702100c1004404034003490805076160f007000201d00d08044914042092580b00b40c3c400d03401c0704a0071034480c00b814000000300155521501400004d41d16913420350504003007981d00030002036082020a054a81840c0000d4200740b0040010940d408480001c10742c2c07542d5185c090f400503001d41495445980c0502102807182031600c000d00100449 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 667161330 1250 667160080 667160089
    0x9040e0c0a06081909050d171515191107050105091305191b0914030a030f0c0f2901080319020f03030906160305010303170604021204030206070e030c 66
    0x41d0310450090042103400991a400680100640040500b00c200468a0103051040e40c50182d420b08002003042c030580c0d01800b1030424143c900c1180030110114400c2c181c2002d00c000811200b000070900c80062049500c10044070320300100c10525966140c0056900802807440c002c1203030302c22414130500304888280c9440b0720f2800c802e143c484030800b081c183c0740c05400325607440c400a261010f00d81307000c5a5240c03010550000c0d4071000e01c82e50381d0140d0640c98031180c0c2e841008007580164558001032001d030010f8080c410703c0780154010705000310380c80907589404501e40032407407003100d40e0707903030322007a0140a490502c481e051040552040e02c03056052030409641e034811000d900c00300741200e90941440510821402100001d08016652203042807140207540c1c0034103940c08804c149040702c02e1084103102e0b10410741240d402d0b65884e00080b0040c2107414046038060000c13a0859000c0019485e11010b0940f56130045119900511181c68800c400400d07020f00e40c40c0032031103900148000155a07030b4 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 667162580 1250 667161330 667161349
    0x109090213050d050c04060b0d0f0e061611070609170a050705040e01020409020d060e01120812060111370201080103060c031d0a020f010c2004110408010209040e0c 72
    0x80540c3d1000c081c0c961810003520300b00010407055171203418400081200c80d4004003508400244900507c8144824804207041c0c4030594078018055210800180710200340f40507000c9114079604069006101c01c1001504001d070b075400c848003040c0e11290802580704001621904203220030050160a00c45966464032004180710341c40c45907032100e0707510740000029070440c2e0081050b81d200b10359400b94062181e0103001e46108076116652207000000303a01d03c2100750080b040b680081e0b10b40c6003061030003864111a030060f00e1070741001010400c040c400d900030000580320407120344060520341e074030400034070035071700101440c1950030102d011010042c0d030040d0030036040d07a5000001189000c5441d40490007409211208180c1d401a0801c40300000008a450384a1034000d4900701901e8411000560741142e500300014030f09040114140c221511a648282c541403006201080618603052000c0e4541c205800c000016503000416004925092041407212008140609a1900300703100003444d011 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 667163830 1250 667162580 667162589
    0x614090f06070813031202190903050f2d0114070c0203010c1404090b030f0304121221020a020f010c0e120607020c09070e0303030703050105040b0306061c05030d0e0c0109090213 78
    0x5184550211b440100e8050703402d901d00500d00c5d507aa610701d01100900f4080c1c0ea10043ea594003d43ca1356090801c40402d07540e4441c141c451250300b44601f50000140d0700c0529004590655599049840c122040101300701c2c0501413039134031455011030b85d004040c21602d02d030080d00d050103c031800100c00044403000b0f8504030b41d1b40c024002410050500072a04001c150301c41c1040034000000c000c103209040340200500f0301d00178040040c0c02c0005050603140c168280000da00c14419035506c0c3c03080c01903d60018950200148143d40c0b242c0b00907a41282034699140240012402000b1186c10b1810300301c4c2c44a0310a034403c00280081d0034160303c06512501410b12443c0078007038402c00074141500488507850300c103001504491b074920307000782e005004003828002e0310320503400e140040030203207800595103000d00d10041085003461030304000385508001a0300120703010f0006103c900a0410305103e1200c007a450703c40540354500010000401054154111404035841880000e514a0140705154142e4 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 667165080 1250 667163830 667163837
    0x504141e060a170a0e0d0302030c09060705011d030307021504080909040305070803010f090c1d01050315121b03190809060d0203090a1103030a02190614090f0607081303 74
    0x220ba0088040f40c00d040344090007024200010b0600507040f9042c1e2010350f04034046010b942044040e220220240d1100b61800d226450050101c460140307044030060255500c1a0000201000c400c101006241c480012285040c1c00100c00c1003106078041c006001c0c841591341c0d0807106031409a40e00d4840c0c0c0222103003180a441088001000c15009030220b0701c50701e0b04a0740c0d1544035a07440030650180341041c051948281d0030a01e00c150285e0260101c00c0704410001c0c0121052070140300112180d82004142d1100c6400c44041c04029848032141c490100416801030602140e10cc0c54014200040c4169140241d0004448000f0800300c1035044c3c4c1a40c0c0d029284036034508002d4001020b0740219034135080c41900c0002403140c8564009482c2c07500798441c080e00f03e8018a41000c050312406003008580158021601c80028102c0084e03c40000c14800c000000c1c00c42c2d54a0080c0c0c0415104a0344000294032201c014407400740304001859000c00d041c9400c02d61880e02c050200308410724580d005007032 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 667166330 1250 667165080 667165087
    0x111e011403070c08031302030114010312080604271b080706080c07020901091406060f09040e070b120708060303040302010c230d0f080f0c07030f02030f0a0504141e06 73
    0x9248180d14903d51107810842c0c16881c1d080003020550f01c00d480b0701e402c82c40b0398a009800d95040c0b502029070b9040300e400c0211861003107007224055a10510003007000c1c0c1c1c0706030b4603050800c15504408126408880381d4028180002051426055168040c00858410f80140e40c00b04000b140c000b030000242c541c54030b440c0c0040c0d02c40d0440980c07240103c08001b035001c0c03a0103002042100f044d520642c41d40c04841806070703064035a1400d00200c1d226400842c0070200d4100000d008609098100b105a54903540440b00364950300e05600485400c464003848840581c3c01c240306000380c0c0200360700e4111400303c0c055442e007880d560000c0c203000030102c3c0081c80c2c0e04004c10703014043c010306448001000403020075112480400000140908a520386040210b20802e002c0340745d040010705102c0c8036084901003d450001e17a501c041d5804c5400e0500141144000c014403c42c914191028204844003611a5610355003031150325003503110303004202c1d8002d64803250b030f142000d148a416a08010000c0c1c80c0030343d5 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 667167580 1250 667166330 667166341
    0xc05090a0f1118130902130207050d080601080a0902180414060108010e031e090301090305090126041b030c0f2d0608101d060102150114041116111e011403 68
    0xa045c003050044c0d0311480c08846030061900f039400802c0110b201b001500c1840511480c142e07804181030713810310700007071031080000c0d0b07910140c1d03200898140c0001d00360000f40b5803400c10b20b0181641154122001c0720086806009440c080088a01420500b0020700c54004d5403103640355a40109250320202c0310560951940d000030110444814200260003400355040302d0038017411550004900900044150030b0303c2c01c504003001c3c2e1080712a6000e881587d02600c45840b0240ca44204007a40c01c81131b0384603000040000c1845e121503005203440c1140300d0807075162008101c0e0f035a015069008850600000f000c8411700722081c0305050b20a1130070187c1c9280c8138403a50388002c120325000000480c060450901074203010404140c0704200c00d13821940c1c11070b4600721b0215150800e100b4010001c2c40d950003c0402d01e0039400403000003e078180c550b801d00e800e00e8407404130074188000598480b040242e020360a410101c0c60900d03440344820100301e200038a500000d03d4900a4078035102014404008580c = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 667168830 1250 667167580 667167619
    0x80a0e010e18060f0a0302150c010b060301080601050310060305031c11070f06050105030c03070b340611090102030412050a080a080a060e06010503070302070c05090a0f1118 76
    0x90752005040c1ca4220200c000d080a015902a503480c1d10a68802600b0b075254030342001c000b41079a40c00790075803030007029420020b10a0340020b41e402d20b6035506c5580a0701c1c1501d070b00000d10b009042840080c481035161100703140c06c1030820020b0f4003e44d42814800d0000c20000000c4920307500108000111010441d1010401415940907102d07090200203000003d01009034611404203015007800c2007e660b032942007542c2d5160341450150143c101c1c180402014070014040c2c0709401d2040d001e2403910240080c1c00c800e02e11540010f4803d0a80d440c01c031800d0210724481c40e03078082c004c0c10130341d85410380b2200080c0d0350703000300d11801c684540014108020003c2c10300640f0682c690010440392284a43c1901810201d17080ba10080c11728a400c0000540586076a4182c0c000c0034180c49061454880a1382100030b90b1041c542a00c840d40c59000000340d90302c07522441881146181c00000380c2505218204081c0e0310700030300350081d001040c40040d0a000c00da041510107800107e80c204882d0180b4961034 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 667170080 1250 667168830 667168847
    0x80a0c09060c1506090c03182d02091e060405010e1807032010030c050403060e0a020a03031e0804050d03231609050102150f07030207141c0c080a0e01 66
    0x141416040010001d4006055000701c41b5858007034a0a102d43ca00020b00303600d4081441001822658004007504004c03581c4800100d80d031082d16401d4150b04d40580c004ca11500000e80d00c1c280c400080b003a000c00b428501c603001d981c00c180100c50a0183e5450008490b02c0103201901a0010f142c0103040f0307510714242085103a000390343c071085003400702c0c80d08103034560b8007249114401c0c0a6101a0528030340c25101c0d1040032224490340d1201401d140c21625010010300d882c0f850b24085100f001d43d1369003d45e5a081c01800114400c1c0e6980c002c80801501c080d012140300e8075918184941d5000f80303c002171010508400700c003402e19002807420720343d1441070f107040e20381a4184024112130301401135440036610280d10281d55a10758000d510780d40c40049035601c0b90009038080c0c41c00001702103090344c00c0c0000e161307070051a80d00d4054200007098480c6010000c0d100005040c680c40055041c50701c4d005125442140c040600b083c01a5440d40e84640340c1d00d101b9100715200b0050800a110301c968021180e0f03 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 667171330 1250 667170080 667170113
    0x70f0209180601030c03170a08150a03050f100e01020903060604050c07170a0f0e1c05031e040311090705030c09011b03080a0e060601020c0402031b03040c0303080a0c09060c 76
    0x80b2071407940d4a04084103c88031a00003524144461174590f90041c1c92481180e00c24080ca40e10300d0029078030000d01484003080102c845030301202a1000102045080007c08000c1d140307003020309070144207a41d102041b244445000c100c5c0740d00500080116903804078134240d20460a680200d1140e4860400204c24416007500070075114803032084000c0c0328808009440c0300300141d1906180022440015100013030350900050f40502c101c0084244c882c00ca0001082940c86101100e040c8581e004410b10b240d48003045005100401242c00c02c00e2040c0b450401000020586070710a05080c041c000030003620004098500051000500105603403203024640360804140500c00508001883d004101c20001d070341d45291142400c0e000c1c0030040020030a6402600d05800901514456006100c040e4100501d10011012000001c02010200c10000c620407031080078151035507402d51a02a010b075034040c101424036450280e00421190b0482e0400003030750f03000d060000c13440e201d0b4600340743c0550b4902c84 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 667172580 1250 667171330 667171333
    0xa020105130e040b0115020714010c030309060608160b09010207061d0a03120206070314071107050a030501090c0b0403020f060d0209150d1d06010b1b01020703050d0b06070f020918 79
    0x300804d000015000034103030f807404070352107000165102040341c1e0350005000e20506048180150780c2590301801c000804148a802c4c08503505125031100c004503408c0707500001c602e4014195852049103200341e803101030005c7c01c51103406c020b602c200003552401c5c0d500480c014062110213120300d25800b8001e114040c00e0003406000c10944034600700700e041c0d950500120141c442d440c041201d0a009009000800000311001600c5d0356814504850708008400c40c0010703801a051b000c1040d4444008082c003443c0513100224501420b40713000342c2c1c220019800214402e506100510050703076000f5043d0584c00701150083c1d00d450422400c0070082c03154800d00f517400a994403010303031907403029005020480300b05030b0200850231201f10b010104841001074009240c00501c01404000e0380c4070040c3c181c040c401d8440c07800360f0780d00c40c020301c2c226800704c0400d4021a6022600503d1074002e8058030b0002d000c1960420b09244480c1d40707a4260482001f8020300c10981c020020f14035084000303000d2007940c4540d0 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 667173830 1250 667172580 667172609
    0x1215060a03120302070c0506180405060a051f0f0f210e01150302190e040b0403020f070801020d0510030336090501080f0a0b01120203120a1d0a05030a02010513 70
    0x54060005e60103100206d411400c1403000042600d4840290740d0500524000364030910b0115003004010030300140000c2d4001c80488001c00c0301e489003060401044140c4c00801c881030403052007d064546908806d40070000b50340c0d0001718580d408185410009244640c42c503414500c0315400014045a40c04604650710f00440c454041c00140d0001003100e0080e61402c5003105200c0b80039101112500030030541103050300100d40042c00122205d0351090092040d00c035508411485941440d13069446040701742e4021132040c01b12004c074400c141d040a0001d12002e5a5840d560b405800c08804408420541c0162148010300c1c0121050140080c0c0006090082190311034030300000800083c0a0a4190710a14641007403d140001c5c8001c0c14a41140c007020b000d0f0300e0324907080080212030700120303054041d04020a0b0381078403180107130400d07000c0c54480c205c2c42001c0315000380014002d0035101e4403481c49030008100c84e0b24080f03140e98242d60203181583c0c3d90504d071070050b50542156030041241c42e00e1030 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 667175080 1250 667173830 667173863
    0x8120a02190f2a061e08040512041508151c050708060a0c030f0b0607120905100e030105060102060f15120a060c02120f040b07050a0c0915051215060a03 67
    0x107030910158003d8540d0030904031520384000b280c000440802c2e01d81040d59683d080188180100d0f41c240c1d01c284228100c980c046104090240d89401c503600040444c0c811303410081009400ca0b40481d40925056400054000c2d40b40000c0c0203140a221009104159513101d074041c00700502c102c801414040c8101c1d1014104030700000003d16880300440c00291804540c1705c40810310b8081c410345000c00604013420b002280d140c0207d0301d50002c01907014012103d09c0054907803512074840456070069214004d05100c10070500d401c0d180000c00071411034120204100104000340205a00150b14a50000808483c2e82c00314405d0031150000c40b120f442643d2a00c0c081084a800c08100f03a0182d0b401d46061015014103151b150058403120f5400c02c0d007e001c24003101c5500360281c204980141c08442d20340c800d5844081500b001e54102c18a07081c0c4424421030140304640c0b28600821081d980784a1180c4c00d511510707254003480c5880e00c086450381000c40e450340d03a01d114a20207580c0000c195103010003003 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 667176330 1250 667175080 667175123
    0xd15090510060605090307051c0f0f0b161d010c0c09050a063008070b0f0a110a021507022b030c0504051819060f08120a02190f 56
    0x1008803020000d810b1100c080b8140d8424000d80e200301d880a8011f00d201420401040b440e0507080030580161420420060080741881c510045001d0154540d00f090a0440c10442c1c01e25070014201071803a050f404110204650044400c030201901000c100b50004507040102c441e8484c0c0e50001d84848500b0202048441e0740b54803840c0900300c4c1e0b050401c540c595640650710401190190007500d4201c1c000c1c810318604101c8070410500340b04a950f2460a510380c0d40748828854141e420310b01302e032202c1040182c0c540584c03140040745100000395509000710460020340d2040d4255140b400041d0f040003140f10303c0e000b040a4004044400d204603a15001042d01540b0751417202d1503d80040c0c207080011001c54081c0049900b41c0b1009070640c1d1041c0108980c0c0f0000d00000b500b0300c00403180f00c048445820310b542c441e44014002889082c21000d28228825181c1050141d503201804030410002900540000e003406440c011584031f440c0c0c1ca006030822040c1545215000740c04040400c100c440d01115 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 667177580 1250 667176330 667176343
    0xb0a0e0a0303050f070c05030706021318020c101a0d020301020d050c120105010e010f111f09060506041515050d1803121a0111030405150a080a0203070507020d150905 73
    0xb07413410380d1000c036519640110360700080da0344094034581081202d80f02050307264004101c0c0300b200460701090380346e488480d403d00b04400d183c00c0062990200d50244808010f201e2581c00010360a0b0520070103c1800c400c005200b0b2003900c09200707804030b40307507041191000c0d0113450300f08820080c108841c2c40c00c40301104140c0d00545000c20705000307000021841c0c1d80680c1e0700600c281c0f01a9509120b50b0300e203e40580b170a10010030030348851302c40c460400c510285040c118000c0c1c25030445020810742e10070b141c03110548130040c0185110340c2c04c000b00541d8103610f11202004680c8091a00c40d082e841903281600c1510400040c1004181031001c40403151203030315030603103074a031007507840d40d06103040d0105003021510000c00750820a915407074411025880389060200520305036060382e14280c1d442c000281c441004040401c0c62100105089201641007141e1079881300c003446040d403071031401c2c4000502138454031000038070520085040100384580792810b4408504d080070200414601410a10360714031 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 667178830 1250 667177580 667177591
    0x70b12150a0b0904110a2001020301180e1e071e030f110117010306150503010b030d0f0e1305090106080f070306150503060a050402120a0c0b0c0f0d0c0c060306050603040b0a0e0a030305 81
    0x428040c800344143e5414820ac034103c83c0040344a0b00000b0540070907401900b200c0c510381c0002d110342c40c0360840000100840b040f4410315a030007061250310740090304007040c4601c103100d64950001c681c01c0000c12003c60310610429440105400d1123100c3c0c0006a44100c1391105e04407007005140300100401441c3c2e403105401d4051042e100b840b10307a440d0201400d880c04481980e415802c40c148412881c0d0140314403000c0c102c441d00b096002082c9a40c082030588140103000000c240d215403d009031301a0a01c501000742445402801d1400c00d01c1c552030782c0c0c6440c580f01c001d0407140d840c0c0005580940c1d03400a1005000000e0545410781404900b50000e010241da05910a0200c410f400c80c1003071000035951071903580b00c51420b0180d841e00d88108410780203c00c0e1610b044c002c0c0e81507041c3c0f2002c140000703c80c01e056612030140c44003560070101d0498071540c11100074180360031070512503a598042501d030311940c00050055655a00c2c0340c02d2010b481400c1042c000ca10880307000004064041d04400e2181 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 667180080 1250 667178830 667178867
    0x1207081902090c180d11040e060a06051c0b07230c070f050f010305130f0c03150501060e0409020d0611040911070201050304120c0203070b12150a0b0904110a 69
    0x60711420849092845903814900c400c1c1a000c0e240d400d181401d03154210307075a0046c4200b400039000f0a010605076103501c02140e0b00d41d0089403c0042d0b015035441150090002964000e1040a0004208003003c071100c0001c1e001400b84c0c000280007601c12503101c1030303852000c500320181e819400c0c411aa40d801c0450380b8a007074000c0200110707a1352682d8940f2800c5035001480f01c4818000c2400540c001c18018040364500030123400e0241c04110038203050440075104183e062621451400c0c895a01c005090f0b60b040c110f401c01c8010020720351310206c000c4801c1011103000a20100c6c41c800581c132081d20890051203681003203441c0c802401e201c4082e104071032203c601400f24001400710347c0c015200c0c0a0009010400600205010980c00040065501000d0030100f88118090300040d02c0e10f002c1d9880001d80c0c1c040041c02207a05104204490707040405444513a01000320a000903400203203901510182500105040c00c03590b55030f1b00110100001c0da040e0540c1d40080c04002000c246002c4610710a0 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 667181330 1250 667180080 667180099
    0x3120e0319020c2d0d0807050703120c0201080703111c0606090807030210081e10230f06032e050f0a060807140403140a020a060c0309051207081902 65
    0x98140702041044c0c040d00d401084501c080c418090790288526a50301c107402600c4170310700c4030002d0100b0300280251409000109001c51452604a50040580821004005c200381c1c80e01d0060360051039403600041a820b01080043d554032402c6881d01030303404040b0520341c040c0c820705032800340780c0d11a0064940a613a00300d2240c1d140c5035116a140040e2000070f420a10b81d204d40c070400752017041d203550030141c0800742c1041080d030b080000511010039507411100c10320b0f07500c080003e1407010303602e80800403407034505d2000341c0c40c00c40001c0d0b0680d0542030b01d41c3c050b040000014241c1001e4808800032403d1703070200c0303c008400294060030b420949000b280e000e1a001c88000c0f8075490301d80da8120484031140c1c1c4000050707940c1304007240da11142614000341e0031010301c004000981c03440c0031080d1195540d0024280d000080c01004400300c01c9a00040901078001c040b0400700783e00c02d80110a464082e9100c04003003150401c614900b0b81951b000a180703005a010500c140071904002c030700098000c8403690070 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 667182580 1250 667181330 667181353
    0x921081c110708030c0d02041701061404050408030a0504031806020a1a041221020c0303040201030f0b100e061e0a03060f060507060906200408100e0a03120e031902 72
    0x40e1240700400b074502c20050000a0703000c0302c11802060386d68070041000d8281030b5103e00030742c2803c4c40103680d40074594464074140503071440103403081c4119504650174402802c040d2038030300c2c01c0e11016110051003519800083e0a250141800400c0940b58008224580717aa55100035203c08400714212454107803a00700c041c160700c0c2903000a0046410107030b083e240d02101c01e0140c1d84442c0000e9440b040b00c250a654903000b24041c0b020f01400466000919a2498144001401c075113450846004442ca0428915115180ca55038000c90805c1c0c6c0c20445070102082c000100c5c10b00a407400c0d036100900c0f851240c0c80d480b8684001c0d141e8084681c40602c6669140c018604820480d03000d0704002400611400002c62095000b001005005003000103d00e503400307a419200c0c54510f207440800c90300008041102035020003000805548400040240d42540b070600d5444044840d0081c04000600512811a0095601c44a0184080000c503030341c621410341f481c0c0c074800003d6130342030150240001e80d00 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 667183830 1250 667182580 667182611
    0x60403020f01410a090608070905030601060302190f0813020d120908192004021b03190212030423030a020c090601080907050907021911040e0d0921081c 67
    0x258525032540f85c00c00458140384048070215002803104041004420000403192003c0c00064080c002d00d59025070340381c0d044c09121200082c400c42400400008e02c240505803a840301c101c40d044004484c4541070248540009002140b0a40c409404032900c0c81983d42160b802c11212030856250740c060b590b4030109644a590b9140c8816409407000c1e00c10081c14450741d90200985040300320040c001805c0002c0401c22400c1d04903400b0301600d00380c1c03000603594403075490000c0b690312481c0c00d480200144100c503402c141d0a07010141000b00b06d0008504080b41c031001402c2c000321003042c0c00e011641c445203000002982c07480c2180402c0d0080c42c40c0c002040065214080c007621469190000740019403a000521036014401846c880440c0501003070001d0030588110404113580c020b15440403502e580004000c1140e0103c0144512944001d4460000300e802c220f040d0100c1c4c1511a00c0300da4105507440764071081d50f0403140184805800104440101070400405c2984003d18008000c101c50300c04141 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 667185080 1250 667183830 667183837
    0x90201140f040605030703090b0a0626100207030e060307090603061403210405040903080108010507030c020703030c0c0f06081f05150d0b0d030804060b03010203010302060403020f0141 81
    0x20403444810071051200d44c0c0504002c41d0800d409141c00113034004640c80315184c01609640a07401c45846540c10804542c00d4400801740010b001c1148000c041801200e0303a43d041590821091507030007107484401e2602405000300d440c0805460156280f4052000030078041b198050440441d15140006c902e407013600002c0c10103244042c0003010005042c400e01c40e0449a42c41074008001d43c20080440d03a038449001c0c2020303007482525101181d50506207030ba0300f0f49200800f0042010300d82011100c00c640c0c0018090122034150030980020076040c2010042078090b5000b09101e05402540010341c1c0d13500c0058070303200f0000e480e000f14120000711101130307103021984074041d07010b54003500214000480c10000c0410003004100051081003d00100f0f10b40c0c00305000a034003040b0700300e0400c014440300307008150402c04120000c5107151305590005015018602000c1d01800c8404003035400c0d030f406405c40e8080345c5409200c030505010384165642d02c1c800001c840744c0341b0400c0741e080d5254011002098 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 667186330 1250 667185080 667185097
    0xe03030709240c0204060302030d02010902011704030e09040c0323010e0106060212160203060106200c1309080d060308272110050901091406070206010e131509020114 73
    0x1042601180340c0e100303e904461155050341d0050390b4010020044c1e4081056403e00c2c0c80b0740e00013003004125800050710514600e12410421460302c000c010000f07502000e20300c2c913410115005901511281441480403200c0d404c002d1a1014442c850300c4c002c040c5d0084007200d200040e000344854040442c110307080e0f4030280b00d0040560b004d0300d1408004514080a40440791444c12502044641a00021310b0301c0c400fa400702000c40d043d103001050b44e0805910305043c6100900c010070041c186980403400394009440b0301d5125541d10541081044001d4007100c1d66020b0811041c4295602ca042c5100243e0106028007220016820001040151044e03851180400100b0340040c009890a01c0300c1c803600c06040c192010b0080b84807121131866148280e0f401204031100002d1807065500d40b001c60702107810b400f0500c0781d000c2e80030450690342c000341240c15a220882410341d640c444c01401c05982900c424020041c1d05010b0754045569910741c08402110700036a41c0c401e0100642c070b00c1c484148955a207 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 667187580 1250 667186330 667186379
    0x20a12200d090b03220605041e080906070f060e0616030e100f02071a0105031b0f0118180e060f040c14010215040b1005091014030309040e03030709 65
    0x8100f101200203006183d20501401d01001e040c00220100d040348580342c0d50441d0748030394a10900c000c0c04103103480c502c08140c1d005840c0651005903154030b60f0502440800522507400002c0c40010010351407924050a0b030306c444240842086091821b456290171200251a194036600c0501980e01c6400b42201d1000035a015154104410400710301030400061917800c016002c015400004952802940260014145600b22075041904160600c40c8000450408841e002400306041c2d8588001e0f0710380c0c3c0001d00b020a50090000c1084082010961104d40d20500c12940d52201480076001040d00400c4030041c0d80e8159607400144071542420b0390054035482c0a41e07014004005401b040c4403260a050045800c1989108942d140d421400c42d0100c03000c60b03c81062244a414030781814001e407504070703a10100c9152032070703800705401081d1045494600404414019584043c404c64a060201900c00d2101c0c2c03040a00c40341e520b40c0182c49240000b80b10410004d01000342c1d001c404100d110601 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 667188830 1250 667187580 667187597
    0x6010f030b0402030319090303030605151b07181a150316021504140d02010506010e060d0b19050312030108070303030f0b120f07050d0f02040c020a12200d 68
    0x4940c1d100002005004a0700f42c03008101000e030320203130f102c208000a905982c4861b540c030704616000782566001d900c914080c5d02500000319411003034074191040368809103800284102d5840724545041550741c840040c81580601c3c206034420303d500964008007021300c100c0e0a2498540034080c1c54081c104083c40b4107203042c0086144103a207405804c070f40000c80d00c11140c150151300780340c3c00292000c0d64111344804680001e0a0700305400d022110050f8283d00081005150100010f090f41110000e650700c01e003000103850b40848100d41c0f0030100c80c03030058410603682c8401070488580400e240200b511910404000302000010101240d050f00e8101c4007519800d46150f80c2a03001c1c000f4015540f031200d445600d540401d49581a82c5003540e21130b040184510301e43c0800c01030501395203800c040c0c0a0401c0c1d031a0344c40801c0480070103c00480d4117540c0003501c0381203c0c404a041c02c2010760010002003a100c136182803154000200982d00c1d801031740e4042a030783c50341c000341c1da00ca1125000c1004210303041c = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 667190080 1250 667188830 667188833
    0x51314150304030c0c0b091f021c0306030c17010e03070305090904110325060302040b040528080c0901051206061e0409210903050a1502120c12070206010f03 69
    0x4007464105100e0b0034550307007800107591072003a0340300030307800041c8a008082801c08503454482c1c400410711404004c95401c4081407a00252580031481041c06200d41d0100b15442d203500c281d029000070f58101549400c2b0782e443d499240c1c201c0c42c205407158125800e05500141010000c81181d0350203a142d200ca40c40d00b04082d007444480e01000b0015507407410301144050140e1030501c1803012200f01007081100899460745205c0d0283d881c2d0b0000c0d001c242c8180018420f01900504032800e0751800c540e5131503000700c8012041808141303450404030b99005160002f900c01c6000038014120030b4119084100c90f81ca460600042c50440c2d60a2240c560160011840701c0c10b0049100d1a00f44031100c0d15011142c1c1130b00402c00395820210100c5041c0300000c47e81001c070fa4401130945940200d45881c0040b145540c595690782c841075a0040e1261000d40000c0507120407580c1102c0c0310801d81f4800500d00d1802e90840c0b03055803c4600c14060218011000445403803010546a040e64256505040003a003035 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 667191330 1250 667190080 667190119
    0x15022a010206013003080601021b0112051512070801050105033d0c090501140c030703050f130f0918020a061116030c05100311030601050325051314 65
    0x115001c1d8000354182110b2010b0384001c0c3c40132241c0081c000d1b04c0700d441e0b0341403400c0020325101410041c18010041802c1c0c190880c0e900c00003482030b003048200c022810340c039007c0d6110100031481c490a540002503240d588004a000b00e0503800301c3d6003a200030801a070740c2d0402e06071910610000e085000c111061004914800002804080903490030b0151081d007162228408031140703101d042c230114071150010065507074040c808031320b00c01402d44140d0400d100e8030282507403400f071031900406211740400e0791036100203203209840c0a11030000e250f1050923507488103042da0b550240a09225a803c1000c00741101c11019540249980c1c0a080409458503100341190811a0030220103414000c19019100c0c1c1c50203540960080c6000e00819410180750008120721441c40c11228400d06044c411280c005c504000113903503011100307081c034607580e66031404a85400b0401c01086803032201d040e1030048406502034041c08520038568119007030f20703031240742102200300421400c07680698108189000b040d02c = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 667192580 1250 667191330 667191359
    0x501061e0c060606050310050109030b15032104170c0d0212030702130e0f0609030403031b1b0602012702100302070c06031a011d09070915022a01020601 67
    0x62800c64240002540c66000f80c80c121341c03100c4c000900c0803041c08060104c007103191005250908017146502c0c0313940c1e200070080c500200b103004800001ca0103843d850300e0074450111350318141141054000c41040a0402e160010b008261445105c0380125044103800541f0001311000144491290040c0b41d0130070501c10f181c420401801d01051050700016112f00d2103d51000d070000d0b0703000c50a541240c21541c9024140c40e42c00b44550302c40c105021413010003008450550703406180540303072054405549844920b018500034658000841ca02c80f00a030101e01007402d803501d0340e000f40304280781d0007000150081214100c440304801004003000500e003044100c800d44246080241c101611030f11440708110b500d82c418400b190321f5130f030401100e1900183e03e8201c000309017018100080e500d14125460a00315104c0c40c05200d914010698a500440d04071004161020b41d00803038007901c2500a44822030b042d40300801c01c0c0c070440800300030031700c1d0240001100e506900a00083e841c0c24114074102c00c = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 667193830 1250 667192580 667192637
    0xa030807090e0f1005030d02030c1002030c03010e06181f0b0415080a060504090510050f01030c050405071403071d03031801051308070e0726160233010801050106 71
    0x40c4c4110001a05403018000c10f0540f0605401039030321034000c40e40d11b50820102c1141c41c54401e10400400018021420659047d111411401180359841c0340200d506240c12220407c802ca15860800140300c1d8800740180c5e6019290f498148865542c0c0302110403402540682c0803e9a600c024420045216210725503010803100400710351107944502050444001000680e16508801c04858051040e13000c0d0315000a40ca07000d09500c2e40c074580b40d00b55007048501030b10307106503160404141f01500c1580e070034401c81d210015040d52400c140070040c1440602d43e00406d07010b400e6440ba03c0c014540130041d00c4401604d809004640b0080708011240365000c408482440f040410b0b01140b031243c10011803001e003d000500101c0c03410056806404a100c48442010700c1442e203101c07190075410340b40d2290b04000011106180021783c0740d8268200000c142c44c10210a0035510f000d40d840521455600b005a0703000ca80f88540c2e40c807510003500707170342c001d00401010031740a0342c64802000c001d480104401 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 667195080 1250 667193830 667193851
    0x3090f03190b070f0c03090e07020328230a03050c070c080102090a080a030f05181201050114091003020f040603150504020112020c0a06020322050a030807090e0f 71
    0x1014070403040c049694403000d4890305450403c0040407038000c07410a5200070a03061040c141c82c0c0343c3c0e40c01082403030640502130030a00c0c0c0402240b4183c0c020020750b0003991390000e40310103c14081540e401ca10728104405000104a0306465132104031001044260340c041d410341914120381c006085d0041c02020342000030030401001400c011408110052014045103c0050fa4688500d020032080340c0b02c0303400c584070b1a04000e010400094114161410f14030721810511744918220306041c400c8030f0010300030382d0001c0c2136250072001450b06501030740c1603030000a440d9024000050134000c130800d0403030b12007008407403c60040c005450901403026030306000030404a11543c5039595040b450601181e40808030761200240303c11580c00c000400c4440d81d1411086080c881840346040d941c8142d28000303003140342e001012454514444450850040c0024a03800d8601c001d48dc015940c0c41d1508010342c0015466004074001910905182c0d080b40c075100c4003040551100054182290350162842c40c00c0c = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 667196330 1250 667195080 667195093
    0x90f020a05010302070b0402090c0405090907090c080106050a0f02010b030d021c0e10030b060912060708070815010311090907200c15090102012a1e020618030d060e150d0503090f03 79
    0x226543c100b003703817040442030060130141d03181c124030341c05079607040501d0f60a01040000500503590f001040c1c0b0302200580c07a140000c40508801a40180409909180c00d8015004c0b00101d1a07000107072010034043c144402c00c200003c40f02c0442d851500d00032001c2e0300020100e4660302091081c1c1001c1d2544500500551030b0800240002d0b10f80d100340000f44039035070409020041c6a94020501e154001c5980c1081c2c407a034a0901c2c00f60424408001c507050500d07a46100c1d003401d4001e590141c0d0708110740641040c90740c0c1420400a030003941c0744040803140c10071001140391140030108282240380e1000e0032100002da4174508455203034004848460456503100802e405443c100ca0050750340d420a0b028901405c00007100091070156000308000310800083c0a46c0c0c003540d40094025401511102e41c408102840010981148168400700c0d0356035091403030100e4031000c24024203000d484686100c0002c2e0b0040720901c9150610600090a2500140f00c0f995841c20301003451400404010700b918034 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 667197580 1250 667196330 667196339
    0x109050111191208060306070e15040e0703150b090303040e0c22180209031e0a120e10020a0b0a0b04060b190207060801080d051309090f020a05010302070b0402090c04 73
    0x500c2c0e01a04066810765a40040500002e410010854102d902a4050122031808090140106141840c1326000d105000c40e0301038004107030b9095502600b40d5a542641905010354018040c203185507904a542c02d4036403002509074054012500d400d00050051030800389441e404000d6010000d01b141c50380201081031140c00d1540c00004006408800c0780f159030782d800c020010b01800e03808071011101070b2041040724203550340060340c1914420b940d088224145161a074041c181103002200410242c1c1c10182503241a80100c20b1120500e0152a101c60007402c2d01d00881e61180c18980c0a4000d4400c3c034049140003c41da089640e00202c0a040400d400303030b51741075010140c1e00c000301c2990401c6004110b040529811f00c40027004040602e8080f25950600d165507807a5480c141c011014004002010500340c401e030f9070510002d180d0107108010b103e0460500110202d0b490f0f0781284940c980020101c1d207580a44240e400071601f10036009650f80d601d5081c40030243c07000e0045400d108042c000020b = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 667198830 1250 667197580 667197613
    0x60f0a020c0a0c080c040b0319140a060506091e070c060e101d2a040b2107080102030108030d181704080c01030902060313061b0507031103090109050111 67
    0x124051082c5061001c0f68504140c59080c001000c040341d100d2418a00d039003040d903a0000328030b43c00003c1052022113000807860300380441809046d0845240c0034910402050141940c00f840c17058906403803404240d40e803a0420004a0101c603886182050800085183e451181010701c641e1743c07180a0000303e507000c0c201d009150400b5041e000c14019141e100f43d0a040584581a0f003000081740020284410140c4400c18070050000302c4044014007030b0940b0312141c5d03030740e005000c440c41c0280405407954a00c1703112524280c0940002d810921860900081d00c1c1014401c690480b0907000185003001c407503440c0d0381c0143c02d1041c4440d040b6860034035960003088142010380da50380000085250340f5850701a01c5030501c1100303c145418540b50030301810258503804200c039880030072100c0d41ca0707c2c000301c2e140c001d0003440220081e40804004000e40180c1c0d541090060108500075205c6a0303685000400960340c034070912803039500040c401d4004111550041030340f0b00d5420207185c1500c3c40e10055402e41c9 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 667200080 1250 667198830 667198843
    0x50f0f01051e091006171e0312040c0f0f030605160905010e01020106031a0907061706040513061407030609050103020a060305070203041505040f0803090108010b1b030c0f070e040302060f0a020c 85
    0x1001c0402c844040703891400703002c00009800c450401f110920038a41d8521050300d9000300f0140305030080000e00003074100440896004040c1000700d840c0410540c8540450094080d54002120400d10700341c0408c03c803d0400244010844107559071050700340c280310044a01c0001d026a0342e05540d00c0c1d80700030000924101003103440701f851410b00005450580e18981c603000f12907000c60144030454940203444c1c210320030069400b40c000c0e200814162101c41d00c0b8000048103280c0a00000d140c0b03041d18802d8111000f03a54061602c0c0c0e071b024410b16440310010411500c081c0310080d030003064010304005440c040c1c0c010b00e51286550058a06050342d5100d03034118103007265011000140002018003115240030901401340c000000190705201c06040041c04502040c083e40da0301c0c081c040740101c80200e1400407003c1308403560013540d403501140100c2942d100680301c0042128040d0103030210700c410a00542d144141e4056004102d2900c0b20103454507000c0303026004c50f14264080200140300d18003000710707 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 667201330 1250 667200080 667200089
    0xf191d040e1b210c10050a0e240706050f01080c0303250b07081f14010c08090a06080109050108010b01080c09041419051f1e0f03050f0f01051e091006 66
    0xc0c0061300d030300600b0809209080e800d140c00b44242070002d6044180e001c1300c0c0300010320050307402e0150303550800603098051044039000c03040d0550001d1800c04000194010b940213940e243c082840700c0c0d07280c83c180c80d11a088800001e40651090001c0640c101d0044075008401c568610074000d40704003600e800b2852903040f24000080f80301c00c2c00b40030f000981c00c110b00c99100910056201900d040c030b0040b46803080e9800c500d504004410400e041881880310880e003140200030003100d082959008040c1c2890740074842d010300720b45070600000300d1b5407040c0a880388510f4141c0d2481e840c1d540b41202642e094116000351a001591094001690052081424018040c20000140d045144118442910b200400f01c008110f0145120f41450b0070100045d0140e88151100d0340034035088000c0811200d0240d401048540c000d03080010501a0104244240c00106800d6490003010050064282d41c03054504c000c40007071061100a01c21815104c950300a103c80058605101a140c0030311f0503100d19030803 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 667202580 1250 667201330 667201333
    0x1b050a030507080606061303030f030e0d090501140304020a05090c042c1e0a02070302010b04090c0303080a09170c0f1005100f1a0f191d040e1b21 64
    0x10030b00030900f003048a26400002100c05500c1d102902c00d40c1c02c421002840024140601402101d03030107030081e000410300e98079680c2203900c01004404010f00b803614501c502e502090282c00d00c1c002c40c4e24004102c13480307540c0103492204014a4034050080c0c10302d005181003c800d906010110380c102c4050300420541e170704035603410085039100128903050301c406440c03181c483c0b484500d04d102080c420101e407680300b00b00850050310b4030740500b4142e0141482d00f140d6603100d441c0000c1d0f2402c20856410030300607a4020354580e480c80d600c0350065402c442040c100540348030405540000000400002060a01d0380030099402c810a401c840c2464103559042030f070007e82d120300401240c1203101c00740301c00805c4a41c03156042c05140480c00100c0c20ba10f001b401081e200b0000320a00548050000c40362000700410707244d039805c010150010302d501540100c1c00590500c5228641c89898a03004000c0c6140204018201c50b4000d51010741c0f14410008080e904445000c01403440d001460011040b030515400 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 667203830 1250 667202580 667202593
    0x3120c07061821091502070509180715121505030102070f2d0f03030e03040602030d05060d1e0507091d0c060c06040f11040615030510050d1b050a0305 66
    0x43c3c1211010014840102c1d440c091070f5803401110f900400c100c0885019103101d44440d0280003080b41085602c0d001160070204803000e010500030b085245202c9020080b090300c4a00b41c66039502c1c1032000c0c4019100000551850140c103080b00c00e548078114512015482d8141d4a50380c00c0800e0036600000320540d04802e100000c0014070000303100100003030b07404140200030b403a02040f0ba0000000c14620140c241403d03c4048002c141c000d50152501419420440b07840c1d5960305c000075a0b0350301a07030064041e1130070709000c113410f4203200c0f00c1041103552000581e041c4c1d0054031003107040814900e105589034890304c0d500240e141020b100c0d03800064088100c5451030540d61441624201c41c0c100c005006d201c0401000d6200034010540c16000380d881014400304140905040c500e00d0069003116034814501a0300042c1d100340721044005600941e102400303107540e408603909501d42d5a210321604107020400c0000061402d1305004802d4054800d642c903030740d48880c0032845100f100e8004481ca83d0066 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 667205080 1250 667203830 667203833
    0x20f011b320c150906070609080906031305100b09040204020c01110a0e0a082d01140a090203060711071503020c1203060a0f0b07080a0e30060903120c070618 69
    0x83e4000c080d010b010340301d645045010780201d0114401c003000648001e40e95841071007000407902c01c0711184000102601e4a80c20314003045807081c8155001225103105402490000030345502900001a038014240304181d500c0707800b880080e5100d001f090b0384555030782410740500e4403001d01400b00802155680803000800205000581c1c0d415001405903506ca988178440114410801450500c240300e01d40d8010100b00c030180e405005048881e00d00482c0345010003840000079441032207002e008030115056600e070844240c5d265801c0c03070a0a0030380e0700411014081d000c00c003803002611200c10701d001442c2580800d0118100076140c1c80e8040c5040d4000241710031403038428003080c06414501c1c0d13502e080a10f001900b0450744a8031900402130a400308103034101c80e000e440d004590940c007805a00d8036043c01c030340002c4841400d20200b40e580c1030b2001d1404001000098592060000c10011031a00041c001107100d010002400d0a000d284100010400104280200803240340074001c0714941d003149 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 667206330 1250 667205080 667205089
    0x10c1101060605090a03060b060c1f050f04050a02010e0307030b0a0603060c0203040b0a1812060903021c08060d0f120f02101a190b070f020f011b320c 66
    0x140c2c021410400c3c10701c40041c079641c0340480b64080320341c4200300081d005984004a00c050183c1100e44125014091043d4640d007041d019001c40710002c03031030070002981e58816100c2010400e0740e000d40140d0000183c84019409130303445804607071b0020102c2e0b011a503a5600c887c8910f00455030140e070703107031148010030030408240200030082d5102e001440c1031074201881e1204e94041c00c420701042210300f9034000c4030f00c4481312400d0040d103190003001312045071a040c080d001e06401c0c0e600310700521842c802c2441500040d10b4076180340c4250740d14844252a0103003048206c580084099424000c110003407000a249a10340740d200d08820380f200c202c5e50103161000303401c01070034014401d102810140c203400d01d40c0c0303101e0903502d039140304640444404031003040e0452032490540142c1000d110005a80045c451181c00000503240300310340400039420700e1001103c440568a5012441c007030003852900000302c1383c16503501049811280346a003102d844103126070521008402c6501c0b50000c0c0060009400d0 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 667207580 1250 667206330 667206341
    0x801020d14010b070b041e08071505010501090b03100b030906040303050106020a02012a05030f180402040503061b071e1208040819090e0a270503030105010e010e03010c1101 76
    0x50081d11541c803580b404150701c442c2e104561000f00760351290f10024041100c445070b0341c41c0c6801d1ba11005080c00c821803038680901e91142c1425290035400020700e16400740e25000e810b06a442c180d5600749660318181d02c1440981000e81807440d81041920080b550110a4000d5849102000c008101d1424981400b80486006030410350440d0071108150002d44d8012862040510340c100406840b00d2900400c406140d59031071000740540400950007076400301d140042c100700c400420041401051110800040f48514402c40742c041c6c010900003040c1d80c42d08402580c40c2c41003503071a607180c145203540e4081004111241c07000d620300150000f42c1840140f0300d241c2400c1c5103074203040304c0c1390501d42c41c3c0c55128001c0c400703080b1082c4c4d0101d403680690b45c444c2e1904001040180030700705860418044c5c07080548084500c0d00c6000b80e02d15550269840b103040203515080e0040e01441c5141d00700340c011510700000750b07405070500002c1d1080101c0c0380c44c2442255400c100035500c1008580d40d000e40d041c20350f01d = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 667208830 1250 667207580 667207601
    0x100c17180a061106040b060117010f06030e2d070e0f010612180b130b010e16090f030b0703020705030c01050114180c070311060109022805070b040c0b040801020d 71
    0x145000f8800a5503c00100181c005070000d403046d40e00d13980c010048403000c040301e500c1411401030703200024081000328001c8080e111640c4080c0110800444a150303650104c5129001000340c6030790724600004807401440343c00071180140c507001c81c0c81e0310010680c4507055440303d036400344003001004203a5210030b1580e01c401e4464020304c40c0c01c91182110b84020340181000d0310707000410020901088000c0c020101c0994030a500f40b249603922294954081021100d0702c6520b041500d502c48400d2152035183c083d01ca00d101080040342c215140c1c80002a402000f11003455801c011000220380104013070310700200c0c400e001140035070501a03a00799080c44030700c009020758500e8185554a123038040929074040302901c15161038443c141400c0b1821070f82013103c02400c0c060381c4004140c06040d5001003500d170401580001c180307102944811109181d030035118000400c180103641c00500e50050030f82e0840e000c0d0080c1da90441e202c51481d1341039030280d40612800d81d0300091030410007055005840d070a0 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 667210080 1250 667208830 667208837
    0x21070b030105090402040c0210150806011d01210c0801050603070603021912090624050904080d0b12011b03180f0b040303090b0f010302041a100c17180a06 68
    0x552529010952203d00070340000c0c80b4036100c0c079000b44202d10802001c00b20025540060180c0b40501c6a00c2c1c401802500648a0324080c1800100c1c04071184640c8030040a800b0001d481175a01c0c01e0030420790025041e00351121100000b112401048030b00d001103014065102c0001014103041040510300f030421742c40710f0141401440203041d1003e2180070009180d9050401e0080c1403103c1100100802c1415001021603180c0f9030381048000d00b0343c2e001c40401c5129402020103d8070f80040091900b4200d90040c224842046003011061540c2c0000c107481001502c000c40c104a80d40f84030b8292101c490390795260080300502c0d09001075241c0544c500603030040d950b1907004c206a80f115041782c20040405846248480045400c040c4071744d02c4550800c1d086500d000407420031008000d03100787c0c280300580c400d900f81318800a0b420f100b604500b01c0c110300208248a90010344c07005071000d904041d404c0c0c1b104010403240060076481000185030b861405010110556410402c218030204207810407401c1 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 667211330 1250 667210080 667210087
    0x15243002030717040c1206110414030601060201180f140714102d0c060c05041508060d0b06150c0c01030e07030309030809060d0e0f0c04090309051e21070b 68
    0xc5445801d0110a03540d030740e820000c0300c81e850b0414502600505188600440002600041000c0312b40390072030400d40c0480584650b0390303840c1d5049090302c80141034070000c004000c6248001446072103403004580c0c8504404c40014000402c17103810400c2560060044005c01400e411403032400806004a90f112401c000900030b195000c120380100802003e1030003503115820031100355000750030040d500c17580100240f06003418a58000c0154210b0711a40310300c00340900300c001c0014002d4583c18402d0802526120280c407507a212a81803800107441b06402182c0402403e80d682462002003810350a05c04c014060004e0190006007262040216810250008130040c400207070b008481501700d940100000d074407a6001000220079120715001d07000708925041c402d5a402c0d0001c40c0c9000b0f02c040a00940300110804018041582d0702c800e40100010b42c010b01c24010b5203040d000c2c6a41e803000f843c02401e50100b000c3c1c0800e0012292980301c4d0240414403000d188080780c104030101c003429540540c01d08 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 667212580 1250 667211330 667211333
    0x90e0a051b0c0d2a110301110f0a0306050904050604120e040e060f0606031006030b0f06040e15040c0c140109140303091c0c061805101524300203071704 67
    0x43d504201320000c03d4072641d501200304070390b02500b00700746ca50a0440f81da41e0b2074004c281110f1041d40b01c2020b640100c3c0c03d01400140d5450f142c80300c1403145810078068000c3c0e58a82d0358401d920a4190407250511020a1020f000c680b244d100d24403030315040d84028507032418404110440048010007040c8241010010040d14400d10b14100c002c681080c2404201840548006104c060640c0c030003d8002401007000100940e9101029004085146880418a490350240300c21383c0d8074507204c14003243d00c0740d07144000103610f0300018110342d074004000600410311380d4070400c9950614501860940c8003205200b500c107014012500d07440601c0c0f4200b0040514144050000514000042c20340c45d5101008816002810b0ba0040c030158860162040e114540200c0c0c002403010380842110241c032010040f40701c6401240943c070401507000980340c1c00c00743c2141100c41e141004601c000c0e251003992140490005c40c0080c5595145c100030140c0c407854008002059107042d4180f90000c00801c41c203220 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 667213830 1250 667212580 667212647
    0xf050702310605040c200703050111090405150915010302070209090a2a0b221502010c0e06032e0303050a030c080720010e100b0a0501090e0a051b0c0d 66
    0x16881c0c041b4910740c01210350300d41d00c19801c0881c540d001a000e0750902100a14106160000705101101140e041000c0d8542c144003190060f244009103800051000100c2e41d91800d00354114408801458050b16000c03080c0e012a0200780c040e110200507607c50f101e21410002120380002ca078105810310100101d142014009020080344604415550009a4001c1a03094850051840c41c004803c15004958941041d00b069541600c01c2c0c0043d460708c0100000c0900c24402140c100d0001448107040d911a00701c101802d041000229080748860b140140200c1c1d030301c200401c0154029190705e51901d804000141c1034425011032101005000000c2141291b04560801c900161411074000744e4690508100c2c010b0002e0754070748405100301501101c681480342c100c4910003a082d5800800d02d5918001981c0c1c800090160150582013030380010351500c0141e00c89a0b100580d148403542c0b40f07001e17001803800e41d4451580c02510760401850600caa68100605070215040902070142c217402100d60740 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 667215080 1250 667213830 667213847
    0x5060c0304020d2a0603020a0e0910150c0204060b211906032f060a0507030302090405010611010b031b01120603050316060608030a0f050702310605040c 67
    0x460219000300c0031805545805074010141a8030070051440075441c205482c0c0c8802143c50a500141400780780030030414480c1c001c0d41d100d1582038503041c0b0030403694810403240e80310081030458203505481c00021810b603000d81074460510140c640c0c04c040d05c0075005201c01e84032517400200815104020111200d103505140e481c5640c000070000410f51248203426440780c0c00e542c070503140c3c2e0382060b001009000e041ea050000314a850181e0700070480c003514040c5d0050640c856080d80c001000d000c3c003480b05010320000c1924034801c2c07030010301d031004503400030301111020380107040000d00c030700307a0041d04aa0901c98024840c50440050195044400391480404c030040329aa041054140c42e00519419a8010401840c0d010701a02d489800720380c10a06903091000d82a41c2850900c80c000030350407000710807104c10a8266842e40d0404179400c3d01a07843d580f111808070381010650104d61500000180c40e488442202001c1f00c01190111076202c09490680d08400e04c254074080003101c4664200058 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 667216330 1250 667215080 667215091
    0x160609090c2307031103300103020f01050d020c0304240206040503180a050d141b0112050c0d0501030804090e01060b25120203040509160807180801020c0a1e0506 71
    0x603e42d03900305440e00301d400d0702d042c03049002d441c4004200544035207500802d1111401000b0b100c09030004c0c0360400f4a003140d400f840040c2d0001d5050702a00300952250f03000b0300c1e8443d0122030140c40d08500c1d420451955215610400807041400c0c00c1c8004c01c504803103518100421031005140e40e080c1502c8864a03440384039150034080c03030801d40e03000c410380700e41000320010b00c8000e020010040b40c03403c151104d032010600c0d05001d4043c5400c10380340785401c2100d6013003a001c10f03918280014003001b4071100402d0050300c110b030070600c1400360000950f543d00409010790f200e540c1840d152860f01d02604107541d03006041e0940f590500c1c6080c400918081c098940080b01214905204c2400d101032400319403002c41c01400d880748001c900070801e900000204112030080c0c7d00c030581aa9500a465401c01645841c40c1c0000d8160001c104600c1c844c98510803240d00d018030001c0310316580c9200c142264041080c0d800c0641000590030140318040c101d941400c4c0000c08840c3e200511540e6981c0c072230000910 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 667217580 1250 667216330 667216397
    0x305070b130b0717071b050105010e041a0c030103030c06020409090c09052202040c03020c0303010909020a061704200607061506110307030804050718050a1d0d0e03160609090c 77
    0x700c0346c001100300c60181c808660820000c019a5844030030f002d02c0c2013000c07202a190a21000305460440d0b51004103a480f0b02c14240416003903900310707581240d40020720b03c1c058074055000e010101e002e041502c42d11140c0f91066000030441413800f10721200390f81c0c2c0100980c01543c2c5280041d241c1d107031030004015405504a4000645030015202070700203006215120a2501c804800031603144450780c40341ca90039000300c0c1d0401070a40d41c0e410480d0355000d400503c60b44212408007244c0000e14201003001c004184401c03500700843d0810200d041500b140c802902d0399034031341034402143c41080e9500000b800e001e1174a440036071007410500fa62440b071900d00034100b140c3d9000050900c00140b0008000c0c000301c1c00d507851448202e200082c00b411050b501da44000b803a00500040c51405110245012040e84014192040030b000341506c4144512024681600072040a0103444002201c0103014005540380d0100050800840904840300346010380c091002c100310150009810803200c82d1031303005070728 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 667218830 1250 667217580 667217597
    0x9060603070b13090c12060b1905070c081209011b0c12031407030c02011209021507060207170a1103040501021e010e15070210060e0a02070305070b130b071707 70
    0x21510f41c0f240c81ca560004000c01e240540b01100b2a42c480742c00c0501d011006010700881d925585024018845d250184001ea4882802c2203040b5000760007800c5c1d818001c40d04142a69074030120981401c040240c04215840000740019003583c011841012805200103030454000441e03aa41150303009600400c280031954503500800c05200300c080c1100520782142544d1a500c1070f04e000351483c8410744c400c9020070318485000310081401d20960200c550018000900e113565503203100345503072003200c05941d03040d004c1190750003107808960bc00c4128003e0300100c1e985e40924031001041c14103a0f076080764590b0000c00c41044142c0e40000c0700c40120880212525030798001d074040b140142121440c200080c01056844041310500f949114440d403080e400b0307241030781e59581c515822034280e0b0081c0841c020752240410360740101d43c0d003d0084a446410300f240752020355154124080c00480703006054452840a940c00c11151040c05034202501d41001c0011081c440604415030b00300506400400102c030 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 667220080 1250 667218830 667218847
    0x3040303030b060c0115090e030306130b060c011d0c0324100302031e01150803070b091e0a02040c030b03060711070b0f130602070e0a18060e030a020609060603070b 72
    0x321883d584c3c0b40d000800510803001421240140c880c0b00d228102441c02d0000501e03004007208403442160300409403407842c0e001103040030050550a0784680c100c1e0052200101c400d009102d0703c0e81d02c1d088100c05102041e40800802c0c90320a0008005019402c101c400c0c00c9030580360f894201c1c60004003e43c0c0704496840540382030f03203895550b001a41c184960800000c50f4010b0a0300710324002d1b0302400903c103101241801107105041c500c2050b0746a40100404804203102485040c0c010307001800307580c0c0820380141102c90488580381840b5194104040800451501e441090340d04001ba080a00050308010b00003500d03050018000c10510075a500502c5560a00307100580103000305e8400a501c1e0122008445619040700340c100c0641050b40380041038950002030301c2d5044a55030401c07a056513403804503140c0070303207130441951040000341c429a00019043d0701031203034100100c1d0011038071940700102c000d2912a000c1c2106046800c220f0a1040c5900c02060f550143c500080391640c1d1044803 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 667221330 1250 667220080 667220089
    0x3190203040503120c1216110405060109050d06020d02040f1401020109030e0904030c080d0204080601140603040314090a15180510141201061806020d020606150903010501300503040303030b 83
    0x190300e081074403483c0024800a0f07c4190840308403001e014019103078881614909200c00c54100346d8245004c50032001d4108030904d0304141003206a4801c0a026041ca020201c1d100c040e81c1003500250b1103d0f6000009201c49140404c030b6180d4001c00348000d000301ca005840c0584029504000b50380a404440001814140251808290143c2c04121107a030790740740c4074071600250014020706805002d1a03000040d800c2600c91000100400100075618540301c03681c041c0c0b180400310640c00c83d5014280301c0d01c2c07925501d6040034001084140100408040c1c42d9100403e080c980c2e5981549940c1481c8c0d05000d1511600c01c11103440b10703d400d180d401800e0401c04440c10307000760070000c41c5031000b400011448603400803107205480486110004034a8480409a07102c5030a9040500141d020704001100380c6008039280001c05003048540b0324110920000c2400c1d03030800d0308000c20303449411050b03c41c200450b040c6500842c840d480e0003c003900d440c0e40c0d03058581c410391001400300340d11800b10f100c040d0f98 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 667222580 1250 667221330 667221343
    0xa020a050a03050c0708063606010f1401050c0a0201080606130f06090608041109180a0605070905031b0f04020405130509010f0c170403051b03190203040503120c 71
    0x4016049440d010700500d4014280e500c801c00800c581c0c05000e400098200380003555502802c4482005c240c486105076512210b5104001c0c0f102035240b8460207072117114014029180039100520b01d094016051071000041c00800003034140c1001820803a20302407900200c0c408681c558240b030003a01684428000401a000f01500801c0b4008070300b04c00680707034060048040031502c680d2220710940f1740e240d40940320510112030141204d0284405441b06180c044000c5a12002c403034054419006000c0000c2d25200c2c031003608035000341d920b8042c0304a00c1c0d040001580108021030081c00154010b8200320020a61070100d5405801c00d29018001c1d641e880d01943c01801010b8040a0024258500d00000e444140e9540c45203500c1d0070144580d4404900803140805203503141e40400c52007284c802280224028810f50405c002444110700844a81000787c0f9241007000007503480f6164445404880100d0007800019503104000411841d00c020440ea2090411441e526403204034840007a4113148 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 667223830 1250 667222580 667222583
    0x70f02030f210601050405130e150a0902030f032b0f090b07030f050c070b1b04140a05040501030302060f04050c151b010506130f091205030601080c0a140a020a 70
    0xb19004100c62100304002e01080c1da400140100340e290b800065400b172103103001b00750300b12219821001410595410a180c541001001c44201304210324406100b40c90540c0ca03070240e99194450f030004c1d8070f0204025001b1050340c034090351902c0206015607001d1b0707044c04001604003016080102c9158100e0707018019442c0a0340c02030003a80340610b00001205002c07a400404a40703070680030b0781c96008034803495116015241c0302c68039044d401d07224050714680050041c01c0c210b0082d01e14180c070038400c0016200402e0341c07100700241034954a0820000c0511900214061854040104080307540000c24580250356842c400c612a11641815810310785401074513038120514121280e80f54800c42c3c02800c5c0e06401007804c80010000e103802900323070350069804070ba002d400d0024000c0201034a5010480050349180c1c0041d14000c0c9584541001c40308079044408114080100182560845c01e125400300750003a809140000030440a44401050307005501c03015408101c0842e000e00030003070341c20240d = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 667225080 1250 667223830 667223857
    0xf06140f0a1d060705071208010303172d0109140402130903120212160f022e1506030b0a08060106180e1f0506040627030f030f081e070f0203 62
    0x61130844030151180d407040c2c50440319030080c22000700c4a10f105030b04c5603050b20b906030340702092019800c0c19480c0048003e06200380c0412002c003084030310b00c40c203181904141c8140c11880c24070741c0f410708104111040031001c2211001c0340c030304000069a0b4800c900300c4403c44160001004035850030100c414283e4a8042c43c0d0036440050030b07155280f840804244244240031214031b800b80556400c80d0040003d041d0782d00580d20a5400c88640c03c09041c0e981382c041122404c81c00030004030003d440540c0c030a43c5041050103d20041032100b640e042c05090f11005061f03c244003c41d2602095039a5088144107210400104490302100e5507147d9002c00c00815001c240303000141400307148405e4201d924000b801d0041c0c1e44800001d014103143c01507608a4801d9184e40c52000140d20070800c9903c1c0300d9440c1140c0c030210036030210000700c2810a0001c83e80c06a5a4611014801e5201800980f405441041d038030440ca0403111007070340500c01e03e030340c40340c0170340703000c04404c00315100903499401f4140da2490362 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 667226330 1250 667225080 667225093
    0x5070b0a0203070b01171c2616080103020a0e0403181e17031c1805060a0e0c15160c1409010f0501020304120c080a0f06140f0a1d 57
    0x400e41e0001c0036141c00d078010814100a031740d88407005a50044254100c00c40d5411841e60034141d10799030850f80654100c0d0b1704203145d20400d51019170301407101c1e4031282e0280e6000e48050125522410880c3c04030130b401801d0041d000c3d41942c00185030b0082a118905114071781c4c0c400981010304c2030854191082244249a00b43e0361168100c20007081c4081242c980107008031000a101c0140202c51140110b240010750301c1c0a80b10060200280318800d8420089078449951080401c100381612045c81e0284006d484c0504080359a00d00b038408494400c00c244d40400d441113070340d96440000303079402200f40100a0780c485000e50100c41c410500a0080c00c03c0e91103500028042403503090100b8960402c40d942da020f42e80350011420031115500030540142d00600c818800c50100300c0e5042c115900030354044203240d503641041c0d4074114145000b146c4160b4038541c40d10400865008010a10407030b080c801ca01441d04040900c10007900400700d910181c1c68040703454007244a41d100142802c501d6094401 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 667227580 1250 667226330 667226347
    0x151a0c010b1e0325090b010207081b0102070b070c0e04151401090c05070b01050d081c0204180207020906011209020a0b09030f0a080a0305190e0c09090c01050d0905070b 74
    0xa2001d0350548040c024020704080c04c2540028440c1c202c0c144a007141003a64803070400b40703680700401103000014158840c1e00004190700c4c0c000c029010741c0402404c0c10040030200b24000904080c083d512851505006001c804002220f42080c070007960b0f41303080c4210459070f0700e0074140860b104c6100751805903480c00d44e044c9003016140701e035241aa20841d005101d0981050012a45841011406440007039a1001442a8a0030f82501203001d80513a00c1103050602003c2c80c0400d03c41040519103820307600090400c04107601002003041c404100c00704508002554010501512000340503d0401c4105000c5026001c07484c1c0c0001206038010f085e640e0b1064580000004a9004002003132191043c0702d4821518400081c20811150784891038a08001c115101075001d8a8045c1540d00c2030002d041c00504030b40700f684102c0c1000c0d004400140301d07039074041d01448803422000c2c19000054000130006a40b598014048070580c09003d2000103154949040480c1400c4940e0400410301100050006 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 667228830 1250 667227580 667227619
    0xf05040f0b070309050a150e0a050a12030b120a0c0b18120111030f1509090c0111011104140a0b030705070305090402070b0c0706050108010e1b0d020d24051306020313080c01090303151a0c010b 84
    0x582c1107120b4074041c01c006869034400750853c010400c03011710b18002d0541400c182d05100e00c0c0c00c440f10440b40c00124907030007525642e060a400807a03400080302d030722170100300e18001c0241c40c10109a10948060000e800e010300106d8440c200c0c000340701d042c06880c008a41300f41c0f000758003009a440002464035266902d45802040414424000d544a10300f2200c000c501a82c0d148100d902409994440301c0c900142a60180c541d03410600b1680d03032056080c4400c0d400f0501e260308051107060315002e19559030020b450501c04485e0107070080d0105a2410159030441000042c601c006649001c80040040454000041300c003100c040e8000d4101c103203035540100700f0013155040848120f6644d03085080f00700280c0c50b81e00311101210003000300c0c0e03034403030b01c81022a00700e078011500440806460040c0107813a4841c0d90b1a0f61010441a00c560b5450440d4002d060b0715120710144506209030031400285400640304144522442c001072003540090035401080017580402040c81014000f02405000c05d004503 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 667230080 1250 667228830 667228843
    0x4051008100c030e0f0a0318050901170d090e2710020c0708060c070803040f051e070e040804050118080a050309040f05040f0b070309050a150e0a050a12030b12 70
    0x5101003400d02c403c01300c0310b60021440003101c1014a009041100050700c046030b60b144903a400701d101410104000c04c1a07107d0503030441c0a043c400c01c19040c070101e001a024a86010300254074204044014248039006c1407541442c0c110030300741803242501c09030500d9135880d501c003020001d0140c0315501041c11100c0b21600946210b003020016244015a14440940ca4a004640c1c112005400b0000c00b40003491060246400900460000f4040781550340c440c0d2510020040444032000381d081400e00c400c60401101c00a8411180441c0d480d090695070841580114003490741171001a000020b200c3c12001d9514000340400d4080700e01c0c4c08030b141003690b00c9500c0259464003450070800c0729030b021601402136601030b40e84070400341c132042c1450322200d00e5100301400c80b0b42050303103800c03455012510403c504001a40101d500d4581d8a0541d00d4038404c0f180c0c400220b14481e000080d45001158000c079504518a4000b06a10000c00640d0412001406001500c2d6031081006151001382500020312 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 667231330 1250 667230080 667230101
    0xc040209030c0d120906081905101e030c080f030301210512030a0501270b06040506070b06030f0a17071e120801090203010b07080c07050d08030a0b100e0405100810 72
    0x10000c1e4261910786c110b03507500c021200c1461074002000c00c450400c1ca1030f80915840420200c04594040e1120503041540c1100714040c0c2010090709401e00500c800301d680c003002465040d00810150045a00d0703da107078041441502000d040f4040c0605041300c41c00d03a90100e0b80d034010261801e46444054101c6c0c5a002580c00300c241c14a840000b00c1c5410309561880d00e4100741c1c500b01307452050450300c1d500c00381c000701043d1504400d0900c000120783d112400605171031403141400c1d140600e085814036180861700c1702c9d00c0306543c3c040e4039100042a4510035060f020070408248980e030f6080340c208a2540c0f03450300103401c909240800c11100f88000840540d42000e6203580d501c41c96641d4150b854146e010a00136860030001c00c004601c00a030641c002000701e04802e0003580c007041d55820018900c0c9940d00420741d06c02800204021800b0401d10900f1450720048a80c0760403105101401070940146050140c0034a40d02c2000c964a1042a100c0c4401026400201c62032000c540d402c0c480038001c03045c034 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 667232580 1250 667231330 667231337
    0x70609120503071803031416060e010209151305120f0d0e040c031109060c0f032a0102030c070609020d02031c110c100e1c06050717090c040209030c0d12 67
    0x100b20140001c400404c0403a03030581e60b08548a002c2c1448100b16a00c4403600e009882100142040001c000b8080c2d1150203028100058483d000c68081c0700c003031010701405858014040090500c0b0300d090903402001d0342d01c240e641d15080c40c0400300c040c0c540701300740c00319220512507110400300340707a40207910a03000c00c07060760f05102e01000e608041d425120000c5401c40300100912001032141000b01c094034025404508944661582062441c1150300c106c15103182948840c440c1414001200c155184140d450b5000b1483c0d80b9004d20f016000d400703800707802014103403264804419940c41030341c243c0c8817a8000f802ea82c0d540401048040300e045130040810045500042d555644079000700b016035a060000e05642510b1a940c00c040701c2c242501c116480d8800100d040c4e440030801401008070303d151245030300044900380018041c2048003501902c94070303400000c00f0042490700100701501e0684017540d002d0b8603202d02d00c1c00070741002662800b00d50080d58100c907400512051080c00d103480e0300941c4 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 667233830 1250 667232580 667232597
    0x10e010e130c080d030f20030702030d060e06041103010605030106050904060e13110301060302091825030309050a061719090b060a0605070209130f0210031b03061a07060912050307 79
    0x115010b8440c030b8007024080f4143c04c0d99947c220300c0513900039a480b5006105403440e09014102c80800ca0703503141c001141880480c01005605d05041c0325920401d40e20035102801d643c98104d0060861205005820400c080400e91303984c02d896642201000e0410006072840601c0c00c071621500d080e0100c90143d070068000301d5032096904040c42480262600644480aa0355803020034110002030945920440c1c0310b500d240402002c41c2c1180010800074000551034070701d01d1400c000300705c61040d030403291080e038001c4000c20000360030039001c2d445803008220702e11036542c4000b10000d40c0b541c4540041141402c0c040700d039040002141e00300d40f0841e42101c0c40311038640c03103400072101030194100003900002d401000ca6001180c681c480b80141d07100b45040c1c207103614158007141001c100c0c4000c020209445042c0010203820000200950500c10308d003c0003410f142405185200161002c0700d4a50400001d02c4018410b50f82c102c10304064000e9070764004030b14070b0440203020341c1c000c50340b400019041c00b = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 667235080 1250 667233830 667233851
    0x607020c0a08070506030411061b06060a12030338030601080a03090e090c041407080612030d1a0d11010219050a03030b0609040f1d06010e010e130c080d03 68
    0xd03059001500d810700000c0400381d003000d050017990b46c8080c005449802c880c030f042403015580d00c030040064111074080c0789180c00c0000d040e180342ca0340240246104078483c44050120f070b540d451491201b90303058607012030448511118522003140b400c019104000c00105901010700f040e40104000100c15821075210340e913110040b40d03da800c030f084014001101050108030001d0042d04003900011020242c8803549017800c000b60807038184901c000190380361202001980741e00007902c5640310400f0b0b11042d14401c503a884064481c0708070301d851108541d071074401741550700e41481d01e808425400782443d9030158903402c0106a581d0200d60883c01441644800c5444100c91540424400d9001c001009010f1844d0703000e5000c0e10b00c0d00c03091500070509014003142c0b075460b0b005a48098440310400100741400303c0051180c1108958802c030141d2000740100901d0319002c2150b0b04441040c011a00c0544510344d180a4500007003070050040c030718150010544007804202600d514050703490800070160217 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 667236330 1250 667235080 667235089
    0xd05041b1a0f0a1205011d01050603070e1e190306110f0901030f1103160e010c0f12021207050102090a1706061003230a2712020a12020607020c 63
    0x440c0004640e500180050402c040100c40a89568101403c1490203403983c11092400c8030b00c268041065484944030800c03040340c0c594000c90242c1420780d2618614507200f0030261414019540d000d000b09000b20490b07015030b00340540f900d0000341c001c0ca90030310250b20b140c0300100c0000c280402d45800b4079112070403a5a065100803502042000b0158074100b0f0962001034000308925120761041e140c40300a16070400c51080003c1d44205003048100e904445081c4004198900c201e00450500208a010342d0104081d002d424010f00e40c004074407000c0d03d0311002c0481c24120030b01000082c001d00030420070100881034010700655401594070714034950792400940c1c05180141c41e020030341e42100f004644141071a510003004042181008140e01301c1003c1500d10001005104000c96070404081c40112512801440790b40c940406102501070003049008203110110180180f848228025031840a4007d01640041d50340002d50000b03035005c1c00c0e03c0651100012031b0002d005014200c510380d42482c1 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 667237580 1250 667236330 667236359
    0x604020f030106060f050f130303020a1406101403150403050403050c0d021e0d080a0504030c0b0903030417012a021006080d0f02031213021c0305030f0402060d05041b 73
    0x240390380e05c040341c4420301005e540caa400005580d50101007008000307501c4416004641c000c51099004200030385031400c20418090511020704002d800000031310040d600030f4641d03041520241941900c2001303925000030301d80b4004243c80610a0f03024400c00051541010141c001c0f0f84c010400d880f90004001d007040190302521000039030180c07640d084550640c201a000b4a01c401d0302a010070746070205512080380c240c01442c480c0700002c0f4001008c2c8104076400d0002001840004040c1d41030019040c0000c1c1c4034040c500032180c0715030071980080441d500942200300001404036100c04084105181407400030400c1380d410004d803168803e10140038886114801c201d4010b0809810084030522080302c40c0e064a108907402c5210a008210f5502d41032000c0d2401400600d212104001071031040c051071003840c2554805603104101d100011a801004481d40716000c500e00120039950b900c0040c0460240c022802c001c6481c0034204420440c20a180380500c03034480504054040d40c849414071841c0 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 667238830 1250 667237580 667237589
    0xc10030219031416020a02090f0a060504060f0306021606052a3606120a0b010203130b0306150d4803061d04020103181a04060f06080604020f030106 65
    0xe080790004c0c42c00c0300302c0820084001081e105440c192066500000c07a29042a04c02c01d0414840100380241c0201c58851100100b1041d50306020141c50144003401551480c070000d00410740003e440940082c0c10048040c00940c03020080105040c06044082d5400d10fa200c0404d01644003401e040581011000b91020901d01104894440154020710541c141c05e107800c4011043c00d00b64070b59410343e5858007400d0714400312074900c0c0c4035140c082e102d00107440d90184403d06640040224003e107400d006480c0c025540c0b00c2c040030b87d1303a880b00d40125203a000c030014015903103000403c641025072021707000710010040e102d00b611030b520b00d003030b01c10340f000310043c1c0ca080380220b40e00c0c0c51031540c084c03001d1080009090a040003d107442d529040f010000c0000b281c01010b0500701d004010840da0180300320880100424080e5803491816555102d07a108242100c040349003090002404020310350300440e018094805040c44090303624454955659001e840803032141084041c20041400d051041c0001c89 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 667240080 1250 667238830 667238861
    0x30b01060e1e0a05060a2c01091502070302060c0105150604360e0d0207080714060304050a02060c07030303050a05130308041505040b04021825020c1003021903 70
    0x4041c0d1240c07800042c40710301e02042e0040c1044000290a580e85030141c4284080354a514081a001201e10713032028043c6030700e500740b1034015144900c43d030340d210000c2c0c8252084900d03a03142c0c84c0c200b0311080e8944606030340001c3d4018000107401c01d0fa0384041d00140e0040c611a490355100700310b00401c0100c14016400341480c08208800a0b0804032020562030020300643c041c1040305050404808050780c0320034000182d42d60081f1416000c05c2da0410090004203034034400b6107400380c10031201c0403036034046444141c403e80010000c20280300d000d000c00c0c08040c2d402081035a03543c03007041910391280541e2000342c0100c7e00c0c1800161502089020f82482041d40c2040300311410b001360307801d0380c0c610320180060b0f80e518001240302c4003216052062078080c0303003e0021241540341c98410003000c060f04a0b8041f1803203840100784007104000300c807100c0d55080e12a40d109c40700712038684100d1900000106056005685443c4107800e1034040d802850703c00c215805486001907208800d4041ea8001400e00898 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 667241330 1250 667240080 667240099
    0x303022106031209131503051005040206030103061a0a091a0a0b040302010503070516030801150c0c0506030604110f0304060c020a0305070602280e03160b03010e100e04050304030b01060e 82
    0xa0f5100c0e0060080c142c0051540b064060414081e00803070700210301e188105000b07084248140002000141200e0b401500b00740418074040c0d021898601040c0310082100c0e4965030946911088208000c83d111006401341c00c1d0326986000e2000174203041d100000c40803082c458a1000c0e410110f142600f603401d1002c00318a0145540d00456099200420b50800c01000303010080221a00c8036003180c05502954603240d180d4181145540e00c0441d13044014248210900002d0004031500c085c0303000c5410850f91640c80c0d03501c6502090240402600d40556548001840d41150350301d10040d45c0901e00486040092004610742a640e5049000b405004960107005060024065800906042d4030100b804000008526450781d220750104010001003200c1c0b00348107055080800c400820350b013040001c080300525007072510b0098441030080c842540c07242d42c0010100c240541c0c1800040c0588021034111f45054284280c50b500300740811286c030301e0b07004c000180c40c903c160380c601e030715103802400c1e41c40 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 667242580 1250 667241330 667241353
    0x100b030c09030304050a090903020c0603090607031a040e1617060c0d0f020c10051b04060804020a030506100321050301060f0e1e09090307031403071407030302210603 73
    0x21036030410001e00398035202c1040301007074a0b1110000e02c402070039074010103d405c09003480d02030305013425160014001e42040c03080100704600010695001900c1c1e04000604100c010722407101c510340a03940350b4005003000541212614000b49441c03084070300d01c84458030705450301b07020b0341c04480f120107030141c6a1200000c2402041924002c0901e0808400001034600010345142d0982e000084030451580124000006a0b03a03640143c6031b04c072146010340e085c608aa40d0140c00c0c0c50040e030281030704010550000404544030781c40031030044d6400504803070440c40c00c01d03181c8248450301d000459110150000d003614140c070307010a20b14030360069180e030b50641c4e0030500110713000b01040640340d0800040d601d11482503100d820b90f1000000404140d078a1400302c184c2805941c50001c0e100380807030b41c400c00c4408042980600045070703080c2d025805641e030340c0b54454100d4080c26040e088101c4060300154140c109a05903004100d00d00050104400840b6a00030100650a003202c2d43c90301500075408225 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 667243830 1250 667242580 667242601
    0xf06020c0d120f02030d0f05012301020d12060314010c1e080112020315071d0d1a18030c0a0204060503060f0a1d030705030909010b0304171c0515010305100b03 70
    0xf0744000039071040301d003000111190300701942d0418480c80b00a95070f6400520240560300f640303500030000d030359120307481186401c0000e54491100030128208480e0a0503010200059004600210340008000407240440c4010301d00134803821140300082603402d03904044035004086201055911521002c0d02c0c0e03071904400058aa244440807070f03150264281550001201ca0030240c02000503941d688450b400c4480780d210f140d046c04581602c928a9054508002000301c26405100400e1041800d15520303244003804210350a1140c0c44640c1c04046800c0110070000680583c9080c000c503001c1c07250710340e11004d058031460180e0740025400b010348009004400550400d1411581c00e034842c01561609003801c5045800c0324004461640002401361094507203070340b483c1d0241c5a00740e0b4076890360602c0c2c0c2d120360031540c41100e45210440c002c40ca04212400031440c00086140c034140c01c0c8000c7c600381070010800020b031001140480e00d00030109450881942c0124151001400400d1a5407514004503 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 667245080 1250 667243830 667243847
    0x6150c070e092a0406052b03030219030b09070c1707030c0206190311041d090304090c110708060c0d0c0203040302130209031203090c0d0203011d1c1d131103010f06020c0d12 76
    0x88d002d054082258040140c40c08400307a480d2805940c002645103c00c1040210305400a02030303004011010400b100442e40b01403055000e0f014003000b26503580210314054501ba601301074041c0d0b1040700490700b2100542c0d03e0440408525841e9000c0095030391f003017004010350095000c0c01c0108980703410514000e00d40407010310b8024030001d04580c00c00f907440c0c0141041d1443c500340040000c221603969045a601000283c0140c40603070090030552526030096140b500880d85070002080e100c00d020410f00b8000d00448000d95000303007910004003c001c9100010b580700d418040d002c0d00c110f481c4050f040c0302100075030303002d020704c5005003250b002c1000401100c00c1a1990980e8155602c1c511240300d601e41051100b08800288040c0c2946a41c41d844074a00d0f9400780a01c005000c4065104030840e510204e0f096071030102120080e4411000306001380040c010b00381c100c02c40b0313280000040ba60b40642c00015040700d20329421a1500511502441404020544001d102c0000242c00191150150740346 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 667246330 1250 667245080 667245083
    0x120606040e040204090c0801050c07020103180b0610090e131e020303040612020c06041a0a0e0606010c150903030b0f010e0604030f021f030506150c070e092a0406052b 73
    0x4622a054075105600d00719127041d00c0d102c078110000108a402c55800d405a17031002d18115030b41c41d143e0080750b181c1e4044004000d114501c100441c4080440e114010034500019103401403002c207652a18030f002c0d130803180c0e4104c3d0503075000c00f0fa52544e801c0d481001150152480d8080c0c051802c040c13070031005851502404101c40d003101e40074019141a0841041150710450042032007450101244d5021b5500c00c50281000c0c05040c104001c1d10700e0700b0350004045400038402e190010745060f83c0c1c1003d1010354240488806924202071a031803c0c5581a005a00400800c90311034200c02264001511003450741100c080d00254144401c02c00f1926101e1034049880c0003500c0503074007190000d103615541d000300808101180e900c80034000b81d420040e00e12001c0ea0450070300341e403400508060940d07903140144140d03640c403121a000250444400d0101b1030340074000c03800121103110b034054216042108003821a000b140341400001c0d039481d04045a0341034000c0411710b5540c201c080e01c83c80321b401107241c80 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 667247580 1250 667246330 667246343
    0x14160e06060d090c2c010302010c02010e030d0806030607092301021c081608060d02091503070306050906070302030709030f0c050a09090312050c04060c11030f03120606040e04020409 80
    0x81e0345800740c907900681010758440c030801c1a5190400042c590717180c500c03102c0c03ca080c065801c2d0900400083c0038003141500d40900b0312124400007440101d51f860307041c5032901d405000c1c0c1c1010b445001d400800c0c03d40560001c030103a48032a55040001c664603802d512842d0710800c01c4403280b11607920042c4100c1c44260741071044e100740c0384294141c03500c800b0002246000043c0c1e04000c100030805c03041740390000500d661611412508040e4002000b201c02100040d1240b110b61002c00c5034000e1031190044250070190a580c5019a039040c04001444125400321060284c6400503d50f18804c1c4200c84c0300744030340d40301c0303c1081d4190f07111943d0900c4001421208205407140c04580d568445800c917004191452003c02c2c03006082c5001014002d20800112455040c542480001c156003819101654030703500c0d15050420480c28a010102031038800660035001e06e01c060782e84540c0220050084200005041c180340d00d880c402d2100340d2084d441b074031a403256a640480c0040c075258101108880c0202d2 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 667248830 1250 667247580 667247587
    0x91008030301060f0207060305060f010e03160801020c060112030807081504090c0513090b181c080108070e01030309030b071e0908101103040204050903160501050414160e0606 77
    0x2818624603070081c0c0004010490400c403a140681d81041003602070813185c07409104030304260000c102c42442e40c0c40c04906000d4404034103038003901d080002510000160805002c0c8981c1c0f05c1e1604e000b503020304488035440c006c500c000f003410600700c5000c00500307500d42d9400346543e403450000c0710ba81030b01822195400c00c0c00f419035005980c641c081c004400d80a04d48a4950342d28020030400420740061700d00c81424140138084001c9803404c0605580000d54a010301c0c002c1d005030b00c555080c10000a80b00c40c4000d00c400c248200c0e154050070071416a46d000c800c4580030340d10741e0f0741c0c002c51190910000700010150201400003401d084011500320a1505040e4400c001c00c80001003a000301003040d84c0003074a060410000008100300800404200e0340e020425030598800044203480000e00c068020b58407003012a03080300702002207443c100c03000f402800038400c5515000f4042c1c4811342e0705561158420507003003401d42000c100d5040c4481c22190307000640380340894003000b06400400d641ea000e030b81031 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 667250080 1250 667248830 667248839
    0x2110053a0609050d08092b09081002030f0702070b09101e0c030f091d10120b0402010e0906030d08060f03010c050c100e100f0b0a061d01030b0a050910 66
    0x50040c05121407040303024061048040900604070750700100703007280c40e1f401b0f54406101c991100b40019011040c0380c0799800e07904030541050740c0320344296200102a104a4087ea001060a40c4c00345010340c003405222030590704c40b03803400c0382c1d01d04140c001c2a00c50501040904201c3c44e108030000300004d81e03810001e80030079031000d80380ba1461901c40c1c020007240b81c40340d002d800c15074452304c0c0c400c2114245c00c0020203a41409850031240801100e1240080300c02c101140b91740e141c107907003140108020381c00c95079403003118030304925100020340717040b0b001c5811108000e00c1d034542241c86a110301800780090603082862501200c4803e4042c15180e003001c1c80c925501400c0e00c080c000e1921000701500c1e85039840c003045140929080c1841440003a50303250012001942d0400f20303051865045684000c00c0303080100d00b520000300084895154800c00c89180010146d0b008030041c82c41c101c0b1003d0000089484c0b03001901915065007040e5402031282a040c091403400c0007000790080c8014201d0090716446 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 667251330 1250 667250080 667250093
    0x60501170417030903070201020c1e0108180102130305070503011812140c0f07120f120e0604270509060705071707113102070204022110053a 62
    0x140c41400c40745d040007800c0025035804000c00e00721000161800c2c603004280c04050300011458a00c03c50401ca20400401c0021a4203d00560700c480400000c556403046000c5070307a200310080c8000c5850f4026040300184ca0300c0c047c4100300381d5802409032801c0c110161781d582c0c94000a0103c45009000e90845104040c20241e001707030401d11100d0000303018240f807042c0300c1851310a9980c840c50420380c00c1040540044c40c1203400540241d8040a1080801111034080d2400204001803d8024001140005074041180030400d1444010120000c8010121005c02c0558104550031410356001e400401c14151164005048041c012110641c0030360f001415258260300106007901c90802e00d00458802c0d180091030340d07100590342001e0350f4244244a00001245481884c40c600741c03a4040b0b401800d44d181d58040740e040c40c05000b100300e6032084511a40c0300402007a45c8260001d007030000c000c10070b4280724031070220480141c05d0a0400d06050901000c1c807903144100445415200e00461000895 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 667252580 1250 667251330 667251337
    0xa031115070e0f030a020f04090203150a0f0f0207051c03140f041734020405070206150301090c0302060a0c1a0405120301240225140103060501170417 66
    0xd0340c1d0758104031040e540d02004034943c0c4080c1002e120743c01c400c40729001651020088419003400303940125001502c1d00000341016400c58207008407000050801c01c604800d64002c0070700110390741c0c2c20407241001c660030000700c1c094504018440d600c0108103c0d030191044100119030901858049110300174100e03203003100340c01620a000803a02d0a8188020080341c1990340c1805a41c001245007040a0040700004d900b100e82010a07441183e2200b01c00b60100c0708140d00080c54018200740514140f40d03000954454084a8007529075000845000c800c3c50180600402a42c00c500b04040d5a820f5030200f002c1030340302d4030090081c0407c5070030607000201c8401c3c95010110050001078000e24090801c80d0601700558031a0840040400040c03040c2e01900380301000c1990055803800603c071007003500b81c1ca0008401c0103003040505030110048400035094070441643c1141c42c030243c0040c0e518006606565a03801340c240403c0058184107030a084e0516a40d44c0a80200307160040a81a40301c2030790070b9030 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 667253830 1250 667252580 667252591
    0x10906061b1106071b0603090b0c033303060f0601140309010e150115080103021507112d030a030905100c020d1109060a080d031d0d09050306010603020c0a031115 71
    0x1d40d1082d2500d45c1c102d4494042c8000c05040c14140b1628060b035440752541e440c0181040005400840820390a251102c0094101c5034150401070f0318049030024006000c40111189100f0301c40e41000428019260280034010304040e102e0040314405a220b00c0d202d900010038400d040d650310000079011540410004070316507034550070141e85504200c0c20008000c444c0c4800c0041c048050010001600c820008290440c1c440300c041d43c0320341c06840c0020f81019500921544000c10754000301851007602c1c038148080e1a0b07000403003030001640080c5502ca4242d000090045140100200110300f08044560080c04451420020b82d801a900085d4210303001074043d24000c031148402d13659418100c90664004500301d5140d900545842c41250381d034041c3e01d24500406031102c0c88100711416000fa00c9903940e01c1030064034202943c8810040400c000e0740328942c82446160000507a82d4024401c03202c003200c5440103041ea2003000d803001d07540c052004840c0d104a01c145010380307000214a5140780e000d03a = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 667255080 1250 667253830 667253843
    0x70b34170c03091501050a050904061d0d0905010c0218060310020406030c0f03090203100216020307030503070203010b06030123060c0d0e03010c030c020303040f020a0506030903030f010906061b110607 88
    0x203007041d03c4102d00e090900780c13075409407800c518018803060740c0d8043c000c0120f40c0700b140d006001e03955500e0014090300d0000c0120071074050105050015000208008055040c4d50742c1d01038091342d41d100111004403d2102c041c0d040010000b00036035141d00e140c5603d61084000d0221441911589200c0b422a44140d1290b400640c0d1010369040d56a40203030803500c948058541403088550b10380000e6140c40c484031100c2d41843d80002d031074aa00312041da8400c4410740040958024503039906106441e80d00008d4201d10075441d000944030689408401e07241a130301d01c059005c5004003d0a180f400300100101456800207091126244414040010440c03008156036140603c000c0c190a050a5074280d04504060500344419030300c00e41e90000a1300d40c050b410041d9660b001300c01d400800c0c200c00d155001140c00c8100002080a95080080158001e42003e220741d5103581e40c4e0b8185c90226801030007203000150941c050f401544608010022405028038841000041c00c0c0000540651103410102d525 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 667256330 1250 667255080 667255087
    0x4060906110313051c050a0e04060510020705040c050f0703030b03030d09030309030e01090b09060904060e0c03040c0f180915060f0303030608061611100908070b34170c 74
    0x10400309112445451040c1c22120405c400300303a01c054035901484d0601010400614002c440e00e56490b000034008120140480d4120300345400003c0d103518103401010300460401c0d480d9440c041c40340b07044840185034205201c0c01d10344650f90441c09400003a2010364035120510a0000c40c200c188a42c80308540b2a48001901c442240303000303440f800c1004d0403a0b040c091080c0d01040b000c810541180c0b0f5103001251295903074240040041c00a1043e50450201d140c801d03801c22962212a40c01035001ea0b00a01410348256650380d80f544000040e401059484030300c600c80075903030000700c0e00030040c040c2c0b094100750700c4e0350314078080b1400b1281d2075482400c801c0d64a0100700240360f0103120702d60180c4609005440149880c4440c003c1079050701c0812400c01414100320a50031205001a8011008001081c0002801d80c10480116000201d054405003030400110302503403090602c8400036840b50070016490201c0c0006160842040c5c4405024003001c00ca01d6007a50340802d480306d20901c03c00907521788 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 667257580 1250 667256330 667256333
    0xa02070509180c040b0108060d0f0804030c1a07080a0c0f0b07120b030f0606091b040801050604111201030204111c02030702060f040c030209100b0307030b09100e04060906110313 78
    0x29200f261001140914580203400352035980c480e504a501c40741c140c0754907000b03404619003500803032000d14001c0c10b003079008280072040040c45032000080b80e0981d02c86420320071010400b401d5a115444000700210f50030000d030020300d40540801080c050140800742c8032000162512800d0319012a900b50008502c0c100e68180c1280b14030034903142c140207038010300021840890080e034614004d0720041c812001100000c45084051032000000144281c1c601c0e113540e0795041d401d01904098810621483c01c0c014643c50242203d0255030242c003424600703100603481c54081c0070040c040200c1c2081040010003c803052007502088040c03040341c15050050fa64a07001d00000d00b0110043d140b0f06203150340f10180404900c081160300140c9030125400c07107890701d5100707941200c040f4581c4041d048850100410412036090760101410000640701c1110543e0b680b4654000003032075004512b1170610f4500407501041c1c0720b90014490900c42c01002500303211081040710560001c030f88100b07001300204980700 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 667258830 1250 667257580 667257583
    0x7060c11011104030c1a0c07090e0d080915220c050a050f01080c0f0409050c07142808070602030c030a0f090f0308092b03180c05060a0207050918 64
    0x214984003a08850f8200742c111382da03900502007244652203003844001d200385080c41845040f92182c2c4519070440751000e540c0c500c0300025004003130708079080b40106444558424051043c8912070310b03090b80681968a04030070722000c00c00700036016120003010b860072228181400e010f0b1144482c01010300d100518a010100221007140d5003155004541100010340b2a903008a03a407508400c3c100100fa0310382d03403c80011503142c001e661000700080d0238041481180d401d40c000a01105014828501d91100000345c0d41c0ea440c805104001c107014101e0700d10303001c5040e0030f0010303010f0b20384102c1906182c07202c903844660aa81064829041c403900c00020301c40600035521400d030711001100c0050081a01c16180d005400c100e040001c0d00348110180020551003090040c0e8982007403008450361000754150924060304641d45404001ca440d0000710460b80d80b49404002c841584103401020280c2040140903072a040b07090081c055114050011699551b05000700d849080080046880001400c1e400ca = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 667260080 1250 667258830 667258841
    0x609061b0b13140120070222090b2707050a0b07050f07080601060908160509060f130f0b120a0f030909090503090f0d02090103020609060c0f0705280905070507060c1101 74
    0x56030403c0070800240141c6a508c001721035032041d1016109412403450800b4040c01001d980204007040701001c006966440300e18a01d100c1d010031401d441d0020b00b89110139540c00c03072030080e141c0c040141c0c481084891104401844030310312031301c16112404990034840b4504244e43c2c00030a0030760011801804526409a4a84020050f42e030003040d0350140346104030103003407281c0109070050212a00261884d1205000c1105a05010b0203440d038034855060214020600c00503807001c0e883c2040c801c95003514080d008c044000c4c60315405044030110507503070b4a5041c070b4409011024006e00740c9001034000c0d01441003904950148001d9076840c0c00310700820003002408000c0a01ca03c54510070000561144640030b815aa415203100c1d946003076010025203a4090b22148640034813403991030302e0302031070301107416030407140280e4403401144610f14a0071032401211650030560408000308110070041d60700801d40086460410510f45007142d124074040d03459151000001c00c10040004403584030034800d4 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 667261330 1250 667260080 667260131
    0x14010503150403050301120f1e02040f06080c04051302090708010501030606050f0306280b0c330a20071202010b01020a14010605190609061b0b131401 66
    0x140d01c0c03a8942a03902a100303003c18040d2410610841035003900300300c101030050081c02d8020b4001d91700d40e0030382d92081800303502c07003070b02203024500b040321450800301d0f00c5c040d51040d25100c00c00b03008610905000d10004040080c80161078151603141540944c40d9030340c900d8060360980c1d0300e40ba900d40c189000982555160362091003080360410680255a00300d10640347c000200319400c0d11442401e40240d501d00703078540c81c10138105d11050b400140040b14a001031100303448510941e142c444050105000030449400b080281d4228a2a00e800135902c15100d66030100340e501c0000340d406540321102204103000340301d444000e100091040d0030b1110b012100080c18883e403000f401a1008800000d4070703001007410040164854100c80d46607a68207411500150030090031107042480a000c5502040e101c0340310300800b140340302401158a501c01c480000c0701d04081c2c0d0390100c4d650786583e10544100700041c00d444441c440a14001c1c000b41c80145100c0c0c080141400200f5034441d695048a075002030102e0 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 667262580 1250 667261330 667261363
    0x40813030323041d060a0306020d020403021302040e040311070e07030f18082b050907051e150a022103010609081507050306061303050303040b01050915040209120114010503 76
    0xc10a040b010340701c00c00b5003007607070070714413600e844e11008600c11614980004140134008240d40951913200e50160040f00d00803641140c52907003940d107003403c030701c44e0b0300420504210f0b4000050109005030b105a14000282c422a000c2035070314840c4801c89081950b240c00003e0704e0b0f680000104880780900d100c041209240c00e10140e0555070340d10050f00c555010003420b0122120314660801907603202e000c0d0030254840500c4a0b1600122540e01c505460044620a410030000540114010010f460002101a01d00400c134841d6010b054540d03000941018110300c5413020000c450601c19004000c9280009450703512541003080c09084850150840400c3d03038084c0902d80c480010b0380c01041d0f0001d403241841e50360b80d110000030031854840c0240b801e03200c88200c80c00000704880040118403e0f4055060100140d80b2001040420304090f103010f800e84050501d030002c0d03407900798014840640028003c5841e2509505d020b800d403002001c00c2d0080322b00c2c02c80100300d0342c00e080c007801c10848803901 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 667263830 1250 667262580 667262587
    0x1911010b130e0f0105040b0412080129040909030c15020915070c0b0309061012050a150f090803090c030c060412261b190b040813030323 60
    0x24041040001078031401c048194480c129000080b2090008181e40c010500c001e10151806051014202c282076808032841c80e1140d400b002000d1040385400c0c1a01c0b040c0001c45c1003085200d0040e078400518100768241580c081100080c010107500c90a64894440d4881caa41031007142400c004000540601d8651680100024001c0390f80b8a84401c004803032940d4400d459510b1410324440702c2c45281c2182000c40c0c0c0020501c450340c4000540300b44180b00c1c070a04400d84989400007811290309050300101281e1110070f0500004034404a000d41011282c03500050b80700c070b400c0c9410240c542049045d03a1102e0008140f003140c0e039081c03114103a83d00c8140e008003618040700300490361504c154850407a01612841d0700c4401c0015003441c6581001d90100d01410303e0101408d440865071004c003510b20244d01400302c000c05200040f075000c41c040103401884040c4004e94880e10a045401841160044400c00070804000302d281c0350880074501039554030500d484030302ca20110301d0000074000e01c035405051 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 667265080 1250 667263830 667263851
    0x40b04290309030435100f0b01080402090405011e0b0103151212050405100906020c03060609070f05070204140f0109060b190210060306230910150308191101 69
    0x811107040301c0b001d04c12101a6040305c01c40c13035240c1c0d4281c0101030440f668182c0314486010001608040011542000c0068044201c082e00860b090003444a020800800c00174002d46000c020042d032140c040d50000c42ca140410003445068400c621260800d90356541c0c500005d541e01d0b1162009108000007450703030043c1091040740200b03011420051040d0740035031580032003601c5170f0309480041c1b5014001da1f5000110004c082d107400d180703003d89001403280e0b8403004c01524001443d03a0003140090050881511000b404542c2e8621642c0030105000b0108410307001620b407440760692022107103100d0030741070038031103d030010b044d1041e880014030700c3c144501403100020f01011504046030368900d00c1c01c05030501d50103074186589060b058084600d011000824450300d50081c1c0c00350020303201d908540c44448441e0b850302c8481a180044513501041301c0041401d801d41c040403280340d10881ca44c0c4240d070b0300d80d204071090344001c10104002c503101e9031414215030040c0310f011000f11010300921586944 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 667266187 1107 667265080 667265083
    0x261315052104141506040c0306030203031b0708030304030f0f09091503140a050705120c0a03060b04050a0b060d0b0a09020705010e060601020601121403040b04290309 73
    0x43c03100d154000e00c40031520481c07810680800c0d080584401d400d010007000181e0000c0c1c140742da0340c0c40201c00b5980c10400703044c003440c10003000090503d0b00c44905040444e2540220015801801840300083e0008a144c40085462405a44108060300102e400e9a020b6115007a071034648921910040e8130185400d003a24000e10000f6000300008000c142c1c2c07024690030140481c0c00c210340170b000518260b00d280642c5007041045524048005001a8100c002070b44101e40e80355440f0040712160800b80100e41e44003000d10303c00c0100a4044022500030311a00c8001800c81d591100108a40d942d02c2601e500508002b080464540c111403602c10300030404e103240c2d4801441480002950b56100150403410f0710300c0703400c819040d5400ba5507002030480a40358120068041800f020405a1026000d0701c010400140803090607400c00d00d07685482501040d502c246000100104042c8010 = true := by decide +kernel

theorem cover : BRFrame.Cov 667086330 667266187 := by
  have h0 := BRFrame.cov_init 667086330
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667086330 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667086330 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667086330 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667086330 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667086330 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667086330 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667086330 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667086330 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667086330 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667086330 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667086330 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667086330 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667086330 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667086330 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667086330 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667086330 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667086330 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667086330 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667086330 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667086330 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667086330 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667086330 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667086330 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667086330 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667086330 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667086330 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667086330 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667086330 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667086330 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667086330 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667086330 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667086330 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667086330 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667086330 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667086330 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667086330 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667086330 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667086330 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667086330 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667086330 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667086330 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667086330 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667086330 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667086330 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667086330 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667086330 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667086330 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667086330 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667086330 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667086330 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667086330 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667086330 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667086330 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667086330 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667086330 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667086330 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667086330 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667086330 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667086330 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667086330 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667086330 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667086330 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667086330 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667086330 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667086330 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667086330 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667086330 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667086330 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667086330 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667086330 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667086330 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667086330 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667086330 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667086330 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667086330 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667086330 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667086330 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667086330 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667086330 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667086330 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667086330 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667086330 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667086330 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667086330 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667086330 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667086330 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667086330 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667086330 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667086330 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667086330 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667086330 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667086330 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667086330 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667086330 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667086330 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667086330 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667086330 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667086330 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667086330 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667086330 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667086330 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667086330 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667086330 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667086330 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667086330 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667086330 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667086330 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667086330 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667086330 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667086330 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667086330 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667086330 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667086330 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667086330 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667086330 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667086330 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667086330 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667086330 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667086330 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667086330 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667086330 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667086330 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667086330 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667086330 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667086330 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667086330 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667086330 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667086330 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667086330 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667086330 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667086330 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667086330 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667086330 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667086330 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667086330 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667086330 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667086330 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667086330 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667086330 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667086330 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667086330 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667086330 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667086330 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667086330 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 667086330 ≤ n) (h2 : n < 667266187) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
